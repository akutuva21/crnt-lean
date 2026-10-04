#!/usr/bin/env python3
"""check_statement_drift.py — did any theorem's *statement* change between two refs?

This is the tool that would have caught the failure mode this repository has
already suffered from once.  A proof-editing pass can quietly make a theorem
*weaker* — drop a hypothesis, weaken a conclusion, turn `h₁ ∧ h₂` into `h₁` — and
because the new version still compiles and still discharges its goal, nothing
downstream breaks and nothing looks wrong.  The theorem keeps its name, its
docstring and its call sites; only its meaning changed.

`git diff` cannot see this, because the diff is full of legitimate proof churn.
What is needed is a comparison restricted to the **statement** of every
declaration, with the proof ignored entirely.

Usage
-----
    # the important case: what did this branch change, mathematically?
    python3 scripts/check_statement_drift.py --base origin/master --head HEAD

    # between any two refs
    python3 scripts/check_statement_drift.py --base holes --head research/sr-a4

    # fail CI when a *public* theorem's statement changed (stronger check)
    python3 scripts/check_statement_drift.py --base origin/master --head HEAD --fail

Exit codes
----------
    0   no drift (or drift found but `--fail` not given)
    1   drift found and `--fail` given
    2   usage / git error

What counts as drift
--------------------
Only a change to a declaration's statement counts.  Re-wrapping a long
signature across lines does **not**: whitespace is normalised before comparison,
so this is reported as formatting, not drift.  Changing a proof does not.
Renaming a declaration is reported separately from changing it, because a rename
is mechanical while a signature edit is a mathematical claim.

Classification
--------------
Each change is labelled with the *direction* of mathematical movement, because
that is what a reviewer needs:

    WEAKENED   a hypothesis was removed, or its type was weakened
    STRENGTHENED a hypothesis was added or its type strengthened
    CHANGED    conclusion or binder types changed in a way not classifiable
    ADDED      the declaration is new in `head`
    REMOVED    the declaration is gone in `head`

Classifying "weakened" exactly requires type comparison, which is undecidable in
general.  This script therefore reports the *evidence* — the set-difference of
hypothesis names, and a diff of the normalised signatures — and leaves the
judgment to the reader.  That is deliberate: a tool that guesses wrong about
whether `h : P ∧ Q` is weaker than `h : P` is worse than one that shows both
signatures and says "these differ".
"""

from __future__ import annotations

import argparse
import difflib
import os
import subprocess
import sys
from dataclasses import dataclass, field

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import leanparse as LP  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

#: Directories whose declarations are subject to drift checking.  `Scaffold` is
#: included because a scaffold that silently drops a hypothesis is exactly as
#: misleading as a proved theorem that does.
SCAN_DIRS = ("CRNT", "Scaffold")

#: Declarations whose statements are checked.  `def`/`instance` are included:
#: a predicate defined as `True` instead of the intended conjunction is the
#: single most damaging kind of drift in this codebase (it has happened).
CHECKED_KINDS = ("theorem", "lemma", "example", "def", "abbrev", "structure", "class", "instance")


# --------------------------------------------------------------------------
# git plumbing
# --------------------------------------------------------------------------


def git(*args: str, cwd: str = ROOT) -> str:
    """Run a git command, returning stdout; raise on failure."""
    p = subprocess.run(
        ["git", "-C", cwd, *args],
        capture_output=True,
        text=True,
        check=False,
    )
    if p.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed: {p.stderr.strip()}")
    return p.stdout


def list_lean_files(ref: str) -> list[str]:
    """Every scanned `.lean` path present at `ref`."""
    out: list[str] = []
    for d in SCAN_DIRS:
        listing = git("ls-tree", "-r", "--name-only", ref, "--", d)
        out += [ln for ln in listing.splitlines() if ln.endswith(".lean")]
    return sorted(out)


def read_all_at(ref: str, paths: list[str]) -> dict[str, str]:
    """Contents of every path at `ref`, in one `git cat-file --batch` process.

    One subprocess per file (the obvious `git show ref:path` loop) costs ~40s
    over this repository's 870 files, because process spawn dominates.  A single
    batched reader costs ~1.5s.  Paths missing at `ref` are simply absent.
    """
    if not paths:
        return {}
    spec = "".join(f"{ref}:{p}\n" for p in paths).encode()
    proc = subprocess.run(
        ["git", "-C", ROOT, "cat-file", "--batch"],
        input=spec,
        capture_output=True,
        check=False,
    )
    out = proc.stdout
    result: dict[str, str] = {}
    pos = 0
    n = len(out)
    for path in paths:
        nl = out.find(b"\n", pos)
        if nl == -1:
            break
        header = out[pos:nl].decode("utf-8", errors="replace")
        pos = nl + 1
        parts = header.split()
        # A missing object comes back as `<spec> missing`, with no payload.
        if len(parts) < 3:
            continue
        try:
            size = int(parts[2])
        except ValueError:
            continue
        result[path] = out[pos : pos + size].decode("utf-8", errors="replace")
        pos += size + 1  # skip the trailing newline git appends
        if pos >= n:
            break
    return result


# --------------------------------------------------------------------------
# Indexing a ref
# --------------------------------------------------------------------------


@dataclass
class Index:
    """All checked declarations at one ref, keyed by qualified name."""

    decls: dict[str, LP.Decl] = field(default_factory=dict)
    modules: set[str] = field(default_factory=set)
    duplicate_names: dict[str, list[str]] = field(default_factory=dict)


def index_ref(ref: str) -> Index:
    """Parse every checked declaration at `ref`, keyed by qualified name."""
    idx = Index()
    paths = list_lean_files(ref)
    idx.modules = {LP.module_of_path(p) for p in paths}
    blobs = read_all_at(ref, paths)
    for path in paths:
        text = blobs.get(path)
        if text is None:
            continue
        for d in LP.parse_decls(text, module=LP.module_of_path(path)):
            if d.kind not in CHECKED_KINDS:
                continue
            if d.qualname in idx.decls:
                idx.duplicate_names.setdefault(d.qualname, []).append(path)
            idx.decls[d.qualname] = d
    return idx


# --------------------------------------------------------------------------
# Drift records
# --------------------------------------------------------------------------


@dataclass
class Change:
    """One statement-level difference between two refs."""

    kind: str  # ADDED / REMOVED / WEAKENED / STRENGTHENED / CHANGED
    name: str
    detail: str = ""
    old_stmt: str = ""
    new_stmt: str = ""
    module: str = ""
    old_module: str = ""
    line: int = 0
    old_line: int = 0

    def where(self) -> str:
        loc = f"{self.module}:{self.line}" if self.module else "?"
        if self.old_module and self.old_module != self.module:
            loc = f"{self.old_module}:{self.old_line} -> {loc}"
        return loc


def _hyp_names(d: LP.Decl) -> set[str]:
    return set(d.binder_names)


def classify(old: LP.Decl, new: LP.Decl) -> tuple[str, str]:
    """Classify a statement change. Returns (kind, human-readable detail).

    Only the *name* set of hypotheses is compared, and only to produce a
    human-readable hint.  The signature diff printed alongside is the actual
    evidence: Lean type-level comparison is not available to a text tool, and
    guessing would be worse than showing both signatures.
    """
    old_h = _hyp_names(old)
    new_h = _hyp_names(new)
    dropped = sorted(old_h - new_h)
    added = sorted(new_h - old_h)

    bits: list[str] = []
    if dropped:
        bits.append("dropped hypothesis " + ", ".join(f"`{h}`" for h in dropped))
    if added:
        bits.append("added hypothesis " + ", ".join(f"`{h}`" for h in added))
    if old.conclusion.strip() != new.conclusion.strip():
        bits.append("conclusion changed")

    detail = "; ".join(bits)

    if dropped and not added:
        # Losing hypotheses is the dangerous direction: the statement is now
        # satisfiable by strictly more arguments.
        return "WEAKENED", detail or "hypothesis set shrank"
    if added and not dropped:
        return "STRENGTHENED", detail or "hypothesis set grew"
    if detail:
        return "CHANGED", detail
    # Same hypotheses, same conclusion text, but the statement text differs:
    # a binder *type* was reworded.  Show the diff; do not guess a direction.
    return "CHANGED", "signature text differs (binder types or body of a `where`)"


def diff_statements(old_s: str, new_s: str) -> str:
    """A unified diff of two whitespace-normalised statements."""
    a = LP.normalize_ws(old_s).split(" ")
    b = LP.normalize_ws(new_s).split(" ")
    # Word-level diff keeps it readable even for a 200-word signature.
    return "\n".join(
        difflib.unified_diff(a, b, lineterm="", n=2, fromfile="base", tofile="head")
    )


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------

COLOR = sys.stdout.isatty() and os.environ.get("NO_COLOR") is None


def _c(code: str, s: str) -> str:
    return f"\033[{code}m{s}\033[0m" if COLOR else s


MARK = {
    "WEAKENED": _c("1;31", "!! WEAKENED  "),
    "STRENGTHENED": _c("1;32", "++ STRENGTHENED"),
    "CHANGED": _c("1;33", "~~ CHANGED   "),
    "REMOVED": _c("1;35", "-- REMOVED   "),
    "ADDED": _c("1;36", "++ ADDED     "),
    "REMOVED_MODULE": _c("1;35", "xx MODULE DELETED"),
    "ADDED_MODULE": _c("1;36", "xx MODULE ADDED"),
}


def rank(c: Change) -> int:
    """Sort key: the dangerous directions first, bulk file churn last."""
    order = {
        "WEAKENED": 0,
        "CHANGED": 1,
        "REMOVED": 2,
        "REMOVED_MODULE": 5,
        "ADDED_MODULE": 6,
        "ADDED": 4,
    }
    return order.get(c.kind, 3)




def compute_changes(base: Index, head: Index) -> list[Change]:
    """All statement-level differences between two indexes.

    Declarations are keyed by qualified name, so a rename shows up as one
    REMOVED plus one ADDED.  That is reported as-is rather than guessed at: a
    rename and a delete+add of a *different* theorem are indistinguishable from
    text alone, and pretending otherwise would hide a real deletion.
    """
    changes: list[Change] = []
    old_names, new_names = set(base.decls), set(head.decls)
    deleted_modules = base.modules - head.modules
    added_modules = head.modules - base.modules

    for name in sorted(new_names - old_names):
        d = head.decls[name]
        kind = "ADDED_MODULE" if d.module in added_modules else "ADDED"
        changes.append(
            Change(kind, name, module=d.module, line=d.line, new_stmt=d.one_line_statement)
        )
    for name in sorted(old_names - new_names):
        d = base.decls[name]
        # A declaration that vanished only because its whole file was deleted
        # is kept in the count but reported under its module, so that one
        # file deletion cannot bury a genuine signature edit in the output.
        kind = "REMOVED_MODULE" if d.module in deleted_modules else "REMOVED"
        changes.append(
            Change(kind, name, old_stmt=d.one_line_statement,
                   old_module=d.module, old_line=d.line)
        )
    for name in sorted(old_names & new_names):
        o, n = base.decls[name], head.decls[name]
        if o.comparable() == n.comparable():
            continue
        kind, detail = classify(o, n)
        changes.append(
            Change(kind, name, detail=detail,
                   old_stmt=o.one_line_statement, new_stmt=n.one_line_statement,
                   old_module=o.module, module=n.module, old_line=o.line, line=n.line)
        )
    changes.sort(key=lambda c: (rank(c), c.name))
    return changes


def report(changes: list[Change], base_ref: str, head_ref: str, verbose: bool) -> None:
    """Print the drift report, bulk file churn collapsed to one line each."""
    counts: dict[str, int] = {}
    for c in changes:
        counts[c.kind] = counts.get(c.kind, 0) + 1

    print(f"statement drift: {base_ref} -> {head_ref}")
    print("=" * 72)
    if not changes:
        print("no declaration statements changed (proof edits and reformatting are ignored)")
        return

    summary = ", ".join(f"{k} {v}" for k, v in sorted(counts.items()))
    print(f"{len(changes)} changed: {summary}")
    print()

    # Collapse whole-module add/remove into one line per module.
    bulk: dict[tuple[str, str], list[Change]] = {}
    for c in changes:
        if c.kind in ("REMOVED_MODULE", "ADDED_MODULE"):
            bulk.setdefault((c.kind, c.old_module or c.module), []).append(c)

    shown = 0
    for c in changes:
        if c.kind in ("REMOVED_MODULE", "ADDED_MODULE"):
            key = (c.kind, c.old_module or c.module)
            if bulk[key] and bulk[key][0] is c:
                print(f"{MARK.get(c.kind, c.kind)} {key[1]}")
                print(f"     {len(bulk[key])} declaration(s) in this module; "
                      f"listing them individually is rarely useful")
                print()
                shown += 1
            continue
        if c.kind in ("ADDED", "STRENGTHENED") and not verbose:
            continue
        if shown >= 40 and not verbose:
            print(f"... (further findings suppressed; use --verbose to list all)")
            break
        shown += 1
        print(f"{MARK.get(c.kind, c.kind)} {c.name}")
        print(f"     at {c.where()}")
        if c.detail:
            print(f"     {c.detail}")
        if c.old_stmt and c.new_stmt:
            d = diff_statements(c.old_stmt, c.new_stmt)
            if d:
                for ln in d.splitlines()[:14]:
                    print(f"       {ln}")
                if len(d.splitlines()) > 14:
                    print("       ...")
        elif c.kind == "ADDED":
            print(f"     {c.new_stmt[:200]}")
        elif c.kind == "REMOVED":
            print(f"     {c.old_stmt[:200]}")
        print()

    if not verbose:
        print("note: ADDED/STRENGTHENED declarations are hidden unless --verbose;")
        print("      the summary above still counts them.")


# --------------------------------------------------------------------------
# Self-test
# --------------------------------------------------------------------------


def self_test() -> int:
    """Exercise the classifier on synthetic declarations.

    These cases are the failure modes the tool exists to catch, expressed
    minimally so a regression in `classify` is caught without a git fixture.
    """
    src_old = """theorem foo (h1 : P) (h2 : Q) : R := by sorry
theorem keep (h : P) : Q := by sorry
theorem concl (h : P) : Q := by sorry
structure S where
  a : Nat
  b : Nat
"""
    src_new = """theorem foo (h1 : P) : R := by exact h1
theorem keep (h : P) : Q := by exact h
theorem concl (h : P) : Q' := by sorry
structure S where
  a : Nat
"""
    old = {d.qualname: d for d in LP.parse_decls(src_old)}
    new = {d.qualname: d for d in LP.parse_decls(src_new)}

    fails: list[str] = []

    # 1. dropping a hypothesis is WEAKENED
    kind, _ = classify(old["foo"], new["foo"])
    if kind != "WEAKENED":
        fails.append(f"dropping a hypothesis gave {kind!r}, expected 'WEAKENED'")

    # 2. an unchanged statement is not reported at all
    if old["keep"].comparable() != new["keep"].comparable():
        fails.append("identical statements compared unequal")

    # 3. changing only the conclusion is caught
    kind, detail = classify(old["concl"], new["concl"])
    if kind == "WEAKENED":
        fails.append("a conclusion change was misreported as WEAKENED")
    if "conclusion" not in detail:
        fails.append(f"conclusion change not described in detail: {detail!r}")

    # 4. a structure losing a field is drift, not a proof edit
    if old["S"].comparable() == new["S"].comparable():
        fails.append("losing a structure field was not detected as drift")

    # 5. whitespace-only rewording is NOT drift
    a = LP.parse_decls("theorem w (h : P)\n  :\n  Q := by sorry")[0]
    b = LP.parse_decls("theorem w (h : P) : Q := by exact h")[0]
    if a.comparable() != b.comparable():
        fails.append("whitespace rewrapping was reported as drift")

    # 6. named-argument `:=` must not truncate a statement
    c = LP.parse_decls("theorem n (f : F) : LipschitzWith 0 (g (Y := Y) f) := by sorry")[0]
    if "LipschitzWith 0 (g (Y := Y) f)" not in c.one_line_statement:
        fails.append(f"named-argument := truncated the statement: {c.one_line_statement!r}")

    for f in fails:
        print(f"FAIL: {f}", file=sys.stderr)
    if fails:
        return 1
    print("self-test ok: weakening, reformatting, structure fields, conclusions")
    return 0


# --------------------------------------------------------------------------
# Entry point
# --------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--base", default="origin/master", help="ref to compare against")
    ap.add_argument("--head", default="HEAD", help="ref to compare")
    ap.add_argument("--fail", action="store_true", help="exit 1 if any drift is found")
    ap.add_argument("--verbose", "-v", action="store_true", help="list ADDED declarations too")
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    try:
        base = index_ref(args.base)
        head = index_ref(args.head)
    except RuntimeError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2

    changes = compute_changes(base, head)
    report(changes, args.base, args.head, args.verbose)

    if base.duplicate_names or head.duplicate_names:
        print("\nnote: duplicate qualified names (shadowing) were seen;",
              "diff by name may be ambiguous for those.")

    if args.json:
        import json

        print(json.dumps([{
            "kind": c.kind, "name": c.name, "detail": c.detail,
            "module": c.module, "line": c.line,
            "old": c.old_stmt, "new": c.new_stmt,
        } for c in changes], indent=2))

    dangerous = [c for c in changes if c.kind in ("WEAKENED", "CHANGED", "REMOVED")]
    if args.fail and dangerous:
        print(f"\n::error::{len(dangerous)} statement(s) weakened or removed", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
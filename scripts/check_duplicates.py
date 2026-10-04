#!/usr/bin/env python3
"""check_duplicates.py — did this PR re-land a declaration that already exists?

    python3 scripts/check_duplicates.py                        # origin/holes -> HEAD
    python3 scripts/check_duplicates.py --base holes --head research/form-sr-route
    python3 scripts/check_duplicates.py --tree                 # whole-tree census
    python3 scripts/check_duplicates.py --self-test            # no git, no Lean, no network
    python3 scripts/check_duplicates.py --json

Why this exists (research/README.md §9, round 1's recurring failure): round 1 lost
researchers to *re-authoring capabilities that were already proved in the tree*.  The live
instance is `comparableGrowthDescent_iff_omegaPointPositive`, proved at
`CRNT/Dynamics/SiphonDimensionDescent.lean:368-377` inside hole A's own import closure,
which was queued for re-landing as a fresh theorem.  `scripts/pr_score.py` counts new
modules, new holes, gate regressions and forbidden constructs; it cannot see this.

What counts as a duplicate (in order of confidence):

* `DUPLICATE` — same name, **byte-identical normalised statement**, in a different file.
  This is the re-land.  Score **0**; the output names the existing `file:line` and says
  CITE IT.
* `ALPHA_DUPLICATE` — same name, statements equal after erasing binder names
  (`(N : Network S)` vs `(M : Network S)`).  A re-author usually keeps the binders; an
  independent proof usually does not.  Score **0** pending eyeball.
* `RENAMED_DUPLICATE` — identical statement under a different name.  Same waste, and the
  case a grep for the name cannot find.  Advisory.
* `SHADOW` — same qualified name, different statement, in a different file.  Legal Lean
  (the later declaration wins), almost always an accident.  Advisory.
* `private` declarations are **excluded**: Lean's `private` is file-scoped, so two files
  may each define `private foo` without either shadowing the other.

Lookup is **cross-tree**: the index covers every `.lean` under `CRNT/` (hence under
`CRNT/Scaffold/`) in the *base* ref, not just the diff, so a declaration already in the
tree is found wherever it lives.

Grading follows README §9 exactly:

* a fresh declaration is *eligible* for the "+10 / +25 new machine-checked lemma" row.
  This tool cannot decide "on an identified route" or "used downstream", so it reports
  eligibility and **does not pay**;
* a declaration that already existed and is merely being **cited** is the "+15, lemma
  another researcher's PR builds on" row, never a fresh +10/+25;
* a re-land is **0**, and the actionable instruction is to cite the existing `file:line`.

The rows this tool cannot decide are printed and, in `--json`, emitted as `unscored_rows`
with `"total_is_floor": true` — the same refusal `pr_score.py` makes, kept machine-visible
so a round-end total containing them is identifiable as human judgement.
"""

from __future__ import annotations

import argparse
import collections
import importlib.util
import io
import json
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

SCAN_BASES = ("CRNT", "Scaffold")

# research/README.md §5.  Only the rows a script can decide carry a number.
# PTS_FRESH_LEMMA is an eligibility marker, never added to a total (see UNSCORED_ROWS).
PTS_DUPLICATE = 0
PTS_CITED = 15          # "+15, a proved lemma another researcher's PR builds on"
PTS_FRESH_LEMMA = 10
PTS_FRESH_LEMMA_USED = 25

UNSCORED_ROWS = (
    "new machine-checked lemma on an identified route (+25 used downstream / +10 not)",
    "route document with signatures, citations and a dead-end list (+12)",
    "machine-checked refutation that kills a route or statement (+30)",
    "a proved lemma another researcher's PR builds on (+15)",
    "`sorry` eliminated in CRNT/ and the enclosing module still elaborates axiom-cleanly (+100)",
)

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?P<mods>(?:(?:private|protected|noncomputable|nonrec|scoped)\s+)*)"
    r"(?P<kind>theorem|lemma)\s+(?P<name>[^\s:({\[]+)"
)

DUPLICATE = "DUPLICATE"
ALPHA = "ALPHA_DUPLICATE"
SHADOW = "SHADOW"
RENAMED = "RENAMED_DUPLICATE"
FRESH = "FRESH"
CITED = "CITED"

SEVERITY = {DUPLICATE: 3, ALPHA: 2, RENAMED: 1, SHADOW: 0, FRESH: 0}


# --------------------------------------------------------------------- plumbing


def git(*args: str) -> str:
    p = subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True, text=True)
    if p.returncode != 0:
        raise SystemExit(f"git {' '.join(args)} failed:\n{p.stderr.strip()}")
    return p.stdout


def export(ref: str, dest: Path) -> None:
    """`git archive | tar -x` — read-only; never touches a worktree."""
    p = subprocess.Popen(["git", "-C", str(ROOT), "archive", "--format=tar", ref],
                         stdout=subprocess.PIPE)
    assert p.stdout is not None
    data = p.stdout.read()
    if p.wait() != 0:
        raise SystemExit(f"git archive {ref} failed")
    with tarfile.open(fileobj=io.BytesIO(data), mode="r|") as tf:
        tf.extractall(dest)


def strip_comments(text: str) -> str:
    return re.sub(r"/-.*?-/", lambda m: re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.S)


def decl_body(code: str, start: int, limit: int = 4000) -> str:
    """`code[start:]` up to the first top-level `:=`, `where` or `begin`.

    `start` is an **absolute** offset into `code`.  (`pr_score.py` calls this with a
    line-relative offset, which truncates the statement to whatever happened to sit at that
    column of the file; the self-test asserts against it so the discrepancy stays visible
    rather than becoming a second, quieter normalisation.)
    """
    depth, i, n = 0, start, min(len(code), start + limit)
    while i < n:
        if code.startswith("/-", i):
            j = code.find("-/", i)
            i = n if j < 0 else j + 2
            continue
        ch = code[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and code.startswith(":=", i):
            return code[start:i]
        elif depth == 0 and re.match(r"\b(where|begin)\b", code[i:i + 6]):
            return code[start:i]
        i += 1
    return code[start:n]


def pop_namespace(stack: list[str], closed: str) -> None:
    """Pop to `closed`, tolerating an `end` that closes a `section` instead."""
    if not stack:
        return
    if stack[-1] == closed:
        stack.pop()
        return
    if closed in stack:
        while stack and stack.pop() != closed:
            pass


# ------------------------------------------------------------------- the index


BINDER_RE = re.compile(
    r"[\(\{]\s*((?:[A-Za-z_][A-Za-z0-9_'.!?]*(?:\s+[A-Za-z_][A-Za-z0-9_'.!?]*)*)"
    r"(?:\s+(?::=|\[.*?\]))?)\s*:"
)


def alpha_key(stmt: str) -> str:
    """`stmt` with every explicitly-bound binder name replaced by a positional token.

    `(N : Network S) (P : Finset S) : h : N.IsCriticalSiphon P -> ...` and
    `(M : Network S) (Q : Finset S) : h : M.IsCriticalSiphon Q -> ...` become equal; a
    proof that genuinely differs does not.  Only *pure identifier lists* are rewritten, so
    `(h : ∀ x, P x)` — which contains `∀` and `,` — is left alone.
    """
    bound: list[str] = []

    def take(m: re.Match) -> str:
        head = m.group(0).split(":")[0].rstrip()
        for nm in m.group(1).split():
            if nm not in bound:
                bound.append(nm)
        return head + ":"

    s = BINDER_RE.sub(take, stmt)
    for i, nm in enumerate(bound):
        s = re.sub(rf"(?<![\w'.]){re.escape(nm)}(?![\w'.!?])", f"#{i}#", s)
    return s


@dataclass(frozen=True)
class Decl:
    file: str
    line: int
    kind: str
    name: str            # namespace-qualified
    bare: str
    stmt: str            # whitespace-normalised statement
    private: bool
    alpha: str


def module_files(root: Path) -> set[str]:
    out: set[str] = set()
    for base in SCAN_BASES:
        top = root / base
        if not top.is_dir():
            continue
        out |= {str(p.relative_to(root)) for p in top.rglob("*.lean")}
    return out


def scan_tree(root: Path) -> list[Decl]:
    """Every `theorem`/`lemma` under `root`, namespace-qualified and normalised."""
    recs: list[Decl] = []
    for rel in sorted(module_files(root)):
        code = strip_comments((root / rel).read_text(encoding="utf-8", errors="replace"))
        stack: list[str] = []
        offset = 0
        for lineno, line in enumerate(code.split("\n"), 1):
            start = offset
            offset += len(line) + 1
            ns = re.match(r"^namespace\s+([A-Za-z_][\w'.]*)", line)
            if ns:
                stack.append(ns.group(1))
                continue
            end = re.match(r"^end\s+([A-Za-z_][\w'.]*)", line)
            if end:
                pop_namespace(stack, end.group(1))
                continue
            m = DECL_RE.match(line)
            if not m:
                continue
            stmt = " ".join(decl_body(code, start + m.end()).split())
            recs.append(Decl(
                file=rel, line=lineno, kind=m.group("kind"),
                name=".".join(stack + [m.group("name")]), bare=m.group("name"),
                stmt=stmt, private="private" in (m.group("mods") or "").split(),
                alpha=alpha_key(stmt),
            ))
    return recs


@dataclass
class Index:
    by_name: dict = field(default_factory=lambda: collections.defaultdict(list))
    by_bare: dict = field(default_factory=lambda: collections.defaultdict(list))
    by_stmt: dict = field(default_factory=lambda: collections.defaultdict(list))
    by_alpha: dict = field(default_factory=lambda: collections.defaultdict(list))

    @classmethod
    def of(cls, decls) -> "Index":
        ix = cls()
        for d in decls:
            ix.by_name[d.name].append(d)
            ix.by_bare[d.bare].append(d)
            ix.by_stmt[d.stmt].append(d)
            ix.by_alpha[d.alpha].append(d)
        return ix


# ------------------------------------------------------------------ the verdict


@dataclass
class Finding:
    verdict: str
    head: Decl
    prior: list
    note: str = ""
    scope: str = ""

    @property
    def points(self) -> int:
        return PTS_DUPLICATE if self.verdict in (DUPLICATE, ALPHA) else 0

    @property
    def site(self) -> str:
        return f"{self.head.file}:{self.head.line}"

    def cites(self) -> str:
        return ", ".join(f"{p.file}:{p.line}" for p in self.prior)


def p_is(p: Decl, h: Decl) -> bool:
    return p.file == h.file and p.line == h.line


def elsewhere(cands, h: Decl) -> list:
    return [p for p in cands if not p_is(p, h)]


def classify(head: Decl, indexes: list[tuple[str, Index]]) -> Finding:
    """One declaration against the *whole base tree* and the rest of the head tree.

    Precedence matters and is deliberate: an *identical statement under a new name* outranks
    a *same name with a new statement*, because the first is wasted work and the second is
    merely a shadow.  Binders are only erased when the name agrees, otherwise every
    `(n : ℕ) : n = n` in the tree would collide.
    """
    if head.private:
        return Finding(FRESH, head, [], "private: file-scoped, cannot shadow")

    for scope, ix in indexes:
        prior = elsewhere(ix.by_name.get(head.name, []), head)

        exact = elsewhere([p for p in prior if p.stmt == head.stmt], head)
        if exact:
            return Finding(DUPLICATE, head, exact, "", f"{scope}/qualified+stmt")

        # Two files may each open `namespace Network` while this scanner saw only one of
        # them; bare name plus identical statement is still the same theorem.
        loose = elsewhere([p for p in ix.by_bare.get(head.bare, []) if p.stmt == head.stmt], head)
        if loose:
            return Finding(DUPLICATE, head, loose,
                           "matched on bare name (namespaces differ)", f"{scope}/bare+stmt")

        same = elsewhere(ix.by_stmt.get(head.stmt, []), head)
        if same and head.stmt:
            return Finding(RENAMED, head, same,
                           "identical statement, different name", f"{scope}/stmt-only")

        if head.alpha:
            al = elsewhere([p for p in ix.by_alpha.get(head.alpha, [])
                            if p.bare == head.bare], head)
            if al:
                return Finding(ALPHA, head, al,
                               "same name, statements equal after erasing binder names — verify",
                               f"{scope}/alpha")

        if prior:
            return Finding(SHADOW, head, prior,
                           "same qualified name, different statement", f"{scope}/name-only")
    return Finding(FRESH, head, [], "", "no-match")


def new_decls(base_decls, head_decls) -> list[Decl]:
    """Head declarations absent from the base *at their own location*.

    A declaration that exists in the base under the same name in a **different** file is
    deliberately kept as a candidate: that is precisely the re-land, and dropping it here
    is how a duplicate checker silently becomes a no-op.
    """
    base_ix = Index.of(base_decls)
    return [d for d in head_decls
            if not any(p.file == d.file and p.stmt == d.stmt
                       for p in base_ix.by_name.get(d.name, []))]


def cited_decls(base_decls, head_decls, new_mods: list[str], head_root: Path) -> list[Decl]:
    """Base declarations a new head module *uses* without re-declaring them.

    This is the README §9 "+15, a proved lemma another researcher's PR builds on" case,
    found by an actual reference search rather than by name coincidence: a bare identifier
    occurring in a new module's body that names a base declaration and is not declared in
    that module.  A re-land is *not* a citation and must not be counted as one.
    """
    base_by_bare: dict[str, list[Decl]] = collections.defaultdict(list)
    for d in base_decls:
        base_by_bare[d.bare].append(d)
    head_by_file: dict[str, set] = collections.defaultdict(set)
    for d in head_decls:
        head_by_file[d.file].add(d.bare)

    found: dict[str, Decl] = {}
    for rel in new_mods:
        path = head_root / rel
        if not path.is_file():
            continue
        code = strip_comments(path.read_text(encoding="utf-8", errors="replace"))
        local = head_by_file.get(rel, set())
        for tok in set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.!?]*", code)):
            if tok in local or tok not in base_by_bare:
                continue
            for d in base_by_bare[tok]:
                found.setdefault(f"{d.file}:{d.line}", d)
    return sorted(found.values(), key=lambda d: (d.file, d.line))


def analyse(base_root: Path, head_root: Path) -> dict:
    base_decls = scan_tree(base_root)
    head_decls = scan_tree(head_root)
    base_ix, head_ix = Index.of(base_decls), Index.of(head_decls)
    base_files, head_files = module_files(base_root), module_files(head_root)
    new_mods = sorted(head_files - base_files)

    findings = [classify(d, [("base-tree", base_ix), ("head-tree", head_ix)])
                for d in new_decls(base_decls, head_decls)]
    for f in findings:
        f.scope += "/new-module" if f.head.file in new_mods else "/edited-module"

    cited = cited_decls(base_decls, head_decls, new_mods, head_root)
    rows = grade(findings, cited)
    return {
        "new_modules": new_mods,
        "findings": findings,
        "rows": rows,
        "duplicates": [f for f in findings if f.verdict in (DUPLICATE, ALPHA)],
        "fresh": [f for f in findings if f.verdict == FRESH],
        "cited": cited,
        "total": sum(r["points"] for r in rows),
        "unscored_rows": list(UNSCORED_ROWS),
        "total_is_floor": True,
    }


# ------------------------------------------------------------------- reporting


def grade(findings: list[Finding], cited: list) -> list[dict]:
    """research/README.md §5 rows, restricted to what a script can decide."""
    rows: list[dict] = []
    for f in findings:
        if f.verdict not in (DUPLICATE, ALPHA, SHADOW, RENAMED):
            continue
        rows.append({
            "event": ("re-land of an existing declaration"
                      if f.verdict in (DUPLICATE, ALPHA)
                      else f"advisory: {f.verdict}"),
            "verdict": f.verdict, "points": f.points, "name": f.head.name, "site": f.site,
            "existing": [{"file": p.file, "line": p.line} for p in f.prior],
            "action": (f"CITE {f.cites()} — do not re-land"
                       if f.verdict in (DUPLICATE, ALPHA)
                       else "check whether this is the same result under another name"),
            "note": f.note, "scope": f.scope, "unscored": False,
        })
    fresh = [f for f in findings if f.verdict == FRESH and not f.head.private]
    if fresh:
        rows.append({
            "event": "fresh declarations (eligible for the +10/+25 lemma row)",
            "verdict": FRESH, "points": 0, "count": len(fresh),
            "sites": [f.site for f in fresh],
            "eligible_for": [PTS_FRESH_LEMMA, PTS_FRESH_LEMMA_USED],
            "action": "not paid here: 'on an identified route' and 'used downstream' are judgements",
            "unscored": True,
        })
    if cited:
        rows.append({
            "event": "pre-existing declaration cited, not re-proved", "verdict": CITED,
            "points": PTS_CITED, "count": len(cited),
            "sites": [f"{d.file}:{d.line}" for d in cited],
            "eligible_for": [PTS_CITED],
            "action": "the +15 row (another PR builds on it), never a fresh +10/+25",
            "unscored": False,
        })

    return rows


def tree_census(root: Path) -> dict:
    """Whole-tree census, reporting each duplicate **pair once**.

    Matching mirrors `classify`: alpha-equality only counts within one name, so the
    common `f_a` / `f_b` pair in the same file is not mistaken for one declaration.
    """
    decls = scan_tree(root)
    ix = Index.of(decls)
    found: list[Finding] = []
    seen: set[tuple] = set()

    def emit(verdict: str, d: Decl, others: list, note: str, scope: str) -> None:
        for o in sorted(others, key=lambda x: (x.file, x.line)):
            pair = tuple(sorted(((d.file, d.line), (o.file, o.line))))
            if pair in seen:
                return
            seen.add(pair)
            found.append(Finding(verdict, d, [o], note, scope))

    for d in decls:
        if d.private:
            continue
        exact = elsewhere([p for p in ix.by_name.get(d.name, []) if p.stmt == d.stmt], d)
        if exact:
            emit(DUPLICATE, d, exact, "", "census/name+stmt")
            continue
        same = elsewhere(ix.by_stmt.get(d.stmt, []), d)
        if same and d.stmt:
            emit(RENAMED, d, same, "identical statement, other name", "census/stmt-only")
            continue
        al = elsewhere([p for p in ix.by_alpha.get(d.alpha, [])
                        if d.alpha and p.bare == d.bare], d)
        if al:
            emit(ALPHA, d, al, "same name, binder-renamed statement", "census/alpha")
            continue
        prior = elsewhere(ix.by_name.get(d.name, []), d)
        if prior:
            emit(SHADOW, d, prior, "same name, different statement", "census/name-only")

    return {
        "modules": len(module_files(root)),
        "declarations": len(decls),
        "exact_duplicates": sum(1 for f in found if f.verdict == DUPLICATE),
        "alpha_duplicates": sum(1 for f in found if f.verdict == ALPHA),
        "shadows": sum(1 for f in found if f.verdict == SHADOW),
        "renamed": sum(1 for f in found if f.verdict == RENAMED),
        "findings": found,
    }


def across_branches(base_root: Path, heads: list[tuple[str, Path]]) -> list[dict]:
    """Declarations landing independently in **more than one open branch**.

    Round 1's four copies of one `False`-level theorem each sat in a *different* PR, so no
    single-ref scan can see them: every branch was clean against `holes`.  This compares
    each branch's new declarations against the base, then intersects the results — a
    declaration that appears new in two branches is landed twice no matter how the merges
    are ordered.
    """
    base_decls = scan_tree(base_root)
    base_ix = Index.of(base_decls)
    per_branch: dict[str, list[tuple[str, Decl]]] = {}
    for ref, root in heads:
        head_decls = scan_tree(root)
        head_files = module_files(root)
        new_mods = head_files - module_files(base_root)
        found: list[tuple[str, Decl]] = []
        for d in head_decls:
            if d.private:
                continue
            prior = base_ix.by_name.get(d.name, [])
            if any(p.stmt == d.stmt for p in prior):
                continue
            same_name = [p for p in base_ix.by_name.get(d.name, []) if p.stmt == d.stmt]
            if same_name:
                continue
            if d.file not in new_mods and not _new_here(base_ix, d):
                continue
            found.append((d.file, d))
        per_branch[ref] = found

    # Group by name *and* the binder-erased statement: two researchers re-deriving the
    # same result rarely choose the same binder names, and grouping on the raw statement
    # would report both branches clean.
    key = collections.defaultdict(list)
    for ref, decls in per_branch.items():
        for rel, d in decls:
            key[(d.name, d.alpha or d.stmt)].append((ref, rel, d))

    out: list[dict] = []
    for (name, sig), hits in sorted(key.items()):
        refs = sorted({h[0] for h in hits})
        if len(refs) < 2:
            continue
        out.append({
            "name": name, "key": sig,
            "branches": refs,
            "sites": [{"ref": r, "file": f, "line": d.line} for r, f, d in hits],
            "action": "one branch keeps it; the others CITE it",
        })
    return out


def _new_here(base_ix: Index, d: Decl) -> bool:
    return not any(p.file == d.file and p.stmt == d.stmt
                   for p in base_ix.by_name.get(d.name, []))


# ------------------------------------------------------------------- self-test


def _mk(root: Path, files: dict[str, str]) -> None:
    for rel, body in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(body, encoding="utf-8")


ORIG = """namespace CRNT
namespace Network
theorem comparableGrowthDescent_iff_omegaPointPositive (N : Network S)
    {P₀ : Finset S} (h : N.IsCriticalSiphon P₀) : True := by trivial
private theorem private_helper (x : ℕ) : x = x := rfl
theorem someOther (n : ℕ) : n = n := rfl
end Network
end CRNT
"""


def self_test() -> int:
    failures: list[str] = []
    groups: set[str] = set()

    def check(name: str, cond: bool, detail: str = "") -> None:
        groups.add(name)
        if not cond:
            failures.append(f"{name}: {detail}")

    tmp = Path(tempfile.mkdtemp(prefix="dupcheck-"))
    try:
        base = tmp / "base"
        _mk(base, {"CRNT/Dynamics/SiphonDimensionDescent.lean": ORIG})

        # ---- 1. the round-1 case: an exact re-land in a new module -------------
        head = tmp / "head"
        shutil.copytree(base, head)
        _mk(head, {"CRNT/Dynamics/DescentAgain.lean": ORIG})
        r = analyse(base, head)
        dups = [f for f in r["findings"]
                if f.verdict == DUPLICATE
                and f.head.name.endswith("comparableGrowthDescent_iff_omegaPointPositive")
                and f.head.file.endswith("DescentAgain.lean")]
        check("exact-reland-found", len(dups) == 1,
              f"got {[f'{f.verdict}@{f.site}' for f in r['findings']]}")
        if dups:
            check("cite-is-given", dups[0].cites() ==
                  "CRNT/Dynamics/SiphonDimensionDescent.lean:3",
                  f"cite was {dups[0].cites()!r}")
            check("zero-points", dups[0].points == 0, str(dups[0].points))
            check("base-tree-lookup", dups[0].scope.startswith("base-tree"),
                  dups[0].scope)
        check("new-module-seen", r["new_modules"] == ["CRNT/Dynamics/DescentAgain.lean"],
              str(r["new_modules"]))
        check("pure-reland-total-zero", r["total"] == 0, f"total {r['total']}")
        check("floor-flag", r["total_is_floor"] is True, "total_is_floor not set")
        check("unscored-rows-listed", len(r["unscored_rows"]) >= 3, "unscored rows missing")
        check("dup-row-zero", any(x["verdict"] == DUPLICATE and x["points"] == 0
                                  for x in r["rows"]), "no zero-point duplicate row")

        # ---- 2. private is exempt --------------------------------------------
        pv = [f for f in r["findings"] if f.head.bare == "private_helper"]
        check("private-exempt", not [f for f in pv if f.verdict != FRESH],
              f"private decl flagged: {[f.verdict for f in pv]}")

        # ---- 3. a genuinely fresh declaration ---------------------------------
        h3 = tmp / "h3"
        shutil.copytree(base, h3)
        _mk(h3, {"CRNT/Dynamics/Fresh.lean": """namespace CRNT
namespace Network
theorem brandNewStatement (n : ℕ) : n + 1 = n + 1 := rfl
end Network
end CRNT
"""})
        r3 = analyse(base, h3)
        bn = [f for f in r3["findings"] if f.head.bare == "brandNewStatement"]
        check("fresh-found", len(bn) == 1, f"got {bn}")
        check("fresh-verdict", bool(bn) and bn[0].verdict == FRESH,
              bn[0].verdict if bn else "-")
        check("fresh-row-unscored",
              any(x["verdict"] == FRESH and x["points"] == 0 and x["unscored"]
                  for x in r3["rows"]), "fresh row missing or scored")

        # ---- 4. renamed binders => ALPHA_DUPLICATE ---------------------------
        b4 = tmp / "b4"
        shutil.copytree(base, b4)
        _mk(b4, {"CRNT/Other/AlphaTwin.lean": """namespace CRNT
namespace Network
theorem someOtherTwin (k : ℕ) : k = k := rfl
end Network
end CRNT
"""})
        h4 = tmp / "h4"
        shutil.copytree(b4, h4)
        _mk(h4, {"CRNT/Dynamics/AlphaCopy.lean": """namespace CRNT
namespace Network
theorem someOtherTwin (j : ℕ) : j = j := rfl
end Network
end CRNT
"""})
        r4 = analyse(b4, h4)
        al = [f for f in r4["findings"] if f.verdict == ALPHA]
        check("alpha-detected", bool(al),
              f"verdicts {[f.verdict for f in r4['findings']]}")

        # ---- 5. shadow: same name, different statement ------------------------
        _mk(h4, {"CRNT/Dynamics/Shadowing.lean": """namespace CRNT
namespace Network
theorem someOther (n : ℕ) : n + 0 = n := by omega
end Network
end CRNT
"""})
        r5 = analyse(b4, h4)
        sh = [f for f in r5["findings"] if f.verdict == SHADOW]
        check("shadow-detected", bool(sh), f"verdicts {[f.verdict for f in r5['findings']]}")
        check("shadow-zero-points", all(f.points == 0 for f in sh), "shadow scored points")

        # ---- 6. intra-head duplicate (two new modules, same theorem) -----------
        h6 = tmp / "h6"
        shutil.copytree(base, h6)
        body = """namespace CRNT
namespace Network
theorem onlyHere (n : ℕ) : n * 2 = 2 * n := by omega
end Network
end CRNT
"""
        _mk(h6, {"CRNT/A/One.lean": body, "CRNT/A/Two.lean": body})
        r6 = analyse(base, h6)
        ihh = [f for f in r6["findings"]
               if f.verdict == DUPLICATE and f.head.bare == "onlyHere"]
        check("intra-head", len(ihh) == 2,
              f"verdicts {[(f.verdict, f.head.file) for f in r6['findings']]}")

        # ---- 7. renamed declaration (same statement, different name) ----------
        b7 = tmp / "b7"
        shutil.copytree(base, b7)
        _mk(b7, {"CRNT/Other/Original.lean": """namespace CRNT
namespace Network
theorem originalName (n : ℕ) : n * 3 = 3 * n := by omega
end Network
end CRNT
"""})
        h7 = tmp / "h7"
        shutil.copytree(b7, h7)
        _mk(h7, {"CRNT/Other/Alias.lean": """namespace CRNT
namespace Network
theorem brandNewName (n : ℕ) : n * 3 = 3 * n := by omega
end Network
end CRNT
"""})
        r7 = analyse(b7, h7)
        rn = [f for f in r7["findings"] if f.verdict == RENAMED]
        check("renamed-detected", len(rn) == 1,
              f"verdicts {[(f.verdict, f.head.name) for f in r7['findings']]}")

        # ---- 8. citing a base declaration is +15, never a fresh +10/+25 -------
        h8 = tmp / "h8"
        shutil.copytree(base, h8)
        _mk(h8, {"CRNT/Dynamics/User.lean": """namespace CRNT
namespace Network
/-- uses the existing descent lemma rather than rebuilding it -/
theorem usesIt (n : ℕ) (h : someOther n) : n = n := by omega
end Network
end CRNT
"""})
        r8 = analyse(base, h8)
        cite_row = [x for x in r8["rows"] if x["verdict"] == CITED]
        check("cite-row-present", bool(cite_row),
              f"rows {[(x['verdict'], x['points']) for x in r8['rows']]}")
        check("cite-row-15", bool(cite_row) and cite_row[0]["points"] == PTS_CITED,
              f"points {cite_row[0]['points'] if cite_row else '-'}")
        check("cite-is-not-fresh",
              all("someOther" not in str(x.get("sites", "")) for x in r8["rows"]
                  if x["verdict"] == FRESH),
              "a cited base declaration was also reported as fresh")
        check("reland-is-not-cited",
              not [x for x in r["rows"] if x["verdict"] == CITED],
              "a re-land was counted as a citation")

        # ---- 10. cross-branch: the same declaration in two open PRs -----------
        # The round-1 shape: four copies of one theorem, one per open PR, each clean
        # against `holes`.  No single-ref scan can see it.
        c1, c2 = tmp / "c1", tmp / "c2"
        shutil.copytree(base, c1)
        shutil.copytree(base, c2)
        _mk(c1, {"CRNT/A/Alpha.lean": """namespace CRNT
namespace Network
theorem falseLevelClaim (n : ℕ) : n < 0 := by omega
end Network
end CRNT
"""})
        _mk(c2, {"CRNT/B/Beta.lean": """namespace CRNT
namespace Network
theorem falseLevelClaim (m : ℕ) : m < 0 := by omega
end Network
end CRNT
"""})
        xb = across_branches(base, [("br-a", c1), ("br-b", c2)])
        check("cross-branch", len(xb) == 1,
              f"got {[(x['name'], x['branches']) for x in xb]}")
        if xb:
            check("cross-branch-both-refs", xb[0]["branches"] == ["br-a", "br-b"],
                  str(xb[0]["branches"]))
        check("cross-branch-single-clean",
              not across_branches(base, [("br-a", c1)]),
              "one clean branch reported a cross-branch duplicate")

        # ---- 11. `end` closing a section must not corrupt the namespace stack ---
        nsroot = tmp / "nsroot"
        _mk(nsroot, {"CRNT/N/One.lean": """namespace CRNT
section S
theorem inner (n : ℕ) : n = n := rfl
end S
theorem afterSection (n : ℕ) : n = n := rfl
end CRNT
"""})
        names = {d.name for d in scan_tree(nsroot)}
        check("section-end", names == {"CRNT.inner", "CRNT.afterSection"}, f"names {names}")

        # ---- 12. statement normalisation starts at the declaration --------------
        d = scan_tree(nsroot)[0]
        check("no-offset-drift", d.stmt == "(n : ℕ) : n = n",
              f"statement was {d.stmt!r}")

        # ---- 13. pr_score.py's normalisation, where present --------------------
        # `pr_score.py::statements` calls its own `decl_body` with a *line-relative*
        # offset into a whole-file slice, so its "normalised statement" begins wherever
        # the declaration happened to sit in the file.  That is recorded here rather than
        # asserted equal, because the two answer different questions and pretending they
        # agree is what made the duplicate check miss a re-land in round 1.
        prs = ROOT / "scripts" / "pr_score.py"
        if prs.is_file():
            spec = importlib.util.spec_from_file_location("_pr_score_chk", prs)
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            theirs = {k: v for k, v in mod.statements(h6).items()
                      if k.split("#", 1)[0].endswith("One.lean")}
            mine = {f"{x.file}#{x.name}": x.stmt for x in scan_tree(h6)
                    if x.file.endswith("One.lean")}
            check("pr-score-key-space", bool(theirs) and bool(mine),
                  "pr_score.py produced no comparable entry")
            check("mine-is-normalised",
                  all(v.lstrip().startswith(("(", "{")) or " : " in v or v == ""
                      for v in mine.values()),
                  f"unnormalised statement: {mine}")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    if failures:
        print("check_duplicates.py --self-test: FAIL")
        for f in failures:
            print(f"  - {f}")
        return 1
    print(f"check_duplicates.py --self-test: ok ({len(groups)} assertions, "
          f"{len(failures)} failed)")
    return 0



def markdown_summary(c: dict, limit: int = 10) -> str:
    """GitHub step-summary block.

    Informational on purpose: the census counts what is already in the tree, which is not
    this PR's doing.  The gates are `--self-test` and a diff-scoped run.
    """
    out = ["### Duplicate declarations", "",
           f"- modules scanned: `{c['modules']}`",
           f"- `theorem`/`lemma` declarations: `{c['declarations']}`",
           f"- exact re-lands (same name, same statement): `{c['exact_duplicates']}`",
           f"- same name, binder-renamed statement: `{c['alpha_duplicates']}`",
           f"- identical statement under another name: `{c['renamed']}`",
           f"- same qualified name, different statement: `{c['shadows']}`", ""]
    top = sorted(c["findings"], key=lambda f: -SEVERITY[f.verdict])[:limit]
    if top:
        out += ["| verdict | declaration | site | also at |", "| --- | --- | --- | --- |"]
        for f in top:
            out.append(f"| {f.verdict} | `{f.head.name}` | `{f.site}` | `{f.cites()}` |")
    return "\n".join(out)


# ------------------------------------------------------------------------- main


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--base", default="origin/holes")
    ap.add_argument("--head", default="HEAD")
    ap.add_argument("--tree", action="store_true",
                    help="census of the working tree instead of a PR diff")
    ap.add_argument("--branches", action="store_true",
                    help="compare every origin/research/* head against --base, reporting "
                         "declarations that land in more than one open branch")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--max-report", type=int, default=40)
    ap.add_argument("--md", action="store_true",
                    help="markdown summary for the CI step summary (implies --tree)")
    args = ap.parse_args()

    if args.self_test:
        return self_test()


    if args.branches:
        refs = [ln.strip() for ln in
                git("for-each-ref", "--format=%(refname:short)",
                    "refs/remotes/origin/research/").splitlines() if ln.strip()]
        with tempfile.TemporaryDirectory() as tmp:
            rb = Path(tmp) / "base"
            rb.mkdir()
            export(args.base, rb)
            heads = []
            for i, ref in enumerate(refs):
                d = Path(tmp) / f"h{i}"
                d.mkdir()
                export(ref, d)
                heads.append((ref, d))
            dupes = across_branches(rb, heads)
        if args.json:
            print(json.dumps({"base": args.base, "branches": len(refs),
                              "cross_branch_duplicates": dupes}, indent=2))
        else:
            print(f"{len(refs)} branches vs {args.base}: "
                  f"{len(dupes)} declaration(s) landing in more than one branch")
            for d in dupes:
                print(f"  {d['name']}")
                for s in d["sites"]:
                    print(f"      {s['ref']}  {s['file']}:{s['line']}")
                print(f"      -> {d['action']}")
        return 1 if dupes else 0
    if args.tree or args.md:
        c = tree_census(ROOT)
        if args.md:
            print(markdown_summary(c))
            return 0
        payload = {k: v for k, v in c.items() if k != "findings"}
        if args.json:
            print(json.dumps(payload, indent=2))
        else:
            print(f"{c['modules']} modules, {c['declarations']} theorem/lemma declarations")
            print(f"exact duplicates {c['exact_duplicates']}, "
                  f"binder-renamed {c['alpha_duplicates']}, "
                  f"renamed {c['renamed']}, shadowed names {c['shadows']}")
            for f in sorted(c["findings"], key=lambda t: -SEVERITY[t.verdict])[:args.max_report]:
                print(f"  {f.verdict:<18}{f.head.name:<48} {f.site}"
                      f"   also at {f.cites()}")
        return 1 if c["exact_duplicates"] else 0

    with tempfile.TemporaryDirectory() as tmp:
        rb, rh = Path(tmp) / "base", Path(tmp) / "head"
        rb.mkdir()
        rh.mkdir()
        export(args.base, rb)
        export(args.head, rh)
        r = analyse(rb, rh)

    payload = {
        "base": args.base, "head": args.head,
        "new_modules": r["new_modules"],
        "rows": r["rows"],
        "scored_total": r["total"],
        "total_is_floor": True,
        "unscored_rows": r["unscored_rows"],
        "duplicates": [
            {"verdict": f.verdict, "name": f.head.name, "site": f.site,
             "existing": [{"file": p.file, "line": p.line} for p in f.prior],
             "note": f.note, "points": 0}
            for f in r["duplicates"]
        ],
    }
    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        print(f"{args.base} -> {args.head}   ({len(r['new_modules'])} new module(s))")
        print(f"{'verdict':<20}{'points':>7}  declaration / action")
        for row in r["rows"]:
            v = row["verdict"]
            if v in (DUPLICATE, ALPHA, SHADOW, RENAMED):
                print(f"{v:<20}{row['points']:>+7}  {row['name']}  ({row['site']})")
                for e in row["existing"]:
                    print(f"{'':<27}existing: {e['file']}:{e['line']}")
                if row["note"]:
                    print(f"{'':<27}note: {row['note']}")
            elif v == CITED:
                print(f"{CITED:<20}{row['points']:>+7}  {row['count']} pre-existing "
                      f"declaration(s) cited, not re-proved")
            elif v == FRESH:
                print(f"{FRESH:<20}{row['points']:>+7}  {row['count']} fresh "
                      f"declaration(s): eligible for +{row['eligible_for']}")
        print(f"{'TOTAL (machine-decidable)':<20}{r['total']:>+7}   [floor]")
        print("not scored here: " + "; ".join(UNSCORED_ROWS))
    return 1 if r["duplicates"] else 0


if __name__ == "__main__":
    sys.exit(main())
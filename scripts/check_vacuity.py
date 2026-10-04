#!/usr/bin/env python3
"""check_vacuity.py — find theorems that do not mean what their signature says.

Vacuity is the failure mode that a type checker cannot see.  A theorem whose
hypothesis is never used still compiles; a theorem whose conclusion is `True`
still compiles; a theorem whose proof is a single closing tactic still compiles.
In each case the declaration *looks* like a mathematical result and discharges no
content.  This repository has been bitten by exactly this: predicates defined as
`∃ (_ : Unit), True` with an `isTrue` decider made analyzer flags true for every
network, and six certificate structures were `structure C where dummy : True`.
`check_stubs.py` catches those particular syntactic shapes.

This script generalizes it along three axes.

1. **Unused hypotheses.**  A hypothesis never mentioned in the proof is a
   hypothesis the theorem does not need: the statement is stronger than the
   result.  Lean itself emits `unused variable` lint warnings for these; pass a
   build log with `--lint-log` to fold those in, or rely on the static analysis
   below, which needs no build.

2. **Trivial conclusions.**  A conclusion that is `True`, `1 = 1` or similar is
   satisfied by any hypothesis at all.

3. **Closing proofs.**  A body that is just `trivial`, `decide`, `simp`,
   `rfl`, `norm_num`, `omega` or `native_decide` is a computation that happened
   to succeed, not an argument.

Findings are **ranked by risk**, because the honest signal is sparse.  A theorem
that is *both* trivially proved *and* trivially stated is a placeholder.  A
theorem with one unused hypothesis out of twenty may simply be redundant, not
vacuous.  The ordering puts the dangerous combinations first.

Known imprecision, stated plainly
---------------------------------
`unused-hypothesis` is a heuristic, and a sound one only under a caveat: a
tactic such as `aesop`, `simp_all`, `linarith` or `omega` can consume a
hypothesis without naming it.  Findings whose body contains such a tactic are
therefore downgraded to `indeterminate` and reported separately, never as
confident vacuity.  Instance binders `[NeZero n]` are excluded outright: a
typeclass argument is legitimately absent from the proof text.

Usage
-----
    python3 scripts/check_vacuity.py --report          # ranked findings
    python3 scripts/check_vacuity.py                   # gate against the baseline
    python3 scripts/check_vacuity.py --lint-log build.log
    python3 scripts/check_vacuity.py --self-test
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass, field

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import leanparse as LP  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(ROOT, "scripts", "vacuity_baseline.txt")

SCAN_DIRS = ("CRNT", "Scaffold")

#: Declarations worth auditing.  `instance` is included on purpose: an instance
#: that is satisfied by `isTrue`, or whose class is inhabited everywhere, is a
#: silent source of `True` for every consumer.
AUDITED_KINDS = ("theorem", "lemma", "example", "def", "instance", "abbrev")

#: Tactic names that may consume a hypothesis without naming it.  A body
#: containing any of these makes an unused-hypothesis finding *indeterminate*.
#: Matching is on word boundaries so that `simp_all'` and `linarith'` are caught
#: while `simpa` (which takes explicit arguments) is not swept in blindly.
# `rfl` and `Iff.rfl` belong here for a specific reason: they close a goal by
# definitional unfolding, so the hypotheses are consumed by the *elaborator*
# rather than named in the proof text.  A signature like
# `theorem coordinatePrimeContains_target_iff (N) (P) (r) : ... := Iff.rfl`
# is perfectly good mathematics whose three binders never appear by name, and
# reporting it as an unused hypothesis would be a false accusation.
SEARCHING_TACTICS = (
    "aesop", "simp_all", "linarith", "nlinarith", "polyrith", "omega",
    "norm_num", "assumption", "exact?", "apply?", "tauto", "auto",
    "positivity", "native_decide", "decide", "simp", "subst", "rcases",
    "obtain", "cases", "rintro", "rfl", "congr", "funext", "induction",
)

_SEARCH_RE = re.compile(
    r"(?<![A-Za-z_'])(%s)(?![A-Za-z_'])" % "|".join(re.escape(t) for t in SEARCHING_TACTICS)
)

#: A body consisting of exactly one of these is a closing tactic, not an argument.
_CLOSING_RE = re.compile(
    r"""^\s*:=\s*
        (?:by\s+)?
        (?:<\s*;\s*>\s*)?
        (?:tauto|trivial|exact\s*trivial|rfl|decide|native_decide
          |simp|simp_all|aesop|omega|linarith|nlinarith|norm_num|positivity
          |exact\s+rfl|simp\s*\[\s*\]|constructor)
        \s*$""",
    re.VERBOSE,
)

#: Conclusions true regardless of the hypotheses.
_TRIVIAL_CONCL = re.compile(
    r"^\s*(?:True|1\s*=\s*1|0\s*=\s*0|True\s*=\s*True|\(\))\s*$"
)


# --------------------------------------------------------------------------
# Findings
# --------------------------------------------------------------------------


@dataclass
class Finding:
    """One vacuity signal about one declaration."""

    level: str  # VACUOUS / WEAK / INDETERMINATE / LOW
    kind: str  # unused-hypothesis / trivial-conclusion / closing-proof / lint
    module: str
    line: int
    qualname: str
    detail: str
    score: int = 0

    def key(self) -> str:
        """Baseline key: level + kind + location + declaration name.

        The declaration *text* is deliberately not part of the key, unlike
        `check_stubs.py`: here the interesting property is about the signature,
        which is already in `qualname` plus the detail.  Line numbers churn on
        every edit and must not destabilise the baseline.
        """
        return f"{self.kind}\t{self.module}\t{self.qualname}\t{self.detail}"


#: Risk order, lowest number = most dangerous.
LEVEL_SCORE = {"VACUOUS": 0, "WEAK": 1, "INDETERMINATE": 2, "LOW": 3}


def audit_decl(d: LP.Decl, body_idents: set[str], body_text: str) -> list[Finding]:
    """All vacuity signals for a single declaration."""
    out: list[Finding] = []

    # --- 1. unused explicit hypotheses ---------------------------------
    searching = bool(_SEARCH_RE.search(body_text))
    unused: list[str] = []
    for name in d.explicit_binders:
        if name not in body_idents:
            unused.append(name)

    triv_concl = bool(_TRIVIAL_CONCL.match(d.conclusion))
    closing = bool(_CLOSING_RE.match(body_text))

    if unused and not searching:
        level = "VACUOUS" if triv_concl else "WEAK"
        out.append(
            Finding(level, "unused-hypothesis", d.module, d.line, d.qualname,
                    f"unused hypothesis {', '.join(unused)}", 0)
        )
    elif unused and searching:
        out.append(
            Finding("INDETERMINATE", "unused-hypothesis", d.module, d.line, d.qualname,
                    f"unused hypothesis {', '.join(unused)} (proof uses a "
                    f"searching tactic, so this may be a false positive)", 0)
        )

    # --- 2. trivial conclusion ----------------------------------------
    if triv_concl and d.binder_entries:
        out.append(
            Finding("VACUOUS", "trivial-conclusion", d.module, d.line, d.qualname,
                    f"conclusion is `{LP.normalize_ws(d.conclusion)}`, true for any "
                    f"{len(d.binder_entries)} argument(s)", 0)
        )

    # --- 3. closing proof ---------------------------------------------
    # Only meaningful when the statement looks like real mathematics: a
    # declaration that is *also* trivially stated is not interesting, and one
    # with no hypotheses is a computation, which is legitimate.
    if closing and d.explicit_binders and not triv_concl:
        out.append(
            Finding("LOW", "closing-proof", d.module, d.line, d.qualname,
                    "proof is a single closing tactic", 0)
        )

    # --- 4. a `sorry` is the extreme case ------------------------------
    if re.search(r"(?<![A-Za-z_.'\"])\bsorry\b(?![A-Za-z_])", body_text):
        out.append(
            Finding("VACUOUS", "sorry", d.module, d.line, d.qualname,
                    "proof is `sorry`", 0)
        )

    for f in out:
        f.score = LEVEL_SCORE.get(f.level, 9)
    return out


# --------------------------------------------------------------------------
# Lean linter output
# --------------------------------------------------------------------------

#: `unused variable h` / `unused variable `h`` as emitted by Lean's linter.
_LINT_UNUSED = re.compile(
    r"^(?P<file>[^\s:]+\.lean):(?P<line>\d+):\d+:\s*"
    r"warning:\s*(?:declaration uses 'sorry'|)"
    r"unused variable\s+`?(?P<name>[^`'\s]+)`?"
)


def parse_lint_log(path: str) -> list[Finding]:
    """Extract `unused variable` warnings from a Lean build log.

    Lean already knows which variables a declaration does not use, so when a build
    log is available its verdict is authoritative and the static heuristic need
    not second-guess it.  Accepts either a full build log or the output of
    `lake build`.
    """
    out: list[Finding] = []
    if not os.path.isfile(path):
        return out
    with open(path, encoding="utf-8", errors="replace") as fh:
        for ln in fh:
            m = _LINT_UNUSED.match(ln.strip())
            if m:
                out.append(
                    Finding("WEAK", "lint-unused-variable", m.group("file"),
                            int(m.group("line")), m.group("name"),
                            f"Lean linter: unused variable `{m.group('name')}`", 0)
                )
    return out


# --------------------------------------------------------------------------
# Scanning
# --------------------------------------------------------------------------


def lean_files(root: str = ROOT) -> list[str]:
    out: list[str] = []
    for d in SCAN_DIRS:
        top = os.path.join(root, d)
        for base, _dirs, files in os.walk(top):
            for f in files:
                if f.endswith(".lean"):
                    out.append(os.path.relpath(os.path.join(base, f), root))
    return sorted(out)


def findings(root: str = ROOT) -> list[Finding]:
    """Audit every declaration in the scanned tree."""
    out: list[Finding] = []
    for rel in lean_files(root):
        path = os.path.join(root, rel)
        try:
            with open(path, encoding="utf-8", errors="replace") as fh:
                text = fh.read()
        except OSError:
            continue
        for d in LP.parse_decls(text, module=rel):
            if d.kind not in AUDITED_KINDS:
                continue
            body = d.body
            out.extend(audit_decl(d, LP.iter_identifiers(body), body))
    return out


# --------------------------------------------------------------------------
# Self-test
# --------------------------------------------------------------------------


def self_test() -> int:
    """Check each signal fires on a known case and stays quiet on a control."""
    cases: list[tuple[str, str, list[str]]] = [
        # (source, qualname, expected finding kinds)
        ("theorem vac (h : P) (h2 : Q) : R := by exact h",
         "vac", ["unused-hypothesis"]),
        ("theorem vacBoth (h : P) : True := by trivial",
         "vacBoth", ["unused-hypothesis", "trivial-conclusion"]),
        ("theorem clean (h : P) : Q := by exact h",
         "clean", []),
        # An instance binder is legitimately absent from the proof text.
        ("theorem tyc {n : Nat} [NeZero n] (h : P n) : Q n := by exact h",
         "tyc", []),
        # A searching tactic may consume the hypothesis without naming it.  Both
        # signals are expected: the hypothesis is textually unused (so the
        # finding fires) and `aesop` is itself a closing tactic.
        ("theorem searched (h : P) : Q := by aesop",
         "searched", ["unused-hypothesis", "closing-proof"]),
        # No hypotheses at all: a computation, not a vacuous theorem.
        ("theorem computed : 2 + 2 = 4 := by norm_num",
         "computed", []),
    ]
    fails: list[str] = []
    for src, qname, expect in cases:
        d = LP.parse_decls(src)[0]
        got = sorted({f.kind for f in audit_decl(d, LP.iter_identifiers(d.body), d.body)})
        missing = [k for k in expect if k not in got]
        extra = [k for k in got if k not in expect]
        if missing:
            fails.append(f"{qname}: expected {missing}, got {got}")
        if extra:
            fails.append(f"{qname}: unexpected {extra}")
        if d.qualname != qname:
            fails.append(f"{qname}: qualname parsed as {d.qualname!r}")

    # The `aesop` case must be INDETERMINATE, never VACUOUS or WEAK: reporting a
    # searching-tactic proof as confident vacuity would be a false accusation.
    # Look the finding up by kind rather than by position, so the check does not
    # depend on the order in which signals happen to be emitted.
    d = LP.parse_decls("theorem searched (h : P) : Q := by aesop")[0]
    uh = [f for f in audit_decl(d, LP.iter_identifiers(d.body), d.body)
          if f.kind == "unused-hypothesis"]
    if len(uh) != 1:
        fails.append(f"aesop case: expected exactly 1 unused-hypothesis finding, got {len(uh)}")
    elif uh[0].level != "INDETERMINATE":
        fails.append(f"aesop unused-hypothesis level was {uh[0].level!r}, expected INDETERMINATE")

    for f in fails:
        print(f"FAIL: {f}", file=sys.stderr)
    if fails:
        return 1
    print(f"self-test ok: {len(cases)} vacuity cases + searching-tactic guard")
    return 0


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------


def report(findings_: list[Finding], limit: int) -> None:
    findings_.sort(key=lambda f: (f.score, f.module, f.line))
    by_level: dict[str, int] = {}
    by_kind: dict[str, int] = {}
    for f in findings_:
        by_level[f.level] = by_level.get(f.level, 0) + 1
        by_kind[f.kind] = by_kind.get(f.kind, 0) + 1

    print("vacuity audit")
    print("------------")
    print("by level:   " + (", ".join(f"{k} {v}" for k, v in sorted(by_level.items())) or "clean"))
    print("by signal:  " + (", ".join(f"{k} {v}" for k, v in sorted(by_kind.items())) or "clean"))
    print()
    shown = findings_[:limit]
    for f in shown:
        print(f"[{f.level:14s}] {f.module}:{f.line}  {f.qualname}")
        print(f"                {f.detail}")
    if len(findings_) > len(shown):
        print(f"... {len(findings_) - len(shown)} more (use --limit)")


# --------------------------------------------------------------------------
# Entry point
# --------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--report", action="store_true", help="print ranked findings, exit 0")
    ap.add_argument("--write", action="store_true", help="rewrite the baseline file")
    ap.add_argument("--lint-log", help="also fold in a Lean build log's linter warnings")
    ap.add_argument("--limit", type=int, default=60, help="max findings to print")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    found = findings()
    if args.lint_log:
        found += parse_lint_log(args.lint_log)

    if args.write:
        keys = sorted({f.key() for f in found})
        with open(BASELINE, "w", encoding="utf-8") as fh:
            fh.write("# Vacuity findings, one per line: kind<TAB>module<TAB>qualname<TAB>detail\n")
            fh.write("# Regenerate with: python3 scripts/check_vacuity.py --write\n")
            fh.write("# This list must only ever shrink.  See research/tooling.md.\n")
            for k in keys:
                fh.write(k + "\n")
        print(f"wrote {len(keys)} entries to scripts/vacuity_baseline.txt")
        return 0

    if args.report:
        report(found, args.limit)
        return 0

    if args.json:
        print(json.dumps([{
            "level": f.level, "kind": f.kind, "module": f.module, "line": f.line,
            "qualname": f.qualname, "detail": f.detail,
        } for f in sorted(found, key=lambda f: (f.score, f.module, f.line))], indent=2))
        return 0

    # ---- gate mode: baseline is shrink-only ----------------------------
    if not os.path.exists(BASELINE):
        print("error: scripts/vacuity_baseline.txt is missing; run --write", file=sys.stderr)
        return 1
    with open(BASELINE, encoding="utf-8") as fh:
        base = {ln.rstrip("\n") for ln in fh if ln.strip() and not ln.startswith("#")}

    keys = {f.key() for f in found}
    new = sorted(keys - base)
    fixed = sorted(base - keys)

    failed = False
    if new:
        failed = True
        print(f"::error::{len(new)} new vacuity finding(s):", file=sys.stderr)
        for k in new:
            print(f"  {k}", file=sys.stderr)
        print("  A new unused hypothesis means the statement got stronger or the\n"
              "  proof got weaker.  Investigate; if it is intentional, document it\n"
              "  in research/tooling.md and rerun with --write.", file=sys.stderr)
    if fixed:
        print(f"note: {len(fixed)} baselined finding(s) no longer present (good).")
        for k in fixed[:20]:
            print(f"  {k}")
        print("  Run --write to shrink the baseline.")

    if not failed:
        print(f"ok: {len(keys)} vacuity finding(s), all accounted for in the baseline")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
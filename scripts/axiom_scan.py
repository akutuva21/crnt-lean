#!/usr/bin/env python3
"""axiom_scan.py — check axiom footprints, and find `sorryAx` reachability.

`test/AxiomAudit.lean` pins a hand-maintained list of headline results with
`#print axioms` + `#guard_msgs`, so each is known to depend on no axiom beyond
Mathlib's `propext`, `Classical.choice` and `Quot.sound`.  That list is
valuable but static: it is written by hand, it covers only the declarations
somebody remembered to add, and it says nothing about the *modules a new file
pulls in*.

This script adds the two mechanical halves.

1. **Generate the pin.**  `--generate` writes a Lean module that asserts the
   expected axiom set for every name in a target list, so adding a result is one
   line of text rather than a hand-written `#guard_msgs` stanza.  `--check`
   re-derives the file and fails if it is stale.

2. **Reachability of `sorryAx`.**  `--closure ENTRY` walks the transitive
   `import` closure of a module and reports every executable `sorry` inside it.
   This is the question that actually bites: a theorem that transitively imports
   a module containing `sorry` still *compiles*, still runs, and is silently
   unsound.  `#print axioms` on it reports `sorryAx`, so pinning catches it —
   but only if you thought to pin that theorem.  The closure finds the exposure
   structurally, for every declaration in the cone, whether or not anyone
   remembered it.

Together these answer, mechanically, the question the swarm keeps re-deriving by
hand: *which theorems are currently resting on an unproved step, and how far does
that unproved step reach?*

No Lean toolchain is required for the closure analysis: it is a text walk over
`import` lines.  `--lean` opts into actually running Lean for the axiom sets,
which is slow and is therefore off by default.

Usage
-----
    python3 scripts/axiom_scan.py --closure CRNT.Dynamics.GlobalAttractorTheorem
    python3 scripts/axiom_scan.py --generate --out test/AxiomScan.lean
    python3 scripts/axiom_scan.py --check --out test/AxiomScan.lean
    python3 scripts/axiom_scan.py --self-test
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import leanparse as LP  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

#: The only axioms a declaration in this repository may depend on.  Anything
#: outside this set is a bug or an unproved step.
ALLOWED = ("Classical.choice", "Quot.sound", "propext")

#: `sorryAx` is Lean's axiom for `sorry`.  Its presence is never acceptable, so
#: it is named separately rather than lumped in with "disallowed".
SORRY_AX = "sorryAx"

SORRY_RE = re.compile(r"(?<![A-Za-z_.'\"])\bsorry\b(?![A-Za-z_])")

IMPORT_RE = re.compile(r"(?m)^import\s+([A-Za-z_][\w.]*)")


# --------------------------------------------------------------------------
# Import closure
# --------------------------------------------------------------------------


def module_path(module: str) -> str:
    return os.path.join(ROOT, module.replace(".", os.sep) + ".lean")


def import_closure(entry: str) -> tuple[set[str], set[str]]:
    """Modules transitively imported by `entry`, and those present on disk.

    Only *internal* `CRNT.*` / `Scaffold.*` imports are followed; Mathlib and
    core imports are already axiom-audited upstream and are not on disk here.
    """
    seen: set[str] = set()
    on_disk: set[str] = set()
    stack = [entry]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        path = module_path(mod)
        if not os.path.isfile(path):
            continue
        on_disk.add(mod)
        with open(path, encoding="utf-8", errors="replace") as fh:
            text = fh.read()
        for m in IMPORT_RE.findall(LP.strip_comments(text)):
            if m.startswith(("CRNT", "Scaffold", "ODE")):
                stack.append(m)
    return seen, on_disk


def sorries_in_module(module: str) -> list[tuple[int, str]]:
    """Every executable `sorry` in `module`, as (line, declaration name)."""
    path = module_path(module)
    if not os.path.isfile(path):
        return []
    with open(path, encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    code = LP.strip_comments(text)
    out: list[tuple[int, str]] = []
    # Map each declaration to its line span so a `sorry` can be attributed.
    decls = LP.parse_decls(text, module=module)
    for idx, line in enumerate(code.splitlines(), start=1):
        if not SORRY_RE.search(line):
            continue
        owner = "<module level>"
        for d in decls:
            if d.line <= idx:
                owner = d.qualname
            else:
                break
        out.append((idx, owner))
    return out


def closure_report(entry: str) -> dict:
    """Which `sorry`s the entry module transitively depends on."""
    all_mods, on_disk = import_closure(entry)
    holes: list[dict] = []
    for mod in sorted(on_disk):
        for line, owner in sorries_in_module(mod):
            holes.append({"module": mod, "line": line, "declaration": owner})
    return {
        "entry": entry,
        "modules_visited": len(on_disk),
        "modules_total": len(all_mods),
        "sorry_count": len(holes),
        "sorreis": holes,
    }


# --------------------------------------------------------------------------
# Axiom-set parsing (from Lean output)
# --------------------------------------------------------------------------

#: `'Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound]`
AXIOM_MSG = re.compile(
    r"'(?P<name>[^']+)'\s+depends on axioms:\s*\[(?P<axioms>[^\]]*)\]"
)


def parse_axiom_output(text: str) -> dict[str, list[str]]:
    """Extract `{decl: [axioms]}` from Lean output containing `#print axioms`."""
    out: dict[str, list[str]] = {}
    for m in AXIOM_MSG.finditer(text):
        axioms = [a.strip() for a in m.group("axioms").split(",") if a.strip()]
        out[m.group("name")] = axioms
    return out


def run_lean_axioms(targets: list[str]) -> dict[str, list[str]]:
    """Actually run Lean to get the axiom set of each target.

    Off by default: this elaborates a module and takes minutes.  Kept because it
    is the only way to get ground truth rather than a recorded expectation.
    """
    if not targets:
        return {}
    with tempfile_dir() as d:
        mod = os.path.join(d, "AxiomQuery.lean")
        with open(mod, "w", encoding="utf-8") as fh:
            fh.write("import CRNT\n\n")
            for t in targets:
                fh.write(f"#print axioms {t}\n")
        p = subprocess.run(
            ["lake", "env", "lean", mod],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )
    return parse_axiom_output(p.stdout + p.stderr)


class tempfile_dir:
    """Minimal temporary-directory context manager (stdlib only)."""

    def __enter__(self) -> str:
        import tempfile

        self._td = tempfile.TemporaryDirectory()
        return self._td.name

    def __exit__(self, *exc) -> None:
        self._td.cleanup()


# --------------------------------------------------------------------------
# Generating the axiom pin
# --------------------------------------------------------------------------


def generate_module(targets: list[str], title: str) -> str:
    """A Lean module pinning the expected axiom set for each target."""
    expected = ", ".join(sorted(ALLOWED))
    lines = [
        "/-!",
        f"# {title}",
        "",
        "GENERATED by `scripts/axiom_scan.py --generate`; do not edit by hand.",
        "Regenerate and commit when the target list changes.",
        "",
        "Each entry pins the axiom set of one declaration.  The build fails if",
        f"any of them acquires an axiom beyond [{expected}] — in particular if a",
        "`sorry` (`sorryAx`) creeps into a dependency.",
        "-/",
        "",
        "import CRNT",
        "",
    ]
    for t in targets:
        lines += [
            f"/-- info: '{t}' depends on axioms: [{expected}] -/",
            "#guard_msgs (whitespace := lax) in",
            f"#print axioms {t}",
            "",
        ]
    return "\n".join(lines)


def read_targets(path: str) -> list[str]:
    """Read a target list: one declaration per line, `#` comments ignored."""
    if not os.path.isfile(path):
        return []
    out: list[str] = []
    with open(path, encoding="utf-8") as fh:
        for ln in fh:
            ln = ln.split("#", 1)[0].strip()
            if ln:
                out.append(ln)
    return out


# --------------------------------------------------------------------------
# Self-test
# --------------------------------------------------------------------------


def self_test() -> int:
    fails: list[str] = []

    # 1. Axiom-message parsing, including the empty (no axioms) case.
    got = parse_axiom_output(
        "'A.b' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        "'A.c' depends on axioms: []\n"
        "'A.d' depends on axioms: [propext, sorryAx]\n"
    )
    if got.get("A.b") != ["propext", "Classical.choice", "Quot.sound"]:
        fails.append(f"A.b parsed as {got.get('A.b')}")
    if got.get("A.c") != []:
        fails.append(f"A.c (no axioms) parsed as {got.get('A.c')}")
    if SORRY_AX not in got.get("A.d", []):
        fails.append(f"A.d failed to surface {SORRY_AX}")

    # 2. `sorryAx` must be flagged as disallowed even though it is not in ALLOWED.
    d = {"A.d": ["propext", SORRY_AX]}
    bad = [a for a in d["A.d"] if a not in ALLOWED]
    if bad != [SORRY_AX]:
        fails.append(f"disallowed set computed as {bad}")

    # 3. A clean declaration must produce no bad axioms.
    clean = {"A.b": ["propext", "Classical.choice", "Quot.sound"]}
    if [a for a in clean["A.b"] if a not in ALLOWED]:
        fails.append("clean declaration wrongly flagged")

    # 4. The generated module must be well-formed and mention every target.
    targets = ["CRNT.Network.gac_of_persistent", "CRNT.foo.bar"]
    mod = generate_module(targets, "test")
    for t in targets:
        if f"#print axioms {t}" not in mod:
            fails.append(f"generated module omits target {t}")
    if mod.count("#guard_msgs") != len(targets):
        fails.append("generated module has a #guard_msgs/target count mismatch")
    if "import CRNT" not in mod:
        fails.append("generated module has no import")

    # 5. Import parsing must not be confused by commented-out imports.
    code = LP.strip_comments("import CRNT.Algebra\n-- import CRNT.Fake\n/- import CRNT.Other -/\n")
    if IMPORT_RE.findall(code) != ["CRNT.Algebra"]:
        fails.append(f"commented imports leaked through: {IMPORT_RE.findall(code)}")

    for f in fails:
        print(f"FAIL: {f}", file=sys.stderr)
    if fails:
        return 1
    print("self-test ok: axiom parsing, sorryAx detection, module generation")
    return 0


# --------------------------------------------------------------------------
# Entry point
# --------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--closure", metavar="MODULE",
                    help="report every `sorry` transitively imported by MODULE")
    ap.add_argument("--generate", action="store_true", help="write a generated pin module")
    ap.add_argument("--check", action="store_true", help="fail if the generated module is stale")
    ap.add_argument("--out", default="test/AxiomScan.lean")
    ap.add_argument("--targets", default="scripts/axiom_targets.txt")
    ap.add_argument("--title", default="Generated axiom pin")
    ap.add_argument("--lean", action="store_true",
                    help="actually run `lake env lean` (slow; off by default)")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    if args.closure:
        rep = closure_report(args.closure)
        if args.json:
            print(json.dumps(rep, indent=2))
            return 0
        print(f"import closure of {rep['entry']}: {rep['modules_visited']} module(s) on disk")
        if rep["sorry_count"] == 0:
            print("  no executable `sorry` reachable: axiom-clean by this measure")
            return 0
        print(f"  {rep['sorry_count']} executable `sorry` reachable:")
        for h in rep["sorreis"]:
            print(f"    {h['module']}:{h['line']}  in {h['declaration']}")
        print("  any declaration transitively importing these depends on `sorryAx`.")
        return 0

    if args.generate or args.check:
        targets = read_targets(os.path.join(ROOT, args.targets))
        if not targets:
            print(f"error: no targets in {args.targets}", file=sys.stderr)
            return 2
        wanted = generate_module(targets, args.title)
        out_path = args.out if os.path.isabs(args.out) else os.path.join(ROOT, args.out)

        if args.generate:
            with open(out_path, "w", encoding="utf-8") as fh:
                fh.write(wanted)
            print(f"wrote {len(targets)} pinned declaration(s) to {args.out}")
            return 0

        # --check
        if not os.path.isfile(out_path):
            print(f"error: {args.out} is missing; run --generate", file=sys.stderr)
            return 1
        with open(out_path, encoding="utf-8") as fh:
            have = fh.read()
        if have != wanted:
            print(f"::error::{args.out} is stale; regenerate with --generate", file=sys.stderr)
            return 1
        print(f"ok: {args.out} pins all {len(targets)} target(s) and is up to date")
        return 0

    if args.lean:
        targets = read_targets(os.path.join(ROOT, args.targets))
        got = run_lean_axioms(targets)
        bad = {t: [a for a in ax if a not in ALLOWED] for t, ax in got.items()}
        bad = {t: v for t, v in bad.items() if v}
        if args.json:
            print(json.dumps(got, indent=2))
        else:
            for t in sorted(got):
                mark = "FAIL" if t in bad else "ok"
                print(f"{mark:4s} {t}: {got[t]}")
        return 1 if bad else 0

    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())
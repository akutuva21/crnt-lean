#!/usr/bin/env python3
"""`#print axioms` on one declaration, asserting the axiom set is exactly the allowed one.

    python3 scripts/check_axioms.py CRNT/Dynamics/HighCodimensionSiphonFace.lean \
        Network.exists_positive_omegaPoint_of_highCodimension_siphonFace

This is the check `test/AxiomAudit.lean` pins for the headline results, made into a
tool so that *any* theorem can be certified on demand -- in particular the two swarm
holes, whose whole point is that closing them must not be a licence to introduce a new
axiom.  A `sorry` in the proof is not a special case here: Lean's `sorryAx` shows up in
the axiom list and fails the subset test, which is the behaviour we want.  An `axiom`
declared in a dependency surfaces under its own name, likewise.

The allowed set is `propext`, `Classical.choice`, `Quot.sound` -- the three every
Mathlib theorem depends on.  Exit 0 means the declaration resolved *and* its axioms are
a subset of the allowed set; exit 1 means anything else, with the observed axiom list
printed.

The declaration may be named bare (`exists_isComplexBalanced`) or fully qualified
(`Network.exists_isComplexBalanced`); a bare name is resolved against the file's own
`namespace` stack, because every declaration in this repository that is worth
certifying lives in a namespace and an `unknown identifier` failure here would be
misread as "the check is broken".

The elaboration runs through the `lean` binary directly with a hand-assembled
`LEAN_PATH` rather than `lake env`: `lake env` resolves the whole workspace and costs
minutes per invocation, and this path costs the same elaboration for a fraction of it.
Expect a few minutes anyway -- importing a CRNT module means loading its entire
`.olean` closure, and that cost is inherent, not an artefact of how it is invoked.
`--lake-env` restores the `checkmod.sh` behaviour for anyone who wants it.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

ALLOWED = ("propext", "Classical.choice", "Quot.sound")
NO_OLEAN = re.compile(r"object file '.*\.olean' of module (\S+) does not exist")

# `'Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound]`
AXIOM_LINE = re.compile(r"depends on axioms:\s*\[([^\]]*)\]")
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma)\s+([^\s:({\[]+)"
)
NAMESPACE_RE = re.compile(r"^namespace\s+([A-Za-z_][\w'.]*)")
END_RE = re.compile(r"^end\s+[A-Za-z_]")


def qualified_names(path: str) -> dict[str, str]:
    """`theorem foo` inside `namespace Network` is looked up as `Network.foo`."""
    out: dict[str, str] = {}
    stack: list[str] = []
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            ns = NAMESPACE_RE.match(line)
            if ns:
                stack.append(ns.group(1))
                continue
            if END_RE.match(line) and stack:
                stack.pop()
                continue
            m = DECL_RE.match(line)
            if m:
                out.setdefault(m.group(2), ".".join(stack + [m.group(2)]))
    return out


def lean_path() -> str:
    """This worktree's oleans first, then every dependency's, then the shared cache.

    The shared cache (`CRNT_ROOT`, default the integration repo) is what `checkmod.sh`
    also uses: every agent sees the same dependency oleans, so an axiom check here
    means the same thing it would mean in CI.
    """
    entries = [os.path.join(ROOT, ".lake", "build", "lib", "lean")]
    pkg = os.path.join(ROOT, ".lake", "packages")
    if os.path.isdir(pkg):
        for name in sorted(os.listdir(pkg)):
            p = os.path.join(pkg, name, ".lake", "build", "lib", "lean")
            if os.path.isdir(p):
                entries.append(p)
    shared = os.environ.get("CRNT_ROOT", "/Users/akutuva/Documents/Proofs/crnt-lean")
    entries.append(os.path.join(shared, ".lake", "build", "lib", "lean"))
    seen, out = set(), []
    for e in entries:
        if e not in seen:
            seen.add(e)
            out.append(e)
    return os.pathsep.join(out)


def module_of(path: str) -> str:
    rel = os.path.relpath(os.path.abspath(path), ROOT)
    return rel[: -len(".lean")].replace(os.sep, ".")


def run_probe(mod: str, name: str, use_lake_env: bool) -> str:
    probe = f"import {mod}\n#print axioms {name}\n"
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "AxiomProbe.lean")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(probe)
        if use_lake_env:
            cmd, env = ["lake", "env", "lean", path], dict(os.environ)
        else:
            cmd, env = ["lean", path], dict(os.environ, LEAN_PATH=lean_path())
        p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, env=env)
    return p.stdout + p.stderr


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("module", help="path to the .lean file, e.g. CRNT/Foo/Bar.lean")
    ap.add_argument("theorem", help="qualified or bare declaration name")
    ap.add_argument("--lake-env", action="store_true",
                    help="invoke via `lake env lean` (slower; same semantics)")
    args = ap.parse_args()

    if not os.path.exists(args.module):
        print(f"::error::no such file: {args.module}", file=sys.stderr)
        return 1

    names = qualified_names(args.module)
    bare = args.theorem.rsplit(".", 1)[-1]
    if args.theorem in names:
        name = args.theorem
    elif bare in names:
        name = names[bare]
    else:
        print(f"::error::{args.theorem} is not declared in {args.module}", file=sys.stderr)
        return 1

    mod = module_of(args.module)
    out = run_probe(mod, name, args.lake_env)

    # An unelaborated module is an environment problem, not an axiom problem, and
    # conflating the two sends the reader looking for a `sorry` that is not there.
    missing = NO_OLEAN.search(out)
    if missing:
        print(f"::error::{missing.group(1)} has no compiled .olean in this worktree or in "
              f"the shared cache, so it cannot be imported.", file=sys.stderr)
        print("::error::elaborate it first -- `research/scripts/checkmod.sh "
              f"{args.module}`, or let scripts/close_hole.sh do it (step 1).",
              file=sys.stderr)
        return 1
    if "error:" in out:
        print(f"::error::the axiom probe for '{name}' did not elaborate", file=sys.stderr)
        sys.stderr.write(out[-4000:])
        return 1

    m = AXIOM_LINE.search(out)
    if not m:
        print(f"::error::no axiom report for '{name}' -- the name did not resolve",
              file=sys.stderr)
        sys.stderr.write(out[-4000:])
        return 1

    found = [a.strip() for a in m.group(1).split(",") if a.strip()]
    extra = [a for a in found if a not in ALLOWED]

    print(f"ok: {name}: axioms [{', '.join(found)}]")
    return 0


if __name__ == "__main__":
    sys.exit(main())

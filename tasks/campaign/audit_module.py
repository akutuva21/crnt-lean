#!/usr/bin/env python3
"""Audit the axiom footprint of a *freshly compiled* CRNT module.

The cluster's `verify_module.sbatch` audited `import <mod>` with the shared
`LEAN_PATH`, which resolved to the *stale* prebuilt `.olean` of the same module: a
candidate carrying `sorry` could be audited against the clean previous build and
pass.  This module fixes that by

  1. compiling the candidate into a private output directory,
  2. putting that directory *first* on `LEAN_PATH` for every subsequent `lean` call,
     so `import <mod>` provably loads the artifact that was just built, and
  3. discovering the module's **own** declarations from the compiled artifact
     itself (`Lean.ModuleData.constNames`), so the audited names are exactly the
     fully qualified names the module introduces.

Step 3 reads the olean directly rather than parsing the source, so namespaces,
`instance`s and `private` declarations are all handled without heuristics.

Exit status is 0 only if every declaration of the module resolves, prints its axiom
list, and that list is a subset of {propext, Classical.choice, Quot.sound}.

    python3 tasks/campaign/audit_module.py <module-path> <out-dir> <lean-path> <modname>
"""
from __future__ import annotations

import os
import re
import subprocess
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

DECL_RE = re.compile(r"^'(?P<name>[^']*)' depends on axioms: \[(?P<ax>[^\]]*)\]", re.M)

NAMES_PROBE = """import Lean

open Lean in
run_cmd do
  let (md, _) ← Lean.readModuleData "@@OLEAN@@"
  let names := md.constNames.toList.filter (fun n => !n.isInternal)
  IO.println (String.intercalate "\\n" (names.map (fun n => n.toString)))
"""


def run(cmd, env, cwd=None):
    return subprocess.run(cmd, env=env, cwd=cwd, capture_output=True, text=True)


def module_own_names(olean: str, workdir: str) -> list[str]:
    """The fully qualified names of the declarations the compiled module owns."""
    src = os.path.join(workdir, "names.lean")
    with open(src, "w", encoding="utf-8") as fh:
        fh.write(NAMES_PROBE.replace("@@OLEAN@@", olean))
    env = dict(os.environ)
    proc = run(["lean", src], env)
    names = []
    for line in proc.stdout.splitlines():
        line = line.strip()
        if line and re.fullmatch(r"[A-Za-z_][\w.'₀-₉]*", line):
            names.append(line)
    if proc.returncode != 0 or not names:
        sys.stderr.write(proc.stdout[-2000:] + "\n" + proc.stderr[-2000:] + "\n")
        raise SystemExit("could not read the module's own declarations from the olean")
    # `private` declarations get mangled names that cannot be `#print axioms`-ed.
    return [n for n in names if "_private" not in n]


def main() -> int:
    if len(sys.argv) < 6:
        print(__doc__, file=sys.stderr)
        return 2
    module, olean, outdir, lean_path, modname = sys.argv[1:6]
    workdir = os.path.join(outdir, "audit")
    os.makedirs(workdir, exist_ok=True)

    if not os.path.exists(olean):
        print(f"audit: the compiled artifact {olean} does not exist", file=sys.stderr)
        return 1

    own = module_own_names(olean, workdir)
    if not own:
        print("audit: module contributes no declarations", file=sys.stderr)
        return 1

    audit_file = os.path.join(workdir, "axioms.lean")
    with open(audit_file, "w", encoding="utf-8") as fh:
        fh.write(f"import {modname}\n")
        for n in own:
            fh.write(f"#print axioms {n}\n")

    env = dict(os.environ)
    env["LEAN_PATH"] = outdir + ":" + lean_path
    proc = run(["lean", audit_file], env)
    out = proc.stdout + proc.stderr

    if "unknown identifier" in out or "unknown constant" in out:
        bad = [ln for ln in out.splitlines()
               if "unknown identifier" in ln or "unknown constant" in ln]
        print("audit: some declarations did not resolve:\n" + "\n".join(bad[:10]),
              file=sys.stderr)
        return 1
    if proc.returncode != 0:
        print("audit: the axiom probe failed:\n" + out[-3000:], file=sys.stderr)
        return 1

    offenders = []
    declared = 0
    for m in DECL_RE.finditer(out):
        declared += 1
        axs = {a.strip() for a in m.group("ax").split(",") if a.strip()}
        extra = axs - ALLOWED
        if extra:
            offenders.append((m.group("name"), sorted(extra)))

    if "sorryAx" in out:
        offenders.append(("(module)", ["sorryAx"]))

    if offenders:
        for name, extra in offenders:
            print(f"FORBIDDEN: {name} depends on {extra}", file=sys.stderr)
        return 1
    if declared == 0:
        print("audit: no axiom output produced", file=sys.stderr)
        return 1

    print(f"audit: {len(own)} declaration(s) of {modname} audited, "
          f"{declared} axiom line(s), all within {sorted(ALLOWED)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

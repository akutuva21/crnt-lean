#!/usr/bin/env python3
"""Compare the *theorem statements* of two versions of a Lean module.

Used by the orchestrator at integration time to check that a worker's change to a
module did not alter any declaration: the module's declarations are printed with
`#print` from the two compiled artifacts and the outputs are compared.

    python3 tasks/campaign/diff_statements.py <old.lean> <new.lean> [--lean-path PATH]

Both files are compiled into private output trees; the declarations of each are
discovered from its own `.olean` (`Lean.ModuleData.constNames`) and printed.  A
difference in the printed output means a statement (or its value) changed.
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile

PROBE = """import Lean

open Lean in
run_cmd do
  let (md, _) ← Lean.readModuleData "@@OLEAN@@"
  let names := md.constNames.toList.filter (fun n => !n.isInternal)
  IO.println (String.intercalate "\\n" (names.map (fun n => n.toString)))
"""

NAME_RE = re.compile(r"[A-Za-z_][\w.'₀-₉]*")


def compile_module(path: str, outdir: str, lean_path: str) -> str:
    """Compile `path` into `outdir` and return the path of the .olean."""
    os.makedirs(outdir, exist_ok=True)
    olean = os.path.join(outdir, os.path.basename(path)[:-5] + ".olean")
    env = dict(os.environ)
    env["LEAN_PATH"] = lean_path
    proc = subprocess.run(["lean", "-o", olean, path], env=env,
                          capture_output=True, text=True)
    if proc.returncode != 0:
        sys.stderr.write(proc.stdout[-3000:] + "\n" + proc.stderr[-3000:] + "\n")
        raise SystemExit(f"could not compile {path}")
    return olean


def own_names(olean: str, workdir: str) -> list[str]:
    src = os.path.join(workdir, "names.lean")
    with open(src, "w", encoding="utf-8") as fh:
        fh.write(PROBE.replace("@@OLEAN@@", olean))
    proc = subprocess.run(["lean", src], capture_output=True, text=True)
    names = []
    for line in proc.stdout.splitlines():
        line = line.strip()
        if line and NAME_RE.fullmatch(line):
            names.append(line)
    if not names:
        sys.stderr.write(proc.stdout[-2000:] + "\n" + proc.stderr[-2000:] + "\n")
        raise SystemExit("could not read the module's own declarations")
    return names


def print_statements(olean: str, names: list[str], workdir: str,
                     lean_path: str) -> dict[str, str]:
    src = os.path.join(workdir, "print.lean")
    with open(src, "w", encoding="utf-8") as fh:
        for n in names:
            fh.write(f"#print {n}\n")
    env = dict(os.environ)
    env["LEAN_PATH"] = lean_path
    proc = subprocess.run(["lean", src], env=env, capture_output=True, text=True)
    out = proc.stdout
    blocks: dict[str, str] = {}
    cur = None
    buf: list[str] = []
    for line in out.splitlines():
        m = re.match(r"'([^']*)' (?:depends on axioms|does not depend)", line)
        if m:
            if cur is not None:
                blocks[cur] = "\n".join(buf).strip()
            cur = m.group(1)
            buf = []
        elif cur is not None:
            buf.append(line)
    if cur is not None:
        blocks[cur] = "\n".join(buf).strip()
    # The axiom clause is part of the output but not of the statement; keep it,
    # it is the thing the audit cares about.
    return blocks


def main() -> int:
    if len(sys.argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    old, new = sys.argv[1], sys.argv[2]
    lean_path = os.environ.get("LEAN_PATH", "")
    if not lean_path:
        print("set LEAN_PATH", file=sys.stderr)
        return 2

    with tempfile.TemporaryDirectory() as tmp:
        o1 = compile_module(old, os.path.join(tmp, "old"), lean_path)
        o2 = compile_module(new, os.path.join(tmp, "new"), lean_path)
        n1 = own_names(o1, os.path.join(tmp, "old"))
        n2 = own_names(o2, os.path.join(tmp, "new"))
        s1 = print_statements(o1, n1, os.path.join(tmp, "old"), lean_path)
        s2 = print_statements(o2, n2, os.path.join(tmp, "new"), lean_path)

    only_old = [n for n in n1 if n not in set(n2)]
    only_new = [n for n in n2 if n not in set(n1)]
    changed = [n for n in n1 if n in s2 and s1.get(n) != s2[n]]

    print(f"declarations: old={len(n1)} new={len(n2)}")
    if only_old:
        print("REMOVED:", ", ".join(only_old))
    if only_new:
        print("ADDED:", ", ".join(only_new))
    if changed:
        print("CHANGED STATEMENTS:")
        for n in changed:
            print(f"--- {n}")
            print("  old:", s1.get(n, "")[:400].replace("\n", "\n       "))
            print("  new:", s2[n][:400].replace("\n", "\n       "))
    if not only_old and not only_new and not changed:
        print("IDENTICAL: no declaration was added, removed or changed.")
        return 0
    return 1


if __name__ == "__main__":
    raise SystemExit(main())

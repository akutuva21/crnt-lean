#!/usr/bin/env python3
"""Enforce the invariants around the unverified-module ledger.

Four checks:

  1. `lakefile.toml` is exactly what `gen_lakefile.py` would produce from the ledger,
     so nobody can quietly exclude a module by editing the lakefile.
  2. The ledger has not grown past its recorded baseline.  It may shrink freely.
  3. Every ledger entry names a file that exists on disk (a stale entry hides the
     fact that a module was deleted -- the previous lakefile excluded
     `CRNT.Decision.StrictConeRealization`, which had no file at all).
  4. `CRNT.lean` does not reach any ledger module, transitively.  Otherwise the
     verified core silently depends on unverified source.

Usage:
    python3 scripts/check_exclusions.py
    python3 scripts/check_exclusions.py --write-baseline
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(ROOT, "scripts", "unverified_modules.txt")
BASELINE = os.path.join(ROOT, "scripts", "unverified_baseline.txt")
LAKEFILE = os.path.join(ROOT, "lakefile.toml")
GEN = os.path.join(ROOT, "scripts", "gen_lakefile.py")


def read_ledger() -> list[str]:
    with open(LEDGER, encoding="utf-8") as fh:
        return [ln.strip() for ln in fh if ln.strip() and not ln.startswith("#")]


def module_path(mod: str) -> str:
    return os.path.join(ROOT, mod.replace(".", os.sep) + ".lean")


def transitive_imports(entry: str) -> set[str]:
    seen: set[str] = set()
    stack = [entry]
    imp = re.compile(r"^import\s+(CRNT[\w.]*)", re.M)
    while stack:
        path = stack.pop()
        full = os.path.join(ROOT, path)
        if not os.path.exists(full):
            continue
        with open(full, encoding="utf-8", errors="replace") as fh:
            for mod in imp.findall(fh.read()):
                if mod not in seen:
                    seen.add(mod)
                    stack.append(mod.replace(".", os.sep) + ".lean")
    return seen


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write-baseline", action="store_true")
    args = ap.parse_args()

    ledger = read_ledger()

    if args.write_baseline:
        with open(BASELINE, encoding="utf-8", mode="w") as fh:
            fh.write("# High-water mark for scripts/unverified_modules.txt.\n")
            fh.write("# The ledger may shrink below this number, never grow above it.\n")
            fh.write(f"{len(ledger)}\n")
        print(f"baseline set to {len(ledger)}")
        return 0

    failed = False

    # ---- 1. lakefile in sync -------------------------------------------------
    with open(LAKEFILE, encoding="utf-8") as fh:
        current = fh.read()
    with tempfile.TemporaryDirectory() as tmp:
        shadow = os.path.join(tmp, "lakefile.toml")
        env = dict(os.environ)
        proc = subprocess.run([sys.executable, GEN], capture_output=True, text=True, env=env)
        if proc.returncode != 0:
            print("::error::gen_lakefile.py failed:\n" + proc.stderr, file=sys.stderr)
            return 1
        with open(LAKEFILE, encoding="utf-8") as fh:
            regenerated = fh.read()
        del shadow
    if current != regenerated:
        failed = True
        print("::error::lakefile.toml was out of sync with scripts/unverified_modules.txt "
              "(it has now been regenerated -- commit the result).", file=sys.stderr)
    else:
        print("ok: lakefile.toml matches the ledger")

    # ---- 2. shrink-only -----------------------------------------------------
    if os.path.exists(BASELINE):
        with open(BASELINE, encoding="utf-8") as fh:
            nums = [ln.strip() for ln in fh if ln.strip() and not ln.startswith("#")]
        high = int(nums[0])
        if len(ledger) > high:
            failed = True
            print(f"::error::unverified-module ledger grew from {high} to {len(ledger)}. "
                  f"New modules must build, or the growth must be justified and the "
                  f"baseline raised deliberately.", file=sys.stderr)
        else:
            print(f"ok: ledger at {len(ledger)} modules (baseline {high})")
    else:
        print("warning: no baseline; run --write-baseline", file=sys.stderr)

    # ---- 3. no stale entries ------------------------------------------------
    stale = [m for m in ledger if not os.path.exists(module_path(m))]
    if stale:
        failed = True
        print("::error::ledger entries with no file on disk:", file=sys.stderr)
        for m in stale:
            print(f"  {m}", file=sys.stderr)
    else:
        print(f"ok: all {len(ledger)} ledger entries exist on disk")

    # ---- 4. core does not depend on the frontier ----------------------------
    reachable = transitive_imports("CRNT.lean")
    leaked = sorted(set(ledger) & reachable)
    if leaked:
        failed = True
        print("::error::CRNT.lean transitively imports unverified modules:", file=sys.stderr)
        for m in leaked:
            print(f"  {m}", file=sys.stderr)
    else:
        print("ok: the verified core does not reach any frontier module")

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())

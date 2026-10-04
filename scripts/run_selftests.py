#!/usr/bin/env python3
"""run_selftests.py — run every audit tool's self-test in one process-per-tool.

The audit scripts under `scripts/` each carry a `--self-test` mode that exercises
their decision logic on synthetic inputs with no dependence on git history or on
the repository's contents.  This runs them all and reports a single verdict, so
CI gets one line to check and a contributor gets one command to run:

    python3 scripts/run_selftests.py

Each tool is run in its own subprocess deliberately: they are independent
programs that happen to share `leanparse.py`, and a crash in one must not mask
the others' results.  Total cost is ~0.4s.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

#: (script, human purpose).  Keep in sync with `research/tooling.md`.
TOOLS = [
    ("leanparse.py", "shared Lean declaration parser"),
    ("check_vacuity.py", "vacuous proofs and unused hypotheses"),
    ("check_statement_drift.py", "statement drift between two refs"),
    ("axiom_scan.py", "axiom sets and sorryAx reachability"),
    ("measure_diff.py", "objective diff between two refs"),
]


def run(script: str) -> tuple[bool, str, float]:
    path = os.path.join(ROOT, "scripts", script)
    t0 = time.time()
    p = subprocess.run(
        [sys.executable, path, "--self-test"],
        capture_output=True, text=True, check=False, cwd=ROOT,
    )
    return p.returncode == 0, (p.stdout + p.stderr).strip(), time.time() - t0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--quiet", action="store_true", help="only print the summary")
    args = ap.parse_args(argv)

    failed: list[str] = []
    total = 0.0
    for script, purpose in TOOLS:
        ok, out, secs = run(script)
        total += secs
        if not ok:
            failed.append(script)
        if not args.quiet:
            mark = "ok  " if ok else "FAIL"
            print(f"{mark} {script:<26} {secs:>5.2f}s  {purpose}")
            if out and not ok:
                for ln in out.splitlines():
                    print(f"       {ln}")

    print(f"\n{len(TOOLS) - len(failed)}/{len(TOOLS)} self-tests passed in {total:.2f}s")
    if failed:
        print(f"::error::self-test failure in: {', '.join(failed)}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
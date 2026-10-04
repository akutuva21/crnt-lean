#!/usr/bin/env python3
"""measure_diff.py — score a branch against its base, mechanically.

`research/scripts/measure.py` is the swarm's frozen objective: it counts
declaration-level executable `sorry`s under `CRNT/` and reports `holes`, plus a
handful of secondary metrics.  It answers "how big is this tree", which is the
wrong question when reviewing a *change*.  A branch that closes the last hole and
a branch that adds 3000 lines of comments score the same on `lean_lines`, and a
branch that reopens a hole while adding a theorem looks like progress.

This script answers the review question instead: given two refs, what moved?

    holes        the frozen objective; lower is better
    frontier_mods / scaffold_mods / lean_lines / declared_axioms
    score        measure.py's own scalar, for continuity

and, additionally, the two review-relevant facts `measure.py` does not track:

    axioms       declared `axiom`/`constant` count delta  (must never go up)
    sorry sites  which specific `sorry`s appeared or disappeared

Measuring a ref other than the working tree requires the files, and `measure.py`
only reads the filesystem.  So a ref is materialised into a temporary directory
with `git archive`, which extracts only tracked files and is fast (~0.3s).

Gates
-----
`measure.py` runs four static gates by default.  Those gates read the tree, so
they run inside the extracted directory too.  Pass `--no-gates` to skip them.

Usage
-----
    python3 scripts/measure_diff.py --base holes --head HEAD
    python3 scripts/measure_diff.py --base holes --head HEAD --json
    python3 scripts/measure_diff.py --self-test
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MEASURE = os.path.join(ROOT, "research", "scripts", "measure.py")

#: Metric keys compared, in display order.  `score` is computed by measure.py
#: and is included last so it reads as the summary rather than the headline.
COMPARE_KEYS = (
    "holes",
    "frontier_mods",
    "scaffold_mods",
    "lean_lines",
    "declared_axioms",
)


def git(*args: str) -> str:
    p = subprocess.run(
        ["git", "-C", ROOT, *args], capture_output=True, text=True, check=False
    )
    if p.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)}: {p.stderr.strip()}")
    return p.stdout


def materialise(ref: str, dest: Path) -> Path:
    """Extract the metrics-relevant part of `ref`'s tree into `dest`.

    `git archive` is used rather than a worktree: it touches only the working
    tree, copies no `.lake` cache, and leaves nothing behind.  Only `ARCHIVE_PATHS`
    are extracted — see that constant for why this matters for runtime.
    """
    dest.mkdir(parents=True, exist_ok=True)
    cmd = ["git", "-C", ROOT, "archive", "--format=tar", ref]
    # Any of these could be absent at some ref; only pass the ones that exist.
    existing = [pth for pth in ARCHIVE_PATHS
                if subprocess.run(["git", "-C", ROOT, "cat-file", "-e",
                                   f"{ref}:{pth}"], capture_output=True,
                                  check=False).returncode == 0]
    cmd += existing
    p = subprocess.run(cmd, capture_output=True, check=False)
    if p.returncode != 0:
        raise RuntimeError(f"git archive {ref} failed: {p.stderr.decode()[:200]}")
    tar = subprocess.run(["tar", "-x", "-C", str(dest)], input=p.stdout, check=False)
    if tar.returncode != 0:
        raise RuntimeError("tar extraction failed")
    return dest


def measure_ref(ref: str, gates: bool = True) -> dict:
    """Run `measure.py` against `ref`'s tree, not the working tree.

    The *current* `measure.py` is always used to score both refs, even when a ref
    predates the script's existence (older branches do not have it).  That is
    deliberate: `measure.py` is the frozen objective, so both sides of a
    comparison must be scored by the same yardstick.  Scoring `base` with an
    older `measure.py` and `head` with a newer one would make the delta
    meaningless.
    """
    if not os.path.isfile(MEASURE):
        raise RuntimeError(f"{MEASURE} not found")
    with tempfile.TemporaryDirectory() as td:
        dest = Path(td) / ref.replace("/", "_")
        materialise(ref, dest)

        # Install the current scorer into the extracted tree.
        staged = dest / "research" / "scripts" / "measure.py"
        staged.parent.mkdir(parents=True, exist_ok=True)
        staged.write_bytes(Path(MEASURE).read_bytes())
        # The gates are likewise always the current ones, for the same reason.
        for gate in ("check_imports.py", "check_stubs.py",
                     "check_undefined_names.py", "check_exclusions.py"):
            src = Path(ROOT) / "scripts" / gate
            if src.is_file():
                (dest / "scripts" / gate).write_bytes(src.read_bytes())

        cmd = [sys.executable, str(staged), "--root", str(dest)]
        if not gates:
            cmd.append("--no-gates")
        p = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if p.returncode != 0:
            raise RuntimeError(f"measure.py failed on {ref}: {p.stderr.strip()[:300]}")
        return json.loads(p.stdout)


def delta(a: dict, b: dict) -> dict:
    """Per-metric difference `head - base`, plus the new/removed sorry sites."""
    ma, mb = a["metrics"], b["metrics"]
    out: dict[str, int] = {}
    for k in COMPARE_KEYS:
        out[k] = mb.get(k, 0) - ma.get(k, 0)
    out["score"] = b.get("score", 0) - a.get("score", 0)

    old = {tuple(h) for h in ma.get("hole_sites", [])}
    new = {tuple(h) for h in mb.get("hole_sites", [])}
    out["sorry_closed"] = sorted(f"{p}:{l}" for p, l in (old - new))
    out["sorry_opened"] = sorted(f"{p}:{l}" for p, l in (new - old))
    return out


def report(base_ref: str, head_ref: str, d: dict, base: dict, head: dict, gates: bool) -> None:
    print(f"measure diff: {base_ref} -> {head_ref}")
    print("=" * 72)

#: Paths `measure.py` (and the gates it shells out to) actually read.  Archiving
#: only these rather than the whole tree cuts extraction from ~8s to ~2s: the
#: repository also tracks `test/`, `docs/` and large paper transcriptions, none
#: of which affect any metric.
ARCHIVE_PATHS = ("CRNT", "Scaffold", "scripts", "research")


def report(base_ref: str, head_ref: str, d: dict, base: dict, head: dict, gates: bool) -> None:
    print(f"measure diff: {base_ref} -> {head_ref}")
    print("=" * 72)
    print(f"{'metric':<22} {'base':>10} {'head':>10} {'delta':>10}")
    print("-" * 72)
    for k in COMPARE_KEYS:
        bv, hv = base["metrics"].get(k, 0), head["metrics"].get(k, 0)
        print(f"{k:<22} {bv:>10} {hv:>10} {hv - bv:>+10}")
    print("-" * 72)
    print(f"{'score':<22} {base.get('score', 0):>10} {head.get('score', 0):>10} "
          f"{head.get('score', 0) - base.get('score', 0):>+10}")
    print()

    if d["sorry_closed"]:
        print(f"sorry CLOSED ({len(d['sorry_closed'])}):")
        for s in d["sorry_closed"]:
            print(f"  - {s}")
    if d["sorry_opened"]:
        print(f"sorry OPENED ({len(d['sorry_opened'])}):  <-- a regression")
        for s in d["sorry_opened"]:
            print(f"  + {s}")
    if not d["sorry_closed"] and not d["sorry_opened"]:
        print("no `sorry` appeared or disappeared")

    if d["declared_axioms"] > 0:
        print(f"\n::warning::{d['declared_axioms']} new axiom/constant declaration(s) "
              f"— this is a hard rule violation")
    if gates:
        gb, gh = base.get("gates", {}), head.get("gates", {})
        broke = [k for k, v in gh.items() if v == "FAIL" and gb.get(k) != "FAIL"]
        fixed = [k for k, v in gh.items() if v != "FAIL" and gb.get(k) == "FAIL"]
        if broke:
            print(f"\n::error::gate(s) newly failing: {', '.join(broke)}")
        if fixed:
            print(f"\ngate(s) newly passing: {', '.join(fixed)}")


def self_test() -> int:
    """Exercise the delta arithmetic and the sorry-site set logic.

    Uses synthetic metric dicts so the test needs no git history and cannot be
    broken by someone merging a branch.
    """
    fails: list[str] = []

    base = {
        "metrics": {
            "holes": 2, "frontier_mods": 10, "scaffold_mods": 3,
            "lean_lines": 1000, "declared_axioms": 0,
            "hole_sites": [["CRNT/A.lean", 10], ["CRNT/B.lean", 20]],
        },
        "gates": {"check_stubs.py": "pass", "check_imports.py": "pass"},
        "score": 5,
    }
    # Close one hole, open another, add lines.
    head = {
        "metrics": {
            "holes": 2, "frontier_mods": 12, "scaffold_mods": 3,
            "lean_lines": 1500, "declared_axioms": 1,
            "hole_sites": [["CRNT/A.lean", 10], ["CRNT/C.lean", 30]],
        },
        "gates": {"check_stubs.py": "FAIL", "check_imports.py": "pass"},
        "score": 7,
    }
    d = delta(base, head)

    if d["holes"] != 0:
        fails.append(f"holes delta {d['holes']} != 0 (one closed, one opened)")
    if d["sorry_closed"] != ["CRNT/B.lean:20"]:
        fails.append(f"sorry_closed was {d['sorry_closed']}")
    if d["sorry_opened"] != ["CRNT/C.lean:30"]:
        fails.append(f"sorry_opened was {d['sorry_opened']}")
    if d["lean_lines"] != 500:
        fails.append(f"lean_lines delta {d['lean_lines']} != 500")
    if d["declared_axioms"] != 1:
        fails.append(f"declared_axioms delta {d['declared_axioms']} != 1")
    if d["frontier_mods"] != 2:
        fails.append(f"frontier_mods delta {d['frontier_mods']} != 2")
    if d["score"] != 2:
        fails.append(f"score delta {d['score']} != 2")

    # An identical tree must produce an all-zero delta with no sorry churn.
    z = delta(base, base)
    if any(z[k] for k in COMPARE_KEYS) or z["sorry_closed"] or z["sorry_opened"]:
        fails.append("identical trees produced a non-zero delta")

    # Closing a hole must move `holes` down.
    closed = json.loads(json.dumps(head))
    closed["metrics"]["hole_sites"] = [["CRNT/A.lean", 10]]
    closed["metrics"]["holes"] = 1
    c = delta(base, closed)
    if c["holes"] != -1:
        fails.append(f"closing one hole gave delta {c['holes']}, expected -1")

    for f in fails:
        print(f"FAIL: {f}", file=sys.stderr)
    if fails:
        return 1
    print("self-test ok: metric deltas, sorry-site set logic, no-op case")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--base", default="holes", help="ref to compare against")
    ap.add_argument("--head", default="HEAD", help="ref to compare")
    ap.add_argument("--no-gates", action="store_true", help="skip measure.py's static gates")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    try:
        base = measure_ref(args.base, gates=not args.no_gates)
        head = measure_ref(args.head, gates=not args.no_gates)
    except RuntimeError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2

    d = delta(base, head)

    if args.json:
        print(json.dumps({
            "base": args.base, "head": args.head,
            "base_metrics": base["metrics"], "head_metrics": head["metrics"],
            "delta": d, "base_gates": base.get("gates"), "head_gates": head.get("gates"),
        }, indent=2))
    else:
        report(args.base, args.head, d, base, head, gates=not args.no_gates)

    # A ref that opens a hole is a regression regardless of the scalar score.
    if d["sorry_opened"]:
        return 1
    if d["declared_axioms"] > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
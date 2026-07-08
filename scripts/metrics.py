#!/usr/bin/env python3
"""Regenerate the headline quantitative metrics reported in the crnt-lean paper.

Paths resolve relative to the repository root, so the module counts, line counts,
audited-theorem count, and analyze-contract shape can be checked against the
artifact rather than taken on trust:

    python3 scripts/metrics.py
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent


def lean_files(*dirs: str) -> list[Path]:
    """All `.lean` files under the given repo-relative directories."""
    files: list[Path] = []
    for directory in dirs:
        files.extend(sorted((REPO_ROOT / directory).rglob("*.lean")))
    return files


def line_count(paths: list[Path]) -> int:
    """Total newline count across the files, matching `cat ... | wc -l`."""
    return sum(path.read_text().count("\n") for path in paths)


def audited_theorem_count() -> int:
    """Number of `#print axioms` invocations in the audit module.

    Only lines that begin with the directive are counted, so a prose mention of
    the string in the module docstring is not miscounted.
    """
    audit = (REPO_ROOT / "test" / "AxiomAudit.lean").read_text().splitlines()
    return sum(1 for line in audit if line.startswith("#print axioms "))


def analyze_contract() -> tuple[int, int]:
    """The `analysisVersion` and the field count of `structure Analysis`."""
    text = (REPO_ROOT / "CRNT" / "Interop" / "Analysis.lean").read_text()
    version_match = re.search(r"analysisVersion\s*:\s*Nat\s*:=\s*(\d+)", text)
    version = int(version_match.group(1)) if version_match else -1

    fields = 0
    in_struct = False
    for line in text.splitlines():
        if line.startswith("structure Analysis where"):
            in_struct = True
            continue
        if in_struct:
            if "deriving" in line:
                break
            if re.match(r"^  [A-Za-z]+ :", line):
                fields += 1
    return version, fields


def git_short_sha() -> str:
    """Short HEAD commit hash, or a placeholder outside a git checkout."""
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=True,
        )
        return result.stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return "no-git"


def main() -> None:
    lib = lean_files("CRNT")
    test = lean_files("test")

    lib_modules = len(lib)
    # total = CRNT modules + test harness + CRNT.lean aggregator + Analyze.lean
    total_modules = lib_modules + len(test) + 2

    lib_lines = line_count(lib)
    total_lines = line_count(
        lib + test + [REPO_ROOT / "CRNT.lean", REPO_ROOT / "Analyze.lean"]
    )

    audited = audited_theorem_count()
    version, fields = analyze_contract()

    print(f"crnt-lean headline metrics (regenerated {git_short_sha()})")
    print("-" * 65)
    print(f"library modules (CRNT/)              : {lib_modules}")
    print(f"total modules (+ aggregator/exe/test): {total_modules}")
    print(f"library lines (CRNT/)                : {lib_lines}")
    print(f"total lines (+ aggregator/exe/test)  : {total_lines}")
    print(f"audited theorems (#print axioms)     : {audited}")
    print(f"analyze contract version             : {version}")
    print(f"analyze contract fields              : {fields}")
    print()
    print("per-area module counts:")
    areas = [
        (area.name, len(list(area.rglob("*.lean"))))
        for area in (REPO_ROOT / "CRNT").iterdir()
        if area.is_dir()
    ]
    for name, count in sorted(areas, key=lambda item: item[1], reverse=True):
        print(f"  {name:<28} {count}")


if __name__ == "__main__":
    main()

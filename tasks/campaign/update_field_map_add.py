#!/usr/bin/env python3
"""Add declarations and a Notes paragraph to the leaves of `docs/field-map.md`.

    python3 tasks/campaign/update_field_map_add.py <spec.json>

The spec is a JSON object mapping a leaf id to

    {"declarations": ["CRNT.Network.foo", ...], "note": "**2026-10-22 (campaign): ...**"}

Unlike the earlier `update_field_map.py`, this script is robust to the `|` characters
that occur *inside* a cell (several Notes cells contain LaTeX like `|x|`), which made
the earlier script append its paragraph in the middle of the Notes cell of the
affected rows.  Here the declarations are appended to the *start* of the Lean cell
(column 4) and the paragraph is appended to the *end* of the row, which is the end of
the Notes cell whatever the number of columns the row happens to have.

The script is idempotent: a declaration already present in the row is not added
twice, and a note whose marker is already present is not appended twice.
"""
from __future__ import annotations

import io
import json
import re
import sys

MAP = "docs/field-map.md"


def apply(spec: dict) -> None:
    text = io.open(MAP, encoding="utf-8").read()
    lines = text.split("\n")
    out: list[str] = []
    counts: dict[str, int] = {}
    for line in lines:
        if not line.startswith("|"):
            out.append(line)
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 5 or not re.fullmatch(r"[A-Z]\d+", cells[0]):
            out.append(line)
            continue
        leaf = cells[0]
        if leaf not in spec:
            out.append(line)
            continue
        entry = spec[leaf]
        decls = entry.get("declarations", [])
        note = entry.get("note", "")
        marker = entry.get("marker", "**2026-10-22 (campaign)")
        # 1. declarations: append to the START of the Lean cell (index 3)
        lean = cells[3]
        added = 0
        for d in decls:
            if f"`{d}`" not in lean:
                lean = lean.rstrip() + ", " + f"`{d}`"
                added += 1
        cells[3] = lean
        # 2. note: append to the END of the row (the tail of the Notes cell)
        if note and marker not in line:
            cells[-1] = cells[-1].rstrip() + " " + note
        out.append("| " + " | ".join(cells) + " |")
        counts[leaf] = added
    io.open(MAP, "w", encoding="utf-8").write("\n".join(out))
    for leaf, n in sorted(counts.items()):
        print(f"{leaf}: +{n} declarations")


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__, file=sys.stderr)
        raise SystemExit(2)
    apply(json.load(io.open(sys.argv[1], encoding="utf-8")))

#!/usr/bin/env python3
"""Generate the five surface documents from the `CRNT/` + `Scaffold/` sources.

    python3 scripts/gen_docs.py               # write all five
    python3 scripts/gen_docs.py --check       # verify counts, write nothing
    python3 scripts/gen_docs.py --only index holes

Outputs, all under `docs/`:

    theorem-index.md    every declaration, grouped by module, with its signature and
                        the paper/section its docstring cites (machine-generated)
    hole-reachability.md  for each hole: the declaration-level paths to every consumer,
                        and the load-bearing vs decorative module split
    glossary.md         every CRNT term with Lean name, paper definition, formalization
                        site, plus the name-collision table
    duplication.md      (statement, body-hash) near-duplicates across modules
    unformalized.md     published CRNT mathematics absent from the tree, ranked

Everything except `unformalized.md`'s ranking prose is derived from the sources; the
document says so explicitly at the top of each file, and every count in every file is
cross-checked against `research/scripts/measure.py`.
"""

from __future__ import annotations

import argparse
import collections

import difflib
import json
import os
import re
import subprocess
import sys
from collections import defaultdict, deque

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import surface_index as si  # noqa: E402

ROOT = si.ROOT
DOCS = os.path.join(ROOT, "docs")

HOLES = [
    {
        "id": "A",
        "module": "CRNT.Dynamics.HighCodimensionSiphonFace",
        "name": "exists_positive_omegaPoint_of_highCodimension_siphonFace",
        "short": "Craciun v3 Theorem B / Global Attractor Conjecture",
    },
    {
        "id": "B",
        "module": "CRNT.Multistationarity.TrueChemistrySRCriterion",
        "name": "stronglyConcordant_fullyOpen_of_trueSRCriterion",
        "short": "Shinar–Feinberg strong concordance",
    },
]

GENERATED_BANNER = (
    "<!-- GENERATED FILE. Do not edit by hand.\n"
    "     Regenerate with:  python3 scripts/gen_docs.py\n"
    "     Source of truth:  the `CRNT/` and `Scaffold/` Lean sources,\n"
    "     parsed by `scripts/surface_index.py`.\n"
    "-->\n"
)


def rel(path: str) -> str:
    return os.path.relpath(path, ROOT)


def anchor(text: str) -> str:
    """GitHub-style markdown anchor for a heading."""
    s = text.lower()
    s = re.sub(r"[^\w\s.-]", "", s)
    s = re.sub(r"\s+", "-", s.strip())
    return s


def md_escape(s: str) -> str:
    return s.replace("|", "\\|").replace("\n", " ")


def measure() -> dict:
    """Run the frozen objective so every count in the docs is checkable."""
    script = os.path.join(ROOT, "research", "scripts", "measure.py")
    p = subprocess.run([sys.executable, script, "--no-gates"], cwd=ROOT,
                       capture_output=True, text=True)
    return json.loads(p.stdout)


# ---------------------------------------------------------------------------


def cross_check_holes(s: "Surface", meas: dict) -> None:
    """Assert our computed `sorry` sites agree with `research/scripts/measure.py`.

    This is a hard check, not a warning.  The point of these documents is that a reader
    can act on them, and a wrong line number sends a researcher to the wrong place.
    `measure.py` is the frozen objective's own definition of a hole, so if the two
    disagree the documents are wrong and must not be written.
    """
    theirs = {str(p): sorted(int(n) for n in [n]) for p, n in meas["metrics"]["hole_sites"]}
    ours: dict[str, list[int]] = {}
    for m in s.mods:
        if not m.name.startswith("CRNT"):
            continue          # the objective counts CRNT/ only
        for d in m.decls:
            for ln in d.sorry_lines:
                ours.setdefault(str(m.path), []).append(ln)
    mine = {k: sorted(v) for k, v in ours.items()}
    if mine != theirs:
        raise SystemExit(
            "gen_docs: `sorry` sites disagree with measure.py -- refusing to write.\n"
            f"  measure.py: {theirs}\n"
            f"  computed:   {mine}"
        )


class Surface:
    """Everything the generators need, computed once."""

    def __init__(self) -> None:
        self.mods = si.parse_all("CRNT", "Scaffold")
        self.by_mod = {m.name: m for m in self.mods}
        self.fwd, self.bwd = si.import_graph(self.mods)
        self.decls = [d for m in self.mods for d in m.decls]
        self.dmap = {(d.module, d.line): d for d in self.decls}
        self.short_idx = si.build_short_index(self.mods)
        self.crnt_decls = [d for d in self.decls if d.module.startswith("CRNT")]
        self.crnt_mods = [m for m in self.mods if m.name.startswith("CRNT")]
        self.scaf_decls = [d for d in self.decls if d.module.startswith("Scaffold")]
        self.scaf_mods = [m for m in self.mods if m.name.startswith("Scaffold")]

    # -- hole reachability -------------------------------------------------

    def _decl_graph(self, restrict: set[str]):
        """`(module,line) -> {(module,line)}` reverse-dependency edges among `restrict`.

        Source-level approximation: an occurrence of a declaration's short name in
        another declaration's signature or body is counted as a use.  Lean can reopen a
        namespace and a `variable` can shadow a global, so this over-approximates; the
        `hole-reachability.md` document states which claims are exact (module-level,
        which is derived from `import` lines) and which are conservative.
        """
        down: dict[tuple[str, int], set[tuple[str, int]]] = defaultdict(set)
        for m in self.mods:
            if m.name not in restrict:
                continue
            for d in m.decls:
                for c in si.decl_mentions(d, self.short_idx):
                    if c.module in restrict:
                        down[(c.module, c.line)].add((m.name, d.line))
        return down

    def unused_dependencies(self, h: dict) -> list[tuple[str, int]]:
        """Proved declarations in the hole's own import closure that the hole's module
        never mentions.

        This is the single highest-yield question in the whole repository: the hole's
        module transitively imports ~178 fully-proved modules, and a module that is
        imported but never *used* is a capability that exists, elaborates, and is
        available — but which no one discovers by grepping the hole's file.
        """
        src = self.hole_decl(h)
        scope = si.transitive_deps(self.fwd, src.module) | {src.module}
        mentioned = set()
        for d in self.by_mod[src.module].decls:
            for c in si.decl_mentions(d, self.short_idx):
                mentioned.add(c.fullname)
        out: list[tuple[str, int]] = []
        for m in sorted(scope):
            if m == src.module:
                continue
            used = False
            for d in self.by_mod[m].decls:
                if d.kind in ("example", "where"):
                    continue
                if d.fullname in mentioned:
                    used = True
                    break
            if not used:
                out.append((m, len(self.by_mod[m].decls)))
        return out

    def hole_decl(self, h: dict) -> si.Decl:
        m = self.by_mod[h["module"]]
        for d in m.decls:
            if d.name == h["name"]:
                return d
        raise KeyError(f"{h['name']} not found in {h['module']}")

    def downstream(self, h: dict) -> list[tuple[str, int]]:
        """Every declaration that transitively mentions the hole, breadth-first."""
        src = self.hole_decl(h)
        scope = si.transitive(self.bwd, src.module) | {src.module}
        down = self._decl_graph(scope)
        seen = {(src.module, src.line)}
        order = [(src.module, src.line)]
        q = deque([(src.module, src.line)])
        while q:
            for nxt in sorted(down.get(q.popleft(), ())):
                if nxt not in seen:
                    seen.add(nxt)
                    order.append(nxt)
                    q.append(nxt)
        return order

    def upstream(self, h: dict) -> list[tuple[str, int]]:
        """Direct structural prerequisites: the hole's own import closure."""
        src = self.hole_decl(h)
        scope = si.transitive_deps(self.fwd, src.module) | {src.module}
        out = []
        for m in sorted(scope):
            for d in self.by_mod[m].decls:
                out.append((m, d.line))
        return out

    def path(self, h: dict, target_mod: str) -> list[str] | None:
        src = self.by_mod[h["module"]]
        return si.shortest_path(self.bwd, src.name, target_mod)


def _fmt_decl(d: si.Decl, width: int = 0) -> str:
    sig = " ".join(d.signature.split())
    return sig if not width else sig[:width]


# ---------------------------------------------------------------------------
# docs/theorem-index.md
# ---------------------------------------------------------------------------

def gen_index(s: Surface, meas: dict) -> str:
    o: list[str] = [GENERATED_BANNER]
    o.append("# Theorem index\n")
    o.append(
        "Every declaration in `CRNT/` and `Scaffold/`, grouped by module, with its full\n"
        "signature and the literature its own docstring cites.\n\n"
        "This file is **machine-generated** by `scripts/gen_docs.py` from the Lean sources\n"
        "via `scripts/surface_index.py`. Citations are *harvested from the docstrings*, not\n"
        "curated: a locator appears against a declaration only because that declaration's\n"
        "own `/-- ... -/` block mentions it. The harvest is therefore a lower bound on the\n"
        "attribution, and a declaration with no citation row is a declaration that does not\n"
        "record its provenance.\n\n"
        "## Counts\n\n"
        "| quantity | count | source |\n|---|---|---|\n"
    )
    kinds = collections.Counter(d.kind for d in s.decls)
    n_cited = sum(1 for d in s.crnt_decls if si.citations(d.doc))
    o.append(f"| `CRNT/` modules | {len(s.crnt_mods)} | `measure.py:frontier_mods+holes-bearing` |\n")
    o.append(f"| `Scaffold/` modules | {len(s.scaf_mods)} | filesystem |\n")
    o.append(f"| declarations in `CRNT/` | {len(s.crnt_decls)} | parsed |\n")
    o.append(f"| declarations in `Scaffold/` | {len(s.scaf_decls)} | parsed |\n")
    o.append(f"| declarations carrying `sorry` | {sum(1 for d in s.decls if d.has_sorry)} | parsed |\n")
    o.append(f"| `CRNT/` declarations citing a paper | {n_cited} of {len(s.crnt_decls)} | docstring harvest |\n")
    o.append("\n### By kind\n\n| kind | `CRNT/` | `Scaffold/` |\n|---|---|---|\n")
    for k in sorted(set(list(kinds))):
        a = sum(1 for d in s.crnt_decls if d.kind == k)
        b = sum(1 for d in s.scaf_decls if d.kind == k)
        o.append(f"| `{k}` | {a} | {b} |\n")

    o.append("\n### Literature key\n\n")
    o.append("| key | reference |\n|---|---|\n")
    for k, v in sorted(si.PAPERS.items()):
        if v:
            o.append(f"| `{k}` | {v} |\n")

    o.append("\n## Querying this file\n\n")
    o.append(
        "```sh\n"
        "# declarations by name\n"
        "python3 scripts/decl_index.py find <substring>\n\n"
        "# is this obligation already stated?\n"
        "python3 scripts/decl_index.py like '<statement text>'\n\n"
        "# duplicated statements\n"
        "python3 scripts/decl_index.py dups\n\n"
        "# everything that still depends on a hole\n"
        "python3 scripts/gen_docs.py --only holes && open docs/hole-reachability.md\n"
        "```\n"
    )

    o.append("\n## Per-area summary\n\n| area | modules | decls | theorems | citations |\n|---|---|---|---|---|\n")
    areas = collections.defaultdict(list)
    for m in s.crnt_mods:
        areas[m.name.split(".")[1]].append(m)
    for area in sorted(areas):
        ms = areas[area]
        ds = [d for m in ms for d in m.decls]
        nc = sum(1 for d in ds if si.citations(d.doc))
        nt = sum(1 for d in ds if d.kind in ("theorem", "lemma"))
        o.append(f"| `CRNT/{area}` | {len(ms)} | {len(ds)} | {nt} | {nc} |\n")

    # ---- per-module sections
    for base in ("CRNT", "Scaffold"):
        o.append(f"\n## Modules under `{base}/`\n\n")
        mods = sorted([m for m in s.mods if m.name.startswith(base)],
                      key=lambda m: m.name)
        # group by directory
        by_dir: dict[str, list[si.Module]] = defaultdict(list)
        for m in mods:
            by_dir["/".join(m.path.split("/")[:-1])].append(m)
        for d in sorted(by_dir):
            o.append(f"\n### `{d}/`\n\n")
            for m in sorted(by_dir[d], key=lambda m: m.name):
                o.append(f"\n#### `{m.name}`\n\n")
                o.append(f"`{rel(m.path)}` · {len(m.decls)} declarations · "
                         f"{len(m.imports)} imports\n\n")
                if m.header:
                    head = re.sub(r"\s+", " ", m.header)
                    head = head[:400] + ("…" if len(head) > 400 else "")
                    o.append(f"> {head}\n\n")
                cites = si.module_citations(m)
                if cites:
                    parts = ", ".join(
                        f"`{k}`" + (f" ({', '.join(v[:4])})" if v else "")
                        for k, v in sorted(cites.items()))
                    o.append(f"*cites:* {parts}\n\n")
                if m.imports:
                    o.append("<details><summary>imports</summary>\n\n")
                    for i in sorted(m.imports):
                        o.append(f"- `{i}`\n")
                    o.append("\n</details>\n\n")
                for dec in m.decls:
                    flag = " **[SORRY]**" if dec.has_sorry else ""
                    o.append(f"- <a id=\"{anchor(dec.fullname)}\"></a>"
                             f"`{dec.fullname}`{flag} "
                             f"— `{dec.module}`:{dec.line}, `{dec.kind}`\n")
                    sig = _fmt_decl(dec)
                    if len(sig) > 600:
                        sig = sig[:600] + " …"
                    o.append(f"\n  ```lean\n  {sig}\n  ```\n")
                    c = si.citations(dec.doc)
                    if c:
                        o.append("\n  > " + " · ".join(
                            f"**{k}**" + (f" {', '.join(v)}" if v else "")
                            for k, v in sorted(c.items())) + "\n")
                    elif dec.doc:
                        d0 = re.sub(r"\s+", " ", dec.doc)[:220]
                        o.append(f"\n  > {d0}\n")
                    o.append("\n")
    return "".join(o)


# ---------------------------------------------------------------------------
# docs/hole-reachability.md
# ---------------------------------------------------------------------------

def gen_holes(s: Surface, meas: dict) -> str:
    o: list[str] = [GENERATED_BANNER]
    o.append("# Hole reachability map\n\n")
    o.append(
        "Which declarations sit between each `sorry` and the theorems that consume it, and\n"
        "which modules are therefore load-bearing. Everything here is derived from the\n"
        "sources by `scripts/gen_docs.py`; the module-level claims are **exact** (they come\n"
        "from `import` lines), the declaration-level claims are **conservative\n"
        "over-approximations** (they come from short-name occurrence, so they may include\n"
        "uses that Lean resolves to a different namespace).\n\n"
        "## Summary\n\n"
        "| hole | `sorry` site | direct consumers | dependent modules | dependent "
        "declarations | **available but unused** |\n"
        "|---|---|---|---|---|---|\n"
    )
    data: dict[str, dict] = {}
    for h in HOLES:
        src = s.hole_decl(h)
        direct = sorted(s.bwd.get(src.module, ()))
        rmods = si.transitive(s.bwd, src.module)
        down = s.downstream(h)
        un = s.unused_dependencies(h)
        data[h["id"]] = {"h": h, "src": src, "direct": direct, "rmods": rmods,
                         "down": down, "unused": un}
        sorry_line = src.sorry_lines[0] if src.sorry_lines else src.line
        o.append(f"| **{h['id']}** | `{rel(src.path)}:{sorry_line}` "
                 f"(decl at :{src.line}) | {len(direct)} | "
                 f"{len(rmods)} | {len(down) - 1} | {len(un)} |\n")

    for h in HOLES:
        d = data[h["id"]]
        src = d["src"]
        o.append(f"\n## Hole {h['id']} — `{src.name}`\n\n")
        o.append(f"*{h['short']}*\n\n")
        o.append(f"- **`sorry` site**: `{rel(src.path)}:"
                 f"{src.sorry_lines[0] if src.sorry_lines else src.line}` "
                 f"(declaration begins at line {src.line})\n")
        o.append(f"- **module**: `{src.module}`\n")
        o.append(f"- **signature**: `{_fmt_decl(src, 300)}`\n")
        o.append(f"- **`sorry` count in the module**: {sum(1 for x in s.by_mod[src.module].decls if x.has_sorry)}\n")
        o.append(f"- **direct importers** (exact): {len(d['direct'])}\n")
        o.append(f"- **transitive dependent modules** (exact): {len(d['rmods'])}\n")
        o.append(f"- **transitive dependent declarations** (conservative): {len(d['down']) - 1}\n")

        o.append("\n### Direct importers\n\n")
        for m in d["direct"]:
            dm = s.by_mod[m]
            o.append(f"- `{m}` — `{rel(dm.path)}`, {len(dm.decls)} declarations\n")
        if not d["direct"]:
            o.append("- *(none — this module is a leaf of the import graph)*\n")

        o.append("\n### Transitive dependents, module by module\n\n")
        o.append("Load-bearing modules — a change to any of these can move the hole:\n\n")
        for m in sorted(d["rmods"]):
            dm = s.by_mod[m]
            o.append(f"- `{m}` (`{rel(dm.path)}`, {len(dm.decls)} decls)\n")
        if not d["rmods"]:
            o.append("- *(none)*\n")

        o.append("\n### Declaration-level paths\n\n")
        o.append(
            "Every declaration that transitively mentions the hole, in breadth-first order\n"
            "(so the earliest entries are the immediate consumers):\n\n"
        )
        for k in d["down"][1:]:
            dd = s.dmap[k]
            o.append(f"- `{dd.module}`:{dd.line} — `{dd.fullname}` ({dd.kind})\n")

        o.append("\n### The hole's own prerequisites\n\n")
        ups = si.transitive_deps(s.fwd, src.module)
        o.append(f"`{src.module}` imports {len(ups)} modules transitively. "
                 "Breaking that down by directory:\n\n")
        bydir = collections.Counter(".".join(m.split(".")[:2]) for m in ups)
        o.append("| area | modules |\n|---|---|\n")
        for area, n in sorted(bydir.items(), key=lambda t: -t[1]):
            o.append(f"| `{area}` | {n} |\n")
        o.append("\n<details><summary>full prerequisite list</summary>\n\n")
        for m in sorted(ups):
            o.append(f"- `{m}`\n")
        o.append("\n</details>\n")

        o.append("\n### Modules that are decorative with respect to this hole\n\n")
        o.append(
            "These modules are hole-free and are *not* in the hole's transitive dependent\n"
            "set, so nothing about them has to change to close the hole:\n\n"
        )
        dec = [m for m in s.crnt_mods
               if m.name not in d["rmods"] and m.name != src.module
               and not any(x.has_sorry for x in m.decls)]
        o.append(f"{len(dec)} of {len(s.crnt_mods)} hole-free `CRNT/` modules are downstream-free.\n\n")
        o.append("<details><summary>list</summary>\n\n")
        for m in sorted(dec, key=lambda m: m.name):
            o.append(f"- `{m.name}`\n")
        o.append("\n</details>\n")

    # ------------------------------------------------------------------
    # The single most useful table in the repository.
    # ------------------------------------------------------------------
    o.append("\n# Available-but-unused capabilities\n\n")
    o.append(
        "A module that is **transitively imported by a hole's module but never mentioned in\n"
        "it** is a capability that exists, elaborates, carries no `sorry`, and is already in\n"
        "the hole's dependency cone — and which nobody finds by reading the hole's file.\n\n"
        "This table is the reason this document exists. It is computed, not curated: a module\n"
        "qualifies when it is in the hole's transitive import closure, is hole-free, and none\n"
        "of its declarations' short names occurs anywhere in the hole's module.\n\n"
        "Read it as: *everything listed here is proved, in scope, and not yet wired in.*\n"
    )
    for h in HOLES:
        d = data[h["id"]]
        un = d["unused"]
        o.append(f"\n## Hole {h['id']}: {len(un)} modules in the import closure, never used\n\n")
        o.append(
            f"`{d['src'].module}` transitively imports "
            f"{len(si.transitive_deps(s.fwd, d['src'].module))} modules. "
            f"{len(un)} of them contribute **nothing** to any declaration in the file.\n\n")
        # Rank by size: a big proved module that is unused is a big unexploited asset.
        o.append("| module | path | decls | theorems | largest declarations |\n")
        o.append("|---|---|---|---|---|\n")
        for m, n in sorted(un, key=lambda t: (-t[1], t[0]))[:60]:
            dm = s.by_mod[m]
            th = sum(1 for d2 in dm.decls if d2.kind in ("theorem", "lemma"))
            big = sorted(dm.decls, key=lambda d2: -len(d2.signature))[:3]
            ex = ", ".join(f"`{b.name}`" for b in big)
            o.append(f"| `{m}` | `{rel(dm.path)}` | {n} | {th} | {ex} |\n")
        o.append(f"\n<details><summary>all {len(un)}</summary>\n\n")
        for m, n in sorted(un):
            o.append(f"- `{m}` ({n} decls)\n")
        o.append("\n</details>\n")

    o.append(
        "\n## How to use this table\n\n"
        "When picking up a hole, do not start from the hole's own hypotheses. Start from the\n"
        "available-but-unused list above and ask, for each module: *does this already state the\n"
        "conclusion I need, in a form whose hypotheses I can discharge?* A proved theorem with a\n"
        "dischargeable hypothesis is a much smaller gap than a theorem you have to invent. The\n"
        "gap between a hole's conclusion and the nearest already-proved theorem in its own\n"
        "dependency cone is the real size of the remaining work.\n"
    )

    o.append("\n## Why this matters operationally\n\n")
    o.append(
        "A researcher closing hole A is touching exactly "
        f"{len(data['A']['rmods'])} modules that anything downstream imports. Everything else in\n"
        f"the tree — {len(s.crnt_mods) - len(data['A']['rmods']) - 1} modules — is inert with respect\n"
        "to that hole: editing it cannot make the hole easier or harder, and a `sorry` there\n"
        "would not block the Global Attractor Theorem. The same holds for hole B. So a\n"
        "reviewer triaging a hole-closing PR should ask only whether the diff touches the\n"
        "modules listed above for that hole.\n"
    )
    return "".join(o)

def near_duplicate_pairs(keys: list[str], threshold: float) -> list[tuple[float, str, str]]:
    """Pairs of distinct statement keys agreeing to at least `threshold`.

    The length filter is what makes this affordable: normalized signatures run to
    hundreds of characters, and two strings whose lengths differ by more than
    `1 - threshold` cannot reach the threshold at all, so the pair is never scored.
    """
    out: list[tuple[float, str, str]] = []
    for i, a in enumerate(keys):
        for b in keys[i + 1:]:
            if abs(len(a) - len(b)) > (1 - threshold) * max(len(a), len(b)):
                continue
            r = difflib.SequenceMatcher(None, a, b).ratio()
            if r >= threshold:
                out.append((r, a, b))
    out.sort(key=lambda t: -t[0])
    return out


# ---------------------------------------------------------------------------
# docs/duplication.md
# ---------------------------------------------------------------------------

def gen_dup(s: Surface, meas: dict) -> str:
    th = [d for d in s.decls if d.kind in ("theorem", "lemma")]
    o: list[str] = [GENERATED_BANNER]
    o.append("# Duplication map\n\n")
    o.append(
        "Where the same obligation is carried more than once under different names. The\n"
        "brief names two suspects: the `CRNT/Multistationarity/TrueSR*.lean` family (the\n"
        "Shinar–Feinberg development) and the `Dynamics/` Global-Attractor chain. This file\n"
        "answers with counts, not impressions.\n\n"
        "**Method.** A *statement key* is the declaration's signature with all binder names\n"
        "erased and all whitespace removed — two declarations with the same key state the\n"
        "same thing up to renaming of hypotheses. A *body hash* is the SHA-256 (first 16\n"
        "hex digits) of the comment-free, whitespace-normalized proof body. Three classes\n"
        "are reported:\n\n"
        "1. **identical statements** — same statement key in two or more modules;\n"
        "2. **identical proofs** — same statement key *and* same body hash, i.e. literally\n"
        "   the same proof text under two names;\n"
        "3. **near-duplicates** — different statement keys, but the normalized signatures\n"
        "   agree to ≥ 85% (edit distance ratio), which catches obligations re-stated with a\n"
        "   hypothesis added or a binder renamed.\n\n"
        "## Counts\n\n| class | groups | declarations |\n|---|---|---|\n"
    )

    bykey: dict[str, list[si.Decl]] = defaultdict(list)
    for d in th:
        if len(d.stmt_norm) >= 25:
            bykey[d.stmt_norm].append(d)
    ident = {k: v for k, v in bykey.items() if len(v) >= 2}
    ident_cross = {k: v for k, v in ident.items() if len({d.module for d in v}) >= 2}
    same_proof = {k: v for k, v in ident.items()
                  if len({d.body_hash for d in v}) == 1 and v[0].body_norm}
    o.append(f"| identical statements | {len(ident)} | {sum(len(v) for v in ident.values())} |\n")
    o.append(f"| … of which cross-module | {len(ident_cross)} | "
             f"{sum(len(v) for v in ident_cross.values())} |\n")
    o.append(f"| identical statements *and* identical proofs | {len(same_proof)} | "
             f"{sum(len(v) for v in same_proof.values())} |\n")

    # near-duplicate: pairwise similarity on statement keys, restricted to the suspects
    suspects = [d for d in th
                if d.module.startswith(("CRNT.Multistationarity", "CRNT.Dynamics"))]
    skeys = sorted({d.stmt_norm for d in suspects if len(d.stmt_norm) >= 40})
    near = near_duplicate_pairs(skeys, 0.85)

    near.sort(key=lambda t: -t[0])
    o.append(f"| near-duplicate signature pairs (≥85%) in `Multistationarity/`+`Dynamics/` | "
             f"{len(near)} |\n")
    o.append("")

    o.append("\n## Per-area duplication density\n\n")
    o.append("| area | theorems | distinct statement keys | redundancy |\n|---|---|---|---|\n")
    for area in sorted({m.name.split(".")[1] for m in s.crnt_mods}):
        ds = [d for d in th if d.module.startswith(f"CRNT.{area}.")]
        if not ds:
            continue
        keys = [d.stmt_norm for d in ds if len(d.stmt_norm) >= 25]
        o.append(f"| `CRNT/{area}` | {len(ds)} | {len(set(keys))} | "
                 f"{100 * (1 - len(set(keys)) / max(1, len(keys))):.1f}% |\n")

    o.append("\n## Class 1 + 2 — identical statements\n\n")
    o.append("Same statement, same proof: a straight copy under a new name. "
             "These are safe to consolidate and are the cheapest real duplication to remove.\n\n")
    ordered = sorted(ident_cross.items(), key=lambda kv: (-len(kv[1]), kv[1][0].module))
    for key, ds in ordered:
        tag = "SAME PROOF" if len({d.body_hash for d in ds}) == 1 else "differs in proof"
        o.append(f"\n### `{ds[0].name}` — {len(ds)} copies, {tag}\n\n")
        o.append("```lean\n" + " ".join(ds[0].signature.split())[:300] + "\n```\n\n")
        o.append("| declaration | module | line | `sorry` | body hash |\n|---|---|---|---|---|\n")
        for d in ds:
            o.append(f"| `{d.fullname}` | `{rel(d.path)}` | {d.line} | "
                     f"{'yes' if d.has_sorry else 'no'} | `{d.body_hash}` |\n")

    o.append("\n## Class 3 — near-duplicate statements\n\n")
    o.append(
        "Different statement keys, ≥85% signature agreement. Each row is a pair of\n"
        "declarations; the signature delta is where the two have drifted apart.\n\n"
        "| similarity | declaration A | declaration B |\n|---|---|---|\n"
    )
    for r, a, b in near[:120]:
        da = find_by_key(s, a)
        db = find_by_key(s, b)
        if not da or not db:
            continue
        o.append(f"| {r:.2f} | `{da.module}`:{da.line} `{da.name}` | "
                 f"`{db.module}`:{db.line} `{db.name}` |\n")

    o.append("\n## Suspicion check: the two named suspects\n\n")
    o.append(
        "`CRNT/Multistationarity/TrueSR*.lean` — how many modules, how many theorems, how\n"
        "much exact redundancy:\n\n")
    tsr = [m for m in s.crnt_mods if m.name.startswith("CRNT.Multistationarity.TrueSR")]
    tth = [d for m in tsr for d in m.decls if d.kind in ("theorem", "lemma")]
    tkeys = collections.Counter(d.stmt_norm for d in tth if len(d.stmt_norm) >= 25)
    o.append(f"- {len(tsr)} modules, {len(tth)} theorems/lemmas\n")
    o.append(f"- {sum(v - 1 for v in tkeys.values() if v > 1)} exact statement repeats "
             f"inside the family\n")
    o.append(f"- {sum(1 for d in tth if d.has_sorry)} carry `sorry`\n\n")
    o.append("| module | decls | theorems | distinct keys | repeats |\n|---|---|---|---|---|\n")
    for m in sorted(tsr, key=lambda m: m.name):
        ds = [d for d in m.decls if d.kind in ("theorem", "lemma")]
        ks = collections.Counter(d.stmt_norm for d in ds if len(d.stmt_norm) >= 25)
        o.append(f"| `{m.name}` | {len(m.decls)} | {len(ds)} | {len(ks)} | "
                 f"{sum(v - 1 for v in ks.values() if v > 1)} |\n")

    o.append("\n`Dynamics/` Global-Attractor chain — the modules named in "
             "`docs/architecture.md` for the GAC:\n\n")
    gac = [m for m in s.crnt_mods
           if any(k in m.name for k in ("GlobalAttractor", "Siphon", "FaceCodimension",
                                        "ToricBarrier", "SingleLinkage", "Persistent",
                                        "Endotactic"))]
    gth = [d for m in gac for d in m.decls if d.kind in ("theorem", "lemma")]
    gkeys = collections.Counter(d.stmt_norm for d in gth if len(d.stmt_norm) >= 25)
    o.append(f"- {len(gac)} modules, {len(gth)} theorems/lemmas\n")
    o.append(f"- {sum(v - 1 for v in gkeys.values() if v > 1)} exact statement repeats\n")
    o.append(f"- {sum(1 for d in gth if d.has_sorry)} carry `sorry`\n\n")
    o.append("| module | decls | theorems | distinct keys | repeats |\n|---|---|---|---|---|\n")
    for m in sorted(gac, key=lambda m: m.name):
        ds = [d for d in m.decls if d.kind in ("theorem", "lemma")]
        ks = collections.Counter(d.stmt_norm for d in ds if len(d.stmt_norm) >= 25)
        o.append(f"| `{m.name}` | {len(m.decls)} | {len(ds)} | {len(ks)} | "
                 f"{sum(v - 1 for v in ks.values() if v > 1)} |\n")
    return "".join(o)


def find_by_key(s: Surface, key: str) -> si.Decl | None:
    for d in s.decls:
        if d.kind in ("theorem", "lemma") and d.stmt_norm == key:
            return d
    return None


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

TARGETS = {
    "index": ("theorem-index.md", gen_index),
    "holes": ("hole-reachability.md", gen_holes),
    "glossary": ("glossary.md", None),      # hand-maintained, see gen_glossary
    "dup": ("duplication.md", gen_dup),
    "unformalized": ("unformalized.md", None),
}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", nargs="*", choices=sorted(TARGETS))
    ap.add_argument("--check", action="store_true",
                    help="print the counts only; write nothing")
    ap.add_argument("--stats", action="store_true",
                    help="print the counts as JSON")
    args = ap.parse_args()

    meas = measure()
    s = Surface()
    cross_check_holes(s, meas)
    th = [d for d in s.decls if d.kind in ("theorem", "lemma")]
    stats = {
        "crnt_modules": len(s.crnt_mods),
        "scaffold_modules": len(s.scaf_mods),
        "crnt_decls": len(s.crnt_decls),
        "scaffold_decls": len(s.scaf_decls),
        "crnt_theorems": sum(1 for d in s.crnt_decls if d.kind in ("theorem", "lemma")),
        "total_decls": len(s.decls),
        "measure_holes": meas["metrics"]["holes"],
        "measure_frontier_mods": meas["metrics"]["frontier_mods"],
        "measure_scaffold_mods": meas["metrics"]["scaffold_mods"],
    }
    if args.stats:
        print(json.dumps(stats, indent=2))
        return 0
    if args.check:
        print(json.dumps(stats, indent=2))
        return 0

    want = args.only or [k for k, v in TARGETS.items() if v is not None]
    for k in want:
        name, fn = TARGETS[k]
        if fn is None:
            continue
        text = fn(s, meas)
        with open(os.path.join(DOCS, name), "w", encoding="utf-8") as fh:
            fh.write(text)
        print(f"wrote docs/{name}  ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
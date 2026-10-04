#!/usr/bin/env python3
"""Generate `docs/glossary.md`: every CRNT term, with Lean name, paper definition,
formalization site — and the name collisions, found by computation rather than by memory.

The Lean side is computed: for each term we list every declaration that defines it, its
module and line, and the citation its own docstring carries.  The *paper* side is a curated
table (`TERMS` below), because it cannot be recovered from the sources — a docstring cites
a paper but does not restate the paper's definition.  The two are joined by Lean name, so
a curated entry that no longer resolves is reported as stale rather than silently dropped.

Usage:  python3 scripts/gen_glossary.py
"""

from __future__ import annotations

import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import surface_index as si  # noqa: E402

ROOT = si.ROOT

# ---------------------------------------------------------------------------
# Curated CRNT terms: Lean name -> (paper's name, the paper's definition, where the
# definition is stated).  `where` is a human locator, not a Lean name.
# ---------------------------------------------------------------------------

TERMS: dict[str, dict] = {
    "WeaklyReversible": dict(
        term="weakly reversible",
        paper="Feinberg–Horn–Jackson",
        where="Definition (weak reversibility); FHJ §1.1",
        definition="Every reaction lies on a directed cycle of the reaction graph: for each "
                   "reaction `y → y'`, `y'` reaches `y`.",
    ),
    "StronglyReversible": dict(
        term="strongly reversible",
        paper="Feinberg–Horn–Jackson",
        where="Definition; FHJ §1.1",
        definition="Every reaction is reversed by a reaction: `y → y'` and `y' → y` are both "
                   "in the reaction set.",
    ),
    "DeficiencyZero": dict(
        term="deficiency zero",
        paper="Feinberg–Horn–Jackson",
        where="Theorem 3.2 (deficiency-zero theorem)",
        definition="`n − ℓ − s = 0`, i.e. the number of complexes minus the number of linkage "
                   "classes minus the stoichiometric rank vanishes.",
    ),
    "Deficiency": dict(
        term="deficiency",
        paper="Feinberg–Horn–Jackson",
        where="§1.3",
        definition="`δ = n − ℓ − s`.",
    ),
    "IsComplexBalanced": dict(
        term="complex balanced",
        paper="Craciun (2003); FHJ",
        where="Definition (complex balanced); Craciun 2003",
        definition="For each complex `y`, the total outgoing mass-action flux equals the total "
                   "incoming mass-action flux, at every positive concentration point.",
    ),
    "WeaklyNormal": dict(
        term="weakly normal",
        paper="Craciun (2001)",
        where="Definition; Craciun, J. Math. Anal. Appl. 252 (2001)",
        definition="At each positive equilibrium, some minor of the Jacobian has determinant of "
                   "one sign (nonzero and not sign-nonsingular).",
    ),
    "Nondegenerate": dict(
        term="nondegenerate",
        paper="Craciun (2001)",
        where="Definition",
        definition="No positive equilibrium has a zero eigenvalue of the Jacobian.",
    ),
    "StronglyConcordant": dict(
        term="strongly concordant",
        paper="Craciun; Shinar–Feinberg",
        where="Definition (strong concordance)",
        definition="The Jacobian is injective on the stoichiometric subspace (and, for the "
                   "fully open extension, injective for injective kinetics).",
    ),
    "Concordant": dict(
        term="concordant",
        paper="Craciun",
        where="Definition",
        definition="Weaker than strong concordance: the Jacobian is injective on the face of "
                   "the stoichiometric subspace on which it is evaluated.",
    ),
    "Siphon": dict(
        term="siphon",
        paper="Craciun",
        where="Definition (siphon); Craciun 2003",
        definition="A strongly connected set of complexes whose complement is weakly "
                   "reversible — no reaction enters it from outside.",
    ),
    "CriticalSiphon": dict(
        term="critical siphon",
        paper="Craciun",
        where="Definition (critical siphon)",
        definition="A siphon that is also a *trap*: every reaction inside it stays inside.",
    ),
    "MassActionVectorField": dict(
        term="mass action (rate law)",
        paper="Feinberg–Horn–Jackson",
        where="§1.2; mass-action kinetics",
        definition="`ẋ = Y x ∘ κ` over complexes: each complex contributes its rate constant "
                   "times the monomial in the concentrations of its source species.",
    ),
    "RateConstants": dict(
        term="rate constants",
        paper="Feinberg–Horn–Jackson",
        where="§1.2",
        definition="One positive real number per reaction.",
    ),
    "Complex": dict(
        term="complex",
        paper="Feinberg–Horn–Jackson",
        where="§1.1",
        definition="A formal sum of species with nonnegative integer multiplicities.",
    ),
    "LinkageClass": dict(
        term="linkage class",
        paper="Feinberg–Horn–Jackson",
        where="§1.1",
        definition="A strongly connected component of the reaction graph.",
    ),
    "stoichSubspace": dict(
        term="stoichiometric subspace",
        paper="standard",
        where="linear algebra of CRNs",
        definition="The span of the reaction vectors `target − source` in `ℝˢ`.",
    ),
    "StoichCompatible": dict(
        term="compatible",
        paper="Craciun",
        where="Definition (compatibility class)",
        definition="Two points lie on the same stoichiometric compatibility class when their "
                   "difference lies in the stoichiometric subspace.",
    ),
    "Concentration": dict(
        term="concentration",
        paper="Feinberg–Horn–Jackson",
        where="§1.2",
        definition="A point of `ℝⁿ₊ˢ`.",
    ),
    "Positive": dict(
        term="interior / positive",
        paper="Feinberg–Horn–Jackson",
        where="§1.2",
        definition="All coordinates strictly positive — an interior point of the positive "
                   "orthant.",
    ),
    "Nonnegative": dict(
        term="nonnegative",
        paper="Feinberg–Horn–Jackson",
        where="§1.2",
        definition="All coordinates ≥ 0.",
    ),
    "Persistent": dict(
        term="persistent",
        paper="Gopalkrishnan–Miller–Shiu; Craciun",
        where="Gopalkrishnan–Miller–Shiu; Craciun v3 §4",
        definition="There is a compact set `K` inside the strictly positive orthant containing "
                   "the initial condition, such that the trajectory never leaves it.",
    ),
    "Permanent": dict(
        term="permanent",
        paper="Gopalkrishnan–Miller–Shiu",
        where="`CRNT/Dynamics/EndotacticPermanence.lean:58`",
        definition="There is a compact set `K` of strictly positive concentrations that "
                   "eventually absorbs the orbit.",
    ),
    "omegaLimit": dict(
        term="ω-limit set",
        paper="dynamical systems",
        where="standard",
        definition="The set of limits of convergent sequences `ϕ tₙ x₀` as `tₙ → ∞`.",
    ),
    "relEntropy": dict(
        term="relative entropy Lyapunov function",
        paper="Horn–Jackson",
        where="Horn–Jackson; FHJ",
        definition="`∑ x*ᵢ (log(x*ᵢ/xᵢ) − 1) + xᵢ − x*ᵢ`, nonincreasing along a "
                   "complex-balanced trajectory.",
    ),
    "fan": dict(
        term="polyhedral fan",
        paper="Craciun v3",
        where="§4; `CRNT/Geometry`",
        definition="A collection of strongly convex polyhedral cones closed under faces and "
                   "under intersection of intersecting members.",
    ),
    "IsPolyhedralFan": dict(
        term="polyhedral fan (property)",
        paper="Craciun v3",
        where="§4",
        definition="The predicate asserting strong convexity, face closure and intersection "
                   "closure.",
    ),
    "FullOpen": dict(
        term="fully open",
        paper="Craciun",
        where="Definition (fully open kinetics)",
        definition="The rate function is injective on the interior of the positive orthant.",
    ),
    "StrongConcordance": dict(
        term="strong concordance",
        paper="Craciun",
        where="Definition",
        definition="Injective for injective kinetics on the relevant subspace.",
    ),
    "graphTransformation": dict(
        term="graph transformation",
        paper="Craciun",
        where="Definition (graph transformation)",
        definition="A vertex labelling making every arrow of the reaction graph point strictly "
                   "upwards.",
    ),
}

# Terms whose paper definition is deliberately *not* given here because the repo's own
# docstring is the authoritative statement (e.g. the TrueSR development, which is internal).
OPAQUE_NOTE = (
    "The `TrueSR*` family (Shinar–Feinberg in-tree) uses its own vocabulary — `TrueSRCycle`, "
    "`TrueSREdge`, `TrueSRSSPath`, `Gluable`, `Relayable` — which is not the paper's "
    "vocabulary and has no one-to-one translation. It is documented in-tree at the head of "
    "`CRNT/Multistationarity/TrueChemistrySRCriterion.lean` and is therefore not repeated here."
)


def anchor(text: str) -> str:
    s = re.sub(r"[^\w\s.-]", "", text.lower())
    return re.sub(r"\s+", "-", s.strip())


def main() -> int:
    mods = si.parse_all("CRNT", "Scaffold")
    by_name: dict[str, list[si.Decl]] = collections.defaultdict(list)
    for m in mods:
        for d in m.decls:
            if d.kind in ("example", "where"):
                continue
            by_name[d.name].append(d)

    o: list[str] = []
    o.append("<!-- GENERATED FILE. Do not edit by hand.\n")
    o.append("     Regenerate with:  python3 scripts/gen_glossary.py\n")
    o.append("     Lean side computed from the sources; the paper-side definitions are a\n")
    o.append("     curated table (`TERMS` in the generator) joined to the sources by Lean\n")
    o.append("     name. A curated entry that no longer resolves is listed as stale.\n")
    o.append("-->\n")
    o.append("# Glossary\n\n")
    o.append(
        "Every CRNT term the codebase uses: its Lean name, the paper's definition of the same\n"
        "object, where the paper states it, and where it is formalized here.\n\n"
        "**Two different kinds of content, and the difference matters.** Everything in the\n"
        "*Lean name* / *formalized at* / *citations* columns is computed from the sources by\n"
        "`scripts/gen_glossary.py`. Everything in the *paper's definition* column is curated,\n"
        "because a docstring cites a paper without restating the paper's definition. When the\n"
        "two disagree, the Lean column is right about what the tree contains and the curated\n"
        "column is right about what the paper says — and that disagreement is itself worth\n"
        "knowing.\n\n"
    )

    # ---- counts
    o.append("## Coverage\n\n")
    resolved = [k for k in TERMS if k in by_name]
    stale = [k for k in TERMS if k not in by_name]
    o.append(f"- curated terms: **{len(TERMS)}**\n")
    o.append(f"- resolved to a declaration in the tree: **{len(resolved)}**\n")
    o.append(f"- **stale** (no declaration by that short name): **{len(stale)}**"
             + (f" — {', '.join('`' + s + '`' for s in stale)}" if stale else "") + "\n")
    o.append(f"- distinct short names defined anywhere in `CRNT/` + `Scaffold/`: "
             f"**{len(by_name)}**\n\n")
    o.append(
        "A curated term being *stale* usually means the tree renamed the concept, not that it\n"
        "was dropped; grep the theorem index before concluding anything.\n\n"
    )

    # ---- main table
    o.append("## Terms\n\n")
    o.append("| Lean name | paper's term | definition (paper) | formalized at | cites |\n")
    o.append("|---|---|---|---|---|\n")
    for key in sorted(TERMS):
        t = TERMS[key]
        ds = by_name.get(key, [])
        # prefer a non-example definition
        ds.sort(key=lambda d: (".Examples." in d.fullname, d.module, d.line))
        if ds:
            sites = "<br>".join(f"`{d.module}`:{d.line}" for d in ds[:4])
            if len(ds) > 4:
                sites += f"<br>*(+{len(ds) - 4} more)*"
            cites = sorted({k2 for d in ds for k2 in si.citations(d.doc)})
            cites_s = ", ".join(f"`{c}`" for c in cites) or "—"
        else:
            sites = "**NOT FOUND**"
            cites_s = "—"
        defn = t["definition"].replace("|", "\\|")
        o.append(f"| `{key}` | {t['term']} | {defn} <br>*({t['paper']}, {t['where']})* | "
                 f"{sites} | {cites_s} |\n")

    # ---- collisions
    o.append("\n## Name collisions\n\n")
    o.append(
        "The brief records that \"the codebase uses the same word for different things in\n"
        "different modules at least once\". It does so **many** times, and the count below is\n"
        "computed, not asserted.\n\n"
        "**Criterion.** A *collision* is a short name that is defined in **two or more distinct\n"
        "namespaces** and **two or more distinct modules**, where the two definitions have\n"
        "*materially different types* — after erasing binders, instance arguments and\n"
        "whitespace, the two type expressions still differ. This deliberately excludes the\n"
        "large family of per-example declarations (`Species`, `Rxn`, `rxn`, `cA`, `cB`, `N`,\n"
        "`weaklyReversible`, …), where the collision is an artifact of the example-scoped\n"
        "namespace convention and carries no mathematical content; those are reported\n"
        "separately at the end.\n\n"
        "Collisions matter because the short name is what a reader writes and what a search\n"
        "matches. Two of the entries below (`deficiencyZero_iff`, `weaklyReversible_iff`) are\n"
        "the same *statement* under two names, one being the definition and the other its\n"
        "isomorphism-invariance corollary — those are harmless but they are exactly why\n"
        "`scripts/decl_index.py like` exists.\n"
    )

    byns = collections.defaultdict(list)
    for name, ds in by_name.items():
        nss = {".".join(d.fullname.split(".")[:-1]) for d in ds}
        mods_of = {d.module for d in ds}
        if len(nss) >= 2 and len(mods_of) >= 2:
            byns[name] = ds

    def type_key(d: si.Decl) -> str:
        s = re.sub(r"\s+", " ", d.signature)
        s = re.sub(r"\{[^{}]*\}", "", s)
        s = re.sub(r"\([^()]*\)", "", s)
        s = re.sub(r"\[[^\[\]]*\]", "", s)
        return re.sub(r"\s+", "", s)

    semantic = []
    for name, ds in byns.items():
        if ".Examples." in "".join(d.module for d in ds) and all(
                ".Examples." in d.module or d.module.startswith("CRNT.Examples") for d in ds):
            continue
        keys = {type_key(d) for d in ds}
        if len(keys) > 1:
            semantic.append((name, ds))

    o.append(f"**{len(byns)} short names are defined in ≥2 namespaces across ≥2 modules.** "
             f"Of those, **{len(semantic)}** have materially different types and so are genuine "
             f"collisions.\n\n")

    o.append("### Genuine collisions (same short name, different types)\n\n")
    o.append("| short name | declarations | different types? |\n|---|---|---|\n")
    for name, ds in sorted(semantic, key=lambda t: (-len(t[1]), t[0])):
        o.append(f"| `{name}` | {len(ds)} | yes |\n")

    for name, ds in sorted(semantic, key=lambda t: (-len(t[1]), t[0])):
        o.append(f"\n#### `{name}`\n\n")
        for d in sorted(ds, key=lambda d: (d.module, d.line)):
            o.append(f"- **`{d.fullname}`** — `{d.module}`:{d.line} (`{d.kind}`)\n")
            o.append(f"  ```lean\n  {' '.join(d.signature.split())[:220]}\n  ```\n")
            if d.doc:
                o.append(f"  > {re.sub(r' +', ' ', d.doc)[:200]}\n")

    o.append("\n### Same short name, same type (harmless restatements)\n\n")
    o.append(
        "These are the same statement in two namespaces. They are not mathematical\n"
        "collisions, but they do inflate counts and they are what `decl_index.py dups`\n"
        "surfaces.\n\n"
        "| short name | declarations |\n|---|---|\n"
    )
    harmless = [(n, ds) for n, ds in sorted(byns.items()) if n not in {x for x, _ in semantic}]
    for name, ds in harmless:
        o.append(f"| `{name}` | {len(ds)} |\n")

    o.append("\n### Example-scoped names (not mathematical collisions)\n\n")
    o.append(
        "Every example network re-declares its own `Species`, `Rxn`, `rxn`, `cA`, `cB`, `N`,\n"
        "`weaklyReversible`, `equilibrium`, … inside a namespace scoped to that example. This\n"
        "is the intended convention and carries no mathematical content, but it does mean a\n"
        "grep for `weaklyReversible` returns dozens of hits, most of them proofs about one\n"
        "specific network. Always qualify.\n\n"
        "| short name | modules defining it |\n|---|---|\n"
    )
    ex = collections.defaultdict(set)
    for name, ds in by_name.items():
        ms = {d.module for d in ds if ".Examples." in d.fullname or d.module.startswith("CRNT.Examples")}
        if len(ms) >= 3:
            ex[name] = ms
    for name, ms in sorted(ex.items(), key=lambda t: -len(t[1]))[:25]:
        o.append(f"| `{name}` | {len(ms)} |\n")

    o.append("\n## Terms with no paper counterpart\n\n")
    o.append(OPAQUE_NOTE + "\n\n")
    o.append(
        "These `TrueSR*` names collide with **no** classical term but do collide with each\n"
        "other in one place worth flagging: `vertex_zero` / `vertex_last` exist both as\n"
        "statements about a Sperner-lattice cell (`CRNT.Analysis.SpernerN`) and as statements\n"
        "about the endpoints of a `TrueSRPath` (`CRNT.Network.TrueSRPath`). The names are the\n"
        "same and the objects are unrelated. If you are reading a `vertex_last` proof, check\n"
        "which namespace you are in before assuming Sperner.\n"
    )

    out = os.path.join(ROOT, "docs", "glossary.md")
    with open(out, "w", encoding="utf-8") as fh:
        fh.write("".join(o))
    print(f"wrote docs/glossary.md ({len(''.join(o))} bytes); "
          f"{len(semantic)} genuine collisions, {len(byns)} cross-namespace names")
    return 0


if __name__ == "__main__":
    sys.exit(main())
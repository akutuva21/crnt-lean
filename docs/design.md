# Design notes

This document records the concrete design decisions realized in the library. The
broader roadmap lives in [`roadmap.md`](roadmap.md).

## Representation

- **Species** are elements of a finite type with decidable equality
  (`[Fintype S] [DecidableEq S]`). Examples use small `inductive` types deriving
  `DecidableEq, Fintype, Repr`. Strings are never used in the core.
- **Complexes** are functions `Complex S := S → ℕ`. Any stoichiometric vector is a
  valid complex; each network carries the finite set of complexes that actually appear
  (`Network.complexes`).
- **Reactions** are `structure Reaction (S) where source target : Complex S`. Self-
  reactions are allowed; `Reaction.Nontrivial` marks the rest. Reactions over a finite
  species type have decidable equality.
- **Networks** index reactions by a finite type `R` (with `decEqR`/`fintypeR` fields)
  rather than a `Finset`. This represents parallel reaction channels and avoids
  duplicate erasure. The instance fields are re-exposed via `attribute [instance]`.

## Settled decisions

| Question | Decision |
|---|---|
| Duplicate reactions allowed? | Yes — distinct indices may share source/target. |
| Self-reactions allowed? | Yes in the structure; `Reaction.Nontrivial` excludes them. |
| Zero complex allowed? | Yes (`Complex.zero`); needed for inflow/outflow/degradation. |
| Complexes globally `S → ℕ`? | Yes; each network has a finite appearing subset. |
| Deficiency in `ℕ` or `ℤ`? | `ℤ` (`deficiencyInt`), to avoid truncated subtraction. |
| Rate constants? | `ℝ` with an explicit positivity field (`RateConstants.positive`). |
| External import path? | Codegen first — Lean checks emitted certificates, no in-Lean parsing. |

## Structure vs. dynamics

The graph and stoichiometric layers do not depend on any analytic ODE theory. The
mass-action vector field is defined early (`Network.massActionVectorField`), but the
deficiency-zero theorem is only a statement interface; its proof is out of scope for
the stable core.

## Reachability and connectivity

Directed reachability `Reaches` is the reflexive-transitive closure
(`Relation.ReflTransGen`) of the one-step relation `DirectlyReacts`, which is
decidable. Linkage `Linked` is the reflexive-transitive closure of the symmetric
one-step relation; it is an equivalence relation on the network's complexes, and
`numLinkageClasses` is the cardinality of the quotient.

Reachability itself is not (yet) equipped with a verified Boolean decision procedure.
Concrete claims are discharged either by explicit witnesses (`Reaches.single`,
`Reaches.trans`) or by the computable walk-certificate checker `reaches_of_walk`, whose
`Bool` premise closes by `decide`.

## Deficiency

`deficiencyInt N = n - ℓ - s` over `ℤ`, with `n = numComplexes`,
`ℓ = numLinkageClasses`, `s = stoichRank`. `DeficiencyZero N` is `deficiencyInt N = 0`,
equivalently `n = ℓ + s` (`deficiencyZero_iff_eq`). `stoichRank` is the noncomputable
`Module.finrank` of the stoichiometric subspace; for concrete networks it is proved by
exhibiting the subspace as a span of explicit vectors.

## Module status

`CRNT.lean` re-exports only stable modules and brings in no axioms beyond Mathlib's.
Example and generated modules `import CRNT` and are therefore not re-exported by it;
they are still built (and checked) via the library's module glob.

# Design notes

This document records the concrete implementation and representation decisions realized in the
library: how the mathematics is encoded in Lean. The mathematical architecture and the per-area
results are in [`architecture.md`](architecture.md).

## Representation

- **Species** are elements of a finite type with decidable equality
  (`[Fintype S] [DecidableEq S]`). Examples use small `inductive` types deriving
  `DecidableEq, Fintype, Repr`. Strings are never used in the core.
- **Complexes** are functions: `Complex S` is the abbreviation `S → ℕ`, a stoichiometric
  coefficient in `ℕ` for each species. Coefficients live in `ℕ` because a complex is a formal
  sum of species with nonnegative integer multiplicities. Any function `S → ℕ` is a valid
  complex; each network carries the finite set of complexes that actually appear as a source or
  target (`Network.complexes`, a `Finset (Complex S)`). The zero complex `Complex.zero` is the
  source or target of inflow, outflow, and degradation reactions.
- **Reactions** are `structure Reaction (S) where source target : Complex S`, a directed edge
  between two complexes. Self-reactions (`source = target`) are permitted in the raw structure;
  the predicate `Reaction.Nontrivial r := r.source ≠ r.target` marks the rest. Because complexes
  `S → ℕ` have decidable equality over a finite species type, `Reaction S` derives
  `DecidableEq`, which powers the `complexes` computation and the graph decision procedures. A
  reaction's stoichiometric `vector` is `target - source` as a real vector `S → ℝ`.
- **Networks** index reactions by a finite type `R` rather than a `Finset`. `Network` is a plain
  structure with explicit `decEqR : DecidableEq R` and `fintypeR : Fintype R` fields (not
  instance-implicit), carrying the finiteness data alongside `reaction : R → Reaction S`. Indexing
  by a type, not a `Finset`, lets distinct indices map to the same source/target, so parallel
  reaction channels are representable and no duplicate erasure is needed. The two finiteness fields
  are re-exposed as instances via `attribute [instance] Network.decEqR Network.fintypeR`.

## Settled decisions

| Question | Decision |
|---|---|
| Duplicate reactions allowed? | Yes: distinct indices in `R` may share source/target. |
| Self-reactions allowed? | Yes in the structure; `Reaction.Nontrivial` excludes them. |
| Zero complex allowed? | Yes (`Complex.zero`); needed for inflow/outflow/degradation. |
| Complexes globally `S → ℕ`? | Yes; each network has a finite appearing subset (`Network.complexes`). |
| Coefficients in `ℕ` or `ℤ`? | `ℕ`; a complex is a formal sum with nonnegative multiplicities. |
| Deficiency in `ℕ` or `ℤ`? | `ℤ` (`deficiencyInt`), to avoid truncated subtraction. |
| Rate constants? | `ℝ` with an explicit positivity field (`RateConstants.positive : ∀ r, 0 < k r`). |
| External import path? | Codegen first: Lean checks emitted certificates, no in-Lean parsing. |

## Structure vs. dynamics

The graph and stoichiometric layers do not depend on any analytic ODE theory. The mass-action
vector field `Network.massActionVectorField` is defined in the kinetics layer
(`CRNT.Kinetics.MassAction`) from rate constants and the reaction vectors alone, without invoking
flows or Lyapunov theory.

The deficiency-zero theorem is proven, not merely stated. `CRNT.Theorems.DeficiencyZero.Statement`
names the hypotheses (`SatisfiesDeficiencyZeroHypotheses := WeaklyReversible ∧ DeficiencyZero`) and
the conclusion (`DeficiencyZeroConclusion`: a unique complex-balanced equilibrium in the positive
compatibility class of any positive start, for any positive rate constants) as a stable API.
`CRNT.Theorems.DeficiencyZero.Existence.deficiencyZeroTheorem` discharges
`SatisfiesDeficiencyZeroHypotheses → DeficiencyZeroConclusion`. Both modules are re-exported by
`CRNT` and are `sorry`-free.

## Reachability and connectivity

Directed reachability `Reaches` (in `CRNT.Graph.Reachability`) is the reflexive-transitive closure
(`Relation.ReflTransGen`) of the one-step relation `DirectlyReacts`, which is decidable. Linkage
`Linked` (in `CRNT.Graph.LinkageClass`) is the reflexive-transitive closure of the symmetric
one-step relation `UndirectedEdge`; it is an equivalence relation on the network's complexes,
realized as `linkedSetoid`, and `numLinkageClasses` is `Nat.card (Quotient linkedSetoid)`.

`Reaches` and `Linked` close over `Complex S = S → ℕ`, an infinite vertex type, so neither is
decidable as stated. The decidable companions live in `CRNT.Decision`:

- `ReachesWithin N k c d` is bounded reachability — reachable by a directed path of at most `k`
  reactions — phrased so each step quantifies over the finite reaction index type, hence decidable.
  It relates to `Reaches` by `reaches_of_reachesWithin` (soundness) and
  `reaches_iff_exists_reachesWithin` (completeness). `WeaklyReversibleWithin k` is the corresponding
  decidable, sound companion for `WeaklyReversible`, so a concrete network discharges weak
  reversibility by exhibiting a depth and running `decide`.

Concrete claims are otherwise discharged by explicit witnesses (`Reaches.single`, `Reaches.trans`)
or by the walk-certificate checker `reaches_of_walk` (in `CRNT.Interop.Certificates`): an external
tool emits a directed walk as a `List (Complex S)`, and the `Bool` checker `reachesWalk` closes by
`decide` on the concrete network, soundly implying `Reaches`.

## Deficiency

`deficiencyInt N = n - ℓ - s` over `ℤ`, with `n = numComplexes`, `ℓ = numLinkageClasses`,
`s = stoichRank`. The deficiency is integer-valued because `ℕ` subtraction truncates at zero.
`DeficiencyZero N` is `deficiencyInt N = 0`, equivalently `n = ℓ + s` (`deficiencyZero_iff_eq`).

`stoichRank` is `Module.finrank ℝ` of the stoichiometric subspace `stoichSubspace`, the `ℝ`-span of
the reaction vectors; it is noncomputable. For concrete networks the rank is pinned either by
exhibiting the subspace as a span of explicit vectors or through the computable certificates in
`CRNT.Decision`: `HasMinorRankGe N k` (decidable existence of a nonsingular `k × k` rational
stoichiometric minor) yields `computeStoichRankLB`, a computable lower bound with a verified
`computeStoichRankLB ≤ stoichRank` theorem. A full-size lower bound discharges `DeficiencyZero`. The
matching upper bound is not provided, since Mathlib lacks the theorem that matrix rank equals the
maximal nonsingular-minor size; the one-sided bound is what the structural deficiency-zero theory
consumes.

## Module status

`CRNT.lean` re-exports the stable core and brings in no axioms beyond Mathlib's
(`[propext, Classical.choice, Quot.sound]`) and no `sorry`. Example and generated modules
`import CRNT` and are therefore not re-exported by it; they are still built and checked via the
library's module glob.

## Decidable companion convention

A propositional definition is paired, where feasible, with a decidable computable companion related
by a theorem, so that a design tool gets a `decide`-checkable verdict rather than a hand-built proof.
`DirectlyReacts` carries a `DecidableRel` instance; `Reaches`/`WeaklyReversible` gain the bounded
decidable companions above; `stoichRank` gains the minor-search lower bound; and structural
deficiency-one conditions have decidable forms in `CRNT.Decision.DeficiencyOneConditionsDecide`. The
`crnt_check` tactic in `CRNT.Decision.Tactic` closes such a decidable goal on a concrete network by
reflection (`decide`).

# Decidability and certificates

This document describes the computable companions of the `CRNT` library: the decision
procedures, exact rational arithmetic, the `crnt_check` and `crnt_deficiency_zero` tactics, and
the certificate checkers that let a concrete network establish its structural properties by
computation rather than by hand-built proof.

Many structural notions in CRNT are defined propositionally: directed reachability is the
reflexive–transitive closure of a one-step relation, the stoichiometric rank is a `finrank ℝ`
of a subspace, the deficiency is `δ = n − ℓ − s`. These definitions are the mathematical truth,
but they are not directly computable as stated. The library's discipline is the two-axis
pattern recorded in [`architecture.md`](architecture.md): wherever it makes sense, a notion
carries **both a propositional definition and a decidable or computable companion, related by a
theorem**. The companion is what `decide` or `#eval` evaluates; the bridging theorem (a
soundness implication, or a two-sided `_iff` / `_eq`) transfers the machine computation back to
the real mathematical statement.

A second discipline governs *how* the companions are evaluated: the development uses kernel
`decide`, not `native_decide` (which would introduce the compiler-trust axiom). Two evaluation
modes appear, and the modules state which applies:

- **Kernel `decide`.** The structural reachability and linkage predicates, the bounded
  reachability companions, and the walk checker reduce inside the kernel, with no compiler trust.
- **Compiled `#eval`.** The exact rational rank and the deficiencies built on it do *not* reduce
  under kernel `decide`: the computable rank `computeRank` expands a determinant over a
  permutation sum, which the kernel does not reduce. Their `Decidable` instances are total, but a
  concrete value is obtained through the equality/`iff` bridge or by `#eval`,
  not by `decide`. The `crnt_deficiency_zero` auto-search runs the determinant search under
  compiled evaluation purely to *find* a witness, then discharges the resulting goal on the
  kernel path.

## Decidable reachability, weak reversibility, and linkage

### Bounded directed reachability

Directed reachability `N.Reaches c d` is the reflexive–transitive closure of the one-step
relation `DirectlyReacts` over `Complex S`, an *infinite* vertex type, so it is not decidable as
written. `CRNT.Decision.Reachability` introduces the **bounded** companion
`N.ReachesWithin k c d`: `d` is reachable from `c` by a directed path of at most `k` reactions.
Each step is a finite existential over the reaction index type `N.R`, so the relation is
decidable (`decidableReachesWithin`). It is related to the unbounded relation by:

- `reaches_of_reachesWithin` (soundness): a bounded path is a path.
- `reaches_iff_exists_reachesWithin` (completeness): a path exists exactly when some bounded
  path does, `N.Reaches c d ↔ ∃ k, N.ReachesWithin k c d`.

`N.WeaklyReversibleWithin k` then states that every reaction's source is reachable from its
target within `k` steps; it is decidable, and `weaklyReversible_of_within` shows it suffices for
`N.WeaklyReversible`. This is a `decide`-friendly entry point that needs no path witnesses:
exhibit a depth `k` and check.

### Full (unbounded) decidability on the finite vertex type

`CRNT.Decision.DirectedReachability` removes the boundedness obstruction by restricting to the
*finite* vertex type of the network's complexes, `{c // c ∈ N.complexes}`. The engine is a
self-contained, domain-general result in the `DirectedReach` namespace:

- `DirectedReach.decidableReflTransGen`: **the reflexive–transitive closure of a decidable
  relation on a `Fintype` is decidable.** It is proved by iterating a monotone forward-closure
  operator `succStep` on `Finset`s; the closure stabilizes within `card V` steps
  (`exists_stable_le_card`), and `mem_reachSet_iff` identifies membership in the stabilized
  reachable set with `Relation.ReflTransGen`.

Transported along the directed reaction graph (`DirectedStep`), this yields full, unbounded
decidability among the network's complexes:

- `reaches_iff_reflTransGen_directedStep`: directed reachability among complexes coincides with
  the closure on the finite vertex type.
- `decidableReachesV`: directed reachability among the network's complexes is decidable.
- `decidableStronglyLinkedV`: strong linkage (mutual directed reachability) is decidable.
- `Decidable N.WeaklyReversible`: weak reversibility is decidable in full, not just within a
  bound.
- `Fintype (Quotient N.stronglyLinkedSetoid)` and `numStrongLinkageClasses`: the strong linkage
  classes form a finite type, with a computable count.
- terminality of a strong linkage class (`N.IsTerminalSLC`) is decidable.

### Strong linkage classes

`CRNT.Decision.StrongLinkage` defines `N.StronglyLinked c d := N.Reaches c d ∧ N.Reaches d c` as
an equivalence relation refining undirected `Linked`, and packages it as `stronglyLinkedSetoid`.
`N.IsTerminalSLC c` records that the strong linkage class of `c` is terminal (no reaction leaves
it); `stronglyLinked_of_reaches_of_terminal` shows such a class is closed under directed
reachability: it is absorbing. The bounded companion `StronglyLinkedWithin k` is decidable and
sound (`stronglyLinked_of_within`); the full `DecidableRel` is the `decidableStronglyLinkedV`
instance above.

### Undirected linkage

`CRNT.Decision.Linkage` models the undirected reaction graph as a Mathlib `SimpleGraph`,
`N.linkageGraph`, on the finite vertex type of complexes. This makes Mathlib's connectivity
toolkit computable:

- `linked_iff_reachable`: undirected linkage `N.Linked` coincides with `Reachable` in the simple
  graph.
- `decidableLinked`: linkage among complexes is decidable.
- `numLinkageClasses_eq_card_connectedComponent`: the linkage count `ℓ` equals
  `Fintype.card N.linkageGraph.ConnectedComponent`, a computable companion for the `ℓ` that
  appears in `δ = n − ℓ − s`.

No single global `reachableBool : Complex S → Complex S → Bool` is offered, because the
propositional `Reaches` lives over the infinite complex type. Decidability is delivered either
through bounded witnesses (`ReachesWithin`, `decide` at a chosen depth) or through the
`Decidable` instances on the finite subtype of network complexes, together with the walk
certificates below.

## Exact rational rank and deficiency

The stoichiometric rank `s = finrank ℝ N.stoichSubspace` and Mathlib's `Matrix.rank` are both
noncomputable. The library builds an exact rational rank over `ℚ` and uses it for the deficiency.

### Computable rank over ℚ via nonsingular minors

`CRNT.Decision.GaussianRank` supplies a computable rank for any `Matrix m n ℚ` over finite
decidable index types, together with the rank-identification theorem that Mathlib lacks:

- `HasNonsingularMinor A k`: there is a `k × k` submatrix of `A` with nonzero determinant. It is
  `Decidable`: the selecting index functions range over finite Pi types, and a nonzero rational
  determinant is decidable from `DecidableEq ℚ`.
- `computeRank A := Nat.findGreatest (HasNonsingularMinor A) (min (card m) (card n))`: the
  largest nonsingular minor size, which reduces by `#eval`. (It does not reduce under kernel
  `decide`, because the determinant runs over a permutation sum.)
- `computeRank_eq_rank` (and its pointwise form `le_rank_iff_hasNonsingularMinor`): the two-sided
  correctness theorem `computeRank A = A.rank`. Its halves are `hasNonsingularMinor_le_rank` (a
  nonsingular minor gives independent columns) and `exists_nonsingularMinor_of_le_rank` (extract
  `k` independent columns, then `k` independent rows, to build a unit minor).

The column/row extraction is packaged by `exists_injOn_linearIndependent_of_le_finrank_span`.

### One-sided minor certificates

`CRNT.Decision.Rank` and `CRNT.Decision.RankExact` provide the *certificate* form, which takes
(or searches for) an explicit selection of reactions and species:

- `stoichRank_ge_of_det_ne_zero`: a `k × k` stoichiometric minor with nonzero **rational**
  determinant witnesses `k ≤ s`. The determinant is exact rational arithmetic, so the hypothesis
  is discharged by reflection.
- `HasMinorRankGe N k`: the searchable existential form, with a `decidableHasMinorRankGe`
  instance.
- `computeStoichRankLB N := Nat.findGreatest (HasMinorRankGe N) (Fintype.card S)`: a *computable
  lower bound* on `s`, with `computeStoichRankLB_le_stoichRank`.
- `deficiencyZero_of_minor` / `deficiencyZero_of_computeStoichRankLB`: because `s ≤ n − ℓ` always
  holds (`stoichRank_add_numLinkageClasses_le`), a full-size minor forces `δ = 0`, giving a
  `DeficiencyZero` certificate.

### The exact computable deficiency

`CRNT.Decision.ExactDeficiency` bridges the `ℚ`-rank to the real stoichiometric rank. The
stoichiometric matrix has integer entries (each reaction vector is `target − source` of
`ℕ`-valued coefficient vectors), so the rational matrix `N.stoichMatrixQ` is computable, and its
`ℚ`-rank equals the real rank by field-extension invariance of rank, proved directly via the
injective `ℚ`-linear cast `castSpeciesLM` and `rank_map_le_rank` / `rank_le_stoichRank`:

- `stoichRank_eq_computeRank`: `N.stoichRank = computeRank N.stoichMatrixQ`. This upgrades the
  one-sided bound to an exact rational rank.
- `computeDeficiency N := numComplexes − numLinkageClasses − computeRank stoichMatrixQ`. This
  `def` is `noncomputable`: it takes the linkage count from `numLinkageClasses`, a quotient
  cardinality.
- `deficiency_eq_computeDeficiency`: `N.deficiency = N.computeDeficiency`, valid for *every*
  deficiency value.
- `deficiencyZero_iff_computeDeficiency_eq_zero` and `deficiencyOne_iff_computeDeficiency_eq_one`:
  the exact `δ = 0` / `δ = 1` decision corollaries, stated as `iff` bridges. They are not kernel
  `decide` reductions; a concrete deficiency value comes through the bridge or `#eval`.

`CRNT.Decision.ComputableDeficiency` removes the `noncomputable` marker by routing the linkage
count through the connected-component count, which evaluates:

- `computeNumLinkageClasses N := Fintype.card N.linkageGraph.ConnectedComponent`, with
  `computeNumLinkageClasses_eq_numLinkageClasses`.
- `computableDeficiency N := numComplexes − computeNumLinkageClasses − computeRank stoichMatrixQ`,
  a genuinely computable `δ`, with `deficiency_eq_computableDeficiency` and
  `deficiencyZero_iff_computableDeficiency_eq_zero`.

The value still does not reduce under kernel `decide` (the `computeRank` permutation sum), so the
deficiency of a concrete network is obtained by `#eval` or an external compiled analyzer, not by
`decide`.

### Per-linkage-class deficiency and the deficiency-one conditions

Feinberg's deficiency-one theorem reads off, for each linkage class `θ`, a class deficiency
`δ_θ = n_θ − 1 − s_θ` and requires `δ_θ ≤ 1` for every class. The class rank
`s_θ = linkageStoichRank θ` is a `finrank` of a real submodule, hence noncomputable as written.
`CRNT.Decision.LinkageDeficiencyExact` pins it to the exact computable rational rank of the
class's stoichiometric submatrix by the same field-extension route, restricted to one class:

- `linkageStoichMatrixQ N q : Matrix S {r // classOf (sourceIdx r) = q} ℚ`: the class's rational
  stoichiometric matrix, columns indexed by the reactions whose source lies in `q`.
- `linkageStoichRank_eq_computeRank`: `linkageStoichRank q = computeRank (linkageStoichMatrixQ q)`.
- `computeLinkageDeficiency` and `linkageDeficiency_eq_computeLinkageDeficiency`: the class
  deficiency in fully computable form.
- `decidableLinkageDeficiency_le_one`: the resulting `Decidable (linkageDeficiency q ≤ 1)`, total,
  evaluated by `#eval` or the equality bridge rather than kernel `decide`.

`CRNT.Decision.DeficiencyOneConditionsDecide` then assembles a `Decidable` instance for
`DeficiencyOneConditions`, the structure bundling conditions (i) and (ii) of the deficiency-one
theorem — `∀ θ, δ_θ ≤ 1` and the tightness identity `∑_θ δ_θ = δ`:

- `sum_linkageDeficiency_eq_deficiencyInt_iff_compute`: the tightness identity is equivalent to
  its fully computable form.
- `decidableDeficiencyOneConditions`: the resulting `Decidable N.DeficiencyOneConditions`, total.
  It is `#eval`-evaluable but does not reduce under kernel `decide`, since
  `computeRank` is a permutation sum and the `Subsingleton.elim` reconciliation between the
  computable and ambient `Fintype` instances on the linkage-class quotient does not reduce in the
  kernel.

### Decidable structural ACR check

`CRNT.Decision.ACRCheck` packages the discrete, graph-structural fragment of the Shinar–Feinberg
sufficient condition for absolute concentration robustness (Shinar and Feinberg, *Structural
Sources of Robustness in Biochemical Reaction Networks*). The predicate
`HasShinarFeinbergPair N s` asserts the existence of two non-terminal complexes lying in distinct
linkage classes and differing in exactly the species `s`. It is stated with `¬ N.Linked` rather
than distinct linkage classes so the synthesized `Decidable` instance reduces under `decide`
without an `Eq.rec` obstruction; `classOf_ne_iff_not_linked` is the human-facing bridge to the
linkage-class formulation. `acrSpecies` collects the species carrying such a witness as a
`Finset`. The non-finite deficiency-one side condition is supplied externally
(`ShinarFeinbergHypotheses.ofPair`).

## The `crnt_check` tactic

`CRNT.Decision.Tactic` defines

```lean
macro "crnt_check" : tactic => `(tactic| decide)
```

It closes a decidable structural goal about a concrete network by kernel reduction. The decision procedures
above make the standard structural predicates decidable — directed and undirected reachability,
weak reversibility, strong linkage, and the linkage- and strong-linkage-class counts — so a goal
stating such a property of a concrete network reduces to `Bool` evaluation the kernel can settle.
The tactic is `decide` alone; it carries no `native_decide` fallback.

A worked use is `CRNT/Examples/CrntCheck.lean`, on the reversible pair `A ⇌ B`:

```lean
theorem weaklyReversible : N.WeaklyReversible := by crnt_check
theorem numStrongLinkageClasses_eq : N.numStrongLinkageClasses = 1 := by crnt_check
```

Here weak reversibility and the strong-linkage-class count are both discharged by computation,
with no hand-built path witnesses. The `CRNT/Examples/Decide*` networks (`DecideReachability`,
`DecideDirectedReachability`, `DecideLinkage`, `DecideStrongLinkage`, `DecideRank`) exercise the
individual decision procedures by `decide`.

## The `crnt_deficiency_zero` tactic

`CRNT.Decision.DeficiencyZeroTactic` defines `crnt_deficiency_zero`, which proves
`N.DeficiencyZero` through `deficiencyZero_of_minor`: a `k × k` stoichiometric minor with nonzero
determinant (witnessing `s ≥ k`) plus the count `n ≤ k + ℓ`. It comes in two forms.

The **explicit** form `crnt_deficiency_zero f, σ` takes the witnessing selection — `f : Fin k →
N.R` choosing `k` reactions, `σ : Fin k → S` choosing `k` species — and discharges both
obligations: the determinant by `simp +decide` with the closed-form determinant lemmas
(`det_fin_one`/`two`/`three`, with a `det_succ_row_zero` cofactor fallback) under ground
reduction, and the count by rewriting `numLinkageClasses` to the evaluable
`computeNumLinkageClasses` and then `decide`.

The **argument-free** form `crnt_deficiency_zero` finds the witness itself: it meta-evaluates
`k = n − ℓ`, runs the compiled search `findMinorWitness` (`CRNT.Decision.MinorSearch`) to locate
a nonsingular minor — the determinant's permutation sum runs under compiled evaluation, which the
kernel `decide` cannot reduce — then builds the selection and discharges as above. Both stay on
the kernel path for the final discharge. On the reversible
pair `A ⇌ B`:

```lean
example : N.DeficiencyZero := by crnt_deficiency_zero                      -- auto-search
example : N.DeficiencyZero := by crnt_deficiency_zero ![Rxn.fwd], ![Species.A]  -- explicit
```

`crnt_stoich_rank_ge f, σ` reuses the same determinant discharge to prove `k ≤ N.stoichRank` from
a nonsingular-minor witness (`stoichRank_ge_of_det_ne_zero`).

## Walk certificates

`CRNT.Interop.Certificates` realizes the path-certificate pattern: an external tool emits, for a
reachability claim `c ⇝ d`, an explicit walk (a list of intermediate complexes), and Lean
verifies it with a computable `Bool` check whose `true` value soundly implies `Reaches`.

- `N.reachesWalk c l : Bool` checks that the complexes in `l`, starting from `c`, form a directed
  walk, each consecutive pair connected by a reaction.
- `reaches_getLastD_of_reachesWalk`: soundness. A verified walk from `c` through `l` witnesses
  that the walk's endpoint (`l.getLastD c`) is reachable from `c`.
- `reaches_of_walk`: the certificate-consuming form. Supply the walk `l` ending at a named `d`,
  discharge the `Bool` check by `decide`, and obtain `N.Reaches c d`.

Because `DirectlyReacts` is decidable, `reachesWalk` reduces by `decide` on concrete networks, so
generated certificates close their goals automatically. This is the in-Lean half of the
external-tool workflow.

## External-tool emission contract

The full contract by which an external tool emits checkable Lean (the recommended codegen
pipeline, the JSON interchange schema, and worked emitted files) is documented separately in
[`generated-certificates.md`](generated-certificates.md). The walk checker above is the Lean
primitive those generated certificates target.

## Modules

- `CRNT/Decision/Reachability.lean`: bounded directed reachability `ReachesWithin`, bounded weak
  reversibility, and their soundness/completeness bridges.
- `CRNT/Decision/DirectedReachability.lean`: the general decidable `ReflTransGen` on a `Fintype`,
  and full decidable reachability, strong linkage, weak reversibility, SLC count, and terminality
  on the network's complexes.
- `CRNT/Decision/Linkage.lean`: the undirected `linkageGraph`, decidable linkage, and the
  computable linkage count.
- `CRNT/Decision/StrongLinkage.lean`: strong linkage classes, terminal classes, and the bounded
  companion.
- `CRNT/Decision/Rank.lean`: one-sided stoichiometric minor rank certificates and the
  `DeficiencyZero` certificate.
- `CRNT/Decision/RankExact.lean`: the searchable `HasMinorRankGe` and the computable rank lower
  bound `computeStoichRankLB`.
- `CRNT/Decision/GaussianRank.lean`: computable rank over `ℚ` via nonsingular minors, with
  `computeRank_eq_rank`.
- `CRNT/Decision/ExactDeficiency.lean`: the exact rational rank and the `noncomputable`
  `computeDeficiency` (`stoichRank_eq_computeRank`, `deficiency_eq_computeDeficiency`) with the
  `δ = 0` / `δ = 1` `iff` bridges.
- `CRNT/Decision/ComputableDeficiency.lean`: the computable linkage count and deficiency assembly
  (`computeNumLinkageClasses`, `computableDeficiency`) with their bridges.
- `CRNT/Decision/LinkageDeficiencyExact.lean`: the computable per-linkage-class rank and
  deficiency, and `decidableLinkageDeficiency_le_one`.
- `CRNT/Decision/DeficiencyOneConditionsDecide.lean`: `decidableDeficiencyOneConditions` for the
  deficiency-one linkage conditions.
- `CRNT/Decision/ACRCheck.lean`: the decidable structural fragment of the Shinar–Feinberg ACR
  condition.
- `CRNT/Decision/Tactic.lean`: the `crnt_check` tactic.
- `CRNT/Decision/MinorSearch.lean`: the compiled nonsingular-minor search (`findMinorWitness`).
- `CRNT/Decision/DeficiencyZeroTactic.lean`: the `crnt_deficiency_zero` tactic (explicit and
  argument-free auto-search forms) and the `crnt_stoich_rank_ge` minor-rank tactic.
- `CRNT/Interop/Certificates.lean`: the walk-certificate checker for reachability.
- `CRNT/Examples/CrntCheck.lean`, `CRNT/Examples/ReversiblePair.lean`, and the
  `CRNT/Examples/Decide*` family: worked uses of `decide` / `crnt_check` and the decision
  procedures on concrete networks.

## Related documents

- [`architecture.md`](architecture.md): how this layer sits in the whole library.
- [`generated-certificates.md`](generated-certificates.md): the external-tool emission contract
  and JSON interchange schema.

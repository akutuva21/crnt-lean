<!-- GENERATED FILE. Do not edit by hand.
     Regenerate with:  python3 scripts/gen_glossary.py
     Lean side computed from the sources; the paper-side definitions are a
     curated table (`TERMS` in the generator) joined to the sources by Lean
     name. A curated entry that no longer resolves is listed as stale.
-->
# Glossary

Every CRNT term the codebase uses: its Lean name, the paper's definition of the same
object, where the paper states it, and where it is formalized here.

**Two different kinds of content, and the difference matters.** Everything in the
*Lean name* / *formalized at* / *citations* columns is computed from the sources by
`scripts/gen_glossary.py`. Everything in the *paper's definition* column is curated,
because a docstring cites a paper without restating the paper's definition. When the
two disagree, the Lean column is right about what the tree contains and the curated
column is right about what the paper says — and that disagreement is itself worth
knowing.

## Coverage

- curated terms: **29**
- resolved to a declaration in the tree: **17**
- **stale** (no declaration by that short name): **12** — `StronglyReversible`, `Deficiency`, `Siphon`, `CriticalSiphon`, `MassActionVectorField`, `LinkageClass`, `Persistent`, `omegaLimit`, `fan`, `FullOpen`, `StrongConcordance`, `graphTransformation`
- distinct short names defined anywhere in `CRNT/` + `Scaffold/`: **9767**

A curated term being *stale* usually means the tree renamed the concept, not that it
was dropped; grep the theorem index before concluding anything.

## Terms

| Lean name | paper's term | definition (paper) | formalized at | cites |
|---|---|---|---|---|
| `Complex` | complex | A formal sum of species with nonnegative integer multiplicities. <br>*(Feinberg–Horn–Jackson, §1.1)* | `CRNT.Basic.Complex`:22 | — |
| `Concentration` | concentration | A point of `ℝⁿ₊ˢ`. <br>*(Feinberg–Horn–Jackson, §1.2)* | `CRNT.Kinetics.Concentration`:19 | — |
| `Concordant` | concordant | Weaker than strong concordance: the Jacobian is injective on the face of the stoichiometric subspace on which it is evaluated. <br>*(Craciun, Definition)* | `CRNT.Multistationarity.Concordance`:86 | — |
| `CriticalSiphon` | critical siphon | A siphon that is also a *trap*: every reaction inside it stays inside. <br>*(Craciun, Definition (critical siphon))* | **NOT FOUND** | — |
| `Deficiency` | deficiency | `δ = n − ℓ − s`. <br>*(Feinberg–Horn–Jackson, §1.3)* | **NOT FOUND** | — |
| `DeficiencyZero` | deficiency zero | `n − ℓ − s = 0`, i.e. the number of complexes minus the number of linkage classes minus the stoichiometric rank vanishes. <br>*(Feinberg–Horn–Jackson, Theorem 3.2 (deficiency-zero theorem))* | `CRNT.Deficiency.Definition`:29 | — |
| `FullOpen` | fully open | The rate function is injective on the interior of the positive orthant. <br>*(Craciun, Definition (fully open kinetics))* | **NOT FOUND** | — |
| `IsComplexBalanced` | complex balanced | For each complex `y`, the total outgoing mass-action flux equals the total incoming mass-action flux, at every positive concentration point. <br>*(Craciun (2003); FHJ, Definition (complex balanced); Craciun 2003)* | `CRNT.Equilibria.ComplexBalanced`:33<br>`CRNT.Kinetics.GeneralizedNetwork`:272 | — |
| `IsPolyhedralFan` | polyhedral fan (property) | The predicate asserting strong convexity, face closure and intersection closure. <br>*(Craciun v3, §4)* | `CRNT.Geometry.ConeFace`:196 | — |
| `LinkageClass` | linkage class | A strongly connected component of the reaction graph. <br>*(Feinberg–Horn–Jackson, §1.1)* | **NOT FOUND** | — |
| `MassActionVectorField` | mass action (rate law) | `ẋ = Y x ∘ κ` over complexes: each complex contributes its rate constant times the monomial in the concentrations of its source species. <br>*(Feinberg–Horn–Jackson, §1.2; mass-action kinetics)* | **NOT FOUND** | — |
| `Nondegenerate` | nondegenerate | No positive equilibrium has a zero eigenvalue of the Jacobian. <br>*(Craciun (2001), Definition)* | `CRNT.Multistationarity.WeakNormality`:170<br>`CRNT.Oscillation.Floquet`:87 | — |
| `Nonnegative` | nonnegative | All coordinates ≥ 0. <br>*(Feinberg–Horn–Jackson, §1.2)* | `CRNT.Kinetics.Concentration`:26 | — |
| `Permanent` | permanent | There is a compact set `K` of strictly positive concentrations that eventually absorbs the orbit. <br>*(Gopalkrishnan–Miller–Shiu, `CRNT/Dynamics/EndotacticPermanence.lean:58`)* | `CRNT.Dynamics.EndotacticPermanence`:58 | `shiu-nagumo` |
| `Persistent` | persistent | There is a compact set `K` inside the strictly positive orthant containing the initial condition, such that the trajectory never leaves it. <br>*(Gopalkrishnan–Miller–Shiu; Craciun, Gopalkrishnan–Miller–Shiu; Craciun v3 §4)* | **NOT FOUND** | — |
| `Positive` | interior / positive | All coordinates strictly positive — an interior point of the positive orthant. <br>*(Feinberg–Horn–Jackson, §1.2)* | `CRNT.Kinetics.Concentration`:29 | — |
| `RateConstants` | rate constants | One positive real number per reaction. <br>*(Feinberg–Horn–Jackson, §1.2)* | `CRNT.Kinetics.MassAction`:24 | — |
| `Siphon` | siphon | A strongly connected set of complexes whose complement is weakly reversible — no reaction enters it from outside. <br>*(Craciun, Definition (siphon); Craciun 2003)* | **NOT FOUND** | — |
| `StoichCompatible` | compatible | Two points lie on the same stoichiometric compatibility class when their difference lies in the stoichiometric subspace. <br>*(Craciun, Definition (compatibility class))* | `CRNT.Equilibria.CompatibilityClass`:25 | — |
| `StrongConcordance` | strong concordance | Injective for injective kinetics on the relevant subspace. <br>*(Craciun, Definition)* | **NOT FOUND** | — |
| `StronglyConcordant` | strongly concordant | The Jacobian is injective on the stoichiometric subspace (and, for the fully open extension, injective for injective kinetics). <br>*(Craciun; Shinar–Feinberg, Definition (strong concordance))* | `CRNT.Multistationarity.StrongConcordance`:60 | — |
| `StronglyReversible` | strongly reversible | Every reaction is reversed by a reaction: `y → y'` and `y' → y` are both in the reaction set. <br>*(Feinberg–Horn–Jackson, Definition; FHJ §1.1)* | **NOT FOUND** | — |
| `WeaklyNormal` | weakly normal | At each positive equilibrium, some minor of the Jacobian has determinant of one sign (nonzero and not sign-nonsingular). <br>*(Craciun (2001), Definition; Craciun, J. Math. Anal. Appl. 252 (2001))* | `CRNT.Multistationarity.WeakNormality`:87 | — |
| `WeaklyReversible` | weakly reversible | Every reaction lies on a directed cycle of the reaction graph: for each reaction `y → y'`, `y'` reaches `y`. <br>*(Feinberg–Horn–Jackson, Definition (weak reversibility); FHJ §1.1)* | `CRNT.Graph.WeakReversibility`:24 | — |
| `fan` | polyhedral fan | A collection of strongly convex polyhedral cones closed under faces and under intersection of intersecting members. <br>*(Craciun v3, §4; `CRNT/Geometry`)* | **NOT FOUND** | — |
| `graphTransformation` | graph transformation | A vertex labelling making every arrow of the reaction graph point strictly upwards. <br>*(Craciun, Definition (graph transformation))* | **NOT FOUND** | — |
| `omegaLimit` | ω-limit set | The set of limits of convergent sequences `ϕ tₙ x₀` as `tₙ → ∞`. <br>*(dynamical systems, standard)* | **NOT FOUND** | — |
| `relEntropy` | relative entropy Lyapunov function | `∑ x*ᵢ (log(x*ᵢ/xᵢ) − 1) + xᵢ − x*ᵢ`, nonincreasing along a complex-balanced trajectory. <br>*(Horn–Jackson, Horn–Jackson; FHJ)* | `CRNT.Theorems.DeficiencyZero.Lyapunov`:58 | `feinberg-horn-jackson` |
| `stoichSubspace` | stoichiometric subspace | The span of the reaction vectors `target − source` in `ℝˢ`. <br>*(standard, linear algebra of CRNs)* | `CRNT.Stoich.Subspace`:25 | — |

## Name collisions

The brief records that "the codebase uses the same word for different things in
different modules at least once". It does so **many** times, and the count below is
computed, not asserted.

**Criterion.** A *collision* is a short name that is defined in **two or more distinct
namespaces** and **two or more distinct modules**, where the two definitions have
*materially different types* — after erasing binders, instance arguments and
whitespace, the two type expressions still differ. This deliberately excludes the
large family of per-example declarations (`Species`, `Rxn`, `rxn`, `cA`, `cB`, `N`,
`weaklyReversible`, …), where the collision is an artifact of the example-scoped
namespace convention and carries no mathematical content; those are reported
separately at the end.

Collisions matter because the short name is what a reader writes and what a search
matches. Two of the entries below (`deficiencyZero_iff`, `weaklyReversible_iff`) are
the same *statement* under two names, one being the definition and the other its
isomorphism-invariance corollary — those are harmless but they are exactly why
`scripts/decl_index.py like` exists.
**168 short names are defined in ≥2 namespaces across ≥2 modules.** Of those, **84** have materially different types and so are genuine collisions.

### Genuine collisions (same short name, different types)

| short name | declarations | different types? |
|---|---|---|
| `N` | 16 | yes |
| `Species` | 15 | yes |
| `Rxn` | 14 | yes |
| `rxn` | 14 | yes |
| `numComplexes_eq` | 7 | yes |
| `numReactions_eq` | 6 | yes |
| `Cell` | 5 | yes |
| `trans` | 5 | yes |
| `exists_rainbow_cell` | 4 | yes |
| `numLinkageClasses_eq` | 4 | yes |
| `Outer` | 3 | yes |
| `cellColors` | 3 | yes |
| `colorOf` | 3 | yes |
| `generalizedRate` | 3 | yes |
| `matrix` | 3 | yes |
| `multiDoorIncidence` | 3 | yes |
| `reactionAt` | 3 | yes |
| `reducedField` | 3 | yes |
| `source` | 3 | yes |
| `speciesAt` | 3 | yes |
| `steadyState_iff` | 3 | yes |
| `stoichRank_eq` | 3 | yes |
| `target` | 3 | yes |
| `toPath` | 3 | yes |
| `vertex_eq_reactionAt` | 3 | yes |
| `vertex_eq_speciesAt` | 3 | yes |
| `IsOscillatoryCoreClassI.not_classII` | 2 | yes |
| `IsOscillatoryCoreClassII.not_classI` | 2 | yes |
| `PeriodicTrajectory.normalizedLoop` | 2 | yes |
| `Pt` | 2 | yes |
| `col` | 2 | yes |
| `colorOf_dec` | 2 | yes |
| `colorOf_pos` | 2 | yes |
| `complexBalanced_geometricInterpolate` | 2 | yes |
| `complexBalanced_iff_treeConstantBinomials` | 2 | yes |
| `complexBalanced_of_linkage_scalars` | 2 | yes |
| `complexBalanced_of_treeConstantBinomials` | 2 | yes |
| `deficiencyZero_iff` | 2 | yes |
| `deficiency_eq` | 2 | yes |
| `doorCount` | 2 | yes |
| `doorCount_odd_iff` | 2 | yes |
| `doorRel` | 2 | yes |
| `edge_reaction_of_even` | 2 | yes |
| `edge_reaction_of_odd` | 2 | yes |
| `edge_species_of_even` | 2 | yes |
| `edge_species_of_odd` | 2 | yes |
| `exists_color_index` | 2 | yes |
| `exists_linkage_scalars_of_complexBalanced` | 2 | yes |
| `finrank_complexBalancedTangentSpace` | 2 | yes |
| `forget` | 2 | yes |
| `inflow` | 2 | yes |
| `linearEquiv` | 2 | yes |
| `manifold` | 2 | yes |
| `manifoldMap_slowDrift_velocity_le` | 2 | yes |
| `manifold_isFixedPt` | 2 | yes |
| `manifold_unique` | 2 | yes |
| `mem_positiveComplexBalancedSet_iff_toric` | 2 | yes |
| `outflow` | 2 | yes |
| `periodicTrajectory` | 2 | yes |
| `realize` | 2 | yes |
| `realizePt` | 2 | yes |
| `realizePt_coe` | 2 | yes |
| `realize_dist_le` | 2 | yes |
| `realize_mem_stdSimplex` | 2 | yes |
| `restrict` | 2 | yes |
| `satisfiesTreeConstantBinomials_of_complexBalanced` | 2 | yes |
| `self` | 2 | yes |
| `species_iff_even` | 2 | yes |
| `spernerColoringOf` | 2 | yes |
| `spernerColoringOf_color` | 2 | yes |
| `sperner_exists_rainbow` | 2 | yes |
| `ssGlueCycle_numCPairs` | 2 | yes |
| `stoichCompatible_iff` | 2 | yes |
| `support` | 2 | yes |
| `tail_vertex` | 2 | yes |
| `toPath_edge` | 2 | yes |
| `toPath_endReaction` | 2 | yes |
| `toPath_startSpecies` | 2 | yes |
| `triVerts` | 2 | yes |
| `vectorField` | 2 | yes |
| `vertex_last` | 2 | yes |
| `vertex_zero` | 2 | yes |
| `weaklyReversible_iff` | 2 | yes |
| `zero` | 2 | yes |

#### `N`

- **`CRNT.Examples.ACRPair.N`** — `CRNT.Decision.ACRCheck`:143 (`def`)
  ```lean
  def N : Network Species
  ```
  > The toy network with non-terminal complexes `A` and `2A` in distinct linkage classes differing only in species `A`.
- **`CRNT.RankExactExample.N`** — `CRNT.Decision.RankExact`:102 (`def`)
  ```lean
  def N : Network Species
  ```
  > The network `X → Y`.
- **`CRNT.DeficiencyOneDecide.Example.N`** — `CRNT.Deficiency.DeficiencyOneDecide`:131 (`def`)
  ```lean
  def N : Network Species
  ```
- **`CRNT.Design.Adaptation.N`** — `CRNT.Design.Adaptation`:80 (`def`)
  ```lean
  def N : Network Species
  ```
  > The antithetic integral feedback network.
- **`CRNT.Examples.SiphonReversiblePair.N`** — `CRNT.Dynamics.Siphon`:176 (`def`)
  ```lean
  def N : Network Species
  ```
  > The reversible pair `A ⇌ B`.
- **`CRNT.Examples.CatalyticChain.N`** — `CRNT.Examples.CatalyticChain`:22 (`def`)
  ```lean
  def N : Network (Fin 3)
  ```
- **`CRNT.Examples.ComplexBalancedBoundaryEquilibrium.N`** — `CRNT.Examples.ComplexBalancedBoundaryEquilibrium`:118 (`def`)
  ```lean
  def N : Network Species
  ```
  > The network `A ⇄ A + B ⇄ …` with the parallel `B` pair.
- **`CRNT.Examples.Enzyme.N`** — `CRNT.Examples.Enzyme`:57 (`def`)
  ```lean
  def N : Network Species
  ```
  > The enzyme network.
- **`CRNT.Examples.GeneExpression.N`** — `CRNT.Examples.GeneExpression`:69 (`def`)
  ```lean
  def N : Network Species
  ```
  > The gene-expression network.
- **`CRNT.Examples.HopfNetwork3.N`** — `CRNT.Examples.HopfNetwork3`:85 (`def`)
  ```lean
  def N : Network (Fin 3)
  ```
  > The genuine three-species autocatalytic network.
- **`CRNT.Examples.IrreversibleChain.N`** — `CRNT.Examples.IrreversibleChain`:53 (`def`)
  ```lean
  def N : Network Species
  ```
  > The network `A → B → C`.
- **`CRNT.Examples.Lotka.N`** — `CRNT.Examples.Lotka`:127 (`def`)
  ```lean
  def N : Network Species
  ```
  > The Lotka network.
- **`CRNT.Examples.Minimal.N`** — `CRNT.Examples.Minimal`:47 (`def`)
  ```lean
  def N : Network Species
  ```
  > The network `A → B`.
- **`CRNT.Examples.ReversiblePair.N`** — `CRNT.Examples.ReversiblePair`:62 (`def`)
  ```lean
  def N : Network Species
  ```
  > The network `A ⇌ B`.
- **`CRNT.Examples.StochasticConvergenceExample.N`** — `CRNT.Examples.StochasticConvergenceExample`:174 (`def`)
  ```lean
  def N : Network Species
  ```
  > The reversible pair `A ⇌ B`.
- **`CRNT.Generated.Example.N`** — `CRNT.Interop.CodegenExamples`:46 (`def`)
  ```lean
  def N : Network Species
  ```

#### `Species`

- **`CRNT.Examples.ACRPair.Species`** — `CRNT.Decision.ACRCheck`:102 (`inductive`)
  ```lean
  inductive Species | A | P | Q deriving DecidableEq, Repr instance : Fintype Species
  ```
  > Three species.
- **`CRNT.RankExactExample.Species`** — `CRNT.Decision.RankExact`:87 (`abbrev`)
  ```lean
  abbrev Species
  ```
  > Two species `X` and `Y`, indexed by `Fin 2` (`0 = X`, `1 = Y`).
- **`CRNT.DeficiencyOneDecide.Example.Species`** — `CRNT.Deficiency.DeficiencyOneDecide`:104 (`inductive`)
  ```lean
  inductive Species | A | B deriving DecidableEq, Repr instance : Fintype Species
  ```
  > Class-level terminality unfolds to the complex-level decidable predicate.
- **`CRNT.Design.Adaptation.Species`** — `CRNT.Design.Adaptation`:40 (`inductive`)
  ```lean
  inductive Species | Z1 | Z2 | X deriving DecidableEq, Repr instance : Fintype Species
  ```
  > Three species: the two controller species `Z1`, `Z2` and the output `X`.
- **`CRNT.Examples.SiphonReversiblePair.Species`** — `CRNT.Dynamics.Siphon`:143 (`inductive`)
  ```lean
  inductive Species | A | B deriving DecidableEq, Repr instance : Fintype Species
  ```
  > Two species, `A` and `B`.
- **`CRNT.Examples.ComplexBalancedBoundaryEquilibrium.Species`** — `CRNT.Examples.ComplexBalancedBoundaryEquilibrium`:78 (`inductive`)
  ```lean
  inductive Species | A | B deriving DecidableEq, Repr instance : Fintype Species
  ```
  > Two species, `A` and `B`.
- **`CRNT.Examples.Enzyme.Species`** — `CRNT.Examples.Enzyme`:27 (`inductive`)
  ```lean
  inductive Species | E | S | ES | P deriving DecidableEq, Fintype, Repr open Species
  ```
  > Four species: free enzyme `E`, substrate `S`, the enzyme–substrate complex `ES`, and product `P`.
- **`CRNT.Examples.GeneExpression.Species`** — `CRNT.Examples.GeneExpression`:34 (`inductive`)
  ```lean
  inductive Species | DNA | mRNA | Protein deriving DecidableEq, Fintype, Repr open Species
  ```
  > Three species: DNA, mRNA, and Protein.
- **`CRNT.Examples.IrreversibleChain.Species`** — `CRNT.Examples.IrreversibleChain`:24 (`inductive`)
  ```lean
  inductive Species | A | B | C deriving DecidableEq, Fintype, Repr open Species
  ```
  > Three species.
- **`CRNT.Examples.Lotka.Species`** — `CRNT.Examples.Lotka`:88 (`abbrev`)
  ```lean
  abbrev Species : Type
  ```
  > Two species, indexed by `Fin 2`.
- **`CRNT.Examples.Minimal.Species`** — `CRNT.Examples.Minimal`:24 (`inductive`)
  ```lean
  inductive Species | A | B deriving DecidableEq, Fintype, Repr open Species
  ```
  > Two species, `A` and `B`.
- **`CRNT.Examples.ReversiblePair.Species`** — `CRNT.Examples.ReversiblePair`:29 (`inductive`)
  ```lean
  inductive Species | A | B deriving DecidableEq, Repr instance : Fintype Species
  ```
  > Two species, `A` and `B`.
- **`CRNT.Examples.StochasticConvergenceExample.Species`** — `CRNT.Examples.StochasticConvergenceExample`:141 (`inductive`)
  ```lean
  inductive Species | A | B deriving DecidableEq, Repr instance : Fintype Species
  ```
  > Two species, `A` and `B`.
- **`CRNT.LogProjectiveFaceCompatibility.TwoSpeciesJetExample.Species`** — `CRNT.Geometry.LogProjectiveFaceCompatibility`:361 (`abbrev`)
  ```lean
  abbrev Species
  ```
- **`CRNT.Generated.Example.Species`** — `CRNT.Interop.CodegenExamples`:27 (`inductive`)
  ```lean
  inductive Species | A | B deriving DecidableEq, Fintype, Repr open Species
  ```

#### `Rxn`

- **`CRNT.Examples.ACRPair.Rxn`** — `CRNT.Decision.ACRCheck`:127 (`inductive`)
  ```lean
  inductive Rxn | r1 | r2 deriving DecidableEq, Repr instance : Fintype Rxn
  ```
  > Two reactions: `A → P` and `2A → Q`.
- **`CRNT.RankExactExample.Rxn`** — `CRNT.Decision.RankExact`:96 (`abbrev`)
  ```lean
  abbrev Rxn
  ```
  > One reaction channel, the irreversible `X → Y`.
- **`CRNT.DeficiencyOneDecide.Example.Rxn`** — `CRNT.Deficiency.DeficiencyOneDecide`:118 (`inductive`)
  ```lean
  inductive Rxn | r1 | r2 deriving DecidableEq, Repr instance : Fintype Rxn
  ```
  > Class-level terminality unfolds to the complex-level decidable predicate.
- **`CRNT.Design.Adaptation.Rxn`** — `CRNT.Design.Adaptation`:62 (`inductive`)
  ```lean
  inductive Rxn | ref | sense | seq deriving DecidableEq, Repr instance : Fintype Rxn
  ```
  > Three reactions: reference production, sensing, and sequestration.
- **`CRNT.Examples.SiphonReversiblePair.Rxn`** — `CRNT.Dynamics.Siphon`:161 (`inductive`)
  ```lean
  inductive Rxn | fwd | bwd deriving DecidableEq, Repr instance : Fintype Rxn
  ```
  > Two reaction channels: forward `A → B` and backward `B → A`.
- **`CRNT.Examples.ComplexBalancedBoundaryEquilibrium.Rxn`** — `CRNT.Examples.ComplexBalancedBoundaryEquilibrium`:99 (`inductive`)
  ```lean
  inductive Rxn | aToAB | abToA | bToAB | abToB deriving DecidableEq, Repr instance : Fintype Rxn
  ```
  > Four reaction channels: `A → A + B`, `A + B → A`, `B → A + B`, `A + B → B`.
- **`CRNT.Examples.Enzyme.Rxn`** — `CRNT.Examples.Enzyme`:44 (`inductive`)
  ```lean
  inductive Rxn | bind | unbind | catalyze deriving DecidableEq, Fintype, Repr
  ```
  > Three reactions: binding, unbinding, and catalysis.
- **`CRNT.Examples.GeneExpression.Rxn`** — `CRNT.Examples.GeneExpression`:54 (`inductive`)
  ```lean
  inductive Rxn | transcribe | translate | degradeMRNA | degradeProt deriving DecidableEq, Fintype, Repr
  ```
  > Four reactions: transcription, translation, and two degradations.
- **`CRNT.Examples.IrreversibleChain.Rxn`** — `CRNT.Examples.IrreversibleChain`:42 (`inductive`)
  ```lean
  inductive Rxn | r1 | r2 deriving DecidableEq, Fintype, Repr
  ```
  > Two reactions: `A → B` and `B → C`.
- **`CRNT.Examples.Lotka.Rxn`** — `CRNT.Examples.Lotka`:96 (`abbrev`)
  ```lean
  abbrev Rxn : Type
  ```
  > Three reactions, indexed by `Fin 3`.
- **`CRNT.Examples.Minimal.Rxn`** — `CRNT.Examples.Minimal`:38 (`inductive`)
  ```lean
  inductive Rxn | r1 deriving DecidableEq, Fintype, Repr
  ```
  > A single reaction channel.
- **`CRNT.Examples.ReversiblePair.Rxn`** — `CRNT.Examples.ReversiblePair`:47 (`inductive`)
  ```lean
  inductive Rxn | fwd | bwd deriving DecidableEq, Repr instance : Fintype Rxn
  ```
  > Two reaction channels: forward `A → B` and backward `B → A`.
- **`CRNT.Examples.StochasticConvergenceExample.Rxn`** — `CRNT.Examples.StochasticConvergenceExample`:159 (`inductive`)
  ```lean
  inductive Rxn | fwd | bwd deriving DecidableEq, Repr instance : Fintype Rxn
  ```
  > Two reaction channels: forward `A → B` and backward `B → A`.
- **`CRNT.Generated.Example.Rxn`** — `CRNT.Interop.CodegenExamples`:37 (`inductive`)
  ```lean
  inductive Rxn | r1 | r2 deriving DecidableEq, Fintype, Repr
  ```

#### `rxn`

- **`CRNT.Examples.ACRPair.rxn`** — `CRNT.Decision.ACRCheck`:137 (`def`)
  ```lean
  def rxn : Rxn → Reaction Species | .r1 => { source := cA, target := cP } | .r2 => { source := c2A, target := cQ }
  ```
  > The reaction map.
- **`CRNT.RankExactExample.rxn`** — `CRNT.Decision.RankExact`:99 (`def`)
  ```lean
  def rxn : Rxn → Reaction Species
  ```
  > The reaction map: the single channel is `X → Y`.
- **`CRNT.Design.Adaptation.rxn`** — `CRNT.Design.Adaptation`:74 (`def`)
  ```lean
  def rxn : Rxn → Reaction Species | .ref => { source := Complex.zero, target := cZ1 } | .sense => { source := cX, target := cXZ2 } | .seq => { source := cZ1Z2, target := Complex.zero }
  ```
  > The reaction map: `ref` is `0 → Z1`, `sense` is `X → X + Z2`, and `seq` is `Z1 + Z2 → 0`.
- **`CRNT.Examples.SiphonReversiblePair.rxn`** — `CRNT.Dynamics.Siphon`:171 (`def`)
  ```lean
  def rxn : Rxn → Reaction Species | .fwd => { source := cA, target := cB } | .bwd => { source := cB, target := cA }
  ```
  > The reaction map.
- **`CRNT.Examples.CatalyticChain.rxn`** — `CRNT.Examples.CatalyticChain`:20 (`def`)
  ```lean
  def rxn (r : Fin 4) : Reaction (Fin 3)
  ```
- **`CRNT.Examples.ComplexBalancedBoundaryEquilibrium.rxn`** — `CRNT.Examples.ComplexBalancedBoundaryEquilibrium`:111 (`def`)
  ```lean
  def rxn : Rxn → Reaction Species | .aToAB => { source := cA, target := cAB } | .abToA => { source := cAB, target := cA } | .bToAB => { source := cB, target := cAB } | .abToB => { source := cAB, target := cB }
  ```
  > The reaction map.
- **`CRNT.Examples.Enzyme.rxn`** — `CRNT.Examples.Enzyme`:51 (`def`)
  ```lean
  def rxn : Rxn → Reaction Species | .bind => { source := cES_sub, target := cESbound } | .unbind => { source := cESbound, target := cES_sub } | .catalyze => { source := cESbound, target := cEP }
  ```
  > The reaction map.
- **`CRNT.Examples.GeneExpression.rxn`** — `CRNT.Examples.GeneExpression`:62 (`def`)
  ```lean
  def rxn : Rxn → Reaction Species | .transcribe => { source := cDNA, target := cDNAmRNA } | .translate => { source := cmRNA, target := cmRNAProt } | .degradeMRNA => { source := cmRNA, target := Complex.zero } | .degradePr
  ```
  > The reaction map. The zero complex `Complex.zero` is the target of degradation.
- **`CRNT.Examples.HopfNetwork3.rxn`** — `CRNT.Examples.HopfNetwork3`:82 (`def`)
  ```lean
  def rxn (r : Fin 6) : Reaction (Fin 3)
  ```
  > The reaction map of the network.
- **`CRNT.Examples.IrreversibleChain.rxn`** — `CRNT.Examples.IrreversibleChain`:48 (`def`)
  ```lean
  def rxn : Rxn → Reaction Species | .r1 => { source := cA, target := cB } | .r2 => { source := cB, target := cC }
  ```
  > The reaction map.
- **`CRNT.Examples.Lotka.rxn`** — `CRNT.Examples.Lotka`:121 (`def`)
  ```lean
  def rxn : Rxn → Reaction Species
  ```
  > The reaction map.
- **`CRNT.Examples.Minimal.rxn`** — `CRNT.Examples.Minimal`:43 (`def`)
  ```lean
  def rxn : Rxn → Reaction Species | .r1 => { source := cA, target := cB }
  ```
  > The reaction map: `r1 : A → B`.
- **`CRNT.Examples.ReversiblePair.rxn`** — `CRNT.Examples.ReversiblePair`:57 (`def`)
  ```lean
  def rxn : Rxn → Reaction Species | .fwd => { source := cA, target := cB } | .bwd => { source := cB, target := cA }
  ```
  > The reaction map.
- **`CRNT.Examples.StochasticConvergenceExample.rxn`** — `CRNT.Examples.StochasticConvergenceExample`:169 (`def`)
  ```lean
  def rxn : Rxn → Reaction Species | .fwd => { source := cA, target := cB } | .bwd => { source := cB, target := cA }
  ```
  > The reaction map.

#### `numComplexes_eq`

- **`CRNT.Network.Isomorphism.numComplexes_eq`** — `CRNT.Basic.Isomorphism`:192 (`theorem`)
  ```lean
  theorem numComplexes_eq (F : N.Isomorphism M) : N.numComplexes = M.numComplexes
  ```
  > Number of complexes is invariant.
- **`CRNT.Examples.CatalyticChain.numComplexes_eq`** — `CRNT.Examples.CatalyticChain`:29 (`theorem`)
  ```lean
  theorem numComplexes_eq : N.numComplexes = 3
  ```
- **`CRNT.Examples.Enzyme.numComplexes_eq`** — `CRNT.Examples.Enzyme`:61 (`theorem`)
  ```lean
  theorem numComplexes_eq : N.numComplexes = 3
  ```
  > `n = 3`: the three complexes are `E + S`, `ES`, and `E + P`.
- **`CRNT.Examples.GeneExpression.numComplexes_eq`** — `CRNT.Examples.GeneExpression`:75 (`theorem`)
  ```lean
  theorem numComplexes_eq : N.numComplexes = 6
  ```
  > `n = 5`: the five complexes are `DNA`, `DNA+mRNA`, `mRNA`, `mRNA+Protein`, `Protein`, and `0` — but `DNA+mRNA` and `mRNA+Protein` together with the others give five distinct complexes appearing in rea
- **`CRNT.Examples.IrreversibleChain.numComplexes_eq`** — `CRNT.Examples.IrreversibleChain`:57 (`theorem`)
  ```lean
  theorem numComplexes_eq : N.numComplexes = 3
  ```
  > `n = 3`: the network has three complexes.
- **`CRNT.Examples.Minimal.numComplexes_eq`** — `CRNT.Examples.Minimal`:53 (`theorem`)
  ```lean
  theorem numComplexes_eq : N.numComplexes = 2
  ```
  > The network has exactly two complexes.
- **`CRNT.Examples.ReversiblePair.numComplexes_eq`** — `CRNT.Examples.ReversiblePair`:68 (`theorem`)
  ```lean
  theorem numComplexes_eq : N.numComplexes = 2
  ```
  > `n = 2`: the network has two complexes.

#### `numReactions_eq`

- **`CRNT.Network.Isomorphism.numReactions_eq`** — `CRNT.Basic.Isomorphism`:199 (`theorem`)
  ```lean
  theorem numReactions_eq (F : N.Isomorphism M) : N.numReactions = M.numReactions
  ```
  > Number of reaction channels is invariant.
- **`CRNT.Examples.Enzyme.numReactions_eq`** — `CRNT.Examples.Enzyme`:64 (`theorem`)
  ```lean
  theorem numReactions_eq : N.numReactions = 3
  ```
  > There are three reactions.
- **`CRNT.Examples.IrreversibleChain.numReactions_eq`** — `CRNT.Examples.IrreversibleChain`:60 (`theorem`)
  ```lean
  theorem numReactions_eq : N.numReactions = 2
  ```
  > There are two reactions.
- **`CRNT.Examples.Lotka.numReactions_eq`** — `CRNT.Examples.Lotka`:137 (`theorem`)
  ```lean
  theorem numReactions_eq : N.numReactions = 3
  ```
  > Five distinct complexes: `A`, `2A`, `A + B`, `2B`, `B`, `0` — with `2A` and `0` both appearing, so six listed but the count is what `decide` says.
- **`CRNT.Examples.Minimal.numReactions_eq`** — `CRNT.Examples.Minimal`:56 (`theorem`)
  ```lean
  theorem numReactions_eq : N.numReactions = 1
  ```
  > There is one reaction.
- **`CRNT.Examples.ReversiblePair.numReactions_eq`** — `CRNT.Examples.ReversiblePair`:71 (`theorem`)
  ```lean
  theorem numReactions_eq : N.numReactions = 2
  ```
  > The network has two reaction channels.

#### `Cell`

- **`CRNT.Analysis.SpernerGrid.Cell`** — `CRNT.Analysis.SpernerGrid`:65 (`inductive`)
  ```lean
  inductive Cell | tri deriving DecidableEq instance : Fintype Cell
  ```
  > The single-triangle datatype of the minimal triangulated domain.
- **`CRNT.Analysis.SpernerN2Geo.Cell`** — `CRNT.Analysis.SpernerGridGeometric`:74 (`inductive`)
  ```lean
  inductive Cell | up1 | up2 | up3 | dn deriving DecidableEq instance : Fintype Cell
  ```
  > The four triangles.
- **`CRNT.Analysis.SpernerN2.Cell`** — `CRNT.Analysis.SpernerGridMulti`:55 (`inductive`)
  ```lean
  inductive Cell | up1 | up2 | up3 | dn deriving DecidableEq instance : Fintype Cell
  ```
  > The four triangles of the `N = 2` subdivision: three corner triangles and the central inverted one.
- **`CRNT.Analysis.SpernerLattice.Cell`** — `CRNT.Analysis.SpernerLattice`:92 (`abbrev`)
  ```lean
  abbrev Cell (N : ℕ) : Type
  ```
  > The triangles of the subdivision: up triangles and down triangles.
- **`CRNT.Analysis.SpernerN.Cell`** — `CRNT.Analysis.SpernerLatticeN`:148 (`structure`)
  ```lean
  structure Cell (n N : ℕ)
  ```
  > A **maximal Kuhn cell** of the `N`-subdivision: a base lattice point and a permutation of the `n` simple-root directions, valid where every partial-sum vertex has nonnegative coordinates.

#### `trans`

- **`CRNT.Network.Isomorphism.trans`** — `CRNT.Basic.Isomorphism`:94 (`def`)
  ```lean
  def trans {U : Type} [DecidableEq U] [Fintype U] {L : Network U} (F : N.Isomorphism M) (G : M.Isomorphism L) : N.Isomorphism L
  ```
  > Composition of network isomorphisms.
- **`CRNT.Network.MassActionRealization.trans`** — `Scaffold.CRNTExpansion.RealizationComposition`:22 (`def`)
  ```lean
  def trans (R : MassActionRealization N κN) (Q : MassActionRealization R.network R.rates) : MassActionRealization N κN
  ```
  > Dynamically equivalent realizations compose.
- **`CRNT.Network.StoichiometricMassActionRealization.trans`** — `Scaffold.CRNTExpansion.RealizationComposition`:36 (`def`)
  ```lean
  def trans (R : StoichiometricMassActionRealization N κN) (Q : StoichiometricMassActionRealization R.network R.rates) : StoichiometricMassActionRealization N κN
  ```
  > Stoichiometric realizations compose, preserving both the vector field and the compatibility subspace.
- **`CRNT.Network.SourceCoefficientRealizationCertificate.trans`** — `Scaffold.CRNTExpansion.RealizationComposition`:51 (`def`)
  ```lean
  def trans (C : SourceCoefficientRealizationCertificate N κN) (D : SourceCoefficientRealizationCertificate C.network C.rates) : SourceCoefficientRealizationCertificate N κN
  ```
  > Finite source-coefficient certificates compose by transitivity of coefficient equality.
- **`CRNT.Network.StoichiometricSourceCoefficientRealizationCertificate.trans`** — `Scaffold.CRNTExpansion.RealizationComposition`:74 (`def`)
  ```lean
  def trans (C : StoichiometricSourceCoefficientRealizationCertificate N κN) (D : StoichiometricSourceCoefficientRealizationCertificate C.network C.rates) : StoichiometricSourceCoefficientRealizationCertificate N κN
  ```
  > Stoichiometric source-coefficient certificates compose.

#### `exists_rainbow_cell`

- **`CRNT.Analysis.SpernerGrid.exists_rainbow_cell`** — `CRNT.Analysis.SpernerGrid`:153 (`theorem`)
  ```lean
  theorem exists_rainbow_cell : ∃ t : Cell, doorIncidence.IsRainbowCell t
  ```
  > **Concrete two-dimensional Sperner.** The concretely constructed single-cell door-incidence datum has a rainbow triangle.
- **`CRNT.Analysis.SpernerN2Geo.exists_rainbow_cell`** — `CRNT.Analysis.SpernerGridGeometric`:167 (`theorem`)
  ```lean
  theorem exists_rainbow_cell : ∃ t : Cell, multiDoorIncidence.IsRainbowCell t
  ```
  > **Geometrically-derived two-dimensional Sperner.** The door-incidence datum built from the `N = 2` subdivision's geometry has a rainbow triangle (the central triangle `dn`).
- **`CRNT.Analysis.SpernerN2.exists_rainbow_cell`** — `CRNT.Analysis.SpernerGridMulti`:105 (`theorem`)
  ```lean
  theorem exists_rainbow_cell : ∃ t : Cell, multiDoorIncidence.IsRainbowCell t
  ```
  > **Concrete multi-triangle two-dimensional Sperner.** The `N = 2` subdivision's door-incidence datum has a rainbow triangle (it is the central triangle `dn`).
- **`CRNT.Analysis.SpernerLattice.exists_rainbow_cell`** — `CRNT.Analysis.SpernerLatticeSperner`:37 (`theorem`)
  ```lean
  theorem exists_rainbow_cell (κ : SpernerColoring N) : ∃ t : Cell N, isRainbow (col κ t).1 (col κ t).2.1 (col κ t).2.2 = true
  ```
  > **Two-dimensional Sperner lemma (parametric `N`).** Every proper Sperner coloring of the `N`-subdivision of the 2-simplex has a rainbow triangle — one whose three vertices carry the three colors `0, 1

#### `numLinkageClasses_eq`

- **`CRNT.Network.Isomorphism.numLinkageClasses_eq`** — `CRNT.Basic.Isomorphism`:308 (`theorem`)
  ```lean
  theorem numLinkageClasses_eq (F : N.Isomorphism M) : N.numLinkageClasses = M.numLinkageClasses
  ```
  > Linkage-class count is an isomorphism invariant.
- **`CRNT.Examples.CatalyticChain.numLinkageClasses_eq`** — `CRNT.Examples.CatalyticChain`:42 (`theorem`)
  ```lean
  theorem numLinkageClasses_eq : N.numLinkageClasses = 1
  ```
- **`CRNT.Examples.DecideLinkage.numLinkageClasses_eq`** — `CRNT.Examples.DecideLinkage`:21 (`theorem`)
  ```lean
  theorem numLinkageClasses_eq : N.numLinkageClasses = 1
  ```
  > Hence `ℓ = 1`, obtained by reduction through the computable component count.
- **`CRNT.Examples.ReversiblePair.numLinkageClasses_eq`** — `CRNT.Examples.ReversiblePair`:104 (`theorem`)
  ```lean
  theorem numLinkageClasses_eq : N.numLinkageClasses = 1
  ```
  > `ℓ = 1`: there is a single linkage class.

#### `Outer`

- **`CRNT.Analysis.SpernerN2Geo.Outer`** — `CRNT.Analysis.SpernerGridGeometric`:83 (`inductive`)
  ```lean
  inductive Outer | edgeAmAB deriving DecidableEq instance : Fintype Outer
  ```
  > The boundary outer vertices: one for the boundary door edge `A–mAB` on side `AB`.
- **`CRNT.Analysis.SpernerN2.Outer`** — `CRNT.Analysis.SpernerGridMulti`:67 (`inductive`)
  ```lean
  inductive Outer | boundary deriving DecidableEq instance : Fintype Outer
  ```
  > The boundary outer vertices: a single `{0,1}`-door on side `AB` (the edge `A–mAB`).
- **`CRNT.Analysis.SpernerLattice.Outer`** — `CRNT.Analysis.SpernerLatticeFullGraph`:27 (`abbrev`)
  ```lean
  abbrev Outer (N : ℕ) : Type
  ```
  > Boundary **outer vertices**: one per hypotenuse (`i+j=N`) sub-edge of the `N`-subdivision.

#### `cellColors`

- **`CRNT.Analysis.SpernerGrid.cellColors`** — `CRNT.Analysis.SpernerGrid`:73 (`def`)
  ```lean
  def cellColors : Cell → Color × Color × Color
  ```
  > The three vertex colors of each triangle: the rainbow triple `(0, 1, 2)`.
- **`CRNT.Analysis.SpernerN2.cellColors`** — `CRNT.Analysis.SpernerGridMulti`:77 (`def`)
  ```lean
  def cellColors : Cell → Color × Color × Color | .up1 => (0, 1, 0) | .up2 => (1, 1, 2) | .up3 => (0, 2, 2) | .dn => (1, 0, 2)
  ```
  > The vertex-color triples of the four triangles under the coloring `A = 0, B = 1, C = 2, mAB = 1, mAC = 0, mBC = 2`.
- **`CRNT.Analysis.SpernerN.cellColors`** — `CRNT.Analysis.SpernerNSperner`:29 (`def`)
  ```lean
  def cellColors (col : SpernerColoring n N) (c : Cell n N) : Fin (n + 1) → Fin (n + 1)
  ```
  > The colors that a cell's `n+1` vertices receive under a Sperner coloring.

#### `colorOf`

- **`CRNT.Analysis.SpernerLattice.colorOf`** — `CRNT.Analysis.SpernerBrouwer2D`:67 (`def`)
  ```lean
  noncomputable def colorOf (hN : 0 < N) (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (p : Pt N) : Color
  ```
  > The chosen non-increasing positive coordinate as a colour.
- **`CRNT.Analysis.SpernerN.colorOf`** — `CRNT.Analysis.SpernerBrouwerN`:67 (`def`)
  ```lean
  noncomputable def colorOf (hN : 0 < N) (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1)))) (p : Pt n N) : Fin (n + 1)
  ```
  > The chosen non-increasing positive coordinate as a color.
- **`CRNT.Analysis.SpernerN2Geo.colorOf`** — `CRNT.Analysis.SpernerGridGeometric`:93 (`def`)
  ```lean
  def colorOf : Vertex → Color | .A => 0 | .B => 1 | .C => 2 | .mAB => 1 | .mAC => 0 | .mBC => 2
  ```
  > The vertex coloring: corners `0, 1, 2`; midpoints chosen in the Sperner-admissible pair of their side (`mAB = 1, mAC = 0, mBC = 2`).

#### `generalizedRate`

- **`CRNT.Network.GeneralizedMassActionData.generalizedRate`** — `CRNT.Kinetics.GeneralizedNetwork`:247 (`def`)
  ```lean
  noncomputable def generalizedRate (G : N.GeneralizedMassActionData) (κ : N.RateConstants) (x : Concentration S) (r : N.R) : ℝ
  ```
  > Generalized mass-action reaction rate.
- **`CRNT.Network.generalizedRate`** — `CRNT.Translation.ComplexBalance`:42 (`def`)
  ```lean
  def generalizedRate (N : Network S) (τ : N.R → Complex S) (κ : RateConstants N) (x : Concentration S) (r : N.R) : ℝ
  ```
  > Generalized reaction rate: translated stoichiometry, original kinetic complex.
- **`CRNT.Network.ReactionTranslation.generalizedRate`** — `CRNT.Translation.ComplexBalance`:143 (`def`)
  ```lean
  def generalizedRate (T : N.ReactionTranslation) (κ : RateConstants N) (x : Concentration S) (r : N.R) : ℝ
  ```
  > Translation-level wrapper for the generalized reaction rate.

#### `matrix`

- **`CRNT.Network.IndexedChildSelection.matrix`** — `CRNT.Oscillation.ChildSelectionSearch`:39 (`def`)
  ```lean
  def matrix (C : N.IndexedChildSelection I) : Matrix I I ℝ
  ```
  > Square stoichiometric matrix associated with an indexed child selection.
- **`CRNT.Network.ChildSelection.matrix`** — `CRNT.Oscillation.StructuralCore`:45 (`def`)
  ```lean
  def matrix (C : N.ChildSelection) : Matrix C.Idx C.Idx ℝ
  ```
  > The stoichiometric child-selection matrix. Column `j` is the reaction vector paired to species `j`; rows are the selected species.
- **`CRNT.Network.PositiveDiagonalChange.matrix`** — `CRNT.Translation.LinearConjugacy`:67 (`def`)
  ```lean
  def matrix (D : PositiveDiagonalChange S) : Matrix S S ℝ
  ```
  > Diagonal matrix of the coordinate change.

#### `multiDoorIncidence`

- **`CRNT.Analysis.SpernerN2Geo.multiDoorIncidence`** — `CRNT.Analysis.SpernerGridGeometric`:159 (`def`)
  ```lean
  def multiDoorIncidence : MultiDoorIncidence Cell Outer
  ```
  > The geometrically-derived four-cell multi-outer door-incidence datum. Its `cell_degree` and `outer_odd` fields hold because the door graph — defined from `triVerts` and `colorOf` — gives each triangle
- **`CRNT.Analysis.SpernerN2.multiDoorIncidence`** — `CRNT.Analysis.SpernerGridMulti`:97 (`def`)
  ```lean
  def multiDoorIncidence : MultiDoorIncidence Cell Outer
  ```
  > The concrete four-cell multi-outer door-incidence datum.
- **`CRNT.Analysis.SpernerLattice.multiDoorIncidence`** — `CRNT.Analysis.SpernerLatticeSperner`:28 (`def`)
  ```lean
  def multiDoorIncidence (κ : SpernerColoring N) : MultiDoorIncidence (Cell N) (Outer N)
  ```
  > The **multi-door-incidence datum** of the `N`-subdivision under a proper Sperner coloring: the full door graph, the per-triangle colors, and the two discharged geometric obligations.

#### `reactionAt`

- **`CRNT.Network.TrueSRClosedWalk.reactionAt`** — `CRNT.Multistationarity.TrueSRClosedWalk`:91 (`def`)
  ```lean
  noncomputable def reactionAt (m : Fin (2 * n)) (hm : m.1 % 2 ≠ 0) : N.InternalTrueReaction
  ```
  > The reaction at an odd position.
- **`CRNT.Network.TrueSRPath.reactionAt`** — `CRNT.Multistationarity.TrueSRPathAccessors`:46 (`def`)
  ```lean
  noncomputable def reactionAt (P : N.TrueSRPath L) (p : Fin (L + 1)) (hp : p.1 % 2 ≠ 0) : N.InternalTrueReaction
  ```
  > The reaction carried by an odd position.
- **`CRNT.Network.TrueSRSSPath.reactionAt`** — `CRNT.Multistationarity.TrueSRSpeciesPath`:162 (`def`)
  ```lean
  noncomputable def reactionAt (P : N.TrueSRSSPath L) (p : Fin (L + 1)) (hp : p.1 % 2 ≠ 0) : N.InternalTrueReaction
  ```
  > The reaction at an odd position.

#### `reducedField`

- **`ODE.ReductionData.reducedField`** — `CRNT.Dynamics.CenterManifoldReduction`:101 (`def`)
  ```lean
  def reducedField (c : Ec) : Ec
  ```
  > **The reduced vector field on the center subspace.** `reducedField c` is the center projection of the full field evaluated on the manifold at center coordinate `c`: `reducedField c = π_c (field (c, h 
- **`CRNT.Network.reducedField`** — `CRNT.Multistationarity.ReducedJacobian`:39 (`def`)
  ```lean
  noncomputable def reducedField (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) : (Fin N.stoichRank → ℝ) → (Fin N.stoichRank → ℝ)
  ```
  > The reduced field on `Fin s → ℝ`: the mass-action vector field on the affine slice through `x₀`, read in chart coordinates.
- **`CRNT.IntermediateLinearBlock.reducedField`** — `CRNT.Reduction.IntermediateSchurComplement`:46 (`def`)
  ```lean
  noncomputable def reducedField (B : IntermediateLinearBlock Core H) (x : Core → ℝ) : Core → ℝ
  ```
  > Reduced core vector field after exact steady-state elimination.

#### `source`

- **`CRNT.Examples.CatalyticChain.source`** — `CRNT.Examples.CatalyticChain`:8 (`def`)
  ```lean
  def source : Fin 4 → Complex (Fin 3) | 0 => ![1,0,1] | 1 => ![0,0,2] | 2 => ![0,0,2] | 3 => ![0,1,1]
  ```
- **`CRNT.Examples.HopfNetwork3.source`** — `CRNT.Examples.HopfNetwork3`:64 (`def`)
  ```lean
  def source : Fin 6 → Complex (Fin 3) | 0 => ![0, 0, 0] | 1 => ![1, 1, 0] | 2 => ![0, 2, 1] | 3 => ![0, 1, 0] | 4 => ![0, 1, 0] | 5 => ![0, 0, 1]
  ```
  > The six source complexes, indexed by reaction (`Fin 6`).
- **`CRNT.Network.ReactionTranslation.source`** — `CRNT.Translation.ReactionTranslation`:127 (`def`)
  ```lean
  def source {N : Network S} (T : N.ReactionTranslation) (r : N.R) : Complex S
  ```
  > Translated source complex of a reaction channel.

#### `speciesAt`

- **`CRNT.Network.TrueSRClosedWalk.speciesAt`** — `CRNT.Multistationarity.TrueSRClosedWalk`:83 (`def`)
  ```lean
  noncomputable def speciesAt (m : Fin (2 * n)) (hm : m.1 % 2 = 0) : S
  ```
  > The species at an even position.
- **`CRNT.Network.TrueSRPath.speciesAt`** — `CRNT.Multistationarity.TrueSRPathAccessors`:36 (`def`)
  ```lean
  noncomputable def speciesAt (P : N.TrueSRPath L) (p : Fin (L + 1)) (hp : p.1 % 2 = 0) : S
  ```
  > The species carried by an even position.
- **`CRNT.Network.TrueSRSSPath.speciesAt`** — `CRNT.Multistationarity.TrueSRSpeciesPath`:154 (`def`)
  ```lean
  noncomputable def speciesAt (P : N.TrueSRSSPath L) (p : Fin (L + 1)) (hp : p.1 % 2 = 0) : S
  ```
  > The species at an even position.

#### `steadyState_iff`

- **`CRNT.Network.MassActionRealization.steadyState_iff`** — `CRNT.Translation.DynamicalEquivalence`:91 (`theorem`)
  ```lean
  theorem steadyState_iff (R : MassActionRealization N κN) (x : Concentration S) : N.IsMassActionSteadyState κN x ↔ R.network.IsMassActionSteadyState R.rates x
  ```
  > Every alternative realization has the same steady-state predicate as the original one.
- **`CRNT.Network.SourceCoefficientRealizationCertificate.steadyState_iff`** — `Scaffold.CRNTExpansion.RealizationCertificates`:39 (`theorem`)
  ```lean
  theorem steadyState_iff (C : SourceCoefficientRealizationCertificate N κN) (x : Concentration S) : N.IsMassActionSteadyState κN x ↔ C.network.IsMassActionSteadyState C.rates x
  ```
  > Every certified source-coefficient realization has exactly the original steady-state set.
- **`CRNT.Network.StoichiometricMassActionRealization.steadyState_iff`** — `Scaffold.CRNTExpansion.RealizationTheory`:96 (`theorem`)
  ```lean
  theorem steadyState_iff (R : StoichiometricMassActionRealization N κN) (x : Concentration S) : N.IsMassActionSteadyState κN x <-> R.network.IsMassActionSteadyState R.rates x
  ```
  > Stoichiometric realizations have the same steady states.

#### `stoichRank_eq`

- **`CRNT.Network.Isomorphism.stoichRank_eq`** — `CRNT.Basic.Isomorphism`:142 (`theorem`)
  ```lean
  theorem stoichRank_eq (F : N.Isomorphism M) : N.stoichRank = M.stoichRank
  ```
  > Stoichiometric rank is an isomorphism invariant.
- **`CRNT.Examples.CatalyticChain.stoichRank_eq`** — `CRNT.Examples.CatalyticChain`:102 (`theorem`)
  ```lean
  theorem stoichRank_eq : N.stoichRank = 2
  ```
- **`CRNT.Examples.ReversiblePair.stoichRank_eq`** — `CRNT.Examples.ReversiblePair`:119 (`theorem`)
  ```lean
  theorem stoichRank_eq : N.stoichRank = 1
  ```
  > `s = 1`: the stoichiometric subspace is the line spanned by the forward reaction vector.

#### `target`

- **`CRNT.Examples.CatalyticChain.target`** — `CRNT.Examples.CatalyticChain`:14 (`def`)
  ```lean
  def target : Fin 4 → Complex (Fin 3) | 0 => ![0,0,2] | 1 => ![1,0,1] | 2 => ![0,1,1] | 3 => ![0,0,2]
  ```
- **`CRNT.Examples.HopfNetwork3.target`** — `CRNT.Examples.HopfNetwork3`:73 (`def`)
  ```lean
  def target : Fin 6 → Complex (Fin 3) | 0 => ![1, 0, 0] | 1 => ![0, 2, 0] | 2 => ![0, 3, 0] | 3 => ![0, 0, 1] | 4 => ![0, 0, 0] | 5 => ![0, 0, 0]
  ```
  > The six target complexes, indexed by reaction (`Fin 6`).
- **`CRNT.Network.ReactionTranslation.target`** — `CRNT.Translation.ReactionTranslation`:131 (`def`)
  ```lean
  def target {N : Network S} (T : N.ReactionTranslation) (r : N.R) : Complex S
  ```
  > Translated target complex of a reaction channel.

#### `toPath`

- **`CRNT.Network.TrueSREdge.toPath`** — `CRNT.Multistationarity.TrueSREdgePath`:20 (`def`)
  ```lean
  def toPath (e : N.TrueSREdge) : N.TrueSRPath 1
  ```
  > A single true-SR edge, read as a species-to-reaction path of length one.
- **`CRNT.Network.TrueSRLinearWalk.toPath`** — `CRNT.Multistationarity.TrueSRLinearWalk`:61 (`def`)
  ```lean
  noncomputable def toPath : N.TrueSRPath (2 * k + 1)
  ```
  > **A linear alternating walk is a species-to-reaction path.**
- **`CRNT.Network.TrueSRSSPath.toPath`** — `CRNT.Multistationarity.TrueSRSpeciesPath`:75 (`def`)
  ```lean
  def toPath (P : N.TrueSRSSPath L) : N.TrueSRPath (L - 1)
  ```
  > Dropping the last edge of a species-to-species path leaves a species-to-reaction path.

#### `vertex_eq_reactionAt`

- **`CRNT.Network.TrueSRClosedWalk.vertex_eq_reactionAt`** — `CRNT.Multistationarity.TrueSRClosedWalk`:95 (`theorem`)
  ```lean
  theorem vertex_eq_reactionAt (m : Fin (2 * n)) (hm : m.1 % 2 ≠ 0) : W.vertex m = Sum.inr (W.reactionAt m hm)
  ```
  > The reaction at an odd position.
- **`CRNT.Network.TrueSRPath.vertex_eq_reactionAt`** — `CRNT.Multistationarity.TrueSRPathAccessors`:50 (`theorem`)
  ```lean
  theorem vertex_eq_reactionAt (P : N.TrueSRPath L) (p : Fin (L + 1)) (hp : p.1 % 2 ≠ 0) : P.vertex p = Sum.inr (P.reactionAt p hp)
  ```
  > The reaction carried by an odd position.
- **`CRNT.Network.TrueSRSSPath.vertex_eq_reactionAt`** — `CRNT.Multistationarity.TrueSRSpeciesPath`:166 (`theorem`)
  ```lean
  theorem vertex_eq_reactionAt (P : N.TrueSRSSPath L) (p : Fin (L + 1)) (hp : p.1 % 2 ≠ 0) : P.vertex p = Sum.inr (P.reactionAt p hp)
  ```
  > The reaction at an odd position.

#### `vertex_eq_speciesAt`

- **`CRNT.Network.TrueSRClosedWalk.vertex_eq_speciesAt`** — `CRNT.Multistationarity.TrueSRClosedWalk`:86 (`theorem`)
  ```lean
  theorem vertex_eq_speciesAt (m : Fin (2 * n)) (hm : m.1 % 2 = 0) : W.vertex m = Sum.inl (W.speciesAt m hm)
  ```
  > The species at an even position.
- **`CRNT.Network.TrueSRPath.vertex_eq_speciesAt`** — `CRNT.Multistationarity.TrueSRPathAccessors`:40 (`theorem`)
  ```lean
  theorem vertex_eq_speciesAt (P : N.TrueSRPath L) (p : Fin (L + 1)) (hp : p.1 % 2 = 0) : P.vertex p = Sum.inl (P.speciesAt p hp)
  ```
  > The species carried by an even position.
- **`CRNT.Network.TrueSRSSPath.vertex_eq_speciesAt`** — `CRNT.Multistationarity.TrueSRSpeciesPath`:157 (`theorem`)
  ```lean
  theorem vertex_eq_speciesAt (P : N.TrueSRSSPath L) (p : Fin (L + 1)) (hp : p.1 % 2 = 0) : P.vertex p = Sum.inl (P.speciesAt p hp)
  ```
  > The species at an even position.

#### `IsOscillatoryCoreClassI.not_classII`

- **`Matrix.IsOscillatoryCoreClassI.not_classII`** — `CRNT.Oscillation.MatrixCriteria`:280 (`theorem`)
  ```lean
  theorem IsOscillatoryCoreClassI.not_classII {M : Matrix n n ℝ} (hI : M.IsOscillatoryCoreClassI) : ¬ M.IsOscillatoryCoreClassII
  ```
  > Class-I and class-II oscillatory-core predicates are mutually exclusive: class I is Hurwitz stable, whereas class II carries a strict right-half-plane eigenvalue.
- **`CRNT.Network.ChildSelection.IsOscillatoryCoreClassI.not_classII`** — `CRNT.Oscillation.StructuralCore`:123 (`theorem`)
  ```lean
  theorem IsOscillatoryCoreClassI.not_classII {C : N.ChildSelection} (h : C.IsOscillatoryCoreClassI) : ¬ C.IsOscillatoryCoreClassII
  ```
  > A child selection cannot simultaneously be a class-I and class-II oscillatory core.

#### `IsOscillatoryCoreClassII.not_classI`

- **`Matrix.IsOscillatoryCoreClassII.not_classI`** — `CRNT.Oscillation.MatrixCriteria`:286 (`theorem`)
  ```lean
  theorem IsOscillatoryCoreClassII.not_classI {M : Matrix n n ℝ} (hII : M.IsOscillatoryCoreClassII) : ¬ M.IsOscillatoryCoreClassI
  ```
  > Symmetric form of class-I/class-II exclusivity.
- **`CRNT.Network.ChildSelection.IsOscillatoryCoreClassII.not_classI`** — `CRNT.Oscillation.StructuralCore`:128 (`theorem`)
  ```lean
  theorem IsOscillatoryCoreClassII.not_classI {C : N.ChildSelection} (h : C.IsOscillatoryCoreClassII) : ¬ C.IsOscillatoryCoreClassI
  ```
  > Symmetric class-I/class-II exclusivity for child selections.

#### `PeriodicTrajectory.normalizedLoop`

- **`CRNT.PeriodicTrajectory.normalizedLoop`** — `CRNT.Oscillation.Basic`:56 (`def`)
  ```lean
  noncomputable def PeriodicTrajectory.normalizedLoop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {field : E → E} (P : PeriodicTrajectory field) (s : ℝ) : E
  ```
  > The periodic orbit reparameterized to the unit interval: `normalizedLoop s = orbit (s * period)`. Used by the planar Jordan-curve machinery, which needs a loop on `[0,1]`. (It was referenced by `Plana
- **`CRNT.Planar.PeriodicTrajectory.normalizedLoop`** — `CRNT.Oscillation.PlanarJordanSeparation`:139 (`def`)
  ```lean
  noncomputable def PeriodicTrajectory.normalizedLoop {field : Phase2 → Phase2} (P : PeriodicTrajectory field) : ℝ → Phase2
  ```
  > Normalize one least-period traversal to `[0,1]`.

#### `Pt`

- **`CRNT.Analysis.SpernerLattice.Pt`** — `CRNT.Analysis.SpernerLattice`:62 (`abbrev`)
  ```lean
  abbrev Pt (N : ℕ) : Type
  ```
  > A lattice point of the `N`-subdivision of the 2-simplex: `(i, j)` with `i + j ≤ N`.
- **`CRNT.Analysis.SpernerN.Pt`** — `CRNT.Analysis.SpernerLatticeN`:31 (`def`)
  ```lean
  def Pt (n N : ℕ) : Type
  ```
  > **Lattice points** of the `N`-subdivision of the standard `n`-simplex: nonnegative integer barycentric coordinates (`n+1` of them) summing to `N`.

#### `col`

- **`CRNT.Analysis.SpernerN2Geo.col`** — `CRNT.Analysis.SpernerGridGeometric`:107 (`def`)
  ```lean
  def col (t : Cell) : Color × Color × Color
  ```
  > The color triple of a triangle, read off its vertices.
- **`CRNT.Analysis.SpernerLattice.col`** — `CRNT.Analysis.SpernerLatticeCellColor`:80 (`def`)
  ```lean
  def col (κ : SpernerColoring N) : Cell N → Color × Color × Color
  ```
  > The vertex-color triple of a triangle.

#### `colorOf_dec`

- **`CRNT.Analysis.SpernerLattice.colorOf_dec`** — `CRNT.Analysis.SpernerBrouwer2D`:76 (`theorem`)
  ```lean
  theorem colorOf_dec (hN : 0 < N) (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (p : Pt N) : (f (realizePt hN p) : Fin 3 → ℝ) (colorOf hN f p) ≤ realize p (colorOf hN f p)
  ```
  > The chosen non-increasing positive coordinate as a colour.
- **`CRNT.Analysis.SpernerN.colorOf_dec`** — `CRNT.Analysis.SpernerBrouwerN`:77 (`theorem`)
  ```lean
  theorem colorOf_dec (hN : 0 < N) (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1)))) (p : Pt n N) : (f (realizePt hN p) : Fin (n + 1) → ℝ) (colorOf hN f p) ≤ realize p (colorOf hN f p)
  ```
  > The chosen non-increasing positive coordinate as a color.

#### `colorOf_pos`

- **`CRNT.Analysis.SpernerLattice.colorOf_pos`** — `CRNT.Analysis.SpernerBrouwer2D`:71 (`theorem`)
  ```lean
  theorem colorOf_pos (hN : 0 < N) (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (p : Pt N) : 0 < realize p (colorOf hN f p)
  ```
  > The chosen non-increasing positive coordinate as a colour.
- **`CRNT.Analysis.SpernerN.colorOf_pos`** — `CRNT.Analysis.SpernerBrouwerN`:72 (`theorem`)
  ```lean
  theorem colorOf_pos (hN : 0 < N) (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1)))) (p : Pt n N) : 0 < realize p (colorOf hN f p)
  ```
  > The chosen non-increasing positive coordinate as a color.

#### `complexBalanced_geometricInterpolate`

- **`CRNT.Network.complexBalanced_geometricInterpolate`** — `CRNT.Equilibria.ComplexBalanceGeometry`:139 (`theorem`)
  ```lean
  theorem complexBalanced_geometricInterpolate (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible) {x y : Concentration S} (hx : x.Positive) (hy : y.Positive) (hcx : N.IsComplexBalanced κ x) (hcy : N.IsComplex
  ```
  > **Log/geodesic convexity of the complex-balanced equilibrium set.**
- **`CRNT.Network.GeneralizedMassActionData.complexBalanced_geometricInterpolate`** — `CRNT.Equilibria.GeneralizedComplexBalanceGeometry`:66 (`theorem`)
  ```lean
  theorem complexBalanced_geometricInterpolate (G : N.GeneralizedMassActionData) (κ : N.RateConstants) (hwr : N.WeaklyReversible) {x y : Concentration S} (hx : x.Positive) (hy : y.Positive) (hcx : G.IsComplexBalanced κ x) 
  ```
  > Geometric interpolation of generalized CBEs stays complex balanced.

#### `complexBalanced_iff_treeConstantBinomials`

- **`CRNT.Network.GeneralizedMassActionData.complexBalanced_iff_treeConstantBinomials`** — `CRNT.Equilibria.GeneralizedTreeConstantCriterion`:121 (`theorem`)
  ```lean
  theorem complexBalanced_iff_treeConstantBinomials (G : N.GeneralizedMassActionData) (κ : N.RateConstants) (hwr : N.WeaklyReversible) {x : Concentration S} : G.IsComplexBalanced κ x ↔ G.SatisfiesTreeConstantBinomials κ x
  ```
  > **Generalized tree-constant criterion.**
- **`CRNT.Network.complexBalanced_iff_treeConstantBinomials`** — `CRNT.Equilibria.TreeConstantCriterion`:76 (`theorem`)
  ```lean
  theorem complexBalanced_iff_treeConstantBinomials (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible) {x : Concentration S} (hx : x.Positive) : N.IsComplexBalanced κ x ↔ N.SatisfiesTreeConstantBinomials κ x
  ```
  > **Classical tree-constant criterion.**

#### `complexBalanced_of_linkage_scalars`

- **`CRNT.Network.GeneralizedMassActionData.complexBalanced_of_linkage_scalars`** — `CRNT.Equilibria.GeneralizedTreeConstantCriterion`:153 (`theorem`)
  ```lean
  theorem complexBalanced_of_linkage_scalars (G : N.GeneralizedMassActionData) (κ : N.RateConstants) (hwr : N.WeaklyReversible) {x : Concentration S} {a : Quotient N.linkedSetoid → ℝ} (ha : ∀ q, 0 < a q) (hparam : ∀ c : N.
  ```
  > Conversely, a positive classwise tree-constant parametrization is generalized complex balance.
- **`CRNT.Network.complexBalanced_of_linkage_scalars`** — `CRNT.Equilibria.TreeConstantCriterion`:107 (`theorem`)
  ```lean
  theorem complexBalanced_of_linkage_scalars (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible) {x : Concentration S} (hx : x.Positive) {a : Quotient N.linkedSetoid → ℝ} (ha : ∀ q, 0 < a q) (hparam : ∀ c : N.
  ```
  > Conversely, any positive classwise tree-constant parametrization is complex-balanced.

#### `complexBalanced_of_treeConstantBinomials`

- **`CRNT.Network.GeneralizedMassActionData.complexBalanced_of_treeConstantBinomials`** — `CRNT.Equilibria.GeneralizedTreeConstantCriterion`:85 (`theorem`)
  ```lean
  theorem complexBalanced_of_treeConstantBinomials (G : N.GeneralizedMassActionData) (κ : N.RateConstants) (hwr : N.WeaklyReversible) {x : Concentration S} (hbin : G.SatisfiesTreeConstantBinomials κ x) : G.IsComplexBalance
  ```
  > On a weakly reversible graph, generalized tree-constant binomials imply generalized complex balance.
- **`CRNT.Network.complexBalanced_of_treeConstantBinomials`** — `CRNT.Equilibria.TreeConstantCriterion`:43 (`theorem`)
  ```lean
  theorem complexBalanced_of_treeConstantBinomials (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible) {x : Concentration S} (hx : x.Positive) (hbin : N.SatisfiesTreeConstantBinomials κ x) : N.IsComplexBalance
  ```
  > Under weak reversibility, the tree-constant binomials are sufficient for positive complex balance.

#### `deficiencyZero_iff`

- **`CRNT.Network.Isomorphism.deficiencyZero_iff`** — `CRNT.Basic.Isomorphism`:358 (`theorem`)
  ```lean
  theorem deficiencyZero_iff (F : N.Isomorphism M) : N.DeficiencyZero ↔ M.DeficiencyZero
  ```
  > Deficiency zero is invariant.
- **`CRNT.Network.deficiencyZero_iff`** — `CRNT.Deficiency.Definition`:32 (`theorem`)
  ```lean
  theorem deficiencyZero_iff (N : Network S) : N.DeficiencyZero ↔ (N.numComplexes : ℤ) - (N.numLinkageClasses : ℤ) - (N.stoichRank : ℤ) = 0
  ```
  > A network has deficiency zero when `n - ℓ - s = 0`. This is the structural hypothesis of the deficiency-zero theorem.

#### `deficiency_eq`

- **`CRNT.Network.Isomorphism.deficiency_eq`** — `CRNT.Basic.Isomorphism`:349 (`theorem`)
  ```lean
  theorem deficiency_eq (F : N.Isomorphism M) : N.deficiency = M.deficiency
  ```
  > Deficiency is invariant under network isomorphism.
- **`CRNT.Examples.DeficiencyBookkeeping.deficiency_eq`** — `CRNT.Examples.DeficiencyBookkeeping`:17 (`theorem`)
  ```lean
  theorem deficiency_eq : N.deficiency = 0
  ```
  > The natural-number deficiency of `A ⇌ B` is zero.

#### `doorCount`

- **`CRNT.Analysis.Sperner2D.doorCount`** — `CRNT.Analysis.Sperner2D`:69 (`def`)
  ```lean
  def doorCount (a b c : Color) : ℕ
  ```
  > The number of `{0, 1}`-doors among a triangle's three edges `{a,b}`, `{b,c}`, `{a,c}`.
- **`CRNT.Analysis.SpernerN.doorCount`** — `CRNT.Analysis.SpernerNParity`:44 (`def`)
  ```lean
  def doorCount (c : Fin (n + 1) → Fin (n + 1)) : ℕ
  ```
  > The number of facets of a colored cell carrying exactly the door colors.

#### `doorCount_odd_iff`

- **`CRNT.Analysis.Sperner2D.doorCount_odd_iff`** — `CRNT.Analysis.Sperner2D`:79 (`theorem`)
  ```lean
  theorem doorCount_odd_iff (a b c : Color) : Odd (doorCount a b c) ↔ isRainbow a b c
  ```
  > **Local door-count parity.** A triangle with vertex colors `a b c` has an odd number of `{0, 1}`-doors among its three edges iff it is rainbow. Proved by finite case analysis over the `27` color tripl
- **`CRNT.Analysis.SpernerN.doorCount_odd_iff`** — `CRNT.Analysis.SpernerNParity`:180 (`theorem`)
  ```lean
  theorem doorCount_odd_iff (c : Fin (n + 1) → Fin (n + 1)) : Odd (doorCount c) ↔ Function.Bijective c
  ```
  > **Local door-count parity.** A colored cell has an odd number of door facets exactly when it is fully labeled (its vertex coloring is a bijection).

#### `doorRel`

- **`CRNT.Analysis.SpernerGrid.doorRel`** — `CRNT.Analysis.SpernerGrid`:85 (`def`)
  ```lean
  def doorRel : Option Cell → Option Cell → Prop
  ```
  > The door relation on `Option Cell`: the outer region `none` and the cell `some Cell.tri` form a single door.
- **`CRNT.Analysis.SpernerN2.doorRel`** — `CRNT.Analysis.SpernerGridMulti`:85 (`def`)
  ```lean
  def doorRel : (Cell ⊕ Outer) → (Cell ⊕ Outer) → Prop
  ```
  > The door relation: the interior door `up1 — dn` (shared edge `mAB–mAC`) and the boundary door `up1 — Outer.boundary` (edge `A–mAB`). `SimpleGraph.fromRel` symmetrizes and removes self-loops.

#### `edge_reaction_of_even`

- **`CRNT.Network.TrueSRPath.edge_reaction_of_even`** — `CRNT.Multistationarity.TrueSRPathAccessors`:67 (`theorem`)
  ```lean
  theorem edge_reaction_of_even (P : N.TrueSRPath L) (q : Fin L) (hq : q.1 % 2 = 0) : (P.edge q).reaction = (P.reactionAt q.succ (by have : (q.succ).1 = q.1 + 1 := rfl omega)).1
  ```
  > An edge at an even position ends at the next position's reaction.
- **`CRNT.Network.TrueSRSSPath.edge_reaction_of_even`** — `CRNT.Multistationarity.TrueSRSpeciesPath`:183 (`theorem`)
  ```lean
  theorem edge_reaction_of_even (P : N.TrueSRSSPath L) (q : Fin L) (hq : q.1 % 2 = 0) : (P.edge q).reaction = (P.reactionAt ⟨q.1 + 1, by have := q.isLt; omega⟩ (by show (q.1 + 1) % 2 ≠ 0; omega)).1
  ```
  > An even-position edge carries the reaction at the next position.

#### `edge_reaction_of_odd`

- **`CRNT.Network.TrueSRPath.edge_reaction_of_odd`** — `CRNT.Multistationarity.TrueSRPathAccessors`:82 (`theorem`)
  ```lean
  theorem edge_reaction_of_odd (P : N.TrueSRPath L) (q : Fin L) (hq : q.1 % 2 ≠ 0) : (P.edge q).reaction = (P.reactionAt (Fin.castSucc q) (by simpa using hq)).1
  ```
  > An edge at an odd position starts at that position's reaction.
- **`CRNT.Network.TrueSRSSPath.edge_reaction_of_odd`** — `CRNT.Multistationarity.TrueSRSpeciesPath`:197 (`theorem`)
  ```lean
  theorem edge_reaction_of_odd (P : N.TrueSRSSPath L) (q : Fin L) (hq : q.1 % 2 ≠ 0) : (P.edge q).reaction = (P.reactionAt ⟨q.1, by have := q.isLt; omega⟩ hq).1
  ```
  > An odd-position edge carries the reaction at its own position.

#### `edge_species_of_even`

- **`CRNT.Network.TrueSRPath.edge_species_of_even`** — `CRNT.Multistationarity.TrueSRPathAccessors`:57 (`theorem`)
  ```lean
  theorem edge_species_of_even (P : N.TrueSRPath L) (q : Fin L) (hq : q.1 % 2 = 0) : (P.edge q).species = P.speciesAt (Fin.castSucc q) (by simpa using hq)
  ```
  > An edge at an even position starts at that position's species.
- **`CRNT.Network.TrueSRSSPath.edge_species_of_even`** — `CRNT.Multistationarity.TrueSRSpeciesPath`:171 (`theorem`)
  ```lean
  theorem edge_species_of_even (P : N.TrueSRSSPath L) (q : Fin L) (hq : q.1 % 2 = 0) : (P.edge q).species = P.speciesAt ⟨q.1,
  ```
  > An even-position edge carries the species at its own position.

#### `edge_species_of_odd`

- **`CRNT.Network.TrueSRPath.edge_species_of_odd`** — `CRNT.Multistationarity.TrueSRPathAccessors`:92 (`theorem`)
  ```lean
  theorem edge_species_of_odd (P : N.TrueSRPath L) (q : Fin L) (hq : q.1 % 2 ≠ 0) : (P.edge q).species = P.speciesAt q.succ (by have : (q.succ).1 = q.1 + 1 := rfl omega)
  ```
  > An edge at an odd position ends at the next position's species.
- **`CRNT.Network.TrueSRSSPath.edge_species_of_odd`** — `CRNT.Multistationarity.TrueSRSpeciesPath`:209 (`theorem`)
  ```lean
  theorem edge_species_of_odd (P : N.TrueSRSSPath L) (q : Fin L) (hq : q.1 % 2 ≠ 0) : (P.edge q).species = P.speciesAt ⟨q.1 + 1,
  ```
  > An odd-position edge carries the species at the next position.

#### `exists_color_index`

- **`CRNT.Analysis.SpernerLattice.exists_color_index`** — `CRNT.Analysis.SpernerBrouwer2D`:38 (`theorem`)
  ```lean
  theorem exists_color_index (hN : 0 < N) (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (p : Pt N) : ∃ i : Fin 3, 0 < realize p i ∧ (f (realizePt hN p) : Fin 3 → ℝ) i ≤ realize p i
  ```
  > **There is a coordinate `f` does not increase, that is positive at `p`.** Both `realize p` and `f (realizePt hN p)` are simplex points (coordinates sum to `1`), so some coordinate that is positive at 
- **`CRNT.Analysis.SpernerN.exists_color_index`** — `CRNT.Analysis.SpernerBrouwerN`:38 (`theorem`)
  ```lean
  theorem exists_color_index (hN : 0 < N) (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1)))) (p : Pt n N) : ∃ i : Fin (n + 1), 0 < realize p i ∧ (f (realizePt hN p) : Fin (n + 1) → ℝ) i ≤ realize p i
  ```
  > **There is a coordinate `f` does not increase, that is positive at `p`.** Both `realize p` and `f (realizePt hN p)` are simplex points (coordinates sum to `1`), so some coordinate that is positive at 

#### `exists_linkage_scalars_of_complexBalanced`

- **`CRNT.Network.GeneralizedMassActionData.exists_linkage_scalars_of_complexBalanced`** — `CRNT.Equilibria.GeneralizedTreeConstantCriterion`:129 (`theorem`)
  ```lean
  theorem exists_linkage_scalars_of_complexBalanced (G : N.GeneralizedMassActionData) (κ : N.RateConstants) (hwr : N.WeaklyReversible) {x : Concentration S} (hcb : G.IsComplexBalanced κ x) : ∃ a : Quotient N.linkedSetoid →
  ```
  > Linkage-class scalar parametrization of a generalized CBE kinetic-monomial vector.
- **`CRNT.Network.exists_linkage_scalars_of_complexBalanced`** — `CRNT.Equilibria.TreeConstantCriterion`:85 (`theorem`)
  ```lean
  theorem exists_linkage_scalars_of_complexBalanced (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible) {x : Concentration S} (hx : x.Positive) (hcb : N.IsComplexBalanced κ x) : ∃ a : Quotient N.linkedSetoid →
  ```
  > Classwise scalar parametrization of a positive complex-balanced monomial vector by its tree constants.

#### `finrank_complexBalancedTangentSpace`

- **`CRNT.Network.finrank_complexBalancedTangentSpace`** — `CRNT.Equilibria.ComplexBalanceGeometry`:101 (`theorem`)
  ```lean
  theorem finrank_complexBalancedTangentSpace (N : Network S) {x : Concentration S} (hx : x.Positive) : Module.finrank ℝ (N.complexBalancedTangentSpace x) = Fintype.card S - N.stoichRank
  ```
  > Dimension of the CBE tangent space equals the number of independent conservation laws, `|S|-s`.
- **`CRNT.Network.GeneralizedMassActionData.finrank_complexBalancedTangentSpace`** — `CRNT.Equilibria.GeneralizedComplexBalanceGeometry`:32 (`theorem`)
  ```lean
  theorem finrank_complexBalancedTangentSpace (G : N.GeneralizedMassActionData) {x : Concentration S} (hx : x.Positive) : Module.finrank ℝ (G.complexBalancedTangentSpace x) = Fintype.card S - G.kineticOrderRank
  ```
  > The generalized CBE manifold has codimension equal to the kinetic-order rank.

#### `forget`

- **`CRNT.Network.LabeledSubnetwork.forget`** — `CRNT.Design.LabeledBufferingStructure`:43 (`def`)
  ```lean
  def forget (L : LabeledSubnetwork N P) : StructuralSubnetwork N
  ```
  > Forget labels and completion provenance.
- **`CRNT.Planar.CanonicalMinimalRecurrentSectionData.forget`** — `CRNT.Oscillation.PlanarCanonicalReturn`:57 (`def`)
  ```lean
  def forget (R : CanonicalMinimalRecurrentSectionData M) : MinimalRecurrentSectionData M
  ```
  > Forgetting canonicality recovers exactly the minimal recurrent-section data already consumed by the Poincare--Bendixson closure theorem.

#### `inflow`

- **`CRNT.Network.inflow`** — `CRNT.Equilibria.ComplexBalanced`:21 (`def`)
  ```lean
  def inflow (N : Network S) (κ : RateConstants N) (x : Concentration S) (c : Complex S) : ℝ
  ```
  > The total mass-action flow into complex `c`: the sum of rates of reactions whose target is `c`.
- **`CRNT.Network.GeneralizedMassActionData.inflow`** — `CRNT.Kinetics.GeneralizedNetwork`:262 (`def`)
  ```lean
  noncomputable def inflow (G : N.GeneralizedMassActionData) (κ : N.RateConstants) (x : Concentration S) (c : N.ComplexIdx) : ℝ
  ```
  > Generalized inflow into a stoichiometric complex.

#### `linearEquiv`

- **`CRNT.Planar.CanonicalFlowBoxRegularity.linearEquiv`** — `CRNT.Oscillation.PlanarFlowBox`:114 (`def`)
  ```lean
  noncomputable def linearEquiv (R : CanonicalFlowBoxRegularity D q) (hne : field q ≠ 0) : Phase2 ≃L[ℝ] Phase2
  ```
  > The derivative bundled as a continuous linear equivalence.
- **`CRNT.Network.PositiveDiagonalChange.linearEquiv`** — `CRNT.Translation.LinearConjugacy`:52 (`def`)
  ```lean
  noncomputable def linearEquiv (D : PositiveDiagonalChange S) : (S → ℝ) ≃ₗ[ℝ] (S → ℝ)
  ```
  > Associated linear automorphism.

#### `manifold`

- **`ODE.CenterManifoldData.manifold`** — `CRNT.Dynamics.CenterManifold`:143 (`def`)
  ```lean
  noncomputable def manifold : Ec →ᵇ Eh
  ```
  > **The local center manifold `h`.** The unique fixed-point section of the center-manifold Lyapunov–Perron operator, furnished by the Banach fixed-point theorem on the complete space of bounded sections
- **`ODE.GraphTransformData.manifold`** — `CRNT.Dynamics.GraphTransform`:116 (`def`)
  ```lean
  noncomputable def manifold : Y →ᵇ E
  ```
  > **The perturbed invariant manifold `M_ε`.** The unique fixed-point section of the graph transform, furnished by the Banach fixed-point theorem (`ContractingWith.fixedPoint`) on `Y →ᵇ E`. Its graph is 

#### `manifoldMap_slowDrift_velocity_le`

- **`ODE.SlowManifoldC1Seed.manifoldMap_slowDrift_velocity_le`** — `CRNT.Dynamics.FenichelC1Manifold`:177 (`theorem`)
  ```lean
  theorem manifoldMap_slowDrift_velocity_le {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y') {y : ℝ → Y} (hy : ∀ t t', dist (y t) (y t') ≤ ε * |t - t'|) {y' : ℝ → Y} {t₀ : ℝ
  ```
  > **The slaved slow-manifold curve's velocity is `O(ε)`, with differentiability derived.** When the fast field is jointly `C¹` with invertible fibre derivative (so `manifoldMap` is `C¹`) and the slow pa
- **`ODE.SlowManifoldSeed.manifoldMap_slowDrift_velocity_le`** — `CRNT.Dynamics.FenichelSlowDrift`:147 (`theorem`)
  ```lean
  theorem manifoldMap_slowDrift_velocity_le {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y') {y : ℝ → Y} (hy : ∀ t t', dist (y t) (y t') ≤ ε * |t - t'|) {γᵣ' : ℝ → E} (t₀ : 
  ```
  > **The slaved slow-manifold curve's velocity is `O(ε)`.** If the constructed manifold curve `t ↦ manifoldMap (y t)` is differentiable at `t₀`, the converse mean-value inequality (`HasDerivAt.le_of_lip'

#### `manifold_isFixedPt`

- **`ODE.CenterManifoldData.manifold_isFixedPt`** — `CRNT.Dynamics.CenterManifold`:149 (`theorem`)
  ```lean
  theorem manifold_isFixedPt : M.op M.manifold = M.manifold
  ```
  > **Defining invariance of the center manifold.** The graph map `h` is a fixed point of the Lyapunov–Perron operator: `op h = h`. The fixed sections of the operator are exactly the locally invariant gra
- **`ODE.GraphTransformData.manifold_isFixedPt`** — `CRNT.Dynamics.GraphTransform`:120 (`theorem`)
  ```lean
  theorem manifold_isFixedPt : G.op G.manifold = G.manifold
  ```
  > The perturbed manifold section is a fixed point of the graph transform: `op M_ε = M_ε`.

#### `manifold_unique`

- **`ODE.CenterManifoldData.manifold_unique`** — `CRNT.Dynamics.CenterManifold`:154 (`theorem`)
  ```lean
  theorem manifold_unique {σ : Ec →ᵇ Eh} (hσ : M.op σ = σ) : σ = M.manifold
  ```
  > **Local uniqueness of the center manifold.** Any fixed-point section of the Lyapunov–Perron operator equals the constructed graph `h`; the local center manifold is unique.
- **`ODE.GraphTransformData.manifold_unique`** — `CRNT.Dynamics.GraphTransform`:125 (`theorem`)
  ```lean
  theorem manifold_unique {σ : Y →ᵇ E} (hσ : G.op σ = σ) : σ = G.manifold
  ```
  > **Uniqueness of the perturbed manifold.** Any fixed-point section of the graph transform equals the constructed `manifold`; the persisted manifold is unique.

#### `mem_positiveComplexBalancedSet_iff_toric`

- **`CRNT.Network.mem_positiveComplexBalancedSet_iff_toric`** — `CRNT.Equilibria.ComplexBalanceGeometry`:61 (`theorem`)
  ```lean
  theorem mem_positiveComplexBalancedSet_iff_toric (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible) {xstar : Concentration S} (hxs : xstar.Positive) (hcbs : N.IsComplexBalanced κ xstar) (x : Concentration S
  ```
  > **Global Horn--Jackson toric characterization.**
- **`CRNT.Network.GeneralizedMassActionData.mem_positiveComplexBalancedSet_iff_toric`** — `CRNT.Equilibria.GeneralizedComplexBalanceGeometry`:52 (`theorem`)
  ```lean
  theorem mem_positiveComplexBalancedSet_iff_toric (G : N.GeneralizedMassActionData) (κ : N.RateConstants) (hwr : N.WeaklyReversible) {xstar : Concentration S} (hxs : xstar.Positive) (hcbs : G.IsComplexBalanced κ xstar) (x
  ```
  > Global toric characterization of positive generalized CBEs.

#### `outflow`

- **`CRNT.Network.outflow`** — `CRNT.Equilibria.ComplexBalanced`:27 (`def`)
  ```lean
  def outflow (N : Network S) (κ : RateConstants N) (x : Concentration S) (c : Complex S) : ℝ
  ```
  > The total mass-action flow out of complex `c`: the sum of rates of reactions whose source is `c`.
- **`CRNT.Network.GeneralizedMassActionData.outflow`** — `CRNT.Kinetics.GeneralizedNetwork`:267 (`def`)
  ```lean
  noncomputable def outflow (G : N.GeneralizedMassActionData) (κ : N.RateConstants) (x : Concentration S) (c : N.ComplexIdx) : ℝ
  ```
  > Generalized outflow from a stoichiometric complex.

#### `periodicTrajectory`

- **`CRNT.Planar.RecurrentSectionData.periodicTrajectory`** — `CRNT.Oscillation.PlanarRecurrentSection`:48 (`theorem`)
  ```lean
  theorem periodicTrajectory (R : RecurrentSectionData D) : ∃ P : PeriodicTrajectory field, True
  ```
  > Witness-producing version, retaining that the periodic orbit is generated by the recurrent xsection.
- **`CRNT.TransversalSection.ReturnIntervalData.periodicTrajectory`** — `CRNT.Oscillation.ReturnInterval`:82 (`theorem`)
  ```lean
  theorem periodicTrajectory (D : S.ReturnIntervalData) : ∃ P : PeriodicTrajectory S.field, True
  ```
  > Witness-producing form of `exists_periodicTrajectory`.

#### `realize`

- **`CRNT.Analysis.SpernerLattice.realize`** — `CRNT.Analysis.SpernerLatticeGeometric`:24 (`def`)
  ```lean
  noncomputable def realize (p : Pt N) : Fin 3 → ℝ
  ```
  > The barycentric realization of a lattice point `(i, j)` as the simplex coordinates `(i/N, j/N, (N-i-j)/N)`.
- **`CRNT.Analysis.SpernerN.realize`** — `CRNT.Analysis.SpernerLatticeN`:51 (`def`)
  ```lean
  noncomputable def realize (p : Pt n N) : Fin (n + 1) → ℝ
  ```
  > The barycentric **realization** of a lattice point into `Fin (n+1) → ℝ`: `x ↦ (x i / N)`.

#### `realizePt`

- **`CRNT.Analysis.SpernerLattice.realizePt`** — `CRNT.Analysis.SpernerBrouwer2D`:29 (`def`)
  ```lean
  noncomputable def realizePt (hN : 0 < N) (p : Pt N) : ↥(stdSimplex ℝ (Fin 3))
  ```
  > The simplex point realizing a lattice point.
- **`CRNT.Analysis.SpernerN.realizePt`** — `CRNT.Analysis.SpernerBrouwerN`:29 (`def`)
  ```lean
  noncomputable def realizePt (hN : 0 < N) (p : Pt n N) : ↥(stdSimplex ℝ (Fin (n + 1)))
  ```
  > The simplex point realizing a lattice point.

#### `realizePt_coe`

- **`CRNT.Analysis.SpernerLattice.realizePt_coe`** — `CRNT.Analysis.SpernerBrouwer2D`:32 (`theorem`)
  ```lean
  @[simp] theorem realizePt_coe (hN : 0 < N) (p : Pt N) : (realizePt hN p : Fin 3 → ℝ) = realize p
  ```
  > The simplex point realizing a lattice point.
- **`CRNT.Analysis.SpernerN.realizePt_coe`** — `CRNT.Analysis.SpernerBrouwerN`:32 (`theorem`)
  ```lean
  @[simp] theorem realizePt_coe (hN : 0 < N) (p : Pt n N) : (realizePt hN p : Fin (n + 1) → ℝ) = realize p
  ```
  > The simplex point realizing a lattice point.

#### `realize_dist_le`

- **`CRNT.Analysis.SpernerLattice.realize_dist_le`** — `CRNT.Analysis.SpernerLatticeGeometric`:56 (`theorem`)
  ```lean
  theorem realize_dist_le (hN : 0 < N) (p q : Pt N) (hi : |(p.1.1 : ℝ) - q.1.1| ≤ 1) (hj : |(p.1.2 : ℝ) - q.1.2| ≤ 1) : dist (realize p) (realize q) ≤ 2 / N
  ```
  > **Mesh bound.** Lattice points whose coordinates each differ by at most `1` realize within sup-distance `2/N`.
- **`CRNT.Analysis.SpernerN.realize_dist_le`** — `CRNT.Analysis.SpernerNGeometric`:27 (`theorem`)
  ```lean
  theorem realize_dist_le (hN : 0 < N) (p q : Pt n N) (h : ∀ i, |(p.1 i : ℝ) - q.1 i| ≤ 1) : dist (realize p) (realize q) ≤ 1 / N
  ```
  > **Mesh bound from coordinate bounds.** Lattice points whose barycentric coordinates each differ by at most `1` realize within sup-distance `1/N`.

#### `realize_mem_stdSimplex`

- **`CRNT.Analysis.SpernerLattice.realize_mem_stdSimplex`** — `CRNT.Analysis.SpernerLatticeGeometric`:39 (`theorem`)
  ```lean
  theorem realize_mem_stdSimplex (hN : 0 < N) (p : Pt N) : realize p ∈ stdSimplex ℝ (Fin 3)
  ```
  > **The realization lands in the standard 2-simplex.**
- **`CRNT.Analysis.SpernerN.realize_mem_stdSimplex`** — `CRNT.Analysis.SpernerLatticeN`:57 (`theorem`)
  ```lean
  theorem realize_mem_stdSimplex (hN : 0 < N) (p : Pt n N) : realize p ∈ stdSimplex ℝ (Fin (n + 1))
  ```
  > **The realization lands in the standard `n`-simplex.**

#### `restrict`

- **`CRNT.Network.IndexedChildSelection.restrict`** — `CRNT.Oscillation.ChildSelectionSearch`:132 (`def`)
  ```lean
  def restrict (C : N.IndexedChildSelection I) (J : Finset I) : N.IndexedChildSelection {i : I // i ∈ J}
  ```
  > Restrict an indexed child selection to a finite subset of its selected indices.
- **`CRNT.Complex.restrict`** — `CRNT.Subnetwork.EmbeddedNetwork`:24 (`def`)
  ```lean
  def restrict (V : Finset S) (y : Complex S) : Complex {s : S // s ∈ V}
  ```
  > Restriction of a complex to a finite species subset.

#### `satisfiesTreeConstantBinomials_of_complexBalanced`

- **`CRNT.Network.GeneralizedMassActionData.satisfiesTreeConstantBinomials_of_complexBalanced`** — `CRNT.Equilibria.GeneralizedTreeConstantCriterion`:62 (`theorem`)
  ```lean
  theorem satisfiesTreeConstantBinomials_of_complexBalanced (G : N.GeneralizedMassActionData) (κ : N.RateConstants) (hwr : N.WeaklyReversible) {x : Concentration S} (hcb : G.IsComplexBalanced κ x) : G.SatisfiesTreeConstant
  ```
  > Generalized complex balance implies the tree-constant binomials.
- **`CRNT.Network.satisfiesTreeConstantBinomials_of_complexBalanced`** — `CRNT.Equilibria.TreeConstantCriterion`:34 (`theorem`)
  ```lean
  theorem satisfiesTreeConstantBinomials_of_complexBalanced (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible) {x : Concentration S} (hx : x.Positive) (hcb : N.IsComplexBalanced κ x) : N.SatisfiesTreeConstant
  ```
  > Complex balance implies all tree-constant binomials.

#### `self`

- **`CRNT.Network.MassActionRealization.self`** — `CRNT.Translation.DynamicalEquivalence`:85 (`def`)
  ```lean
  def self (N : Network S) (κN : RateConstants N) : MassActionRealization N κN
  ```
  > The original network is itself a realization.
- **`CRNT.Network.StoichiometricMassActionRealization.self`** — `Scaffold.CRNTExpansion.RealizationTheory`:57 (`def`)
  ```lean
  def self (N : Network S) (κN : N.RateConstants) : StoichiometricMassActionRealization N κN
  ```
  > The original system is its own stoichiometric realization.

#### `species_iff_even`

- **`CRNT.Network.TrueSRPath.species_iff_even`** — `CRNT.Multistationarity.TrueSRPath`:86 (`theorem`)
  ```lean
  theorem species_iff_even (P : N.TrueSRPath L) : ∀ k : ℕ, ∀ hk : k ≤ L, (∃ s : S, P.vertex ⟨k, by omega⟩ = Sum.inl s) ↔ Even k
  ```
  > **Alternation.** A path's position `k` carries a species vertex exactly when `k` is even.
- **`CRNT.Network.TrueSRSSPath.species_iff_even`** — `CRNT.Multistationarity.TrueSRSpeciesPath`:120 (`theorem`)
  ```lean
  theorem species_iff_even (P : N.TrueSRSSPath L) (m : ℕ) (hm : m ≤ L) : (∃ x : S, P.vertex ⟨m, by omega⟩ = Sum.inl x) ↔ Even m
  ```
  > A vertex of a species-to-species path is a species vertex exactly at even positions. Inherited from `TrueSRPath.species_iff_even` through `toPath` below the last position, and from `ends_at_species` t

#### `spernerColoringOf`

- **`CRNT.Analysis.SpernerLattice.spernerColoringOf`** — `CRNT.Analysis.SpernerBrouwer2D`:82 (`def`)
  ```lean
  noncomputable def spernerColoringOf (hN : 0 < N) (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) : SpernerColoring N
  ```
  > **The Sperner colouring induced by a continuous self-map.**
- **`CRNT.Analysis.SpernerN.spernerColoringOf`** — `CRNT.Analysis.SpernerBrouwerN`:83 (`def`)
  ```lean
  noncomputable def spernerColoringOf (hN : 0 < N) (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1)))) : SpernerColoring n N
  ```
  > **The Sperner coloring induced by a continuous self-map.**

#### `spernerColoringOf_color`

- **`CRNT.Analysis.SpernerLattice.spernerColoringOf_color`** — `CRNT.Analysis.SpernerBrouwer2D`:107 (`theorem`)
  ```lean
  @[simp] theorem spernerColoringOf_color (hN : 0 < N) (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (p : Pt N) : (spernerColoringOf hN f).color p = colorOf hN f p
  ```
  > **The Sperner colouring induced by a continuous self-map.**
- **`CRNT.Analysis.SpernerN.spernerColoringOf_color`** — `CRNT.Analysis.SpernerBrouwerN`:94 (`theorem`)
  ```lean
  @[simp] theorem spernerColoringOf_color (hN : 0 < N) (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1)))) (p : Pt n N) : (spernerColoringOf hN f).color p = colorOf hN f p
  ```
  > **The Sperner coloring induced by a continuous self-map.**

#### `sperner_exists_rainbow`

- **`CRNT.Analysis.Sperner.sperner_exists_rainbow`** — `CRNT.Analysis.Sperner`:110 (`theorem`)
  ```lean
  theorem sperner_exists_rainbow {n : ℕ} {c : ℕ → Bool} (h : IsSpernerColoring n c) : ∃ i < n, c (i + 1) ≠ c i
  ```
  > **Existence of a rainbow edge.** A Sperner-colored triangulated segment contains an edge `{i, i+1}` whose endpoints receive opposite colors.
- **`CRNT.Analysis.SpernerN.sperner_exists_rainbow`** — `CRNT.Analysis.SpernerNClose`:563 (`theorem`)
  ```lean
  theorem sperner_exists_rainbow {m N : ℕ} (col : SpernerColoring m N) (hN : 0 < N) : ∃ c : Cell m N, IsRainbowCell col c
  ```
  > **The n-dimensional Sperner lemma.** Every Sperner coloring of the `n`-simplex has a rainbow cell — one whose `n+1` vertices realize all `n+1` colors.

#### `ssGlueCycle_numCPairs`

- **`CRNT.Network.ssGlueCycle_numCPairs`** — `CRNT.Multistationarity.TrueChemistrySRCriterion`:7852 (`theorem`)
  ```lean
  private theorem ssGlueCycle_numCPairs {N : Network S} {i j : ℕ} (P : N.TrueSRSSPath (2 * j + 2)) (Q : N.TrueSRSSPath (2 * i + 2)) (h : TrueSRSSPath.SSGluable P Q) : (TrueSRSSPath.ssGlueCycle P Q h).numCPairs = ssPathCPai
  ```
  > The glued cycle from two species-to-species paths has exactly the c-pairs internal to those paths. There is no extra c-pair at either shared species endpoint.
- **`CRNT.Network.TrueSRSSPath.ssGlueCycle_numCPairs`** — `CRNT.Multistationarity.TrueSRSSGlueCPairs`:107 (`theorem`)
  ```lean
  theorem ssGlueCycle_numCPairs : (ssGlueCycle P Q h).numCPairs = ssNumCPairs P + ssNumCPairs Q
  ```
  > **The species-to-species glue count has no seam term.**

#### `stoichCompatible_iff`

- **`CRNT.Network.Isomorphism.stoichCompatible_iff`** — `CRNT.Basic.IsomorphismKinetics`:127 (`theorem`)
  ```lean
  theorem stoichCompatible_iff (F : N.Isomorphism M) (x y : Concentration S) : N.StoichCompatible x y ↔ M.StoichCompatible (F.mapConcentration x) (F.mapConcentration y)
  ```
  > Stoichiometric compatibility is preserved by network isomorphism.
- **`CRNT.Network.StoichiometricMassActionRealization.stoichCompatible_iff`** — `Scaffold.CRNTExpansion.RealizationTheory`:103 (`theorem`)
  ```lean
  theorem stoichCompatible_iff (R : StoichiometricMassActionRealization N κN) (x y : Concentration S) : N.StoichCompatible x y <-> R.network.StoichCompatible x y
  ```
  > Equality of stoichiometric subspaces identifies compatibility.

#### `support`

- **`CRNT.Complex.support`** — `CRNT.Basic.Complex`:42 (`def`)
  ```lean
  def support [Fintype S] [DecidableEq S] (c : Complex S) : Finset S
  ```
  > The species occurring in a complex with nonzero coefficient.
- **`CRNT.support`** — `CRNT.LinearAlgebra.ConformalDecomposition`:45 (`def`)
  ```lean
  noncomputable def support (v : ι → ℝ) : Finset ι
  ```
  > The **support** of a real vector: the finite set of coordinates where it is nonzero.

#### `tail_vertex`

- **`CRNT.RelPath.tail_vertex`** — `CRNT.Graph.RelPath`:94 (`theorem`)
  ```lean
  @[simp] theorem tail_vertex (P : RelPath E T k) (m : ℕ) (hm : m ≤ k) (i : Fin (k - m + 1)) : (P.tail m hm).vertex i = P.vertex ⟨m + i.1,
  ```
  > The initial segment of a directed walk, up to position `m`.
- **`CRNT.Network.TrueSRPathRR.tail_vertex`** — `CRNT.Multistationarity.TrueSRParityRR`:126 (`theorem`)
  ```lean
  theorem tail_vertex (A : N.TrueSRPathRR j) (k : Fin (2 * j + 2)) : A.tail.vertex k = A.vertexAt ⟨k.1 + 1,
  ```
  > The tail's vertex at position `k` sits at position `k + 1` of the path.

#### `toPath_edge`

- **`CRNT.Network.TrueSREdge.toPath_edge`** — `CRNT.Multistationarity.TrueSREdgePath`:38 (`theorem`)
  ```lean
  @[simp] theorem toPath_edge (e : N.TrueSREdge) (q : Fin 1) : (toPath e).edge q = e
  ```
  > A single true-SR edge, read as a species-to-reaction path of length one.
- **`CRNT.Network.TrueSRSSPath.toPath_edge`** — `CRNT.Multistationarity.TrueSRSpeciesPath`:101 (`theorem`)
  ```lean
  @[simp] theorem toPath_edge (P : N.TrueSRSSPath L) (q : Fin (L - 1)) : P.toPath.edge q = P.edge ⟨q.1,
  ```
  > Dropping the last edge of a species-to-species path leaves a species-to-reaction path.

#### `toPath_endReaction`

- **`CRNT.Network.TrueSREdge.toPath_endReaction`** — `CRNT.Multistationarity.TrueSREdgePath`:46 (`theorem`)
  ```lean
  theorem toPath_endReaction (e : N.TrueSREdge) : (toPath e).endReaction = ⟨e.reaction, e.internal⟩
  ```
  > A single true-SR edge, read as a species-to-reaction path of length one.
- **`CRNT.Network.TrueSRSSPath.toPath_endReaction`** — `CRNT.Multistationarity.TrueSRSpeciesPath`:349 (`theorem`)
  ```lean
  theorem toPath_endReaction (P : N.TrueSRSSPath L) : P.toPath.endReaction = P.reactionAt ⟨L - 1,
  ```

#### `toPath_startSpecies`

- **`CRNT.Network.TrueSREdge.toPath_startSpecies`** — `CRNT.Multistationarity.TrueSREdgePath`:40 (`theorem`)
  ```lean
  theorem toPath_startSpecies (e : N.TrueSREdge) : (toPath e).startSpecies = e.species
  ```
  > A single true-SR edge, read as a species-to-reaction path of length one.
- **`CRNT.Network.TrueSRSSPath.toPath_startSpecies`** — `CRNT.Multistationarity.TrueSRSpeciesPath`:339 (`theorem`)
  ```lean
  theorem toPath_startSpecies (P : N.TrueSRSSPath L) : P.toPath.startSpecies = P.speciesAt ⟨0,
  ```

#### `triVerts`

- **`CRNT.Analysis.SpernerN2Geo.triVerts`** — `CRNT.Analysis.SpernerGridGeometric`:104 (`def`)
  ```lean
  def triVerts (t : Cell) : Finset Vertex
  ```
  > Each triangle as its set of three vertices.
- **`CRNT.Analysis.SpernerLattice.triVerts`** — `CRNT.Analysis.SpernerLattice`:107 (`def`)
  ```lean
  def triVerts {N : ℕ} (c : Cell N) : Finset (Pt N)
  ```
  > The three vertices of a triangle.

#### `vectorField`

- **`CRNT.Network.Kinetics.vectorField`** — `CRNT.Kinetics.General`:58 (`def`)
  ```lean
  def vectorField (K : Kinetics N) (x : Concentration S) : S → ℝ
  ```
  > The vector field induced by a kinetics: for each species, the net rate of change is the sum over reactions of the rate times the species' entry in the reaction vector. This is the right-hand side of t
- **`CRNT.Network.GeneralizedMassActionData.vectorField`** — `CRNT.Kinetics.GeneralizedNetwork`:252 (`def`)
  ```lean
  noncomputable def vectorField (G : N.GeneralizedMassActionData) (κ : N.RateConstants) (x : Concentration S) : S → ℝ
  ```
  > Generalized mass-action vector field.

#### `vertex_last`

- **`CRNT.Analysis.SpernerN.vertex_last`** — `CRNT.Analysis.SpernerNBoundaryCorr`:58 (`theorem`)
  ```lean
  theorem vertex_last (c : Cell (n + 1) N) (k : Fin (n + 2)) : ((c.vertex k).1 (Fin.last (n + 1)) : ℤ) = (c.base (Fin.last (n + 1)) : ℤ) + if ((c.perm⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ) < (k : ℕ) then -1 else 0
  ```
  > The last coordinate of a cell vertex: `base_(last) + (−1 if the d_(last) step has been taken)`.
- **`CRNT.Network.TrueSRPath.vertex_last`** — `CRNT.Multistationarity.TrueSRGlueInterface`:41 (`theorem`)
  ```lean
  theorem vertex_last (P : N.TrueSRPath L) : P.vertex (Fin.last L) = Sum.inr P.endReaction
  ```
  > The reaction vertex a path ends at.

#### `vertex_zero`

- **`CRNT.Analysis.SpernerN.vertex_zero`** — `CRNT.Analysis.SpernerNIncidence`:148 (`theorem`)
  ```lean
  theorem vertex_zero (c : Cell n N) (i : Fin (n + 1)) : (c.vertex 0).1 i = c.base i
  ```
  > The `0`-th vertex's coordinates equal the base.
- **`CRNT.Network.TrueSRPath.vertex_zero`** — `CRNT.Multistationarity.TrueSRGlueInterface`:33 (`theorem`)
  ```lean
  theorem vertex_zero (P : N.TrueSRPath L) : P.vertex 0 = Sum.inl P.startSpecies
  ```
  > The species vertex a path starts at.

#### `weaklyReversible_iff`

- **`CRNT.Network.Isomorphism.weaklyReversible_iff`** — `CRNT.Basic.Isomorphism`:364 (`theorem`)
  ```lean
  theorem weaklyReversible_iff (F : N.Isomorphism M) : N.WeaklyReversible ↔ M.WeaklyReversible
  ```
  > Weak reversibility is invariant.
- **`CRNT.Network.weaklyReversible_iff`** — `CRNT.Graph.WeakReversibility`:29 (`theorem`)
  ```lean
  theorem weaklyReversible_iff (N : Network S) : N.WeaklyReversible ↔ ∀ r : N.R, N.Reaches (N.reaction r).target (N.reaction r).source
  ```
  > To prove weak reversibility it suffices to exhibit, for each reaction, a return path from its target to its source.

#### `zero`

- **`CRNT.Complex.zero`** — `CRNT.Basic.Complex`:30 (`def`)
  ```lean
  def zero : Complex S
  ```
  > The zero complex, written `0` in informal chemistry. It is the source/target of inflow, outflow, and degradation reactions.
- **`Polynomial.CoeffNonneg.zero`** — `CRNT.Oscillation.HalfPlanePolynomial`:33 (`theorem`)
  ```lean
  @[simp] theorem zero : CoeffNonneg (0 : Polynomial ℝ)
  ```
  > Every coefficient of a real polynomial is nonnegative.

### Same short name, same type (harmless restatements)

These are the same statement in two namespaces. They are not mathematical
collisions, but they do inflate counts and they are what `decl_index.py dups`
surfaces.

| short name | declarations |
|---|---|
| `HasNegativeFeedbackSign` | 2 |
| `HasPositiveFeedbackSign` | 2 |
| `InteriorReaction` | 2 |
| `InteriorSpecies` | 2 |
| `IsComplexBalanced` | 2 |
| `IsOscillatoryCoreClassI` | 3 |
| `IsOscillatoryCoreClassII` | 3 |
| `IsStable` | 2 |
| `IsSteadyState` | 2 |
| `IsUnstable` | 2 |
| `IsUnstableCore` | 3 |
| `IsUnstableNegativeFeedback` | 2 |
| `IsUnstablePositiveFeedback` | 2 |
| `J` | 2 |
| `Nondegenerate` | 2 |
| `Plane` | 2 |
| `SatisfiesTreeConstantBinomials` | 2 |
| `SpernerColoring` | 2 |
| `StoichIndependent` | 2 |
| `attractsTrajectory` | 2 |
| `boundaryFlux` | 2 |
| `c2A` | 2 |
| `cA` | 10 |
| `cAB` | 2 |
| `cA_ne_cB` | 2 |
| `cB` | 9 |
| `cX` | 2 |
| `carrier` | 2 |
| `complexBalancedTangentSpace` | 2 |
| `complexes_eq` | 2 |
| `c₂Fin3_J` | 2 |
| `deficiencyZero` | 3 |
| `det_J` | 2 |
| `det_ne_zero` | 2 |
| `divergenceIntegral` | 2 |
| `doorGraph` | 3 |
| `duration` | 2 |
| `duration_pos` | 2 |
| `endReaction` | 2 |
| `equilibrium` | 3 |
| `equilibrium_isSteadyState` | 2 |
| `even_iff_mod_two_count` | 2 |
| `eventually_periodicTrajectory` | 2 |
| `eventually_positive_family_branch` | 2 |
| `exists_localContraction` | 2 |
| `exists_periodicTrajectory` | 2 |
| `exists_reaction_of_odd` | 2 |
| `hasDerivAt_p` | 2 |
| `hasDerivAt_q` | 2 |
| `hasDerivAt_r` | 2 |
| `hasDynamicallyEquivalentRealizationWith` | 2 |
| `hasWeaklyReversibleRealization` | 2 |
| `hopf_crossing_at_μ₀` | 2 |
| `hurwitz_boundary_data_at_μ₀` | 2 |
| `logRatio` | 2 |
| `loopCurve` | 2 |
| `loopCurve_continuousOn` | 2 |
| `loopCurve_half` | 2 |
| `loopCurve_one` | 2 |
| `loopCurve_zero` | 2 |
| `not_weaklyReversible` | 3 |
| `numStrongLinkageClasses_eq` | 2 |
| `orbitArc_injective` | 2 |
| `orbitTime` | 2 |
| `oscillatoryCapacity` | 3 |
| `oscillatoryCapacity_of_fiedler` | 3 |
| `p` | 2 |
| `positiveComplexBalancedSet` | 2 |
| `positiveComplexBalancedSet_pathConnected` | 2 |
| `principalSubmatrix` | 2 |
| `prod_univ_species` | 2 |
| `q` | 2 |
| `r` | 2 |
| `rates` | 2 |
| `reaction` | 2 |
| `revStruct` | 2 |
| `singletonComplex` | 2 |
| `toMassActionRealization` | 2 |
| `toSpanSingleton_isInvertible` | 2 |
| `trace_J` | 2 |
| `weaklyReversible` | 6 |
| `xstar_positive` | 2 |
| `κ` | 2 |
| `μ₀` | 2 |

### Example-scoped names (not mathematical collisions)

Every example network re-declares its own `Species`, `Rxn`, `rxn`, `cA`, `cB`, `N`,
`weaklyReversible`, `equilibrium`, … inside a namespace scoped to that example. This
is the intended convention and carries no mathematical content, but it does mean a
grep for `weaklyReversible` returns dozens of hits, most of them proofs about one
specific network. Always qualify.

| short name | modules defining it |
|---|---|
| `rxn` | 12 |
| `N` | 12 |
| `Species` | 10 |
| `Rxn` | 10 |
| `cA` | 8 |
| `cB` | 7 |
| `numComplexes_eq` | 6 |
| `numReactions_eq` | 5 |
| `weaklyReversible` | 5 |
| `numLinkageClasses_eq` | 3 |
| `deficiencyZero` | 3 |
| `equilibrium` | 3 |
| `not_weaklyReversible` | 3 |

## Terms with no paper counterpart

The `TrueSR*` family (Shinar–Feinberg in-tree) uses its own vocabulary — `TrueSRCycle`, `TrueSREdge`, `TrueSRSSPath`, `Gluable`, `Relayable` — which is not the paper's vocabulary and has no one-to-one translation. It is documented in-tree at the head of `CRNT/Multistationarity/TrueChemistrySRCriterion.lean` and is therefore not repeated here.

These `TrueSR*` names collide with **no** classical term but do collide with each
other in one place worth flagging: `vertex_zero` / `vertex_last` exist both as
statements about a Sperner-lattice cell (`CRNT.Analysis.SpernerN`) and as statements
about the endpoints of a `TrueSRPath` (`CRNT.Network.TrueSRPath`). The names are the
same and the objects are unrelated. If you are reading a `vertex_last` proof, check
which namespace you are in before assuming Sperner.

<!-- GENERATED FILE. Do not edit by hand.
     Regenerate with:  python3 scripts/gen_docs.py
     Source of truth:  the `CRNT/` and `Scaffold/` Lean sources,
     parsed by `scripts/surface_index.py`.
-->
# Duplication map

Where the same obligation is carried more than once under different names. The
brief names two suspects: the `CRNT/Multistationarity/TrueSR*.lean` family (the
Shinar–Feinberg development) and the `Dynamics/` Global-Attractor chain. This file
answers with counts, not impressions.

**Method.** A *statement key* is the declaration's signature with all binder names
erased and all whitespace removed — two declarations with the same key state the
same thing up to renaming of hypotheses. A *body hash* is the SHA-256 (first 16
hex digits) of the comment-free, whitespace-normalized proof body. Three classes
are reported:

1. **identical statements** — same statement key in two or more modules;
2. **identical proofs** — same statement key *and* same body hash, i.e. literally
   the same proof text under two names;
3. **near-duplicates** — different statement keys, but the normalized signatures
   agree to ≥ 85% (edit distance ratio), which catches obligations re-stated with a
   hypothesis added or a binder renamed.

## Counts

| class | groups | declarations |
|---|---|---|
| identical statements | 20 | 47 |
| … of which cross-module | 20 | 47 |
| identical statements *and* identical proofs | 10 | 21 |
| near-duplicate signature pairs (≥85%) in `Multistationarity/`+`Dynamics/` | 567 |

## Per-area duplication density

| area | theorems | distinct statement keys | redundancy |
|---|---|---|---|
| `CRNT/Algebra` | 31 | 31 | 0.0% |
| `CRNT/Analysis` | 361 | 360 | 0.3% |
| `CRNT/Basic` | 84 | 84 | 0.0% |
| `CRNT/Combinatorics` | 2 | 2 | 0.0% |
| `CRNT/Compose` | 22 | 22 | 0.0% |
| `CRNT/Decision` | 167 | 167 | 0.0% |
| `CRNT/Decomposition` | 32 | 32 | 0.0% |
| `CRNT/Deficiency` | 379 | 379 | 0.0% |
| `CRNT/Design` | 157 | 157 | 0.0% |
| `CRNT/Dynamics` | 1450 | 1445 | 0.2% |
| `CRNT/Equilibria` | 293 | 293 | 0.0% |
| `CRNT/Examples` | 348 | 324 | 5.5% |
| `CRNT/Flux` | 51 | 51 | 0.0% |
| `CRNT/Geometry` | 807 | 807 | 0.0% |
| `CRNT/Graph` | 86 | 86 | 0.0% |
| `CRNT/Interop` | 46 | 46 | 0.0% |
| `CRNT/Kinetics` | 152 | 152 | 0.0% |
| `CRNT/LinearAlgebra` | 100 | 100 | 0.0% |
| `CRNT/Multistationarity` | 952 | 950 | 0.2% |
| `CRNT/Open` | 32 | 32 | 0.0% |
| `CRNT/Oscillation` | 736 | 736 | 0.0% |
| `CRNT/Reduction` | 16 | 16 | 0.0% |
| `CRNT/Stability` | 22 | 22 | 0.0% |
| `CRNT/Stochastic` | 298 | 298 | 0.0% |
| `CRNT/Stoich` | 17 | 17 | 0.0% |
| `CRNT/Subnetwork` | 14 | 14 | 0.0% |
| `CRNT/Theorems` | 187 | 187 | 0.0% |
| `CRNT/Topology` | 1 | 1 | 0.0% |
| `CRNT/Translation` | 102 | 102 | 0.0% |

## Class 1 + 2 — identical statements

Same statement, same proof: a straight copy under a new name. These are safe to consolidate and are the cheapest real duplication to remove.


### `weaklyReversible` — 5 copies, differs in proof

```lean
theorem weaklyReversible : N.WeaklyReversible
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Examples.CatalyticChain.weaklyReversible` | `CRNT/Examples/CatalyticChain.lean` | 28 | no | `bf2b76cea717c5c2` |
| `CRNT.Examples.CrntCheck.weaklyReversible` | `CRNT/Examples/CrntCheck.lean` | 17 | no | `bf2b76cea717c5c2` |
| `CRNT.Examples.DecideReachability.weaklyReversible` | `CRNT/Examples/DecideReachability.lean` | 23 | no | `e6d6aad2f8cddbdc` |
| `CRNT.Examples.ReversiblePair.weaklyReversible` | `CRNT/Examples/ReversiblePair.lean` | 77 | no | `5e459ee347bb95a4` |
| `CRNT.Examples.StochasticConvergenceExample.weaklyReversible` | `CRNT/Examples/StochasticConvergenceExample.lean` | 178 | no | `5e459ee347bb95a4` |

### `numComplexes_eq` — 3 copies, SAME PROOF

```lean
theorem numComplexes_eq : N.numComplexes = 3
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Examples.CatalyticChain.numComplexes_eq` | `CRNT/Examples/CatalyticChain.lean` | 29 | no | `d831e2ab55053d80` |
| `CRNT.Examples.Enzyme.numComplexes_eq` | `CRNT/Examples/Enzyme.lean` | 61 | no | `d831e2ab55053d80` |
| `CRNT.Examples.IrreversibleChain.numComplexes_eq` | `CRNT/Examples/IrreversibleChain.lean` | 57 | no | `d831e2ab55053d80` |

### `numLinkageClasses_eq` — 3 copies, differs in proof

```lean
theorem numLinkageClasses_eq : N.numLinkageClasses = 1
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Examples.CatalyticChain.numLinkageClasses_eq` | `CRNT/Examples/CatalyticChain.lean` | 42 | no | `e6af36003c9017c5` |
| `CRNT.Examples.DecideLinkage.numLinkageClasses_eq` | `CRNT/Examples/DecideLinkage.lean` | 21 | no | `552e37c4942835b1` |
| `CRNT.Examples.ReversiblePair.numLinkageClasses_eq` | `CRNT/Examples/ReversiblePair.lean` | 104 | no | `e31cca0d59908bf5` |

### `deficiencyZero` — 3 copies, differs in proof

```lean
theorem deficiencyZero : N.DeficiencyZero
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Examples.CatalyticChain.deficiencyZero` | `CRNT/Examples/CatalyticChain.lean` | 106 | no | `772c79d6a7464aaa` |
| `CRNT.Examples.DecideRank.deficiencyZero` | `CRNT/Examples/DecideRank.lean` | 25 | no | `36986aefc3d6802f` |
| `CRNT.Examples.ReversiblePair.deficiencyZero` | `CRNT/Examples/ReversiblePair.lean` | 139 | no | `772c79d6a7464aaa` |

### `not_weaklyReversible` — 3 copies, differs in proof

```lean
theorem not_weaklyReversible : ¬ N.WeaklyReversible
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Examples.IrreversibleChain.not_weaklyReversible` | `CRNT/Examples/IrreversibleChain.lean` | 70 | no | `068ea59a8e5cfe7a` |
| `CRNT.Examples.Lotka.not_weaklyReversible` | `CRNT/Examples/Lotka.lean` | 148 | no | `34774ef8658fba72` |
| `CRNT.Examples.Minimal.not_weaklyReversible` | `CRNT/Examples/Minimal.lean` | 74 | no | `d0e38b9c45263f6e` |

### `exists_rainbow_cell` — 2 copies, differs in proof

```lean
theorem exists_rainbow_cell : ∃ t : Cell, multiDoorIncidence.IsRainbowCell t
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Analysis.SpernerN2Geo.exists_rainbow_cell` | `CRNT/Analysis/SpernerGridGeometric.lean` | 167 | no | `816ded5e3f7cb4a5` |
| `CRNT.Analysis.SpernerN2.exists_rainbow_cell` | `CRNT/Analysis/SpernerGridMulti.lean` | 105 | no | `13923f5e2e00ff94` |

### `log_complexMonomialVector` — 2 copies, differs in proof

```lean
theorem log_complexMonomialVector (N : Network S) {x : Concentration S} (hx : x.Positive) (c : N.ComplexIdx) : Real.log (N.complexMonomialVector x c) = ∑ s, (c.val s : ℝ) * Real.log (x s)
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Network.log_complexMonomialVector` | `CRNT/Deficiency/LogMonomialRatio.lean` | 44 | no | `1f12f02db7c353d2` |
| `CRNT.Network.log_complexMonomialVector` | `CRNT/Theorems/DeficiencyZero/Toric.lean` | 42 | no | `e56811577de2ab03` |

### `properMap_subtype_eq_pointedMap` — 2 copies, differs in proof

```lean
private theorem properMap_subtype_eq_pointedMap (N : Network S) (C : ProperCone ℝ N.euclideanStoichSubspace) : ((ProperCone.map N.euclideanStoichSubspace.subtypeL C : ProperCone ℝ (EuclideanSpace ℝ S)) : PointedCone ℝ (EuclideanSpace ℝ S)) = PointedCone.map N.euclideanStoichSubspace.subtypeL.toLinea
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Network.properMap_subtype_eq_pointedMap` | `CRNT/Dynamics/ComplexBalanceStoichFan.lean` | 156 | no | `b0d5bd1651bfb95b` |
| `CRNT.Network.properMap_subtype_eq_pointedMap` | `CRNT/Dynamics/ComplexBalanceStoichFanInclusion.lean` | 627 | no | `c2de3dbfafde84e0` |

### `comap_map_subtype_eq` — 2 copies, SAME PROOF

```lean
private theorem comap_map_subtype_eq (N : Network S) (C : ProperCone ℝ N.euclideanStoichSubspace) : (ProperCone.map N.euclideanStoichSubspace.subtypeL C).comap N.euclideanStoichSubspace.subtypeL = C
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Network.comap_map_subtype_eq` | `CRNT/Dynamics/ComplexBalanceStoichFan.lean` | 214 | no | `7aadcb9c7b4913e9` |
| `CRNT.Network.comap_map_subtype_eq` | `CRNT/Dynamics/ComplexBalanceStoichFanInclusion.lean` | 687 | no | `7aadcb9c7b4913e9` |

### `toSpanSingleton_isInvertible` — 2 copies, SAME PROOF

```lean
theorem toSpanSingleton_isInvertible {c : ℝ} (hc : c ≠ 0) : (ContinuousLinearMap.toSpanSingleton ℝ c).IsInvertible
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.PlanarHopfData.toSpanSingleton_isInvertible` | `CRNT/Dynamics/HopfPersistentOrbit.lean` | 78 | no | `5c94fc11d38a486d` |
| `CRNT.toSpanSingleton_isInvertible` | `CRNT/Dynamics/TransversalCrossingTime.lean` | 70 | no | `5c94fc11d38a486d` |

### `coe_atTop` — 2 copies, SAME PROOF

```lean
private theorem coe_atTop : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Network.coe_atTop` | `CRNT/Examples/CodimTwoFaceModel.lean` | 95 | no | `33b787efc0cecaf7` |
| `CRNT.Network.coe_atTop` | `CRNT/Examples/OmegaPointFakeFlow.lean` | 120 | no | `33b787efc0cecaf7` |

### `prod_univ_species` — 2 copies, SAME PROOF

```lean
theorem prod_univ_species (f : Species → ℝ) : (∏ s : Species, f s) = f A * f B
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Examples.ComplexBalancedBoundaryEquilibrium.prod_univ_species` | `CRNT/Examples/ComplexBalancedBoundaryEquilibrium.lean` | 130 | no | `270fb196dde6ced3` |
| `CRNT.Examples.ReversiblePair.prod_univ_species` | `CRNT/Examples/ReversiblePair.lean` | 160 | no | `270fb196dde6ced3` |

### `numStrongLinkageClasses_eq` — 2 copies, differs in proof

```lean
theorem numStrongLinkageClasses_eq : N.numStrongLinkageClasses = 1
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Examples.CrntCheck.numStrongLinkageClasses_eq` | `CRNT/Examples/CrntCheck.lean` | 20 | no | `90bb145305194575` |
| `CRNT.Examples.DecideDirectedReachability.numStrongLinkageClasses_eq` | `CRNT/Examples/DecideDirectedReachability.lean` | 29 | no | `b5e5b16b98bd7bc1` |

### `numReactions_eq` — 2 copies, SAME PROOF

```lean
theorem numReactions_eq : N.numReactions = 3
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Examples.Enzyme.numReactions_eq` | `CRNT/Examples/Enzyme.lean` | 64 | no | `d831e2ab55053d80` |
| `CRNT.Examples.Lotka.numReactions_eq` | `CRNT/Examples/Lotka.lean` | 137 | no | `d831e2ab55053d80` |

### `hurwitz_boundary_data_at_μ₀` — 2 copies, differs in proof

```lean
theorem hurwitz_boundary_data_at_μ₀ : 0 < -(J μ₀).trace ∧ 0 < (J μ₀).c₂Fin3 ∧ 0 < -(J μ₀).det ∧ (-(J μ₀).det) = (-(J μ₀).trace) * (J μ₀).c₂Fin3
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Examples.HopfNetwork3.hurwitz_boundary_data_at_μ₀` | `CRNT/Examples/HopfNetwork3.lean` | 179 | no | `6b40297bdb52a8a6` |
| `CRNT.Examples.HopfOscillator3.hurwitz_boundary_data_at_μ₀` | `CRNT/Examples/HopfOscillator3.lean` | 67 | no | `110e848d62c83fbd` |

### `numReactions_eq` — 2 copies, SAME PROOF

```lean
theorem numReactions_eq : N.numReactions = 2
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Examples.IrreversibleChain.numReactions_eq` | `CRNT/Examples/IrreversibleChain.lean` | 60 | no | `d831e2ab55053d80` |
| `CRNT.Examples.ReversiblePair.numReactions_eq` | `CRNT/Examples/ReversiblePair.lean` | 71 | no | `d831e2ab55053d80` |

### `numComplexes_eq` — 2 copies, SAME PROOF

```lean
theorem numComplexes_eq : N.numComplexes = 2
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Examples.Minimal.numComplexes_eq` | `CRNT/Examples/Minimal.lean` | 53 | no | `d831e2ab55053d80` |
| `CRNT.Examples.ReversiblePair.numComplexes_eq` | `CRNT/Examples/ReversiblePair.lean` | 68 | no | `d831e2ab55053d80` |

### `toMatrix'_massActionJacobianCLM` — 2 copies, SAME PROOF

```lean
theorem toMatrix'_massActionJacobianCLM (N : Network S) (κ : N.RateConstants) (x : Concentration S) : LinearMap.toMatrix' (N.massActionJacobianCLM κ x : (S → ℝ) →ₗ[ℝ] (S → ℝ)) = N.massActionJacobian κ x
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Network.toMatrix'_massActionJacobianCLM` | `CRNT/Multistationarity/ReducedJacobianSign.lean` | 78 | no | `0fc99e8d20194951` |
| `CRNT.Network.toMatrix'_massActionJacobianCLM` | `CRNT/Multistationarity/ReducedPMatrixDecide.lean` | 167 | no | `0fc99e8d20194951` |

### `massActionVectorField_mem_stoichSubspace` — 2 copies, differs in proof

```lean
theorem massActionVectorField_mem_stoichSubspace (N : Network S) (κ : N.RateConstants) (x : Concentration S) : N.massActionVectorField κ x ∈ N.stoichSubspace
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Network.massActionVectorField_mem_stoichSubspace` | `CRNT/Multistationarity/SteadyStateDegree.lean` | 43 | no | `66f3dcfaaec77c8c` |
| `CRNT.Network.massActionVectorField_mem_stoichSubspace` | `CRNT/Theorems/DeficiencyZero/AsymptoticStability.lean` | 223 | no | `3ef73ee9d1b0819a` |

### `even_iff_mod_two_count` — 2 copies, SAME PROOF

```lean
private theorem even_iff_mod_two_count (m : ℕ) : Even m ↔ m % 2 = 0
```

| declaration | module | line | `sorry` | body hash |
|---|---|---|---|---|
| `CRNT.Network.even_iff_mod_two_count` | `CRNT/Multistationarity/TrueSRChordParity.lean` | 20 | no | `9f70e1f4dc8f659b` |
| `CRNT.Network.TrueSRPath.even_iff_mod_two_count` | `CRNT/Multistationarity/TrueSRParityLemma.lean` | 69 | no | `9f70e1f4dc8f659b` |

## Class 3 — near-duplicate statements

Different statement keys, ≥85% signature agreement. Each row is a pair of
declarations; the signature delta is where the two have drifted apart.

| similarity | declaration A | declaration B |
|---|---|---|
| 0.99 | `CRNT.Multistationarity.TrueSRCycleSplit`:492 `gluable_chord_arcBwd` | `CRNT.Multistationarity.TrueSRCycleSplit`:443 `gluable_chord_arcFwd` |
| 0.99 | `CRNT.Multistationarity.TrueSRPathAccessors`:24 `exists_reaction_of_odd` | `CRNT.Multistationarity.TrueSRSpeciesPath`:141 `exists_reaction_of_odd` |
| 0.99 | `CRNT.Dynamics.ComplexBalanceStoichFanInclusion`:305 `massActionVectorField_mem_toricField_relativeSourceOrderNegativeConeStoichFan` | `CRNT.Dynamics.ComplexBalanceStoichFanInclusion`:373 `massActionVectorField_mem_toricField_relativeSourceOrderNegativeStoichFan` |
| 0.99 | `CRNT.Multistationarity.TrueSRPathAccessors`:50 `vertex_eq_reactionAt` | `CRNT.Multistationarity.TrueSRSpeciesPath`:166 `vertex_eq_reactionAt` |
| 0.99 | `CRNT.Multistationarity.TrueSRPathAccessors`:40 `vertex_eq_speciesAt` | `CRNT.Multistationarity.TrueSRSpeciesPath`:157 `vertex_eq_speciesAt` |
| 0.99 | `CRNT.Dynamics.GershgorinColumnMarginQ`:74 `gershgorinColStabilityMarginQ_hurwitz` | `CRNT.Dynamics.GershgorinMarginQ`:74 `gershgorinStabilityMarginQ_hurwitz` |
| 0.99 | `CRNT.Dynamics.ForwardInvariance`:78 `gac_of_local_confinement` | `CRNT.Dynamics.GACSeparatingWitness`:93 `gac_of_local_separatingConfinement` |
| 0.98 | `CRNT.Dynamics.HurwitzGershgorinColumn`:82 `massActionJacobian_hurwitz_of_strict_col_diag_dominance` | `CRNT.Dynamics.HurwitzGershgorin`:87 `massActionJacobian_hurwitz_of_strict_diag_dominance` |
| 0.98 | `CRNT.Dynamics.SpectralSplittingReal`:276 `isConjStable_stableSubspace` | `CRNT.Dynamics.SpectralSplittingReal`:286 `isConjStable_unstableSubspace` |
| 0.98 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:2027 `trueSREdgeOfReactionVectorNe_representative` | `CRNT.Multistationarity.TrueSRCausalCycleFacts`:24 `trueSREdgeOfReactionVectorNe_representative` |
| 0.98 | `CRNT.Multistationarity.StoichChart`:52 `stoichChartLM_apply` | `CRNT.Multistationarity.StoichChart`:81 `stoichChart_apply` |
| 0.98 | `CRNT.Dynamics.ComplexBalanceCycleDecomposition`:2187 `massActionVectorField_mem_polar_relativeSourceOrderCone` | `CRNT.Dynamics.ComplexBalanceCycleDecomposition`:2230 `massActionVectorField_mem_polar_relativeSourceOrderStoichCone` |
| 0.98 | `CRNT.Multistationarity.TrueSRCycleSplit`:109 `arcBwd_endReaction` | `CRNT.Multistationarity.TrueSRCycleSplit`:95 `arcFwd_endReaction` |
| 0.98 | `CRNT.Multistationarity.TrueSRCPairThirdEdge`:274 `false_of_single_shared_edge_of_trueSRCriterion` | `CRNT.Multistationarity.TrueSRSingleSharedEdge`:125 `no_single_shared_edge_of_trueSRCriterion` |
| 0.98 | `CRNT.Dynamics.HurwitzGershgorinColumn`:51 `hurwitz_of_strict_col_diag_dominance` | `CRNT.Dynamics.HurwitzGershgorin`:46 `hurwitz_of_strict_diag_dominance` |
| 0.98 | `CRNT.Dynamics.ComplexBalanceCycleDecomposition`:1362 `relativeSourceOrderStoichProperCone_inter_isExposedFaceOf` | `CRNT.Dynamics.ComplexBalanceCycleDecomposition`:1378 `relativeSourceOrderStoichProperCone_inter_isExposedFaceOf_right` |
| 0.98 | `CRNT.Multistationarity.StoichChart`:67 `stoichChartLM_mem` | `CRNT.Multistationarity.StoichChart`:90 `stoichChart_mem` |
| 0.98 | `CRNT.Dynamics.TierSubsequenceExtraction`:142 `everyPositiveLogEscapingSequenceHasTierSubsequence` | `CRNT.Dynamics.TierSubsequenceExtraction`:178 `everyPositiveLogEscapingSequenceHasTierSubsequence_claim` |
| 0.98 | `CRNT.Dynamics.HurwitzGershgorinColumn`:65 `hurwitz_of_strict_col_diag_dominance_real` | `CRNT.Dynamics.HurwitzGershgorin`:67 `hurwitz_of_strict_diag_dominance_real` |
| 0.98 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:1300 `original_inflow_term_nonpos` | `CRNT.Multistationarity.TrueChemistrySRCriterion`:1346 `original_outflow_term_nonpos` |
| 0.97 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:1942 `exists_causal_unit_predecessor` | `CRNT.Multistationarity.TrueChemistrySRCriterion`:1954 `exists_causal_unit_predecessor_ne` |
| 0.97 | `CRNT.Multistationarity.TrueSRCycleSplit`:182 `arcBwd_interiorReaction` | `CRNT.Multistationarity.TrueSRCycleSplit`:167 `arcFwd_interiorReaction` |
| 0.97 | `CRNT.Multistationarity.StoichChart`:59 `stoichChartLM_injective` | `CRNT.Multistationarity.StoichChart`:85 `stoichChart_injective` |
| 0.97 | `CRNT.Dynamics.ComplexBalanceStoichFanInclusion`:286 `exists_relativeSourceOrderNegativeConeStoichFan_mem` | `CRNT.Dynamics.ComplexBalanceStoichFan`:377 `exists_relativeSourceOrderNegativeStoichFan_mem` |
| 0.97 | `CRNT.Multistationarity.SignConstruction`:72 `signConstructX_pos` | `CRNT.Multistationarity.SignConstruction`:57 `signConstructY_pos` |
| 0.97 | `CRNT.Multistationarity.TrueSRSpeciesPath`:980 `ssGluable_chord_arcBwd` | `CRNT.Multistationarity.TrueSRSpeciesPath`:946 `ssGluable_chord_arcFwd` |
| 0.97 | `CRNT.Dynamics.GlobalAttractorTheorem`:1126 `positiveOmega_or_criticalSiphonFaceEquilibrium` | `CRNT.Dynamics.GlobalAttractorTheorem`:1388 `positiveOmega_or_nonstationary_criticalSiphonFaceEquilibrium` |
| 0.97 | `CRNT.Dynamics.HopfLimitCycle`:197 `hopfLimitCycle_periodic_abs` | `CRNT.Dynamics.HopfLimitCycle`:178 `hopfLimitCycle_periodic` |
| 0.97 | `CRNT.Multistationarity.TrueSRCycleChord`:230 `closeInitialArcWithReturnReaction_leftEdge` | `CRNT.Multistationarity.TrueSRCycleChord`:241 `closeInitialArcWithReturnReaction_rightEdge` |
| 0.97 | `CRNT.Dynamics.TierScaleExtractionLemma44`:1095 `everyTierSequenceHasScaleDecomposition` | `CRNT.Dynamics.TierScaleExtractionLemma44`:1115 `everyTierSequenceHasScaleDecomposition_claim` |
| 0.97 | `CRNT.Dynamics.ComplexBalanceStoichFanInclusion`:780 `relativeSourceOrderNegativeConeStoichFan_isPolyhedralFan` | `CRNT.Dynamics.ComplexBalanceStoichFan`:362 `relativeSourceOrderNegativeStoichFan_isPolyhedralFan` |
| 0.97 | `CRNT.Multistationarity.TrueSRCycleSplit`:99 `arcBwd_startSpecies` | `CRNT.Multistationarity.TrueSRCycleSplit`:91 `arcFwd_startSpecies` |
| 0.97 | `CRNT.Dynamics.MichaelisMentenLipschitz`:237 `mmReg_coupled_tracking_ceiling_certified` | `CRNT.Dynamics.CertifiedReduction`:153 `mmReg_tracking_ceiling_via_abstract` |
| 0.97 | `CRNT.Dynamics.FacetRepulsionAndersonShiu`:1372 `no_omegaLimit_meets_locally_repelling_face` | `CRNT.Dynamics.FacetRepulsionAndersonShiu`:1201 `no_omegaLimit_on_face_of_locally_repelling` |
| 0.97 | `CRNT.Dynamics.ComplexBalanceCycleDecomposition`:1221 `inner_relativeSourceOrderIntersectionNormal_nonneg` | `CRNT.Dynamics.ComplexBalanceCycleDecomposition`:1283 `inner_relativeSourceOrderIntersectionNormal_nonpos` |
| 0.97 | `CRNT.Dynamics.MichaelisMentenFenichel`:320 `mmFenichelPersistence` | `CRNT.Dynamics.MichaelisMentenFenichelAllTime`:103 `mmFenichelPersistence_allTime` |
| 0.97 | `CRNT.Dynamics.SpectralSplitting`:85 `mapsTo_stableSubspace` | `CRNT.Dynamics.SpectralSplitting`:88 `mapsTo_unstableSubspace` |
| 0.97 | `CRNT.Dynamics.MichaelisMentenCertified`:112 `mmRegSlavedVelocity_certified` | `CRNT.Dynamics.MichaelisMentenSlowDriftSpeed`:73 `mmRegSlavedVelocity_le_of_drift` |
| 0.96 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:813 `lowerTrueSRCycle_sCycleNet_iff` | `CRNT.Multistationarity.TrueChemistrySRCriterion`:787 `lowerTrueSRCycle_sCycle_iff` |
| 0.96 | `CRNT.Dynamics.ExponentialDichotomy`:92 `exp_smul_mem_mulVecStabilizer` | `CRNT.Dynamics.ExponentialDichotomy`:81 `smul_mem_mulVecStabilizer` |
| 0.96 | `CRNT.Multistationarity.TrueSRSpeciesPath`:865 `speciesArcBwd_interiorReaction` | `CRNT.Multistationarity.TrueSRSpeciesPath`:822 `speciesArc_interiorReaction` |
| 0.96 | `CRNT.Dynamics.FenichelLogisticInstance`:103 `logisticMovingBase_graphSet_isInvariant_allTime` | `CRNT.Dynamics.FenichelContinuousMovingTarget`:213 `logisticMovingTarget_isInvariant_allTime` |
| 0.96 | `CRNT.Multistationarity.Concordance`:119 `concordanceWitness_of_eq_vectorField` | `CRNT.Multistationarity.StrongConcordance`:200 `strongConcordanceWitness_of_eq_vectorField` |
| 0.96 | `CRNT.Multistationarity.TrueSRCycleSplit`:234 `arcBwd_edge_on_cycle` | `CRNT.Multistationarity.TrueSRCycleSplit`:225 `arcFwd_edge_on_cycle` |
| 0.96 | `CRNT.Dynamics.TierOriginGeometry`:49 `tierEntropyCoordinate_le_one` | `CRNT.Dynamics.TierOriginGeometry`:57 `tierEntropyCoordinate_lt_one` |
| 0.96 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:556 `liftTrueSRCycle_sCycleNet_iff` | `CRNT.Multistationarity.TrueChemistrySRCriterion`:548 `liftTrueSRCycle_sCycle_iff` |
| 0.96 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:832 `containsEdge_lift_iff_lower` | `CRNT.Multistationarity.TrueChemistrySRCriterion`:824 `containsEdge_lower` |
| 0.96 | `CRNT.Dynamics.GershgorinColumnMarginQ`:52 `gershgorinColValueQ_cast` | `CRNT.Dynamics.GershgorinMarginQ`:52 `gershgorinRowValueQ_cast` |
| 0.96 | `CRNT.Dynamics.SpectralSplittingReal`:135 `imPi_mem_realPoints` | `CRNT.Dynamics.SpectralSplittingReal`:123 `rePi_mem_realPoints` |
| 0.96 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:3598 `cyclic_gain_no_strict'` | `CRNT.Multistationarity.TrueChemistrySRCriterion`:3577 `cyclic_gain_no_strict` |
| 0.96 | `CRNT.Multistationarity.StoichChart`:99 `stoichProjLM_stoichChartLM` | `CRNT.Multistationarity.StoichChart`:114 `stoichProj_stoichChart` |
| 0.96 | `CRNT.Dynamics.ExponentialDichotomy`:107 `mulVec_exp_smul_mapsTo_realStableSubspace` | `CRNT.Dynamics.ExponentialDichotomy`:119 `mulVec_exp_smul_mapsTo_realUnstableSubspace` |
| 0.96 | `CRNT.Multistationarity.TrueSRGlueBlocks`:46 `card_block_above` | `CRNT.Multistationarity.TrueSRGlueBlocks`:21 `card_block_below` |
| 0.96 | `CRNT.Multistationarity.TrueSRMidSegment`:128 `midSegmentRev_startSpecies` | `CRNT.Multistationarity.TrueSRMidSegment`:44 `midSegment_startSpecies` |
| 0.96 | `CRNT.Multistationarity.TrueSRCycleSplit`:619 `hasVertex_of_sameIncidence_left` | `CRNT.Multistationarity.TrueSRCycleSplit`:626 `hasVertex_of_sameIncidence_right` |
| 0.96 | `CRNT.Multistationarity.TrueSRMidSegment`:139 `midSegmentRev_endReaction` | `CRNT.Multistationarity.TrueSRMidSegment`:56 `midSegment_endReaction` |
| 0.96 | `CRNT.Multistationarity.TrueSRSpeciesPath`:836 `speciesArcBwd_speciesAt_zero` | `CRNT.Multistationarity.TrueSRSpeciesPath`:789 `speciesArc_speciesAt_zero` |
| 0.96 | `CRNT.Multistationarity.Concordance`:303 `Concordant.subsingleton_steadyState` | `CRNT.Multistationarity.StrongConcordance`:265 `StronglyConcordant.subsingleton_steadyState` |
| 0.96 | `CRNT.Dynamics.HopfTransversality3`:150 `hopf_transversal_crossing` | `CRNT.Dynamics.HopfTransversality3`:118 `hopf_transversality_iff` |
| 0.96 | `CRNT.Dynamics.SpectralSplittingReal`:158 `conjPi_sub_smul` | `CRNT.Dynamics.SpectralSplittingReal`:168 `conjPi_sub_smul_pow` |
| 0.96 | `CRNT.Dynamics.HopfNormalForm`:194 `subcritical_branch_side` | `CRNT.Dynamics.HopfNormalForm`:182 `supercritical_branch_side` |
| 0.96 | `CRNT.Multistationarity.TrueSRCausalCycleFacts`:34 `trueInternalCausalLeftEdge_representative` | `CRNT.Multistationarity.TrueSRCausalCycleFacts`:40 `trueInternalCausalRightEdge_representative` |
| 0.95 | `CRNT.Multistationarity.TrueSRSpeciesPath`:563 `hasEnds_of_left` | `CRNT.Multistationarity.TrueSRSpeciesPath`:570 `hasEnds_of_right` |
| 0.95 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:1153 `inflow_nonneg_of_sigma_neg` | `CRNT.Multistationarity.TrueChemistrySRCriterion`:1119 `outflow_neg_of_sigma_neg` |
| 0.95 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:1103 `inflow_nonpos_of_sigma_pos` | `CRNT.Multistationarity.TrueChemistrySRCriterion`:1071 `outflow_pos_of_sigma_pos` |
| 0.95 | `CRNT.Multistationarity.TrueSRSpeciesPath`:758 `speciesArcBwd_vertex_zero` | `CRNT.Multistationarity.TrueSRSpeciesPath`:744 `speciesArc_vertex_zero` |
| 0.95 | `CRNT.Dynamics.MichaelisMentenC1`:159 `mmFastField_hasFDerivAt_fibre` | `CRNT.Dynamics.MichaelisMentenRegularized`:254 `mmRegFastField_hasFDerivAt_fibre` |
| 0.95 | `CRNT.Dynamics.GershgorinColumnMarginQ`:46 `gershgorinColMarginQ_neg_iff` | `CRNT.Dynamics.GershgorinMarginQ`:46 `gershgorinMarginQ_neg_iff` |
| 0.95 | `CRNT.Multistationarity.TrueSRCycleSplit`:147 `arcBwd_interiorSpecies` | `CRNT.Multistationarity.TrueSRCycleSplit`:130 `arcFwd_interiorSpecies` |
| 0.95 | `CRNT.Dynamics.TierSubsequenceExtraction`:82 `tierStrictBelow_of_ennrealRatio_tendsto_zero` | `CRNT.Dynamics.TierSubsequenceExtraction`:111 `tierStrictBelow_reverse_of_ennrealRatio_tendsto_top` |
| 0.95 | `CRNT.Multistationarity.TrueSRMidSegment`:117 `midSegmentRev_vertex` | `CRNT.Multistationarity.TrueSRMidSegment`:33 `midSegment_vertex` |
| 0.95 | `CRNT.Multistationarity.TrueSRSpeciesPath`:774 `speciesArcBwd_edge_even` | `CRNT.Multistationarity.TrueSRSpeciesPath`:780 `speciesArcBwd_edge_odd` |
| 0.95 | `CRNT.Dynamics.GlobalPersistenceFrontier`:174 `singleLinkagePermanence_of_strongEndotacticPermanence` | `CRNT.Dynamics.GlobalPersistenceFrontier`:187 `singleLinkagePersistence_of_strongEndotacticPermanence` |
| 0.95 | `CRNT.Dynamics.ComplexBalanceCycleDecomposition`:1008 `isClosed_relativeSourceOrderCone` | `CRNT.Dynamics.ComplexBalanceCycleDecomposition`:1195 `isClosed_relativeSourceOrderStoichCone` |
| 0.95 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:4644 `exists_positive_off_cycle_aggregate_class` | `CRNT.Multistationarity.TrueChemistrySRCriterion`:4520 `no_degree_two_aggregate_causal_cycle` |
| 0.95 | `CRNT.Dynamics.SpectralSplittingReal`:348 `mulVec_mapsTo_realStableSubspace` | `CRNT.Dynamics.SpectralSplittingReal`:358 `mulVec_mapsTo_realUnstableSubspace` |
| 0.95 | `CRNT.Dynamics.MichaelisMentenManifold`:93 `mmFastField_oneSidedContraction` | `CRNT.Dynamics.MichaelisMentenRegularized`:225 `mmRegFastField_oneSidedContraction` |
| 0.95 | `CRNT.Dynamics.TierOrderAlgebra`:75 `TierStrictBelow.trans_same` | `CRNT.Dynamics.TierOrderAlgebra`:64 `TierStrictBelow.trans` |
| 0.95 | `CRNT.Dynamics.ToricBarrierExplicit`:969 `hm_of_cone_family` | `CRNT.Dynamics.ToricBarrierExplicit`:688 `hm_of_single_chamber` |
| 0.95 | `CRNT.Dynamics.GlobalAttractorTheorem`:1490 `complexBalanced_genuinePermanent` | `CRNT.Dynamics.GlobalAttractorTheorem`:1561 `complexBalanced_permanent` |
| 0.95 | `CRNT.Multistationarity.TrueSRDegreeTwoNoSToR`:31 `sameIncidence_trans` | `CRNT.Multistationarity.TrueSRTwoGluedCycles`:24 `SameIncidence.trans` |
| 0.95 | `CRNT.Dynamics.TierOrderAlgebra`:195 `TierStrictBelow.not_same_reverse` | `CRNT.Dynamics.TierOrderAlgebra`:204 `TierStrictBelow.not_tierLE_reverse` |
| 0.95 | `CRNT.Dynamics.ToricBarrierTrapping`:120 `barrier_le_of_toric_descent` | `CRNT.Dynamics.ToricBarrierTrapping`:165 `barrier_le_of_toric_descent_in_band` |
| 0.95 | `CRNT.Multistationarity.TrueSRSpeciesPath`:171 `edge_species_of_even` | `CRNT.Multistationarity.TrueSRSpeciesPath`:209 `edge_species_of_odd` |
| 0.94 | `CRNT.Multistationarity.WeakNormalityCriterion`:421 `normal_of_sourceMinorCertificate` | `CRNT.Multistationarity.WeakNormalityCriterion`:403 `weaklyNormal_of_sourceMinorCertificate` |
| 0.94 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:4520 `no_degree_two_aggregate_causal_cycle` | `CRNT.Multistationarity.TrueChemistrySRCriterion`:7019 `no_degree_two_aggregate_causal_cycle_of_offCycle_hrest` |
| 0.94 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:5735 `no_reaction_species_ear_of_trueSRCriterion` | `CRNT.Multistationarity.TrueChemistrySRCriterion`:5688 `no_species_reaction_ear_of_trueSRCriterion` |
| 0.94 | `CRNT.Dynamics.MinimalInvariant`:46 `isInvariant_sInter` | `CRNT.Dynamics.IsolatedInvariant`:45 `isInvariant_sUnion` |
| 0.94 | `CRNT.Multistationarity.TrueSRMidSegment`:122 `midSegmentRev_edge` | `CRNT.Multistationarity.TrueSRMidSegment`:38 `midSegment_edge` |
| 0.94 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:5200 `relPathAdj` | `CRNT.Multistationarity.TrueChemistrySRCriterion`:5554 `relPathAdjRev` |
| 0.94 | `CRNT.Multistationarity.TrueSRSpeciesPath`:324 `extend_edge_last` | `CRNT.Multistationarity.TrueSRSpeciesPath`:320 `extend_edge_lt` |
| 0.94 | `CRNT.Dynamics.ComplexBalanceCycleDecomposition`:2331 `exists_relativeSourceOrderNegativeConeFamily_mem` | `CRNT.Dynamics.ComplexBalanceCycleDecomposition`:2166 `exists_relativeSourceOrderStoichConeFamily_mem` |
| 0.94 | `CRNT.Dynamics.SublevelNagumo`:114 `frontier_sublevel_le` | `CRNT.Dynamics.SublevelNagumo`:121 `le_frontier_sublevel` |
| 0.94 | `CRNT.Multistationarity.WeakNormality`:949 `concordant_of_fullyOpen_concordant_of_normal` | `CRNT.Multistationarity.WeakNormality`:631 `concordant_of_fullyOpen_concordant_of_weaklyNormal` |
| 0.94 | `CRNT.Dynamics.ComplexBalanceStoichFan`:110 `comap_inf_relativeSourceOrder` | `CRNT.Dynamics.ComplexBalanceStoichFanInclusion`:722 `comap_inf_stoich` |
| 0.94 | `CRNT.Dynamics.GraphTransform`:120 `manifold_isFixedPt` | `CRNT.Dynamics.CenterManifold`:149 `manifold_isFixedPt` |
| 0.94 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:2965 `trueInternalCausalStep_mem_signSource` | `CRNT.Multistationarity.TrueChemistrySRCriterion`:2953 `trueInternalCauseReaction_mem_signSource` |
| 0.94 | `CRNT.Dynamics.SiphonFaceWeakReversibility`:553 `massActionVectorField_eq_zero_of_confined_constantEntropy_siphonFaceOrbit` | `CRNT.Dynamics.SiphonFaceWeakReversibility`:536 `massActionVectorField_eq_zero_of_constantEntropy_siphonFaceOrbit` |
| 0.94 | `CRNT.Multistationarity.TrueSRArc`:67 `arcVertex_odd` | `CRNT.Multistationarity.TrueSRSpeciesPath`:639 `sarcVertex_odd` |
| 0.94 | `CRNT.Dynamics.ToricEmbeddingWR`:219 `NetworkCycleDecomposition.cycleVelocity_mem_polarCone` | `CRNT.Dynamics.ToricEmbeddingWR`:232 `NetworkCycleDecomposition.velocity_mem_polarCone` |
| 0.94 | `CRNT.Multistationarity.TrueSRCycleSplit`:212 `arcBwd_edge_cases` | `CRNT.Multistationarity.TrueSRCycleSplit`:202 `arcFwd_edge_cases` |
| 0.94 | `CRNT.Dynamics.ComplexBalanceStoichFanInclusion`:33 `relativeSourceOrderNegativeStoichFan_hasDualFGCells` | `CRNT.Dynamics.ComplexBalanceStoichFanInclusion`:24 `relativeSourceOrderStoichFan_hasDualFGCells` |
| 0.94 | `CRNT.Multistationarity.FullyOpenConcordanceSpectral`:80 `concordant_fullyOpen_iff_influence` | `CRNT.Multistationarity.FullyOpenConcordanceSpectral`:61 `discordant_fullyOpen_iff_influence` |
| 0.94 | `CRNT.Multistationarity.TrueSRCycleReverse`:164 `reverse_sCycle` | `CRNT.Multistationarity.TrueSRCycleReverse`:150 `reverse_sCycleNet` |
| 0.94 | `CRNT.Dynamics.FenichelContinuousMovingTarget`:110 `movingFlowAt_mapsTo` | `CRNT.Dynamics.FenichelContinuousMovingTarget`:136 `movingTarget_mapsTo_allTime` |
| 0.94 | `CRNT.Dynamics.GACOmegaPositive`:326 `massActionVectorField_eq_zero_of_mem_boundaryOmega` | `CRNT.Dynamics.GACOmegaPositive`:307 `massActionVectorField_eq_zero_of_mem_boundaryOmega_siphon` |
| 0.94 | `CRNT.Multistationarity.TrueSRSpeciesPath`:724 `speciesArc_edge_even` | `CRNT.Multistationarity.TrueSRSpeciesPath`:729 `speciesArc_edge_odd` |
| 0.94 | `CRNT.Dynamics.ToricBarrierExplicit`:985 `hm_of_cone_family_margins` | `CRNT.Dynamics.ToricBarrierExplicit`:807 `hm_of_separating_margins` |
| 0.94 | `CRNT.Dynamics.ToricBarrierExplicit`:853 `inner_faceLogPart_ge_of_depth` | `CRNT.Dynamics.ToricBarrierExplicit`:886 `margin_of_depth` |
| 0.94 | `CRNT.Multistationarity.TrueSRArc`:219 `initialArcPath_edge_even` | `CRNT.Multistationarity.TrueSRArc`:225 `initialArcPath_edge_odd` |
| 0.94 | `CRNT.Multistationarity.TrueSRSpeciesPath`:852 `speciesArcBwd_interiorSpecies` | `CRNT.Multistationarity.TrueSRSpeciesPath`:805 `speciesArc_interiorSpecies` |
| 0.94 | `CRNT.Multistationarity.RegularValueDegree`:102 `regularDegree_eq_card_of_det_pos` | `CRNT.Multistationarity.RegularValueDegree`:115 `regularDegree_nonneg_of_det_pos` |
| 0.94 | `CRNT.Dynamics.EscapeSiphonFace`:98 `forwardLimit_positive_of_hasNoCriticalSiphon` | `CRNT.Dynamics.NoCriticalSiphonPersistence`:35 `omegaLimit_positive_of_hasNoCriticalSiphon` |
| 0.94 | `CRNT.Dynamics.ButlerMcGehee`:134 `exists_mem_omegaLimit_notMem_isolating` | `CRNT.Dynamics.FacetRepulsion`:100 `exists_omegaLimit_escape_of_not_subset_isolating` |
| 0.94 | `CRNT.Dynamics.ToricBarrierTrapping`:102 `continuousOn_euclideanStoichState_comp` | `CRNT.Dynamics.ToricBarrierTrapping`:95 `continuous_euclideanStoichState_comp` |
| 0.94 | `CRNT.Multistationarity.TrueSRCycleSplit`:212 `arcBwd_edge_cases` | `CRNT.Multistationarity.TrueSRCycleSplit`:234 `arcBwd_edge_on_cycle` |
| 0.94 | `CRNT.Dynamics.ThmBGenuine`:68 `genuine_sublevel_invariant` | `CRNT.Dynamics.SublevelNagumo`:151 `sublevel_invariant_of_neighborhood_descent` |
| 0.94 | `CRNT.Dynamics.MichaelisMentenCoupledContraction`:83 `coupled_dissipative_ceiling_nonauto` | `CRNT.Dynamics.MichaelisMentenCertifiedUniform`:82 `coupled_dissipative_ceiling` |
| 0.94 | `CRNT.Multistationarity.TrueChemistrySRCriterion`:1153 `inflow_nonneg_of_sigma_neg` | `CRNT.Multistationarity.TrueChemistrySRCriterion`:1103 `inflow_nonpos_of_sigma_pos` |
| 0.94 | `CRNT.Multistationarity.TrueSRArc`:63 `arcVertex_even` | `CRNT.Multistationarity.TrueSRSpeciesPath`:635 `sarcVertex_even` |

## Suspicion check: the two named suspects

`CRNT/Multistationarity/TrueSR*.lean` — how many modules, how many theorems, how
much exact redundancy:

- 40 modules, 334 theorems/lemmas
- 1 exact statement repeats inside the family
- 0 carry `sorry`

| module | decls | theorems | distinct keys | repeats |
|---|---|---|---|---|
| `CRNT.Multistationarity.TrueSRArc` | 13 | 10 | 10 | 0 |
| `CRNT.Multistationarity.TrueSRCPairThirdEdge` | 8 | 8 | 8 | 0 |
| `CRNT.Multistationarity.TrueSRCausalCycleFacts` | 13 | 13 | 13 | 0 |
| `CRNT.Multistationarity.TrueSRChordExtraction` | 2 | 2 | 2 | 0 |
| `CRNT.Multistationarity.TrueSRChordParity` | 2 | 2 | 2 | 0 |
| `CRNT.Multistationarity.TrueSRClosedWalk` | 14 | 7 | 7 | 0 |
| `CRNT.Multistationarity.TrueSRCycleChord` | 10 | 7 | 7 | 0 |
| `CRNT.Multistationarity.TrueSRCycleReverse` | 13 | 11 | 11 | 0 |
| `CRNT.Multistationarity.TrueSRCycleSplit` | 39 | 37 | 37 | 0 |
| `CRNT.Multistationarity.TrueSRDegreeTwoNoSToR` | 5 | 5 | 5 | 0 |
| `CRNT.Multistationarity.TrueSREdgePath` | 6 | 5 | 5 | 0 |
| `CRNT.Multistationarity.TrueSRGlueBlocks` | 2 | 2 | 2 | 0 |
| `CRNT.Multistationarity.TrueSRGlueCPairs` | 5 | 5 | 5 | 0 |
| `CRNT.Multistationarity.TrueSRGlueCount` | 2 | 2 | 2 | 0 |
| `CRNT.Multistationarity.TrueSRGlueIndex` | 6 | 6 | 6 | 0 |
| `CRNT.Multistationarity.TrueSRGlueInterface` | 11 | 6 | 6 | 0 |
| `CRNT.Multistationarity.TrueSRGlueMaps` | 19 | 15 | 15 | 0 |
| `CRNT.Multistationarity.TrueSRGlueSeams` | 6 | 6 | 6 | 0 |
| `CRNT.Multistationarity.TrueSRLinearWalk` | 9 | 5 | 5 | 0 |
| `CRNT.Multistationarity.TrueSRMidSegment` | 11 | 9 | 9 | 0 |
| `CRNT.Multistationarity.TrueSRMinimalChord` | 8 | 4 | 4 | 0 |
| `CRNT.Multistationarity.TrueSRNoArcChord` | 1 | 1 | 1 | 0 |
| `CRNT.Multistationarity.TrueSRParityCount` | 3 | 3 | 3 | 0 |
| `CRNT.Multistationarity.TrueSRParityLemma` | 3 | 3 | 3 | 0 |
| `CRNT.Multistationarity.TrueSRParityRR` | 40 | 27 | 27 | 0 |
| `CRNT.Multistationarity.TrueSRPath` | 7 | 6 | 6 | 0 |
| `CRNT.Multistationarity.TrueSRPathAccessors` | 11 | 9 | 9 | 0 |
| `CRNT.Multistationarity.TrueSRPathCPairs` | 5 | 4 | 4 | 0 |
| `CRNT.Multistationarity.TrueSRPathSegment` | 4 | 3 | 3 | 0 |
| `CRNT.Multistationarity.TrueSRPathTerminalSegment` | 5 | 4 | 4 | 0 |
| `CRNT.Multistationarity.TrueSRReactionInteriorPath` | 2 | 2 | 2 | 0 |
| `CRNT.Multistationarity.TrueSRRotate` | 14 | 11 | 11 | 0 |
| `CRNT.Multistationarity.TrueSRSSGlueCPairs` | 8 | 6 | 6 | 0 |
| `CRNT.Multistationarity.TrueSRSeamParity` | 3 | 3 | 3 | 0 |
| `CRNT.Multistationarity.TrueSRSegmentEndpoints` | 4 | 4 | 4 | 0 |
| `CRNT.Multistationarity.TrueSRSingleSharedEdge` | 4 | 2 | 2 | 0 |
| `CRNT.Multistationarity.TrueSRSpeciesPath` | 80 | 65 | 65 | 0 |
| `CRNT.Multistationarity.TrueSRTwoGluedCycles` | 4 | 4 | 4 | 0 |
| `CRNT.Multistationarity.TrueSRTwoWeightGain` | 1 | 1 | 1 | 0 |
| `CRNT.Multistationarity.TrueSRWalkEdges` | 9 | 9 | 9 | 0 |

`Dynamics/` Global-Attractor chain — the modules named in `docs/architecture.md` for the GAC:

- 33 modules, 302 theorems/lemmas
- 0 exact statement repeats
- 1 carry `sorry`

| module | decls | theorems | distinct keys | repeats |
|---|---|---|---|---|
| `CRNT.Algebra.SiphonIdeal` | 12 | 7 | 7 | 0 |
| `CRNT.Compose.InterconnectSiphon` | 5 | 5 | 5 | 0 |
| `CRNT.Decision.CriticalSiphonDecide` | 26 | 12 | 12 | 0 |
| `CRNT.Decision.IsCriticalSiphonDecidable` | 6 | 5 | 5 | 0 |
| `CRNT.Decision.PersistenceSingleLinkage` | 2 | 2 | 2 | 0 |
| `CRNT.Deficiency.BorosSingleLinkageEstimate` | 5 | 4 | 4 | 0 |
| `CRNT.Dynamics.BoundaryOmegaSiphon` | 1 | 1 | 1 | 0 |
| `CRNT.Dynamics.CriticalSiphonDissipationRepulsion` | 9 | 9 | 9 | 0 |
| `CRNT.Dynamics.CriticalSiphonNearFacetInflux` | 3 | 3 | 3 | 0 |
| `CRNT.Dynamics.CriticalSiphonOmega` | 1 | 1 | 1 | 0 |
| `CRNT.Dynamics.EndotacticPermanence` | 6 | 5 | 5 | 0 |
| `CRNT.Dynamics.EscapeSiphonFace` | 3 | 3 | 3 | 0 |
| `CRNT.Dynamics.FaceCodimension` | 10 | 10 | 10 | 0 |
| `CRNT.Dynamics.GACNoCriticalSiphon` | 1 | 1 | 1 | 0 |
| `CRNT.Dynamics.GlobalAttractorSpecialCases` | 1 | 1 | 1 | 0 |
| `CRNT.Dynamics.GlobalAttractorTheorem` | 40 | 33 | 33 | 0 |
| `CRNT.Dynamics.HighCodimensionSiphonFace` | 26 | 26 | 26 | 0 |
| `CRNT.Dynamics.HopfPersistentOrbit` | 9 | 6 | 6 | 0 |
| `CRNT.Dynamics.NoCriticalSiphonPersistence` | 1 | 1 | 1 | 0 |
| `CRNT.Dynamics.NoDrainableSiphonPersistence` | 5 | 5 | 5 | 0 |
| `CRNT.Dynamics.SingleLinkageGAC` | 4 | 2 | 2 | 0 |
| `CRNT.Dynamics.SingleLinkageStructure` | 6 | 5 | 5 | 0 |
| `CRNT.Dynamics.Siphon` | 22 | 7 | 7 | 0 |
| `CRNT.Dynamics.SiphonAutocatalysis` | 69 | 47 | 47 | 0 |
| `CRNT.Dynamics.SiphonConservation` | 2 | 2 | 2 | 0 |
| `CRNT.Dynamics.SiphonDimensionDescent` | 13 | 11 | 11 | 0 |
| `CRNT.Dynamics.SiphonFaceWeakReversibility` | 18 | 14 | 14 | 0 |
| `CRNT.Dynamics.SiphonFacetEscape` | 6 | 5 | 5 | 0 |
| `CRNT.Dynamics.ToricBarrierExplicit` | 38 | 37 | 37 | 0 |
| `CRNT.Dynamics.ToricBarrierTrapping` | 15 | 13 | 13 | 0 |
| `CRNT.Equilibria.BoundarySiphon` | 9 | 8 | 8 | 0 |
| `CRNT.Geometry.Endotactic` | 11 | 5 | 5 | 0 |
| `CRNT.Geometry.EndotacticGlobal` | 9 | 6 | 6 | 0 |

import CRNT

/-!
# Axiom-cleanliness regression guard

`#print axioms` on the headline results, each pinned with `#guard_msgs` so the build
fails if any of them ever acquires an axiom beyond Mathlib's `propext`, `Classical.choice`,
and `Quot.sound` — in particular if a `sorry` (`sorryAx`) creeps into a dependency.

The `(whitespace := lax)` mode makes the comparison insensitive to how long names wrap.
-/

/-- info: 'CRNT.Network.exists_isComplexBalanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_isComplexBalanced

/-- info: 'CRNT.Network.gac_of_hasNoCriticalSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_hasNoCriticalSiphon

/-- info: 'CRNT.Network.singleLinkageClass_gac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.singleLinkageClass_gac

/-- info: 'CRNT.Network.gac_of_persistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_persistent

/-- info: 'CRNT.Network.deficiencyOneUniqueness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.deficiencyOneUniqueness

/-- info: 'CRNT.omegaLimit_negInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.omegaLimit_negInvariant

/-- info: 'CRNT.ZeroSeparatingCurve2D.polyRegion_invariant_of_strictSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.ZeroSeparatingCurve2D.polyRegion_invariant_of_strictSupport

/-- info: 'CRNT.Analysis.SpernerN.sperner_exists_rainbow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Analysis.SpernerN.sperner_exists_rainbow

/-- info: 'CRNT.Analysis.SpernerN.brouwer_stdSimplex_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Analysis.SpernerN.brouwer_stdSimplex_fin

/-- info: 'CRNT.injOn_of_pmatrix_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.injOn_of_pmatrix_fderiv

/-- info: 'CRNT.Network.jumpKernel_invariantProb_singleton_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.jumpKernel_invariantProb_singleton_pos

/-- info: 'ODE.SlowManifoldC1Seed.contDiff_manifoldMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.SlowManifoldC1Seed.contDiff_manifoldMap
/-- info: 'CRNT.Network.isCriticalSiphon_iff_no_supported_cone_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isCriticalSiphon_iff_no_supported_cone_vector

/-- info: 'CRNT.Network.mem_conservationCone_iff_farkas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.mem_conservationCone_iff_farkas
/-- info: 'CRNT.Network.cmeSemigroup_preserves_stationarity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.cmeSemigroup_preserves_stationarity

/-- info: 'CRNT.det_ne_zero_of_coverTerm_signDefinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.det_ne_zero_of_coverTerm_signDefinite
/-- info: 'CRNT.Network.isCriticalSiphon_iff_exists_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isCriticalSiphon_iff_exists_pointwise
/-- info: 'CRNT.Network.cmeSemigroup_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.cmeSemigroup_comp

/-- info: 'CRNT.hopf_transversal_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.hopf_transversal_crossing

/-- info: 'CRNT.Examples.HopfOscillator3.admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.HopfOscillator3.admissible

/-- info: 'CRNT.Network.coverProductSingle_eq_magnitude_mul_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.coverProductSingle_eq_magnitude_mul_sign

/-- info: 'CRNT.MichaelisMenten.mmRegManifoldMap_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.MichaelisMenten.mmRegManifoldMap_contDiff

/-- info: 'CRNT.Network.isPMatrix_massActionJacobian_of_consistentSRSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isPMatrix_massActionJacobian_of_consistentSRSign

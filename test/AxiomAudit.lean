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

/-- info: 'CRNT.FaithfulCurve2D.apexField_region_persistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.FaithfulCurve2D.apexField_region_persistent

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

/-- info: 'CRNT.TransversalSection.hasFDerivAt_returnMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.TransversalSection.hasFDerivAt_returnMap

/-- info: 'CRNT.PlanarHopfData.hopf_andronov_full_field_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PlanarHopfData.hopf_andronov_full_field_realized

/-- info: 'CRNT.Examples.HopfOscillator3.admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.HopfOscillator3.admissible

/-- info: 'CRNT.Examples.HopfNetwork3.hopf_crossing_at_μ₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.HopfNetwork3.hopf_crossing_at_μ₀

/-- info: 'CRNT.Examples.HopfNetwork3.boundary_crossing_transversal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.HopfNetwork3.boundary_crossing_transversal

/-- info: 'CRNT.Network.coverProductSingle_eq_magnitude_mul_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.coverProductSingle_eq_magnitude_mul_sign

/-- info: 'CRNT.MichaelisMenten.mmRegManifoldMap_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.MichaelisMenten.mmRegManifoldMap_contDiff

/-- info: 'CRNT.Network.isPMatrix_massActionJacobian_of_consistentSRSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isPMatrix_massActionJacobian_of_consistentSRSign

/-- info: 'CRNT.primitive_of_stronglyConnected_self_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.primitive_of_stronglyConnected_self_loop

/-- info: 'CRNT.Network.regionPrimitive_of_stronglyConnected_self_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.regionPrimitive_of_stronglyConnected_self_loop

/-- info: 'CRNT.Network.weaklyReversible_pow_mulVec_tendsto_stationaryVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.weaklyReversible_pow_mulVec_tendsto_stationaryVec
/-- info: 'CRNT.Network.subsingleton_steadyState_of_consistentSRSign_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.subsingleton_steadyState_of_consistentSRSign_decide

/-- info: 'CRNT.NetworkData.analyze_srSignConsistent_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.analyze_srSignConsistent_eq

/-- info: 'CRNT.NetworkData.isPMatrix_massActionJacobian_box_of_srPMatrixPointIndep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.isPMatrix_massActionJacobian_box_of_srPMatrixPointIndep

/-- info: 'CRNT.Network.massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix

/-- info: 'CRNT.Network.massActionInjectiveOnClass_of_concretePivotChart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionInjectiveOnClass_of_concretePivotChart

/-- info: 'CRNT.Network.isPMatrix_pivotReducedJacobian_of_pivotCoverSignQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isPMatrix_pivotReducedJacobian_of_pivotCoverSignQ

/-- info: 'CRNT.NetworkData.analyze_hasCriticalSiphon_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.analyze_hasCriticalSiphon_eq

/-- info: 'CRNT.RationalFarkas.feasibleStrict_eliminateLast_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.RationalFarkas.feasibleStrict_eliminateLast_iff

/-- info: 'CRNT.Network.complexShiftRegion_pow_mulVec_tendsto_stationaryVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexShiftRegion_pow_mulVec_tendsto_stationaryVec
/-- info: 'CRNT.Network.feasible_supportedFeasSystem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.feasible_supportedFeasSystem_iff

/-- info: 'CRNT.RationalFarkas.feasibleℝ_iff_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.RationalFarkas.feasibleℝ_iff_feasible
/-- info: 'CRNT.Network.massActionInjectiveOnClass_of_compressionSRSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionInjectiveOnClass_of_compressionSRSign

/-- info: 'ODE.SlowManifoldC1Seed.certified_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.SlowManifoldC1Seed.certified_reduction

/-- info: 'CRNT.MichaelisMenten.mmReg_tracking_ceiling_via_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.MichaelisMenten.mmReg_tracking_ceiling_via_abstract
/-- info: 'CRNT.ExponentialDichotomy.mulVec_exp_smul_mapsTo_realStableSubspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.ExponentialDichotomy.mulVec_exp_smul_mapsTo_realStableSubspace
/-- info: 'CRNT.Network.uRegionMatrix_pow_mulVec_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.uRegionMatrix_pow_mulVec_tendsto
/-- info: 'CRNT.Network.chartProjQ_mul_chartBasisQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.chartProjQ_mul_chartBasisQ
/-- info: 'CRNT.Network.gac_of_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_decide

/-- info: 'CRNT.NetworkData.hasNoCriticalSiphon_of_persistenceStructural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.hasNoCriticalSiphon_of_persistenceStructural

/-- info: 'ODE.GraphTransformData.manifold_dist_base_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.GraphTransformData.manifold_dist_base_le

/-- info: 'CRNT.ExponentialDecay.LyapunovCertificate.norm_exp_smul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.ExponentialDecay.LyapunovCertificate.norm_exp_smul_le
/-- info: 'CRNT.Network.gac_of_deficiencyZero_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_deficiencyZero_decide

/-- info: 'CRNT.NetworkData.gac_of_persistenceCertified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.gac_of_persistenceCertified

/-- info: 'CRNT.Network.gac_of_singleLinkage_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_singleLinkage_decide

/-- info: 'CRNT.Network.isPMatrix_massActionJacobian_box_of_pointIndep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isPMatrix_massActionJacobian_box_of_pointIndep

/-- info: 'CRNT.tendsto_poissonAverage_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.tendsto_poissonAverage_atTop

/-- info: 'CRNT.Examples.ConservationClassRegion.conservationClass_cmeRegionVec_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.ConservationClassRegion.conservationClass_cmeRegionVec_tendsto
/-- info: 'ODE.fenichel_persistence_contracting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.fenichel_persistence_contracting

/-- info: 'ODE.slowManifold_reduction_conjugacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.slowManifold_reduction_conjugacy

/-- info: 'ODE.equilibrium_lift_of_baseEquilibrium' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.equilibrium_lift_of_baseEquilibrium

/-- info: 'ODE.invariantSet_lift_of_baseInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.invariantSet_lift_of_baseInvariant

/-- info: 'CRNT.Network.WeaklyReversible.toricMassActionField_isStrictSupportField_of_activeWalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.WeaklyReversible.toricMassActionField_isStrictSupportField_of_activeWalls

/-- info: 'CRNT.Stochastic.variance_id_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.variance_id_poissonMeasure

/-- info: 'CRNT.Stochastic.tendsto_meas_scaled_centered_poisson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.tendsto_meas_scaled_centered_poisson

/-- info: 'CRNT.Stochastic.variance_aggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.variance_aggregate

/-- info: 'CRNT.Stochastic.tendsto_meas_aggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.tendsto_meas_aggregate
/-- info: 'CRNT.eventually_localDegree_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.eventually_localDegree_eq

/-- info: 'CRNT.regularDegree_comp_continuousLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.regularDegree_comp_continuousLinearMap

/-- info: 'CRNT.Stochastic.indepFun_scaledClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.indepFun_scaledClock

/-- info: 'CRNT.Stochastic.variance_scaledClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.variance_scaledClock

/-- info: 'CRNT.Stochastic.variance_aggregate_scaledClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.variance_aggregate_scaledClock

/-- info: 'CRNT.Stochastic.tendsto_meas_aggregate_scaledClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.tendsto_meas_aggregate_scaledClock
/-- info: 'CRNT.eventually_regularDegree_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.eventually_regularDegree_eq

/-- info: 'CRNT.Stochastic.variance_centeredTimeChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.variance_centeredTimeChange

/-- info: 'CRNT.Stochastic.variance_aggregate_centeredTimeChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.variance_aggregate_centeredTimeChange

/-- info: 'CRNT.Stochastic.tendsto_meas_aggregate_centeredTimeChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.tendsto_meas_aggregate_centeredTimeChange

/-- info: 'CRNT.Stochastic.exists_timeChanged_fluct_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.exists_timeChanged_fluct_bound
/-- info: 'CRNT.eventually_confinement_of_isProperMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.eventually_confinement_of_isProperMap

/-- info: 'CRNT.eventually_regularDegree_eq_of_isProperMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.eventually_regularDegree_eq_of_isProperMap

/-- info: 'CRNT.isLocallyConstant_regularDegree_of_isProperMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.isLocallyConstant_regularDegree_of_isProperMap

/-- info: 'CRNT.regularDegree_param_eq_of_disjointCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.regularDegree_param_eq_of_disjointCover

/-- info: 'CRNT.regularDegree_homotopy_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.regularDegree_homotopy_invariant
/-- info: 'ODE.tendsto_flow_difference_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.tendsto_flow_difference_quotient

/-- info: 'ODE.hasDerivAt_flow_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.hasDerivAt_flow_initial
/-- info: 'ODE.tendsto_dist_slowManifold_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.tendsto_dist_slowManifold_zero

/-- info: 'ODE.asymptoticStability_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.asymptoticStability_lift

/-- info: 'CRNT.Network.separatingConfinement_of_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.separatingConfinement_of_local

/-- info: 'CRNT.Network.separatingConfinement_of_persistentFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.separatingConfinement_of_persistentFrom

/-- info: 'CRNT.Network.persistentFrom_of_omegaLimit_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.persistentFrom_of_omegaLimit_singleton

/-- info: 'CRNT.Network.persistentFrom_of_hasNoCriticalSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.persistentFrom_of_hasNoCriticalSiphon

/-- info: 'CRNT.Network.separatingConfinement_of_hasNoCriticalSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.separatingConfinement_of_hasNoCriticalSiphon

/-- info: 'CRNT.Network.genuineOrbit_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.genuineOrbit_unique

/-- info: 'CRNT.IsPolyhedralFan.toricMassActionField_isStrictSupportField_of_inwardReactions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.IsPolyhedralFan.toricMassActionField_isStrictSupportField_of_inwardReactions

/-- info: 'CRNT.Network.gac_of_gacCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_gacCertificate

/-- info: 'CRNT.Network.gacCertificate_of_hasNoCriticalSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gacCertificate_of_hasNoCriticalSiphon

/-- info: 'CRNT.Network.omegaLimit_eq_singleton_of_comparableGrowthDescent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.omegaLimit_eq_singleton_of_comparableGrowthDescent

/-- info: 'CRNT.Network.siphonFacet_floor_of_nearFacet_dissipation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.siphonFacet_floor_of_nearFacet_dissipation

/-- info: 'CRNT.Network.computeNumTerminalSLC_eq_numTerminalSLC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.computeNumTerminalSLC_eq_numTerminalSLC

/-- info: 'CRNT.Network.numDiagonalDriveSpecies_eq_card_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.numDiagonalDriveSpecies_eq_card_iff

/-- info: 'CRNT.hopfBoundaryQ_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.hopfBoundaryQ_cast

/-- info: 'CRNT.Network.hopfBoundaryMarginQ_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hopfBoundaryMarginQ_cast

/-- info: 'CRNT.NetworkData.analyze_numTerminalSLC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.analyze_numTerminalSLC_eq

/-- info: 'CRNT.NetworkData.analyze_numDiagonalDriveSpecies_eq_card_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.analyze_numDiagonalDriveSpecies_eq_card_iff

/-- info: 'CRNT.NetworkData.analyze_hopfBoundaryMargin_eq_none_of_ne_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.analyze_hopfBoundaryMargin_eq_none_of_ne_three

/-- info: 'CRNT.measure_criticalValues_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.measure_criticalValues_eq_zero

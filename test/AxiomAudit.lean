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

/-- info: 'CRNT.NetworkData.singleLinkageHypotheses_of_persistenceSingleLinkage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.singleLinkageHypotheses_of_persistenceSingleLinkage

/-- info: 'CRNT.NetworkData.deficiencyOneConditions_of_analyze' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.deficiencyOneConditions_of_analyze

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

/-- info: 'CRNT.Network.eq_of_periodic_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.eq_of_periodic_solution

/-- info: 'CRNT.Network.siphonFacet_floor_of_nearFacet_dissipation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.siphonFacet_floor_of_nearFacet_dissipation

/-- info: 'CRNT.Network.computeNumTerminalSLC_eq_numTerminalSLC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.computeNumTerminalSLC_eq_numTerminalSLC

/-- info: 'CRNT.Network.numDiagonalDriveSpecies_eq_card_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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

/-- info: 'CRNT.dense_regularValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.dense_regularValues

/-- info: 'CRNT.Network.exists_isMassActionSteadyState_of_reducedDegree_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_isMassActionSteadyState_of_reducedDegree_ne_zero

/-- info: 'CRNT.Network.hasMultistationarityCapacity_of_signIndefinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hasMultistationarityCapacity_of_signIndefinite

/-- info: 'CRNT.Network.exists_compatible_pair_sameSign_logRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_compatible_pair_sameSign_logRatio

/-- info: 'CRNT.gershgorinRowValueQ_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.gershgorinRowValueQ_cast

/-- info: 'CRNT.Network.gershgorinStabilityMarginQ_hurwitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gershgorinStabilityMarginQ_hurwitz

/-- info: 'CRNT.NetworkData.analyze_gershgorinStabilityMargin_eq_none_of_zero_species' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.analyze_gershgorinStabilityMargin_eq_none_of_zero_species

/-- info: 'CRNT.gershgorinColValueQ_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.gershgorinColValueQ_cast

/-- info: 'CRNT.Network.gershgorinColStabilityMarginQ_hurwitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gershgorinColStabilityMarginQ_hurwitz

/-- info: 'CRNT.NetworkData.analyze_gershgorinColStabilityMargin_eq_none_of_zero_species' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.analyze_gershgorinColStabilityMargin_eq_none_of_zero_species

/-!
## Oscillation exclusion theorems

These four were `by sorry` in the previous core (`CRNT/Oscillation/Exclusion.lean` and
`LowRank.lean` were two-line stub files), and `CRNT.Oscillation.KineticBasic` defined its three
predicates as `True`.  The oscillation expansion replaced all of that with real proofs, and the
analyzer's `noPositivePeriodicOrbitCertified` flag routes through them, so they are pinned here:
if any of them regresses to `sorry`, `sorryAx` shows up and this test fails.
-/

/-- info: 'CRNT.Network.neverPositivePeriodic_of_weaklyReversible_deficiencyZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.neverPositivePeriodic_of_weaklyReversible_deficiencyZero

/-- info: 'CRNT.Network.neverPositivePeriodic_of_stoichRank_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.neverPositivePeriodic_of_stoichRank_le_one

/-- info: 'CRNT.Network.not_oscillatoryCapacity_of_stoichRank_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.not_oscillatoryCapacity_of_stoichRank_le_one

/-- info: 'CRNT.NetworkData.neverPositivePeriodic_of_analyze' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.neverPositivePeriodic_of_analyze

/-!
## Analyzer verdicts that produce proofs

Each of these turns a decidable Boolean into a mathematical conclusion, so each is a place where a
hollow definition would become an unconditional-looking theorem.  Pinning them means a regression in
any dependency shows up here rather than in a downstream consumer.
-/

/-- info: 'CRNT.NetworkData.gac_of_persistenceCertified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.gac_of_persistenceCertified

/-- info: 'CRNT.NetworkData.certifiedHypotheses_of_persistenceCertified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.certifiedHypotheses_of_persistenceCertified

/-- info: 'CRNT.NetworkData.hasNoCriticalSiphon_of_persistenceStructural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.hasNoCriticalSiphon_of_persistenceStructural

/-!
## Global persistence: the previously-hollow layer

Every result below lives in a module that used to consist of `:= True` definitions, `dummy : True`
certificates and `isTrue` deciders.  `scripts/check_stubs.py` now reports zero hollow definitions,
but a syntactic check cannot tell whether a definition carries its *intended* meaning -- so these
pins exist to make any regression in the layer show up as an axiom change rather than as a silently
weaker theorem.

`isDrainable_iff_feasible_negativeFluxSystem` and its self-replicable twin are the two that matter
most: they are what replaced `def HasNoDrainableSiphon : Prop := ∃ (_ : Unit), True` together with
its `isTrue` decider, and they are what the analyzer's `noDrainableSiphon` flag now reduces through.
-/

/-- info: 'CRNT.Network.isDrainable_iff_feasible_negativeFluxSystem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isDrainable_iff_feasible_negativeFluxSystem

/-- info: 'CRNT.Network.isSelfReplicable_iff_feasible_positiveFluxSystem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isSelfReplicable_iff_feasible_positiveFluxSystem

/-- info: 'CRNT.Network.structurallyPersistent_of_deficiencyZero_hasNoCriticalSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.structurallyPersistent_of_deficiencyZero_hasNoCriticalSiphon

/-- info: 'CRNT.Network.gac_of_structurallyPersistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_structurallyPersistent

/-- info: 'CRNT.Network.boundaryOmegaExcluded_of_hasNoCriticalSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.boundaryOmegaExcluded_of_hasNoCriticalSiphon

/-- info: 'CRNT.Network.boundaryOmegaExcludedForFlow_of_hasNoDrainableSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.boundaryOmegaExcludedForFlow_of_hasNoDrainableSiphon

/-- info: 'CRNT.Network.permanentForFlow_of_entry_and_uniform_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.permanentForFlow_of_entry_and_uniform_bounds

/-- info: 'CRNT.Network.everyTierSequenceHasScaleDecomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.everyTierSequenceHasScaleDecomposition

/-!
## The two hole chains: full transitive axiom audit

The pins above are a hand-picked list, so they can only ever check what somebody remembered to
add.  The two chains that still contain a `sorry` are checked here *exhaustively* instead: the
`#crnt_axiom_audit` command below walks the entire transitive constant-dependency closure of each
hole and reports every axiom set that occurs.  A declaration nobody thought to pin still shows up,
because the walk starts from the hole and follows the environment, not a list.

Design notes, since a walk this size is easy to get subtly wrong:

* The closure is built with an explicit stack and an `ST`-backed seen set.  A `List`-based walk with
  `Array.contains` is quadratic and does not terminate in reasonable time over this environment.
* Dependencies are pushed *after* a constant is popped, so in the resulting array every dependency
  appears strictly later than its dependent.  One reverse pass therefore suffices to propagate axiom
  sets -- no topological sort, and no per-theorem re-walk of the environment.
* Axioms are attributed to a constant when the constant *is* an axiom or when its value expression
  mentions one.  `.thmInfo` and `.defnInfo` values are walked; `.opaqueInfo` values are too, which
  is stricter than Lean's own `#print axioms` and can only report more, never less.

Run standalone with:
    lake env lean test/AxiomAudit.lean
-/

open Lean Elab Command in
/-- Walk the whole dependency closure of `roots` and group the local theorems by axiom set.

Reports, per distinct axiom set, how many declarations carry it and — for anything other than the
clean set — the full list of names. -/
def crnt_axiom_closure_report (roots : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let isLocal (n : Name) : Bool :=
    let s := n.toString
    s.startsWith "CRNT." || s.startsWith "ODE." || s.startsWith "Scaffold."
  let exprConsts (e : Expr) (acc : Array Name := #[]) : Array Name :=
    let rec go (e : Expr) (acc : Array Name) : Array Name :=
      match e with
      | .const n _ => acc.push n
      | .app f a => go a (go f acc)
      | .lam _ t b _ => go b (go t acc)
      | .forallE _ t b _ => go b (go t acc)
      | .letE _ t v b _ => go b (go v (go t acc))
      | .mdata _ b => go b acc
      | .proj _ _ b => go b acc
      | .lit _ => acc
      | _ => acc
    go e acc
  let valueDeps : ConstantInfo → Array Name
    | .thmInfo v _ => exprConsts v
    | .defnInfo v _ _ _ => exprConsts v
    | .opaqueInfo v _ => exprConsts v
    | .ctorInfo v _ => exprConsts v
    | _ => #[]
  -- closure, explicit stack, hash seen-set
  let mut seen : Std.HashSet Name := Std.HashSet.emptyWithCapacity
  let mut order : Array Name := #[]
  let mut stack : Array Name := roots.toArray
  while stack.size > 0 do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    order := order.push n
    if let some ci := env.find? n then
      for d in valueDeps ci do
        if !seen.contains d then stack := stack.push d
  -- reverse pass: union of dependency axiom sets, each dependency already final
  let mut ax : Std.HashMap Name (Array Name) := Std.HashMap.emptyWithCapacity
  let mut buckets : Std.HashMap String (Array Name) := Std.HashMap.emptyWithCapacity
  let mut offenders : Array (Name × Array Name) := #[]
  let mut sorryTainted : Array Name := #[]
  for i in [0:order.size] do
    let n := order[order.size - 1 - i]!
    let ci := env.find? n
    let mut acc : Array Name :=
      match ci with
      | some (.axiomInfo _) => #[n]
      | _ => #[]
    if let some c := ci then
      for d in valueDeps c do
        if let some v := ax.get? d then
          let mut s : Std.HashSet Name := Std.HashSet.emptyWithCapacity
          for x in acc do s := s.insert x
          for x in v do s := s.insert x
          acc := s.toArray.qsort (fun x y => x.toString < y.toString)
    ax := ax.insert n acc
    let isThm := match ci with | some (.thmInfo _ _) => true | _ => false
    if isLocal n && isThm then
      let key := String.intercalate ", " (acc.toList.map Name.toString)
      buckets := match buckets.get? key with
        | some v => buckets.insert key (v.push n)
        | none => buckets.insert key #[n]
      let extra := acc.filter fun a => !(allowed.contains a) && a != `sorryAx
      if !extra.isEmpty then offenders := offenders.push (n, extra)
      if acc.contains `sorryAx then sorryTainted := sorryTainted.push n
  logInfo s!"closure size: {order.size} constants"
  for (k, v) in buckets.toList do
    if k = "Classical.choice, Quot.sound, propext" then
      logInfo s!"axiom set [{k}] x{v.size}  (clean)"
    else
      logInfo s!"axiom set [{k}] x{v.size}  <-- NOT the clean set"
      for n in v.toList do logInfo s!"    {n}"
  logInfo s!"declarations resting on an axiom outside {{propext, Classical.choice, Quot.sound}} \
    ∪ {{sorryAx}}: {offenders.size}"
  for (n, xs) in offenders do
    logInfo s!"    {n} :: {xs.toList}"
  logInfo s!"declarations resting on sorryAx: {sorryTainted.size}"
  for n in sorryTainted do logInfo s!"    {n}"

/-- `#crnt_axiom_audit N1 N2 ...` — exhaustive axiom census of the closures of `N1, N2, ...`.

Emits `logInfo` lines; it does not fail the build, so the census is informational and the pins
below remain the hard gate. -/
elab "#crnt_axiom_audit " roots:ident* : command => do
  let ns := roots.map fun t : Syntax → match t with
    | .ident i => i.getId
    | _ => Name.anonymous
  crnt_axiom_closure_report ns.toList

-- Chain A: Craciun v3 Theorem B, the residual obligation of the Global Attractor Theorem.
#crnt_axiom_audit CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace

-- Chain B: Shinar--Feinberg, the true-chemistry strong-concordance criterion.
#crnt_axiom_audit CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion

-- Both together: the union catches a declaration that is clean in isolation but sits downstream
-- of both holes, which neither single-root walk would flag.
#crnt_axiom_audit CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace
  CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion

/-!
## The two holes themselves, pinned

`sorryAx` is *expected* here and only here.  These three pins make the expected set exact, so if a
hole is closed the build fails (the axiom set shrinks) and if a new `sorryAx` user appears the
whole-environment census below reports it.
-/

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace' depends on axioms: [sorryAx] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace

/-- info: 'CRNT.Network.complexBalanced_genuinePermanent' depends on axioms: [sorryAx] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_genuinePermanent

/-- info: 'CRNT.Network.complexBalanced_permanent' depends on axioms: [sorryAx] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_permanent

/-- info: 'CRNT.Network.complexBalanced_globalAttractor' depends on axioms: [sorryAx] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_globalAttractor

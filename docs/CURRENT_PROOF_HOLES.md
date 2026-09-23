# Current Proof Holes — machine generated 2026-09-20

```text
total sorries: 28
keyword-'major': 12
distinct declarations with a sorry: 28

====================================================================================================
CRNT.Multistationarity.ConcordanceConverse:78  [theorem realize_concordanceWitness]
theorem realize_concordanceWitness
    (N : Network S) {α : N.R → ℝ} {σ : S → ℝ}
    (W : N.ConcordanceWitness α σ) :
    Nonempty (N.ConcordanceKineticsRealization α σ W)
====================================================================================================
CRNT.Multistationarity.Normality:307  [theorem concordant_of_fullyOpen_concordant_of_normal]
theorem concordant_of_fullyOpen_concordant_of_normal (N : Network S)
    (hnormal : N.Normal) (hopen : N.fullyOpen.Concordant) :
    N.Concordant
====================================================================================================
CRNT.Multistationarity.StrongConcordance:279  [theorem stronglyConcordant_of_fullyOpen_of_weaklyNormal]
theorem stronglyConcordant_of_fullyOpen_of_weaklyNormal
    (N : Network S) (hwn : N.WeaklyNormal)
    (hopen : N.fullyOpen.StronglyConcordant) : N.StronglyConcordant
====================================================================================================
CRNT.Multistationarity.TrueChemistrySRCriterion:29  [theorem fullyOpen_trueSRCriterion_iff]
theorem fullyOpen_trueSRCriterion_iff (N : Network S) :
    N.fullyOpen.TrueSRStrongCriterion ↔ N.TrueSRStrongCriterion
====================================================================================================
CRNT.Multistationarity.TrueChemistrySRCriterion:38  [theorem stronglyConcordant_fullyOpen_of_trueSRCriterion]
theorem stronglyConcordant_fullyOpen_of_trueSRCriterion
    (N : Network S) (hSR : N.TrueSRStrongCriterion) :
    N.fullyOpen.StronglyConcordant
====================================================================================================
CRNT.Multistationarity.WeakNormality:431  [theorem concordant_of_fullyOpen_concordant_of_weaklyNormal]
theorem concordant_of_fullyOpen_concordant_of_weaklyNormal (N : Network S)
    (hwn : N.WeaklyNormal) (hopen : N.fullyOpen.Concordant) :
    N.Concordant
====================================================================================================
CRNT.Multistationarity.WeakNormalityCriterion:102  [theorem weaklyNormal_of_minorCertificate]
theorem weaklyNormal_of_minorCertificate
    (N : Network S) {I : Type} [Fintype I] [DecidableEq I]
    (C : N.WeakNormalMinorCertificate I) : N.WeaklyNormal
====================================================================================================
CRNT.Multistationarity.WeakNormalityCriterion:153  [theorem normal_of_sourceMinorCertificate]
theorem normal_of_sourceMinorCertificate
    (N : Network S) {I : Type} [Fintype I] [DecidableEq I]
    (C : N.SourceMinorCertificate I) : N.Normal
====================================================================================================
CRNT.Theorems.DeficiencyOne.DegreeExistence:91  [theorem exists_zero_of_deficiencyOneDegreeCertificate]
theorem exists_zero_of_deficiencyOneDegreeCertificate
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (C : N.DeficiencyOneDegreeCertificate κ x₀)
    (href : C.reference_localDegree_nonzero) :
    ∃ u ∈ C.domain.U, N.reducedMassActionField κ x₀ u = 0
====================================================================================================
CRNT.Theorems.DeficiencyOne.DegreeExistence:103  [theorem exists_deficiencyOneDegreeCertificate]
theorem exists_deficiencyOneDegreeCertificate
    (N : Network S) (h : N.DeficiencyOneHypotheses) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ C : N.DeficiencyOneDegreeCertificate κ x₀,
      C.reference_localDegree_nonzero
====================================================================================================
CRNT.Theorems.DeficiencyOne.Theorem:60  [theorem deficiencyOne_jacobianOnStoich_injective]
theorem deficiencyOne_jacobianOnStoich_injective
    (N : Network S) (h : N.DeficiencyOneHypotheses)
    (κ : N.RateConstants) {x : Concentration S}
    (hx : x.Positive) (hss : N.IsMassActionSteadyState κ x) :
    Function.Injective (N.massActionJacobianOnStoich κ x)
====================================================================================================
CRNT.Theorems.DeficiencyOne.Theorem:125  [theorem deficiencyOne_existsUnique_every_class_of_exists_positive]
theorem deficiencyOne_existsUnique_every_class_of_exists_positive
    (N : Network S) (h : N.DeficiencyOneHypotheses)
    (κ : N.RateConstants)
    (hex : ∃ x : Concentration S, x.Positive ∧ N.IsMassActionSteadyState κ x) :
    ∀ x₀ : Concentration S, x₀.Positive →
      ∃! x : Concentration S,
        x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x
====================================================================================================
CRNT.Theorems.DeficiencyOne.WeaklyReversibleExistence:34  [theorem weaklyReversible_deficiencyOne_exists_positive_steadyState]
theorem weaklyReversible_deficiencyOne_exists_positive_steadyState
    (N : Network S) (hwr : N.WeaklyReversible) (hδ : N.DeficiencyOne)
    (κ : N.RateConstants) (x₀ : Concentration S) (hx₀ : x₀.Positive) :
    ∃ x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x
====================================================================================================
CRNT.Dynamics.GlobalAttractorTheorem:60  [theorem complexBalanced_permanent]
theorem complexBalanced_permanent
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.PermanentForRates κ
====================================================================================================
CRNT.Dynamics.GlobalAttractorTheorem:76  [theorem complexBalanced_globalAttractor]
theorem complexBalanced_globalAttractor
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.HasGlobalAttractorProperty κ xstar
====================================================================================================
CRNT.Dynamics.GlobalAttractorTheorem:104  [theorem complexBalanced_trajectory_converges]
theorem complexBalanced_trajectory_converges
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.PositiveClassTrajectoryConverges κ xstar
====================================================================================================
CRNT.Stochastic.BirthDeathExhaustive:121  [theorem countLatticeIrreducible_of_birth_death_fullLattice]
theorem countLatticeIrreducible_of_birth_death_fullLattice
    (N : Network S)
    (hbirth : N.BirthExhaustive)
    (hdeath : N.DeathExhaustive)
    (hlattice : N.GeneratesFullIntegerLattice)
    (hfull : N.stoichSubspace = ⊤) :
    N.CountLatticeIrreducible
====================================================================================================
CRNT.Translation.DeficiencyImprovement:58  [theorem exists_originalSteadyState_via_translation]
theorem exists_originalSteadyState_via_translation
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (H : T.DeficiencyZeroResolution K κ)
    (hclosure : OrientedMatroidConditions.ClosureCondition
      T.network.stoichSubspace T.generalizedData.kineticOrderSubspace)
    (hface : OrientedMatroidConditions.FaceCondition
      T.network.stoichSubspace T.generalizedData.kineticOrderSubspace)
    {x₀ : Concentration S} (hx₀ : x₀.Positive)
    (hclass : N.positiveCompatibilityClass x₀ ⊆ H.resolutionSet)
    (hcompat : T.network.stoichSubspace = N.stoichSubspace) :
    ∃ x ∈ N.positiveCompatibilityClass x₀, N.IsMassActionSteadyState κ x
====================================================================================================
CRNT.Equilibria.ComplexBalanceLinearStability:207  [theorem complexBalanceJacobianQuadratic_eq_secondVariation]
theorem complexBalanceJacobianQuadratic_eq_secondVariation
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (h : Concentration S) :
    N.complexBalanceJacobianQuadratic κ xstar h =
      deriv (fun t =>
        ∑ s : S,
          (Real.log (xstar s + t * h s) - Real.log (xstar s)) *
            N.massActionVectorField κ (fun j => xstar j + t * h j) s) 0
====================================================================================================
CRNT.Equilibria.ComplexBalanceLinearStability:460  [theorem complexBalanced_locallyExponentiallyStable_in_class]
theorem complexBalanced_locallyExponentiallyStable_in_class
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.LocallyExponentiallyStableInClass κ xstar
====================================================================================================
CRNT.Equilibria.DirectedMatrixTreeProof:54  [theorem cycleFree_iff_arborescence]
theorem cycleFree_iff_arborescence
    (F : N.FunctionalReactionSelection root) :
    ¬ F.HasDirectedCycle ↔ N.IsRootedInArborescence root F.selected
====================================================================================================
CRNT.Equilibria.DirectedMatrixTreeProof:108  [theorem kineticCofactor_eq_sum_expandedTerms]
theorem kineticCofactor_eq_sum_expandedTerms
    (N : Network S) (κ : N.RateConstants) (root : N.ComplexIdx) :
    N.kineticCofactor κ root =
      ∑ t : N.ExpandedCofactorTerm root, t.value κ
====================================================================================================
CRNT.Equilibria.DirectedMatrixTreeProof:122  [theorem exists_cycleCancellationInvolution]
theorem exists_cycleCancellationInvolution
    (N : Network S) (root : N.ComplexIdx) :
    ∃ f : {t : N.ExpandedCofactorTerm root // t.selection.HasDirectedCycle} →
          {t : N.ExpandedCofactorTerm root // t.selection.HasDirectedCycle},
      Function.Involutive f ∧
      (∀ t, f t ≠ t) ∧
      (∀ (κ : N.RateConstants) t, (f t).1.value κ = -t.1.value κ)
====================================================================================================
CRNT.Equilibria.DirectedMatrixTreeProof:156  [theorem sum_cycleTerms_eq_zero]
theorem sum_cycleTerms_eq_zero
    (N : Network S) (κ : N.RateConstants) (root : N.ComplexIdx) :
    (∑ t : {t : N.ExpandedCofactorTerm root // t.selection.HasDirectedCycle},
      t.1.value κ) = 0
====================================================================================================
CRNT.Equilibria.DirectedMatrixTreeProof:166  [theorem cycleFreeTerm_eq_treeWeight]
theorem cycleFreeTerm_eq_treeWeight
    (N : Network S) (κ : N.RateConstants) (root : N.ComplexIdx)
    (t : N.ExpandedCofactorTerm root)
    (hfree : ¬ t.selection.HasDirectedCycle) :
    t.value κ = N.treeWeight κ t.selection.selected
====================================================================================================
CRNT.Equilibria.DirectedMatrixTreeProof:175  [theorem kineticCofactor_eq_treeConstant_combinatorial]
theorem kineticCofactor_eq_treeConstant_combinatorial
    (N : Network S) (κ : N.RateConstants) (root : N.ComplexIdx) :
    N.kineticCofactor κ root = N.treeConstant κ root
====================================================================================================
CRNT.Equilibria.MatrixTreeCofactor:101  [theorem kineticCofactor_eq_treeConstant]
theorem kineticCofactor_eq_treeConstant (N : Network S) (κ : N.RateConstants)
    (root : N.ComplexIdx) :
    N.kineticCofactor κ root = N.treeConstant κ root
====================================================================================================
CRNT.Kinetics.GeneralizedBirchExistence:87  [theorem generalized_birch_existence_of_conditions]
theorem generalized_birch_existence_of_conditions
    (S T : Submodule ℝ (ι → ℝ))
    (hclosure : GeneralizedClosureCondition S T)
    (hface : GeneralizedFaceCondition S T) :
    GeneralizedBirchSurjective S T

```

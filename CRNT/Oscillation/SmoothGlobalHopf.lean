import CRNT.Oscillation.GlobalHopfIndexTheorem
import CRNT.Oscillation.SpectralOpenness

/-!
# Smooth global Hopf by analytic approximation

The parameter-rich CRN interfaces promise a `C∞` parameter/state vector field, whereas the Fiedler
kernel is formulated analytically.  This file bridges the two without strengthening the kinetics
API.  A Whitney--Carleman analytic approximation is taken relative to the equilibrium branch so
that the branch remains fixed.  Uniform `C¹` approximation on a compact tube preserves:

* the Hurwitz endpoint;
* the strict unstable endpoint;
* nonsingularity on the compact parameter interval;
* positivity of the equilibrium branch.

The analytic global-Hopf theorem is applied to each approximation.  Arzelà--Ascoli/ODE compactness
then sends a sequence of nonstationary periodic solutions back to the original smooth family.
-/

namespace CRNT

open Set Filter Topology

/-- Smooth continuation restricted to the physical parameter interval. -/
structure SmoothGlobalHopfData
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) : Type where
  /-- Uniform nonsingularity margin on `[0,1]`. -/
  detMargin : ℝ
  detMargin_pos : 0 < detMargin
  det_lower : ∀ μ ∈ Set.Icc (0 : ℝ) 1, detMargin ≤ |(C.jacobian μ).det|
  /-- Positive equilibrium margin on the compact branch. -/
  positiveMargin : ℝ
  positiveMargin_pos : 0 < positiveMargin
  equilibrium_lower : ∀ μ ∈ Set.Icc (0 : ℝ) 1, ∀ i,
    positiveMargin ≤ C.equilibrium μ i

/-- Compactness of `[0,1]` turns pointwise nonsingularity and positivity into uniform margins. -/
theorem SmoothEquilibriumContinuation.globalHopfData
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) : Nonempty (SmoothGlobalHopfData C) := by
  classical
  let fdet : ℝ → ℝ := fun μ => |(C.jacobian μ).det|
  have hdetcont : Continuous fdet :=
    (continuous_abs.comp (Matrix.continuous_det.comp C.jacobianContinuous))
  obtain ⟨δ, hδpos, hδ⟩ :=
    exists_pos_lower_bound_on_compact_of_continuous_ne_zero
      isCompact_Icc hdetcont (fun μ hμ => abs_pos.mpr (C.nonsingular μ))
  let feq : Set.Icc (0 : ℝ) 1 × I → ℝ := fun p => C.equilibrium p.1 p.2
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set I)) :=
    isCompact_Icc.prod isCompact_univ
  have hpos : ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set I), 0 < feq p := by
    intro p hp
    exact C.equilibriumPositive p.1 hp.1 p.2
  obtain ⟨η, hηpos, hη⟩ :=
    exists_pos_lower_bound_on_compact_of_continuous_pos
      hcompact (C.equilibriumSmooth.continuous.comp continuous_fst |>.apply_finite) hpos
  exact ⟨{
    detMargin := δ
    detMargin_pos := hδpos
    det_lower := hδ
    positiveMargin := η
    positiveMargin_pos := hηpos
    equilibrium_lower := by
      intro μ hμ i
      exact hη (μ, i) ⟨hμ, Set.mem_univ i⟩ }⟩

/-- Analytic approximation that fixes the equilibrium branch exactly. -/
structure RelativeAnalyticApproximation
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) (ε : ℝ) : Type where
  continuation : AnalyticEquilibriumContinuation I
  equilibrium_eq : continuation.equilibrium = C.equilibrium
  field_C1_close :
    CRNT.C1DistanceOnPhysicalTube continuation.field C.field ≤ |ε|
  jacobian_close :
    CRNT.MatrixSupDistanceOnIcc continuation.jacobian C.jacobian ≤ |ε|

/-- Whitney analytic approximation relative to the smooth zero-set/equilibrium graph. -/
theorem exists_relativeAnalyticApproximation
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Nonempty (RelativeAnalyticApproximation C ε) := by
  exact CRNT.real_analytic_approximation_relative_to_equilibrium_graph
    C.fieldSmooth C.equilibriumSmooth C.steady C.hasFDerivAt_equilibrium

/-- For sufficiently close analytic approximations all Fiedler hypotheses persist. -/
theorem eventually_analyticApproximation_preserves_hopf_data
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) (H : SmoothGlobalHopfData C) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ A : RelativeAnalyticApproximation C ε,
        A.continuation.toSmoothEquilibriumContinuation.stableAtZero.IsTrue ∧
        A.continuation.toSmoothEquilibriumContinuation.unstableAtOne.IsTrue ∧
        (∀ μ, A.continuation.jacobian μ |>.det ≠ 0) := by
  have hstableOpen := Matrix.hurwitz_open_at C.jacobianContinuous C.stableAtZero
  have hunstableOpen := Matrix.strict_rhp_eigenvalue_open_at
    C.jacobianContinuous C.unstableAtOne
  have hnonsingOpen := Matrix.uniform_nonsingular_open_on_Icc
    C.jacobianContinuous H.detMargin_pos H.det_lower
  filter_upwards [eventually_abs_lt_pos H.detMargin_pos,
    hstableOpen, hunstableOpen, hnonsingOpen] with ε hε hs hu hn A
  exact ⟨hs A.jacobian_close, hu A.jacobian_close, hn A.jacobian_close⟩

/-- Analytic approximants admit positive periodic witnesses. -/
theorem eventually_periodic_analyticApproximation
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) (H : SmoothGlobalHopfData C) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ A : RelativeAnalyticApproximation C ε,
        Nonempty (PositiveContinuationPeriodicWitness
          A.continuation.toSmoothEquilibriumContinuation) := by
  have happ := eventually_analyticApproximation_preserves_hopf_data C H
  filter_upwards [happ] with ε hε A
  let A' : AnalyticEquilibriumContinuation I :=
    CRNT.replaceAnalyticContinuationSpectralProofs A.continuation hε.1 hε.2.1 hε.2.2
  exact analyticGlobalHopfIndex I A' A'.indexData

/-- Periodic witnesses of arbitrarily close analytic approximants compactly converge to a
nonstationary periodic witness of the original smooth family. -/
theorem periodicWitness_of_smooth_analyticApproximation
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) (H : SmoothGlobalHopfData C) :
    Nonempty (PositiveContinuationPeriodicWitness C) := by
  have happ := exists_relativeAnalyticApproximation C
  have hper := eventually_periodic_analyticApproximation C H
  exact CRNT.periodic_orbit_compactness_under_C1_analytic_approximation
    C H.positiveMargin_pos H.equilibrium_lower happ hper

/-- **Smooth global-Hopf theorem.** This is the form consumed by the parameter-rich kinetic routes. -/
theorem smoothGlobalHopf
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) :
    Nonempty (PositiveContinuationPeriodicWitness C) := by
  obtain ⟨H⟩ := C.globalHopfData
  exact periodicWitness_of_smooth_analyticApproximation C H

end CRNT

namespace CRNT

/-- A periodic witness controlled in distance from the equilibrium branch.  This is the correct
coordinate-free output for reduced stoichiometric dynamics. -/
structure LocalContinuationPeriodicWitness
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) (radius : ℝ) : Type where
  parameter : ℝ
  parameter_mem : parameter ∈ Set.Icc (0 : ℝ) 1
  trajectory : PeriodicTrajectory (C.field parameter)
  close : ∀ t, ‖trajectory.orbit t - C.equilibrium parameter‖ < radius

/-- The index proof can choose a periodic solution in an arbitrarily small neighbourhood of a
nonzero-index center component.  This is the local form needed after coordinate reduction. -/
theorem smoothGlobalHopf_local
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I)
    {radius : ℝ} (hr : 0 < radius) :
    Nonempty (LocalContinuationPeriodicWitness C radius) := by
  obtain ⟨H⟩ := C.globalHopfData
  have hcenter := C.hopfCenterSet_inter_Icc_nonempty
  obtain ⟨μ, hμcenter, hμI⟩ := hcenter
  -- Apply the phase-fixed local Hopf degree on a cylinder of radius `< radius`; if the first
  -- center is degenerate, use the relative analytic perturbations from the smooth theorem and
  -- pass the small cycles to the limit.
  exact CRNT.local_periodic_witness_of_nonzero_spectral_flow
    C μ hμcenter hμI hr H.detMargin_pos H.det_lower

end CRNT

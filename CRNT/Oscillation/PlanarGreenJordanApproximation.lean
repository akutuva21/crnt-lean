import CRNT.Oscillation.PlanarGreenGrid
import CRNT.Oscillation.GreenJordanFoundations

/-!
# Approximation route from finite Green domains to Jordan domains

The analytic Green identity is already proved on finite rectilinear complexes.  To pass to a smooth
Jordan domain it suffices to approximate its interior by finite complexes such that

1. indicators of the complex carriers converge in measure/L1 to the Jordan interior;
2. exterior-edge flux converges to the flux of the oriented Jordan boundary.

The first convergence is measure-theoretic.  The second is geometric and uses the C1 boundary.
This file packages those limits and proves Green's theorem by passing to the limit.
-/

namespace CRNT
namespace Planar

open Set Filter MeasureTheory

/-- Rectilinear approximations to one periodic Jordan interior. -/
structure JordanGridApproximation
    {field : Phase2 → Phase2} (P : PeriodicTrajectory field)
    (J : PeriodicJordanInterior P) : Type where
  grid : ℕ → RectCellComplex
  carrier_subset : ∀ n, (grid n).carrier ⊆ J.interior
  exhaust_ae : Tendsto
    (fun n => volume (J.interior \ (grid n).carrier)) atTop (𝓝 0)
  /-- Orientation of the displayed ODE traversal relative to the positively oriented cell boundary. -/
  orientation : ℝ
  orientation_sq : orientation ^ 2 = 1
  /-- Boundary-current convergence.  Cell-complex boundaries use positive orientation, so a clockwise
  ODE traversal contributes the factor `orientation = -1`. -/
  boundaryCurrentConverges :
    ∀ G : Phase2 → Phase2, ContDiffOn ℝ 1 G (closure J.interior) →
      Tendsto (fun n => (grid n).boundaryFlux G) atTop
        (𝓝 (orientation * periodBoundaryFlux G P))

/-- Area integrals of a continuous integrable function converge along an exhausting inner grid. -/
theorem integral_grid_tendsto_interior
    {field : Phase2 → Phase2} {P : PeriodicTrajectory field}
    {J : PeriodicJordanInterior P}
    (A : JordanGridApproximation P J)
    {g : Phase2 → ℝ}
    (hcont : ContinuousOn g (closure J.interior))
    (hint : IntegrableOn g J.interior) :
    Tendsto (fun n => ∫ x in (A.grid n).carrier, g x) atTop
      (𝓝 (∫ x in J.interior, g x)) := by
  apply tendsto_setIntegral_of_measure_symmDiff_tendsto_zero
  · exact hint
  · intro n
    exact A.carrier_subset n
  · simpa [Set.symmDiff_of_subset (A.carrier_subset _)] using A.exhaust_ae
  · exact hcont.aestronglyMeasurable.restrict

/-- **Green on a Jordan interior from grid approximation.** -/
theorem periodicGreenDivergence_of_gridApproximation
    {field G : Phase2 → Phase2} {P : PeriodicTrajectory field}
    (J : PeriodicJordanInterior P)
    (A : JordanGridApproximation P J)
    (hG : ContDiffOn ℝ 1 G (closure J.interior)) :
    periodBoundaryFlux G P = A.orientation *
      (∫ x in J.interior, divergence G x) := by
  have hdivCont : ContinuousOn (divergence G) (closure J.interior) :=
    continuousOn_divergence_of_contDiffOn_closure hG
  have hdivInt : IntegrableOn (divergence G) J.interior :=
    integrableOn_divergence_of_bounded
      (J.open_interior) (hG.mono (subset_trans subset_closure le_rfl))
      subset_rfl J.measurable J.bounded
  have harea := A.integral_grid_tendsto_interior hdivCont hdivInt
  have hflux := A.boundaryCurrentConverges G hG
  have hgreen_n : ∀ n,
      (A.grid n).boundaryFlux G =
        ∫ x in (A.grid n).carrier, divergence G x := by
    intro n
    exact (A.grid n).boundaryFlux_eq_integral_divergence G
      (contDiff_of_contDiffOn_closure_extend hG)
      (hdivInt.mono_set (A.carrier_subset n))
  have hlim : A.orientation * periodBoundaryFlux G P =
      ∫ x in J.interior, divergence G x :=
    tendsto_nhds_unique hflux (harea.congr' (Filter.Eventually.of_forall hgreen_n).symm)
  have hsigma : A.orientation ≠ 0 := by
    intro h0
    have hfld := A.orientation_sq
    rw [h0, zero_pow (by norm_num)] at hfld
    norm_num at hfld
  calc
    periodBoundaryFlux G P
        = A.orientation * (A.orientation * periodBoundaryFlux G P) := by
            rw [← mul_assoc, ← pow_two, A.orientation_sq, one_mul]
    _ = A.orientation * (∫ x in J.interior, divergence G x) := by rw [hlim]

/-- Geometric approximation theorem for C1 periodic Jordan curves.  This is now the only missing
Green-specific geometry: construct inner finite rectilinear approximations with convergence of the
associated boundary currents. -/
def JordanGridApproximationTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (P : PeriodicTrajectory field)
    (J : PeriodicJordanInterior P),
    P.SimpleClosedCycle → Nonempty (JordanGridApproximation P J)

/-- Grid approximation proves the orientation-free Green identity.  The sign is `+1` because
`periodBoundaryFlux` follows the time orientation of `P`; if the Jordan interior chooses the
opposite positive boundary orientation the historical API absorbs that by `sigma=-1`. -/
theorem periodicGreenDivergence_of_gridTarget
    (hgrid : JordanGridApproximationTarget) :
    PeriodicGreenDivergenceTarget := by
  intro field G P J hG
  obtain ⟨A⟩ := hgrid field P J J.simple
  have h := periodicGreenDivergence_of_gridApproximation J A hG
  refine ⟨A.orientation, A.orientation_sq, ?_⟩
  exact h

end Planar
end CRNT

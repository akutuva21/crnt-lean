import CRNT.Oscillation.PlanarJordanDyadic
import CRNT.Oscillation.PlanarDivergenceRegularity

/-!
# Boundary-current convergence for C1 Jordan curves

`PlanarGreenRectangle` and `PlanarGreenGrid` already prove Green's theorem exactly on finite
rectilinear cell complexes.  `PlanarJordanDyadic` supplies canonical inner dyadic approximations
whose missed area tends to zero.  This file proves the remaining boundary-current convergence.

The proof is the classical polygonal-current approximation argument.  Uniform continuity of a C1
field on a compact neighbourhood of the Jordan closure controls the field error.  The C1 Jordan
parameterization is uniformly approximated in position and tangent by inscribed polygons.  The
positive boundary of the inner dyadic approximation differs from that polygon by finitely many
oppositely oriented grid edges; those cancel in the current.  The residual boundary is confined to
a vanishing tubular neighbourhood and has uniformly bounded total variation.  Consequently the
normal-flux current converges, with the orientation sign determined by the ODE traversal.
-/

namespace CRNT

-- `⟪x, y⟫_ℝ` lives in the `InnerProductSpace` scope; without this open the bracket is
-- not a valid token.
open scoped InnerProductSpace

namespace Planar

open Set Filter MeasureTheory

/-- Normal flux of a C1 parameterized curve on `[a,b]`. -/
def curveFlux (G : Phase2 → Phase2) (γ γ' : ℝ → Phase2) (a b : ℝ) : ℝ :=
  ∫ t in Set.uIcc a b, ⟪G (γ t), quarterTurn (γ' t)⟫_ℝ

/-- Uniform C1 approximation controls flux currents. -/
theorem curveFlux_tendsto_of_C1_uniform
    {G : Phase2 → Phase2} {γ γ' : ℝ → Phase2}
    {γn γn' : ℕ → ℝ → Phase2}
    {a b : ℝ}
    (hG : ContinuousOn G (compactTube (γ '' Set.uIcc a b)))
    (hγ : ContinuousOn γ (Set.uIcc a b))
    (hγ' : ContinuousOn γ' (Set.uIcc a b))
    (hpos : ∀ᶠ n in atTop, ∀ t ∈ Set.uIcc a b,
      γn n t ∈ compactTube (γ '' Set.uIcc a b))
    (hγconv : Tendsto (fun n => supNormOn (γn n - γ) (Set.uIcc a b)) atTop (𝓝 0))
    (hγ'conv : Tendsto (fun n => supNormOn (γn' n - γ') (Set.uIcc a b)) atTop (𝓝 0)) :
    Tendsto (fun n => curveFlux G (γn n) (γn' n) a b) atTop
      (𝓝 (curveFlux G γ γ' a b)) := by
  have hGunif := hG.uniformContinuousOn
  have hboundG := hG.isCompact_image.isBounded
  have hboundDeriv : Bornology.IsBounded (γ' '' Set.uIcc a b) :=
    (isCompact_uIcc.image_of_continuousOn hγ').isBounded
  apply tendsto_integral_of_uniform_integrand
  intro ε hε
  obtain ⟨δ, hδ, hGδ⟩ := hGunif ε hε
  filter_upwards [hpos,
    (Metric.tendsto_atTop.1 hγconv) δ hδ,
    (Metric.tendsto_atTop.1 hγ'conv) δ hδ] with n hn hclose hclose'
  intro t ht
  exact flux_integrand_close_of_position_derivative_close
    hGδ hboundG hboundDeriv hn ht hclose hclose'

/-- The least-period normalized periodic orbit is C1 and its derivative is the normalized vector
field tangent. -/
theorem normalizedLoop_hasDeriv
    {field : Phase2 → Phase2} (P : PeriodicTrajectory field) (s : ℝ) :
    HasDerivAt P.normalizedLoop
      (P.period • field (P.normalizedLoop s)) s := by
  simpa [PeriodicTrajectory.normalizedLoop] using
    (P.solution (s * P.period)).comp s (hasDerivAt_id s).mul_const P.period

/-- C1 simple cycles admit positively oriented polygonal approximations in current norm. -/
theorem exists_oriented_polygonal_current_approximation
    {field : Phase2 → Phase2} (P : PeriodicTrajectory field)
    (J : PeriodicJordanInterior P) (hsimple : P.SimpleClosedCycle) :
    ∃ (polygon : ℕ → RectifiableClosedPolygon),
      (∀ n, polygon n |>.trace ⊆ closure J.interior) ∧
      Tendsto (fun n => hausdorffDist (polygon n).trace P.orbitSet) atTop (𝓝 0) ∧
      ∃ σ : ℝ, σ ^ 2 = 1 ∧
        ∀ G, ContDiffOn ℝ 1 G (closure J.interior) →
          Tendsto (fun n => (polygon n).boundaryFlux G) atTop
            (𝓝 (σ * periodBoundaryFlux G P)) := by
  classical
  let γ := P.normalizedLoop
  let γ' : ℝ → Phase2 := fun s => P.period • field (γ s)
  have hC1 : ContDiffOn ℝ 1 γ (Set.Icc (0 : ℝ) 1) := by
    exact contDiffOn_of_hasDerivAt_continuous
      (fun s hs => P.normalizedLoop_hasDeriv s)
      ((P.solution.continuous.comp (continuous_id.mul continuous_const)).continuousOn)
  let mesh : ℕ → Finset ℝ := fun n => dyadicPartition (0 : ℝ) 1 n
  let polygon := fun n => inscribedPolygon γ (mesh n)
  have hmesh : Tendsto (fun n => meshSize (mesh n)) atTop (𝓝 0) := dyadic_mesh_tendsto_zero
  have htrace : ∀ n, (polygon n).trace ⊆ closure J.interior := by
    intro n
    exact convexHull_vertices_subset_closure_of_jordan J hsimple
      (inscribedPolygon_vertices_subset_range γ (mesh n))
  have hhaus : Tendsto (fun n => hausdorffDist (polygon n).trace P.orbitSet) atTop (𝓝 0) :=
    inscribedPolygon_hausdorff_tendsto hC1.continuousOn hmesh
  obtain ⟨σ, hσ, horient⟩ := jordan_orientation_sign P J hsimple
  refine ⟨polygon, htrace, hhaus, σ, hσ, ?_⟩
  intro G hG
  have hpolyC1 := inscribedPolygon_C1_current_tendsto γ γ' hC1 hmesh
  have hflux := curveFlux_tendsto_of_C1_uniform
    (G := G) (γ := γ) (γ' := γ') hG.continuousOn
    hC1.continuousOn (continuousOn_derivative_of_contDiffOn hC1)
    hpolyC1.eventually_in_tube hpolyC1.position hpolyC1.derivative
  simpa [periodBoundaryFlux, horient, curveFlux] using hflux

/-- Inner dyadic boundaries and a positively oriented inscribed polygon represent the same limiting
1-current.  Interior grid edges cancel exactly; the unmatched edges are confined to the shrinking
boundary tube. -/
theorem innerDyadic_boundary_current_matches_polygon
    {field : Phase2 → Phase2} (P : PeriodicTrajectory field)
    (J : PeriodicJordanInterior P) (hsimple : P.SimpleClosedCycle)
    (polygon : ℕ → RectifiableClosedPolygon)
    (hhaus : Tendsto (fun n => hausdorffDist (polygon n).trace P.orbitSet) atTop (𝓝 0)) :
    ∀ G : Phase2 → Phase2, ContDiffOn ℝ 1 G (closure J.interior) →
      Tendsto
        (fun n => (J.innerDyadicAreaApproximation n).boundaryFlux G -
          (polygon n).boundaryFlux G)
        atTop (𝓝 0) := by
  intro G hG
  have hGunif := hG.continuousOn.uniformContinuousOn
  have hvariation : ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      boundaryTotalVariation (J.innerDyadicAreaApproximation n) ≤ C :=
    jordan_inner_grid_uniform_perimeter_bound J hsimple
  obtain ⟨C, hC, hperim⟩ := hvariation
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := hGunif ε hε
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 hhaus δ hδ
  obtain ⟨N2, hN2⟩ := innerDyadic_boundary_tube_tendsto J δ hδ
  refine ⟨max N1 N2, ?_⟩
  intro n hn
  have hn1 := hN1 n (le_trans (le_max_left _ _) hn)
  have hn2 := hN2 n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq, sub_zero]
  exact abs_boundaryFlux_difference_le_of_tube_matching
    G hG hn1 hn2 (hperim n) hC hclose

/-- **Boundary-current convergence theorem for periodic C1 Jordan cycles.** -/
theorem jordanBoundaryCurrentConvergence : JordanBoundaryCurrentConvergenceTarget := by
  intro field P J hsimple
  obtain ⟨polygon, _hsubset, hhaus, σ, hσ, hpoly⟩ :=
    exists_oriented_polygonal_current_approximation P J hsimple
  refine ⟨σ, hσ, ?_⟩
  intro G hG
  have hdiff := innerDyadic_boundary_current_matches_polygon P J hsimple polygon hhaus G hG
  have hpolyG := hpoly G hG
  exact tendsto_of_tendsto_sub_zero hdiff hpolyG

/-- Hence the full Jordan-grid approximation theorem is internal. -/
theorem jordanGridApproximation_proved : JordanGridApproximationTarget :=
  jordanGridApproximation_of_boundaryCurrent jordanBoundaryCurrentConvergence

end Planar
end CRNT

import CRNT.Oscillation.PlanarGreenJordanApproximation

/-!
# Dyadic inner exhaustion of bounded planar Jordan domains

Every bounded open set of finite planar measure can be exhausted from inside by finitely many dyadic
squares whose closures lie in the set.  This closes the measure/area half of the Jordan approximation
used by Green's theorem.  No regularity of the boundary is needed here.
-/

namespace CRNT
namespace Planar

open Set Filter MeasureTheory

/-- Closed dyadic square at scale `n` and integer lattice coordinate `(i,j)`. -/
def dyadicSquare (n : ℕ) (i j : ℤ) : AxisRectangle where
  x0 := i * (2 : ℝ) ^ (-(n : ℤ))
  x1 := (i+1) * (2 : ℝ) ^ (-(n : ℤ))
  y0 := j * (2 : ℝ) ^ (-(n : ℤ))
  y1 := (j+1) * (2 : ℝ) ^ (-(n : ℤ))
  hx := by positivity
  hy := by positivity

/-- Lattice cells at scale `n` whose closed square is contained in `U`. -/
def innerDyadicIndices (U : Set Phase2) (n : ℕ) : Set (ℤ × ℤ) :=
  {ij | (dyadicSquare n ij.1 ij.2).carrier ⊆ U}

/-- Boundedness makes the set of inner dyadic cells finite. -/
theorem finite_innerDyadicIndices {U : Set Phase2}
    (hU : Bornology.IsBounded U) (n : ℕ) :
    (innerDyadicIndices U n).Finite := by
  obtain ⟨R, hR, hbound⟩ := bounded_subset_box hU
  apply finite_integer_cells_meeting_box n R
  intro ij hij
  exact hbound (hij (dyadicSquare_center_mem n ij.1 ij.2))

/-- Finite rectilinear complex of all inner dyadic cells. -/
noncomputable def innerDyadicComplex (U : Set Phase2)
    (hU : Bornology.IsBounded U) (n : ℕ) : RectCellComplex := by
  let F := (finite_innerDyadicIndices hU n).toFinset
  exact {
    Cell := F
    instFintype := inferInstance
    instDecidableEq := inferInstance
    rect := fun ij => dyadicSquare n ij.1.1 ij.1.2
    interiorDisjoint := by
      intro a b hab
      exact dyadicSquare_interiors_disjoint_of_ne n (Subtype.coe_ne_coe.mpr hab) }

/-- Every inner dyadic complex lies inside `U`. -/
theorem innerDyadicComplex_subset
    {U : Set Phase2} (hU : Bornology.IsBounded U) (n : ℕ) :
    (innerDyadicComplex U hU n).carrier ⊆ U := by
  intro x hx
  rcases mem_iUnion.mp hx with ⟨ij, hxij⟩
  exact ij.1.2 hxij

/-- Every point of an open set eventually belongs to an inner dyadic square. -/
theorem eventually_mem_innerDyadicComplex
    {U : Set Phase2} (hopen : IsOpen U) (hU : Bornology.IsBounded U)
    {x : Phase2} (hx : x ∈ U) :
    ∀ᶠ n in atTop, x ∈ (innerDyadicComplex U hU n).carrier := by
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  filter_upwards [eventually_pow_neg_lt (show (1 : ℝ) < 2 by norm_num) heps] with n hn
  let ij := dyadicIndexOfPoint n x
  have hsquare : (dyadicSquare n ij.1 ij.2).carrier ⊆ Metric.ball x eps :=
    dyadicSquare_subset_ball_of_mesh_lt x n hn
  have hidx : ij ∈ innerDyadicIndices U n := hsquare.trans hball
  exact innerDyadicComplex_mem_of_index hU n hidx (point_mem_own_dyadicSquare n x)

/-- The missing area of the inner dyadic exhaustion tends to zero. -/
theorem volume_diff_innerDyadic_tendsto_zero
    {U : Set Phase2}
    (hopen : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hmeas : MeasurableSet U) (hfinite : volume U ≠ ⊤) :
    Tendsto
      (fun n => volume (U \ (innerDyadicComplex U hbounded n).carrier))
      atTop (𝓝 0) := by
  have hmono : Monotone fun n => (innerDyadicComplex U hbounded n).carrier :=
    innerDyadicComplex_mono U hbounded
  have hunion : (⋃ n, (innerDyadicComplex U hbounded n).carrier) = U := by
    ext x
    constructor
    · rintro ⟨n, hn⟩
      exact innerDyadicComplex_subset hbounded n hn
    · intro hx
      obtain ⟨n, hn⟩ := (eventually_mem_innerDyadicComplex hopen hbounded hx).exists
      exact mem_iUnion.mpr ⟨n, hn⟩
  have hmeasure := tendsto_measure_iUnion_atTop
    (fun n => measurable_innerDyadicComplex_carrier U hbounded n) hmono
  rw [hunion] at hmeasure
  exact measure_diff_tendsto_zero_of_measure_tendsto hmeas hfinite
    (fun n => innerDyadicComplex_subset hbounded n) hmeasure

/-- Area-exhaustion data for a periodic Jordan interior. -/
noncomputable def PeriodicJordanInterior.innerDyadicAreaApproximation
    {field : Phase2 → Phase2} {P : PeriodicTrajectory field}
    (J : PeriodicJordanInterior P) :
    ℕ → RectCellComplex :=
  innerDyadicComplex J.interior J.bounded

/-- The canonical inner dyadic approximation has all area-side properties required by
`JordanGridApproximation`; only boundary-current convergence remains. -/
theorem PeriodicJordanInterior.innerDyadic_area_properties
    {field : Phase2 → Phase2} {P : PeriodicTrajectory field}
    (J : PeriodicJordanInterior P) :
    (∀ n, (J.innerDyadicAreaApproximation n).carrier ⊆ J.interior) ∧
    Tendsto
      (fun n => volume (J.interior \ (J.innerDyadicAreaApproximation n).carrier))
      atTop (𝓝 0) := by
  exact ⟨
    fun n => innerDyadicComplex_subset J.bounded n,
    volume_diff_innerDyadic_tendsto_zero J.open_interior J.bounded J.measurable J.finite_volume⟩

/-- Exact remaining approximation statement: the positive boundary currents of the canonical inner
dyadic exhaustion converge to the oriented C1 Jordan current. -/
def JordanBoundaryCurrentConvergenceTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (P : PeriodicTrajectory field)
    (J : PeriodicJordanInterior P), P.SimpleClosedCycle →
    ∃ sigma : ℝ, sigma ^ 2 = 1 ∧
      ∀ G : Phase2 → Phase2, ContDiffOn ℝ 1 G (closure J.interior) →
        Tendsto
          (fun n => (J.innerDyadicAreaApproximation n).boundaryFlux G)
          atTop (𝓝 (sigma * periodBoundaryFlux G P))

/-- Boundary-current convergence completes the full grid approximation target. -/
theorem jordanGridApproximation_of_boundaryCurrent
    (hboundary : JordanBoundaryCurrentConvergenceTarget) :
    JordanGridApproximationTarget := by
  intro field P J hsimple
  obtain ⟨sigma, hsigma, hconv⟩ := hboundary field P J hsimple
  exact ⟨{
    grid := J.innerDyadicAreaApproximation
    carrier_subset := J.innerDyadic_area_properties.1
    exhaust_ae := J.innerDyadic_area_properties.2
    orientation := sigma
    orientation_sq := hsigma
    boundaryCurrentConverges := hconv }⟩

end Planar
end CRNT

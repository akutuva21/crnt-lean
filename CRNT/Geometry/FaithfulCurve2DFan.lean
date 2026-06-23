import CRNT.Geometry.FaithfulCurve2D
import CRNT.Geometry.FaithfulCurve

/-!
# The abstract-angle ↔ actual-fan bridge in the plane

`FaithfulCurve2D` carries the *abstract* angular data of a planar fan: the walls sit at increasing
angles `θ`, and the attracting direction of each wall is the unit vector `dir θ = (cos θ, sin θ)`.
`ToricFan`/`FaithfulCurve` carry the *actual* fan: a finite family of `ProperCone` cells, with the
toric field supported in a wall's half-plane exactly when that wall direction lies in every δ-near
cell (`Faithful.AttractsTowardAll`, `toricField_subset_dualHalfPlane_of_attractsAll`). This module
connects the two: it builds the genuine planar fan cells *between consecutive wall rays* and shows
the abstract wall directions are honest attracting directions of those cells.

## The angular-sector cell

`sectorCell θ₁ θ₂ = coneDual {dir θ₁, dir θ₂}` is the planar `ProperCone` whose two bounding face
normals are `dir θ₁` and `dir θ₂`. A vector `dir θ` lies in it precisely when it pairs nonnegatively
with both generators, i.e. `0 ≤ cos (θ₁ − θ) ∧ 0 ≤ cos (θ₂ − θ)` (`mem_sectorCell`). This is a
genuine member of the `Fan` type (a `ProperCone`), so it feeds the toric-field machinery directly.

## What this module formalizes (sorry-free)

* `sectorCell θ₁ θ₂` — the planar `ProperCone` cut out by the two wall normals `dir θ₁`, `dir θ₂`,
  with `mem_sectorCell` reducing membership to the two cosine inequalities.

* `dir_mem_sectorCell_of_close` — a direction `dir θ` lies in `sectorCell θ₁ θ₂` whenever it is
  within a quarter turn of *both* generating angles. In particular each generating direction lies in
  its own cell (`dir_mem_sectorCell_left`, `dir_mem_sectorCell_right`).

* `wall_mem_both_adjacent` — **the shared-wall membership.** The wall direction `dir θⱼ` lies in
  *both* adjacent sector cells `sectorCell θⱼ₋₁ θⱼ` and `sectorCell θⱼ θⱼ₊₁` whenever the consecutive
  wall gaps are below a quarter turn: the wall normal is on the shared boundary face of the two
  adjacent cells, the attracting-direction membership powering the toric-field support.

* `wall_attractsTowardAll` — **the fan bridge.** For a two-cell adjacent fan
  `{sectorCell θ₀ θ₁, sectorCell θ₁ θ₂}` sharing wall `θ₁`, the wall direction `dir θ₁` attracts
  toward *all* cells of the fan (`Faithful.AttractsTowardAll`), at every point and scale, whenever
  the gaps `|θ₁ − θ₀|, |θ₂ − θ₁|` are below a quarter turn.

* `toricField_subset_wall_halfPlane` — the toric field of the adjacent fan lies in the wall's
  region-side half-plane `{y | 0 ≤ ⟪dir θ₁, y⟫_ℝ}`, discharging the support side of
  `exists_faithful_separating_region` from genuine fan geometry. The support is **non-strict**: the
  wall ray sits on each cell's boundary, so equality is possible; the strictness of the dynamics
  comes from the selection elsewhere, not from this cone membership.

* `firstQuadrant_sector` — a worked instance of the sector hypothesis: walls at `0, π/4, π/2`
  all lie within a quarter turn of the midpoint `π/4`, so the chaining of
  `FaithfulCurve2D.exists_faithful_separating_region` closes.

## Scope

This module establishes the per-wall bridge for the adjacent two-cell fan: the sector cell, its
membership criterion, the shared-wall membership, the `AttractsTowardAll` bridge, the resulting
half-plane support, and the worked first-quadrant sector instance. The general `N`-cell assembly from
an arbitrary increasing wall list — that the consecutive-gap conditions hold simultaneously across the
whole fan and that the per-wall two-cell bridges combine into one global support certificate — is not
constructed here; it is the full-fan traversal underlying the faithful curve.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Geometry.FaithfulCurve2D`,
`CRNT.Geometry.FaithfulCurve`.
-/

namespace CRNT

namespace FaithfulCurve2DFan

open scoped InnerProductSpace Classical
open FaithfulCurve2D Real CRNT.Faithful

/-! ## The angular-sector cell -/

/-- **The angular-sector cell.** The planar `ProperCone` whose two bounding face normals are the
wall directions `dir θ₁` and `dir θ₂`: `coneDual {dir θ₁, dir θ₂}`. Its interior is the cone of
directions making a nonnegative angle with both walls — the exponential cone between consecutive
fan rays. -/
noncomputable def sectorCell (θ₁ θ₂ : ℝ) : ProperCone ℝ Plane :=
  coneDual ({dir θ₁, dir θ₂} : Set Plane)

/-- **Membership in a sector cell.** `dir θ ∈ sectorCell θ₁ θ₂` iff `dir θ` pairs nonnegatively with
both wall normals, i.e. `0 ≤ cos (θ₁ − θ)` and `0 ≤ cos (θ₂ − θ)`. -/
theorem mem_sectorCell {θ₁ θ₂ θ : ℝ} :
    dir θ ∈ (sectorCell θ₁ θ₂ : Set Plane) ↔
      0 ≤ Real.cos (θ₁ - θ) ∧ 0 ≤ Real.cos (θ₂ - θ) := by
  simp only [sectorCell, SetLike.mem_coe, mem_coneDual, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h (Or.inl rfl); rwa [inner_dir] at this
    · have := h (Or.inr rfl); rwa [inner_dir] at this
  · rintro ⟨h₁, h₂⟩ x (rfl | rfl)
    · rwa [inner_dir]
    · rwa [inner_dir]

/-! ## Direction membership from angular closeness -/

/-- A direction `dir θ` lies in `sectorCell θ₁ θ₂` whenever its angle is within a quarter turn of
*both* generating angles. The cosine of an angle below `π/2` in absolute value is nonnegative. -/
theorem dir_mem_sectorCell_of_close {θ₁ θ₂ θ : ℝ}
    (h₁ : |θ₁ - θ| ≤ π / 2) (h₂ : |θ₂ - θ| ≤ π / 2) :
    dir θ ∈ (sectorCell θ₁ θ₂ : Set Plane) := by
  rw [mem_sectorCell]
  refine ⟨?_, ?_⟩
  · rw [← Real.cos_abs]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg (θ₁ - θ), Real.pi_pos], h₁⟩
  · rw [← Real.cos_abs]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg (θ₂ - θ), Real.pi_pos], h₂⟩

/-- **Each generating ray lies in its own cell (left generator).** `dir θ₁ ∈ sectorCell θ₁ θ₂`
whenever the cell is no wider than a quarter turn: the first wall ray is a bounding ray of the
sector. -/
theorem dir_mem_sectorCell_left {θ₁ θ₂ : ℝ} (h : |θ₂ - θ₁| ≤ π / 2) :
    dir θ₁ ∈ (sectorCell θ₁ θ₂ : Set Plane) :=
  dir_mem_sectorCell_of_close (by rw [sub_self, abs_zero]; positivity) h

/-- **Each generating ray lies in its own cell (right generator).** `dir θ₂ ∈ sectorCell θ₁ θ₂`
whenever the cell is no wider than a quarter turn: the second wall ray is a bounding ray of the
sector. -/
theorem dir_mem_sectorCell_right {θ₁ θ₂ : ℝ} (h : |θ₁ - θ₂| ≤ π / 2) :
    dir θ₂ ∈ (sectorCell θ₁ θ₂ : Set Plane) :=
  dir_mem_sectorCell_of_close h (by rw [sub_self, abs_zero]; positivity)

/-! ## The shared-wall membership -/

/-- **The wall ray is shared by both adjacent cells.** Given three consecutive wall angles
`θ₀ < θ₁ < θ₂` with consecutive gaps below a quarter turn, the middle wall direction `dir θ₁` lies
in *both* the left cell `sectorCell θ₀ θ₁` and the right cell `sectorCell θ₁ θ₂`. The wall normal
sits on the shared boundary face of the two adjacent cells — this intersection membership is the
attracting-direction condition (`Faithful.AttractsToward` in each adjacent cell) that powers the
toric-field support across the uncertainty region between the cells. -/
theorem wall_mem_both_adjacent {θ₀ θ₁ θ₂ : ℝ}
    (h₀₁ : |θ₁ - θ₀| ≤ π / 2) (h₁₂ : |θ₂ - θ₁| ≤ π / 2) :
    dir θ₁ ∈ (sectorCell θ₀ θ₁ : Set Plane) ∧
      dir θ₁ ∈ (sectorCell θ₁ θ₂ : Set Plane) :=
  ⟨dir_mem_sectorCell_right (by rwa [abs_sub_comm]), dir_mem_sectorCell_left h₁₂⟩

/-! ## The fan bridge: AttractsTowardAll for the adjacent two-cell fan -/

/-- The adjacent two-cell fan around the wall `θ₁`: the left cell `sectorCell θ₀ θ₁` and the right
cell `sectorCell θ₁ θ₂`, the two exponential cones meeting along the wall ray `dir θ₁`. -/
noncomputable def adjacentFan (θ₀ θ₁ θ₂ : ℝ) : Fan Plane :=
  {sectorCell θ₀ θ₁, sectorCell θ₁ θ₂}

/-- **The wall direction attracts toward all cells of the adjacent fan.** With the consecutive gaps
below a quarter turn, the wall direction `dir θ₁` lies in both cells of `adjacentFan θ₀ θ₁ θ₂`, so
the `Faithful.AttractsTowardAll` condition holds at every point and scale, regardless of which cells
are δ-near. This is the genuine fan-geometry input to the toric-field support. -/
theorem wall_attractsTowardAll {θ₀ θ₁ θ₂ : ℝ}
    (h₀₁ : |θ₁ - θ₀| ≤ π / 2) (h₁₂ : |θ₂ - θ₁| ≤ π / 2) (δ : ℝ) (X : Plane) :
    AttractsTowardAll (adjacentFan θ₀ θ₁ θ₂) δ X (dir θ₁) := by
  obtain ⟨hL, hR⟩ := wall_mem_both_adjacent h₀₁ h₁₂
  intro C hC _
  simp only [adjacentFan, Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with h | h
  · subst h; exact hL
  · subst h; exact hR

/-- **The toric field of the adjacent fan lies in the wall's region-side half-plane.** Because the
wall direction `dir θ₁` attracts toward all cells, the entire toric field at any point — hull of the
δ-near polar cones — pairs nonnegatively with `dir θ₁`: it lies in `{y | 0 ≤ ⟪dir θ₁, y⟫_ℝ}`. This
discharges the support side of the faithful-curve construction from genuine 2-D fan geometry.

The support is **non-strict** (`0 ≤`, equality possible): the wall ray `dir θ₁` lies on the boundary
of each adjacent cell, so the cone membership cannot give strict positivity. That is expected — the
strictness in the dynamics comes from the genuine selection elsewhere, not from this cone. -/
theorem toricField_subset_wall_halfPlane {θ₀ θ₁ θ₂ : ℝ}
    (h₀₁ : |θ₁ - θ₀| ≤ π / 2) (h₁₂ : |θ₂ - θ₁| ≤ π / 2) (δ : ℝ) (X : Plane) :
    (toricField (adjacentFan θ₀ θ₁ θ₂) δ X : Set Plane) ⊆
      {y : Plane | 0 ≤ ⟪dir θ₁, y⟫_ℝ} :=
  toricField_subset_dualHalfPlane_of_attractsAll (wall_attractsTowardAll h₀₁ h₁₂ δ X)

/-- **The wall direction is a planar support face of the adjacent fan.** For any field value `v` of
the adjacent two-cell toric field at `X`, the constant field `fun _ => v` is a
`ZeroSeparatingCurve2D.IsSupportFace` with the wall normal `dir θ₁`: the segment crossing the
uncertainty region between the two cells in the wall's attracting direction is a support segment. -/
theorem wall_isSupportFace {θ₀ θ₁ θ₂ : ℝ}
    (h₀₁ : |θ₁ - θ₀| ≤ π / 2) (h₁₂ : |θ₂ - θ₁| ≤ π / 2) (δ : ℝ) (X v : Plane)
    (hv : v ∈ toricField (adjacentFan θ₀ θ₁ θ₂) δ X) {a : ℝ} {faces : List (Plane × ℝ)} :
    ZeroSeparatingCurve2D.IsSupportFace (fun _ => v) faces (dir θ₁) a :=
  isSupportFace_of_attractsAll (wall_attractsTowardAll h₀₁ h₁₂ δ X) hv

/-! ## Worked sector instance: the first-quadrant fan -/

/-- **The first-quadrant sector hypothesis closes.** The walls at `0, π/4, π/2` all lie within a
quarter turn of the midpoint apex `π/4`, so the sector hypothesis of
`FaithfulCurve2D.exists_faithful_separating_region` — `∀ w ∈ walls, |w.1 − φ| < π/2` — holds with
`φ = π/4`. A worked instance of the chaining-closure condition. -/
theorem firstQuadrant_sector :
    ∀ w ∈ FaithfulCurve2D.threeWalls, |w.1 - π / 4| < π / 2 := by
  have hpi := Real.pi_pos
  intro w hw
  simp only [FaithfulCurve2D.threeWalls, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · show |(0 : ℝ) - π / 4| < π / 2
    rw [show (0 : ℝ) - π / 4 = -(π / 4) by ring, abs_neg, abs_of_nonneg (by positivity)]
    linarith
  · show |π / 4 - π / 4| < π / 2
    rw [sub_self, abs_zero]; linarith
  · show |π / 2 - π / 4| < π / 2
    rw [show π / 2 - π / 4 = π / 4 by ring, abs_of_nonneg (by positivity)]
    linarith

end FaithfulCurve2DFan

end CRNT

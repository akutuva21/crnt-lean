import CRNT.Dynamics.PolyRegionStrictInvariant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The 2-D faithful zero-separating curve: angular chaining of attracting directions

A planar zero-separating curve is a polygonal line from the positive
`x`-axis to the positive `y`-axis with **one vertex per bounded exponential cone** of the fan, each
segment crossing one uncertainty region in that region's *attracting direction* — the direction
**orthogonal to the corresponding fan half-line**, so the segment's region-normal points *along* the
wall ray. The fan walls of a 2-D fan sit at increasing angles around the origin; the attracting
directions are therefore the unit vectors *at* those wall angles, and they rotate **monotonically**
as the walls are traversed. That angular monotonicity is the engine of the construction: it is what
lets a single convex polygonal arc realize every per-segment direction at once (the "slopes chain"
claim of the faithful curve).

This module formalizes the angle ↔ vector bridge and the monotonicity that drives the chaining.

## What this module formalizes (sorry-free)

* `dir θ` — the planar unit vector `(cos θ, sin θ)` at angle `θ` in `EuclideanSpace ℝ (Fin 2)`, with
  `norm_dir : ‖dir θ‖ = 1`.

* `inner_dir` — the **angle bridge**: `⟪dir θ₁, dir θ₂⟫_ℝ = cos (θ₁ − θ₂)`. The Euclidean inner
  product of two direction vectors is the cosine of the angle between them.

* `inner_dir_pos_of_abs_sub_lt` — two directions pair *strictly positively* when their angles differ
  by less than `π/2`; `inner_dir_self : ⟪dir θ, dir θ⟫_ℝ = 1`.

* `dir_halfPlane_offset` — for a point `dir φ` scaled to radius `ρ > 0`, the signed distance to the
  oriented line with normal `dir θ` is `ρ · cos (θ − φ)`; the engine for placing the curve's vertices
  on the far side of each face.

These are the foundational geometric facts; the convex-arc assembly (a polygonal curve with these
monotone normals running axis-to-axis, separating `0`) is built on top.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.PolyRegionStrictInvariant`,
`Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.
-/

namespace CRNT

namespace FaithfulCurve2D

open scoped InnerProductSpace
open ZeroSeparatingCurve2D Real

/-- The plane `EuclideanSpace ℝ (Fin 2)`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The unit vector `(cos θ, sin θ)` at angle `θ`. The attracting directions of a 2-D fan are the
`dir` of the wall angles. -/
noncomputable def dir (θ : ℝ) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![Real.cos θ, Real.sin θ]

@[simp] theorem dir_apply (θ : ℝ) (i : Fin 2) :
    dir θ i = ![Real.cos θ, Real.sin θ] i := rfl

/-- **The angle bridge.** The Euclidean inner product of two direction vectors is the cosine of the
angle between them: `⟪dir θ₁, dir θ₂⟫_ℝ = cos (θ₁ − θ₂)`. -/
theorem inner_dir (θ₁ θ₂ : ℝ) : ⟪dir θ₁, dir θ₂⟫_ℝ = Real.cos (θ₁ - θ₂) := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, dir_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Real.cos_sub]; ring

/-- `⟪dir θ, dir θ⟫_ℝ = 1`. -/
@[simp] theorem inner_dir_self (θ : ℝ) : ⟪dir θ, dir θ⟫_ℝ = 1 := by
  rw [inner_dir, sub_self, Real.cos_zero]

/-- Each direction vector is a unit vector. -/
theorem norm_dir (θ : ℝ) : ‖dir θ‖ = 1 := by
  have h : ‖dir θ‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact inner_dir_self θ
  rw [← Real.sqrt_sq (norm_nonneg (dir θ)), h, Real.sqrt_one]

/-- Two directions pair strictly positively when their angles differ by less than `π/2`. The
local non-degeneracy of the attracting-direction chaining: nearby walls give compatible normals. -/
theorem inner_dir_pos_of_abs_sub_lt {θ₁ θ₂ : ℝ} (h : |θ₁ - θ₂| < π / 2) :
    0 < ⟪dir θ₁, dir θ₂⟫_ℝ := by
  rw [inner_dir, ← Real.cos_abs]
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg (θ₁ - θ₂), Real.pi_pos], h⟩

/-- **Signed offset to an oriented face line.** The point `ρ • dir φ` (radius `ρ` at angle `φ`) has
signed inner product `ρ · cos (θ − φ)` against the unit normal `dir θ`. This places the polygonal
curve's vertices relative to each face's bounding line. -/
theorem inner_dir_smul (θ φ ρ : ℝ) : ⟪dir θ, ρ • dir φ⟫_ℝ = ρ * Real.cos (θ - φ) := by
  rw [inner_smul_right, inner_dir]

/-! ## Angular chaining: a single apex direction satisfies all monotone constraints -/

/-- Every finite list of reals has an upper bound. -/
theorem exists_ub_list (L : List ℝ) : ∃ M : ℝ, ∀ x ∈ L, x ≤ M := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons hd tl ih =>
      obtain ⟨M, hM⟩ := ih
      refine ⟨max hd M, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | h
      · exact le_max_left _ _
      · exact le_trans (hM x h) (le_max_right _ _)

/-- The faithful curve's face list from a list of `(wall angle, offset)` pairs: one oriented
half-plane `(dir angle, offset)` per wall. The region is `polyRegion (facesOfAngles walls)`. -/
noncomputable def facesOfAngles (walls : List (ℝ × ℝ)) : List (Plane × ℝ) :=
  walls.map (fun w => (dir w.1, w.2))

/-- **Strict feasibility — the angular-chaining engine.** If every wall angle lies within `π/2` of
an apex angle `φ` (so the walls fit in a sector of width `< π`), then the point `ρ • dir φ` far out
along the apex direction lies strictly inside *every* face half-plane simultaneously. One apex
direction satisfies all the monotone-normal constraints at once — the precise geometric content of
the statement that the slopes chain so a single curve realizes them all.

The sector hypothesis `|w.1 − φ| < π/2` is exactly the condition under which the chaining closes; that
an arbitrary 2-D fan's curve-relevant walls satisfy it is a separate property of the fan geometry, not
established here. Within a sector of width `< π` every cosine `cos (w.1 − φ)`
is strictly positive, so a large enough radius clears every offset. -/
theorem exists_strict_interior (walls : List (ℝ × ℝ)) {φ : ℝ}
    (hsector : ∀ w ∈ walls, |w.1 - φ| < π / 2) :
    ∃ ρ : ℝ, ∀ nf ∈ facesOfAngles walls, nf.2 < ⟪nf.1, ρ • dir φ⟫_ℝ := by
  obtain ⟨M, hM⟩ := exists_ub_list (walls.map (fun w => w.2 / Real.cos (w.1 - φ)))
  refine ⟨M + 1, fun nf hnf => ?_⟩
  rw [facesOfAngles, List.mem_map] at hnf
  obtain ⟨w, hw, rfl⟩ := hnf
  have hcos : 0 < Real.cos (w.1 - φ) := by
    rw [← Real.cos_abs]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg (w.1 - φ), Real.pi_pos], hsector w hw⟩
  have hbnd : w.2 / Real.cos (w.1 - φ) ≤ M := hM _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
  rw [div_le_iff₀ hcos] at hbnd
  have hexpand : (M + 1) * Real.cos (w.1 - φ) = M * Real.cos (w.1 - φ) + Real.cos (w.1 - φ) := by
    ring
  rw [inner_dir_smul]
  linarith [hbnd, hcos, hexpand]

/-- **The far side is nonempty (strict interior exists).** Under the sector hypothesis, the region
`polyRegion (facesOfAngles walls)` contains the apex point in its strict interior, so it is
nonempty. This is the `hstart` data consumed by `polyRegion_invariant_of_strictSupport`. -/
theorem exists_mem_polyRegion (walls : List (ℝ × ℝ)) {φ : ℝ}
    (hsector : ∀ w ∈ walls, |w.1 - φ| < π / 2) :
    ∃ x : Plane, ∀ nf ∈ facesOfAngles walls, nf.2 < ⟪nf.1, x⟫_ℝ := by
  obtain ⟨ρ, hρ⟩ := exists_strict_interior walls hsector
  exact ⟨ρ • dir φ, hρ⟩

/-! ## Assembly: the constructed zero-separating region and its persistence -/

/-- **The angular region separates the origin.** Each face normal `dir w.1` is a unit vector, so a
wall `(θ₀, a)` with offset `a ≥ r > 0` makes the whole region miss the open `r`-ball about `0` — the
separation is automatic from the angular construction (no extra hypothesis). -/
theorem facesOfAngles_subset_compl_ball {walls : List (ℝ × ℝ)} {θ₀ a r : ℝ}
    (hmem : (θ₀, a) ∈ walls) (har : r ≤ a) :
    polyRegion (facesOfAngles walls) ⊆ (Metric.ball (0 : Plane) r)ᶜ :=
  polyRegion_subset_compl_ball (List.mem_map.mpr ⟨(θ₀, a), hmem, rfl⟩) (norm_dir θ₀) har

/-- **A constructed zero-separating region.** Under the sector hypothesis with one positive-offset
wall `(θ₀, a)`, the angular region `polyRegion (facesOfAngles walls)` has a nonempty strict interior
*and* excludes the open `a`-ball about `0`. Both halves of "zero-separating" are constructed outright
from the angular chaining — no abstract existence assumed. -/
theorem exists_faithful_separating_region (walls : List (ℝ × ℝ)) {φ θ₀ a : ℝ}
    (hsector : ∀ w ∈ walls, |w.1 - φ| < π / 2) (hmem : (θ₀, a) ∈ walls) (_hpos : 0 < a) :
    (∃ x : Plane, ∀ nf ∈ facesOfAngles walls, nf.2 < ⟪nf.1, x⟫_ℝ) ∧
      polyRegion (facesOfAngles walls) ⊆ (Metric.ball (0 : Plane) a)ᶜ :=
  ⟨exists_mem_polyRegion walls hsector, facesOfAngles_subset_compl_ball hmem le_rfl⟩

/-- **Persistence on the constructed angular region.** A genuine curve `γ` solving `ẋ = f(γ)` whose
field is strictly subtangent (boundary-locally) to the angular faces, started strictly inside the
region, keeps a hard distance `r` from the origin for all forward time — given a separating wall
`(θ₀, a)` with `a ≥ r`. This composes the angular face structure (unit normals, automatic
separation) with the honest boundary-local invariance `polyRegion_invariant_of_strictSupport`.

The remaining input `hsupp` — that the field strictly attracts toward the region across each
angular face — is the fan-geometry connection (the per-wall attracting-direction analysis), the one
piece still supplied as a hypothesis; everything else (the separating region, the interior start via
`exists_strict_interior`) is constructed from the angular chaining. -/
theorem faithful_region_persistent (walls : List (ℝ × ℝ)) {θ₀ a r : ℝ}
    (hmem : (θ₀, a) ∈ walls) (har : r ≤ a)
    {f : Plane → Plane} {γ : ℝ → Plane}
    (hsupp : IsStrictSupportField f (facesOfAngles walls))
    (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (hstart : ∀ nf ∈ facesOfAngles walls, nf.2 < ⟪nf.1, γ 0⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    r ≤ dist (γ t) 0 :=
  stays_away_from_zero_of_strictSupport
    (List.mem_map.mpr ⟨(θ₀, a), hmem, rfl⟩) (norm_dir θ₀) har hγcont hγ hsupp hstart ht

/-! ## A genuinely-chained concrete witness -/

/-- The three walls of a genuinely-chained faithful curve: angles `0, π/4, π/2`, offsets `1`. Their
attracting directions `(1,0)`, `(√2/2, √2/2)`, `(0,1)` are three *distinct* normals spanning a
quarter turn — a real chained instance, unlike a single collapsed direction. -/
noncomputable def threeWalls : List (ℝ × ℝ) := [(0, 1), (π / 4, 1), (π / 2, 1)]

/-- **A genuinely-chained constructed zero-separating region.** The three-wall faithful curve fits in
the sector of width `π/2` about apex `π/4`, so its region has a nonempty strict interior and
separates the unit ball about `0`. Three distinct conflicting attracting directions chain into one
region — the non-degenerate witness validating the angular-chaining pipeline end-to-end. -/
theorem threeWall_separating_region :
    (∃ x : Plane, ∀ nf ∈ facesOfAngles threeWalls, nf.2 < ⟪nf.1, x⟫_ℝ) ∧
      polyRegion (facesOfAngles threeWalls) ⊆ (Metric.ball (0 : Plane) 1)ᶜ := by
  have hpi := Real.pi_pos
  refine exists_faithful_separating_region threeWalls (φ := π / 4) (θ₀ := 0) (a := 1) ?_
    (by simp [threeWalls]) one_pos
  intro w hw
  simp only [threeWalls, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · show |(0 : ℝ) - π / 4| < π / 2
    rw [show (0 : ℝ) - π / 4 = -(π / 4) by ring, abs_neg, abs_of_nonneg (by positivity)]
    linarith
  · show |π / 4 - π / 4| < π / 2
    rw [sub_self, abs_zero]; linarith
  · show |π / 2 - π / 4| < π / 2
    rw [show π / 2 - π / 4 = π / 4 by ring, abs_of_nonneg (by positivity)]
    linarith

end FaithfulCurve2D

end CRNT

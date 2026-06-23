import CRNT.Dynamics.PolyRegionStrictInvariant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The 2-D faithful zero-separating curve: angular chaining of attracting directions (Craciun §4.2)

Craciun's §4.2 builds the planar zero-separating curve as a polygonal line from the positive
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

end FaithfulCurve2D

end CRNT

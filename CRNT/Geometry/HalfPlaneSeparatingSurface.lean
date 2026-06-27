import CRNT.Geometry.ZeroSeparatingSurface
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Affine half-plane zero-separating surfaces

A single closed half-plane `{y | a ≤ ⟪n, y⟫}` with unit normal `n` and positive offset `a` is a
`C¹` zero-separating surface for a field that points into it across a band around its boundary. The
defining function `g y = a − ⟪n, y⟫` is affine, hence `C¹`, with constant derivative `−⟪n, ·⟫`, so
the band descent is `0 ≤ ⟪n, f y⟫` and the half-plane misses the open `a`-ball about the origin by
Cauchy–Schwarz. This realizes `DifferentialInclusion.ZeroSeparatingSurfaceExists` for the affine
surface in any dimension, generalizing the one-dimensional base case, and feeds the genuine-flow
away-from-origin conclusion with no viability hypothesis: a single inward half-plane already keeps
the genuine trajectory a fixed distance from the origin.

## Contents

* `DifferentialInclusion.zeroSeparatingSurfaceExists_halfPlane` — from a unit normal `n`, offset
  `a > 0`, band radius `δ > 0`, a start with `a ≤ ⟪n, x₀⟫`, and inward-in-band `0 ≤ ⟪n, f y⟫` for
  `⟪n, y⟫ ∈ [a − δ, a + δ]`, the affine half-plane is a `ZeroSeparatingSurfaceExists` for `f` at `x₀`.

* `DifferentialInclusion.halfPlane_away_from_origin` — the genuine-flow consequence with the
  viability content discharged: a genuine trajectory through `x₀` keeps a hard distance from the
  origin, with no distance-nonincreasing hypothesis carried.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Geometry.ZeroSeparatingSurface`,
`Mathlib.Analysis.InnerProductSpace.Calculus`.
-/

namespace CRNT

namespace DifferentialInclusion

open scoped InnerProductSpace
open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Affine half-plane zero-separating surface.** With unit normal `n` (`‖n‖ = 1`), offset
`a > 0`, band radius `δ > 0`, a start `x₀` inside the half-plane (`a ≤ ⟪n, x₀⟫`), and the field
inward across the boundary band (`0 ≤ ⟪n, f y⟫` whenever `a − δ ≤ ⟪n, y⟫ ≤ a + δ`), the affine
function `g y = a − ⟪n, y⟫` is a zero-separating surface: `C¹` with constant derivative `−⟪n, ·⟫`,
band descent `−⟪n, f y⟫ ≤ 0`, start in the sublevel set, and sublevel set `{a ≤ ⟪n, y⟫}` missing the
open `a`-ball about the origin (Cauchy–Schwarz). -/
theorem zeroSeparatingSurfaceExists_halfPlane {f : E → E} {x₀ : E} {n : E} {a δ : ℝ}
    (hn : ‖n‖ = 1) (ha : 0 < a) (hδ : 0 < δ) (hstart : a ≤ ⟪n, x₀⟫_ℝ)
    (hinward : ∀ y, a - δ ≤ ⟪n, y⟫_ℝ → ⟪n, y⟫_ℝ ≤ a + δ → 0 ≤ ⟪n, f y⟫_ℝ) :
    ZeroSeparatingSurfaceExists f x₀ where
  exists_surface := by
    refine ⟨fun y => a - ⟪n, y⟫_ℝ, fun _ => -(innerSL ℝ n), 0, δ, a, ?_, ?_, hδ, ?_, ?_, ha, ?_⟩
    · exact continuous_const.sub (continuous_const.inner continuous_id)
    · intro y
      have hi : HasFDerivAt (fun y => ⟪n, y⟫_ℝ) (innerSL ℝ n) y := by
        simpa using (innerSL ℝ n).hasFDerivAt
      simpa using hi.const_sub a
    · intro y hlo hhi
      have h1 : a - δ ≤ ⟪n, y⟫_ℝ := by linarith
      have h2 : ⟪n, y⟫_ℝ ≤ a + δ := by linarith
      have hf := hinward y h1 h2
      show (-(innerSL ℝ n)) (f y) ≤ 0
      rw [neg_apply, innerSL_apply_apply]
      linarith
    · show a - ⟪n, x₀⟫_ℝ ≤ 0
      linarith
    · intro y hy
      have hge : a ≤ ⟪n, y⟫_ℝ := by
        have : a - ⟪n, y⟫_ℝ ≤ 0 := hy
        linarith
      rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt]
      have hcs : ⟪n, y⟫_ℝ ≤ ‖y‖ := by
        have := real_inner_le_norm n y
        rwa [hn, one_mul] at this
      linarith

/-- **Away-from-origin for the genuine flow, no viability hypothesis.** Under the half-plane
inward-in-band condition, a genuine trajectory `γ` through `x₀` (`γ 0 = x₀`, solving `ẋ = f (γ t)`)
keeps a hard distance `r > 0` from the origin for all forward times. The viability content is
discharged through the affine surface's `C¹` sublevel-descent invariance — no distance-nonincreasing
hypothesis is carried. -/
theorem halfPlane_away_from_origin {f : E → E} {x₀ : E} {n : E} {a δ : ℝ}
    (hn : ‖n‖ = 1) (ha : 0 < a) (hδ : 0 < δ) (hstart : a ≤ ⟪n, x₀⟫_ℝ)
    (hinward : ∀ y, a - δ ≤ ⟪n, y⟫_ℝ → ⟪n, y⟫_ℝ ≤ a + δ → 0 ≤ ⟪n, f y⟫_ℝ)
    {γ : ℝ → E} (hγcont : Continuous γ)
    (hγderiv : ∀ t, 0 ≤ t → HasDerivAt γ (f (γ t)) t) (h0 : γ 0 = x₀) :
    ∃ r : ℝ, 0 < r ∧ ∀ t, 0 ≤ t → r ≤ dist (γ t) 0 :=
  (zeroSeparatingSurfaceExists_halfPlane hn ha hδ hstart hinward).away_from_origin
    hγcont hγderiv h0

end DifferentialInclusion

end CRNT

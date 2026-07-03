import CRNT.Analysis.ConvexProjection

/-!
# Brouwer zero-of-field corollary on compact convex sets

Two corollaries of Brouwer's fixed-point theorem for a nonempty compact convex set `K` in
`EuclideanSpace ℝ (Fin n)`, recasting fixed points of a displacement map as zeros of a vector
field `v`:

* `exists_zero_of_displacement_mapsTo`: if the inward displacement `x ↦ x - v x` maps `K` into
  itself, then `v` vanishes somewhere in `K`.
* `exists_projected_fixedPoint`: the projected displacement `x ↦ projK (x - v x)` always has a
  fixed point in `K`, at which the projection variational inequality `∀ w ∈ K, ⟪v x, w - x⟫ ≤ 0`
  holds. This is the Stampacchia form needed when the displacement need not be inward.

Depends on: `CRNT.Analysis.ConvexProjection`.
-/

namespace CRNT.Analysis

open Set
open scoped RealInnerProductSpace

variable {n : ℕ}
variable {K : Set (EuclideanSpace ℝ (Fin n))} (hne : K.Nonempty) (hconv : Convex ℝ K)
  (hcomp : IsCompact K)

include hne hconv hcomp in
/-- Brouwer equilibrium via inward displacement: if `x ↦ x - v x` maps the nonempty compact
convex `K` into itself, then `v` has a zero in `K`. -/
theorem exists_zero_of_displacement_mapsTo
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : ContinuousOn v K)
    (hmaps : Set.MapsTo (fun x => x - v x) K K) : ∃ x ∈ K, v x = 0 := by
  set g := fun x => x - v x with hg
  have hg_cont : ContinuousOn g K := continuousOn_id.sub hv
  obtain ⟨x, hxK, hxfix⟩ := brouwer_compact_convex hne hconv hcomp g hg_cont hmaps
  refine ⟨x, hxK, ?_⟩
  have : x - v x = x := hxfix
  exact sub_eq_self.mp this

include hne hconv hcomp in
open scoped RealInnerProductSpace in
/-- Brouwer equilibrium via metric projection: the projected displacement `x ↦ projK (x - v x)`
has a fixed point in `K`, at which the Stampacchia variational inequality `0 ≤ ⟪v x, w - x⟫` holds
for every `w ∈ K`. Equivalently `-v x` lies in the normal cone of `K` at `x`; when `x` is an
interior point of `K` this forces `v x = 0`. -/
theorem exists_projected_fixedPoint
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : ContinuousOn v K) :
    ∃ x ∈ K, projK hne hconv hcomp (x - v x) = x ∧ ∀ w ∈ K, 0 ≤ ⟪v x, w - x⟫ := by
  set g := fun x => projK hne hconv hcomp (x - v x) with hg
  have hg_cont : ContinuousOn g K :=
    (continuous_projK hne hconv hcomp).comp_continuousOn (continuousOn_id.sub hv)
  have hg_maps : Set.MapsTo g K K := fun x _ => projK_mem hne hconv hcomp _
  obtain ⟨x, hxK, hfix⟩ := brouwer_compact_convex hne hconv hcomp g hg_cont hg_maps
  have hfix' : projK hne hconv hcomp (x - v x) = x := hfix
  refine ⟨x, hxK, hfix', ?_⟩
  intro w hw
  have hvar : ⟪(x - v x) - projK hne hconv hcomp (x - v x), w - projK hne hconv hcomp (x - v x)⟫ ≤ 0 :=
    projK_variational hne hconv hcomp (x - v x) w hw
  rw [hfix'] at hvar
  -- `(x - v x) - x = -v x`, so the projection inequality reads `-⟪v x, w - x⟫ ≤ 0`
  have hsimp : ⟪(x - v x) - x, w - x⟫ = -⟪v x, w - x⟫ := by
    rw [sub_sub_cancel_left, inner_neg_left]
  rw [hsimp] at hvar
  linarith

import CRNT.Dynamics.SupportDiniBridge

/-!
# Forward invariance of the convex polygonal region (Craciun §4.2, Dini half)

The closed region `ZeroSeparatingCurve2D.polyRegion faces` is the intersection of the closed
half-planes `dotHalfPlane n a` over the oriented faces `(n, a) ∈ faces`. Forward invariance of this
intersection follows half-plane by half-plane, with **no** appeal to a distance-to-intersection
(Hoffman) identity: a curve that satisfies the support condition on every face stays in every
half-plane individually, hence in their intersection.

The mechanism is the per-face slack `s ↦ a − ⟪n, γ s⟫_ℝ`. Along a curve with
`HasDerivAt γ (f (γ s)) s`, this slack is antitone under the support condition
`0 ≤ ⟪n, f (γ s)⟫_ℝ` (the half-plane Dini monotonicity
`ZeroSeparatingCurve2D.slack_antitoneOn_of_support`). If `γ 0 ∈ polyRegion faces` then each slack is
`≤ 0` at time `0`; antitonicity carries that to all forward times, so each slack stays `≤ 0` and
`γ t` lies in every half-plane.

## What this module formalizes (sorry-free)

* `polyRegion_invariant_of_support` — **forward invariance via per-half-plane invariance.** A
  continuous curve solving the field on `(0, ∞)` with the support condition on every face, starting
  in the region, stays in the region for all forward time. Proved directly from
  `slack_antitoneOn_of_support` applied to each face; no intersection-distance identity is used.

* `stays_away_from_zero_of_support_invariant` — **persistence.** Combined with a separating face
  (unit normal, offset `a ≥ r > 0`), the invariant curve keeps a hard distance `r` from the origin,
  fed by `polyRegion_subset_compl_ball`. This is the membership-only persistence route, parallel to
  the distance-form `stays_away_from_zero_of_infDist_antitone` but routed through
  `polyRegion_invariant_of_support` rather than an `infDist` antitone hypothesis.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.SupportDiniBridge`.
-/

namespace CRNT

namespace ZeroSeparatingCurve2D

open Set Metric
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Forward invariance of the convex polygonal region via per-half-plane invariance.** Let `γ` be
a continuous curve solving the field on `(0, ∞)` (`HasDerivAt γ (f (γ t)) t`), with the support
condition `0 ≤ ⟪n, f (γ t)⟫_ℝ` on `(0, ∞)` for every face `(n, a) ∈ faces`, starting in the region
(`γ 0 ∈ polyRegion faces`). Then `γ t ∈ polyRegion faces` for all `t ≥ 0`.

The proof is half-plane by half-plane: for each face the per-face slack `s ↦ a − ⟪n, γ s⟫_ℝ` is
antitone on `[0, ∞)` (`slack_antitoneOn_of_support`), so `slack t ≤ slack 0 ≤ 0`, i.e.
`a ≤ ⟪n, γ t⟫_ℝ`. Membership in every half-plane is membership in the intersection. No
distance-to-intersection identity is needed. -/
theorem polyRegion_invariant_of_support {faces : List (E × ℝ)} {γ : ℝ → E} {f : E → E}
    (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (hsupp : ∀ na ∈ faces, ∀ t > 0, 0 ≤ ⟪na.1, f (γ t)⟫_ℝ)
    (h0 : γ 0 ∈ polyRegion faces) {t : ℝ} (ht : 0 ≤ t) :
    γ t ∈ polyRegion faces := by
  rw [mem_polyRegion]
  intro na hna
  -- The per-face slack is continuous on `[0, ∞)`.
  have hcont : ContinuousOn (fun s => na.2 - ⟪na.1, γ s⟫_ℝ) (Set.Ici 0) :=
    (continuous_const.sub (continuous_const.inner hγcont)).continuousOn
  -- and antitone there, by half-plane Dini monotonicity.
  have hanti : AntitoneOn (fun s => na.2 - ⟪na.1, γ s⟫_ℝ) (Set.Ici 0) :=
    slack_antitoneOn_of_support hcont hγ (hsupp na hna)
  -- The slack is `≤ 0` at time `0`, since `γ 0` is in the region's half-plane for this face.
  have h0slack : na.2 - ⟪na.1, γ 0⟫_ℝ ≤ 0 := by
    have := (mem_polyRegion.mp h0) na hna
    linarith
  -- Antitonicity carries `slack 0 ≤ 0` to `slack t ≤ 0`.
  have htslack : na.2 - ⟪na.1, γ t⟫_ℝ ≤ 0 :=
    le_trans (hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht) h0slack
  linarith

/-- **Persistence away from `0` via membership invariance.** With `polyRegion_invariant_of_support`
giving membership for all forward time, and a separating face `(n, a)` (unit normal, offset
`a ≥ r > 0`), the curve keeps a hard distance `r` from the origin: each in-region point lies outside
the open `r`-ball (`polyRegion_subset_compl_ball`).

This is the direct, membership-only persistence route, using no `infDist` antitone hypothesis. -/
theorem stays_away_from_zero_of_support_invariant {faces : List (E × ℝ)} {γ : ℝ → E} {f : E → E}
    {n : E} {a r : ℝ}
    (hmem : (n, a) ∈ faces) (hn : ‖n‖ = 1) (har : r ≤ a)
    (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (hsupp : ∀ na ∈ faces, ∀ t > 0, 0 ≤ ⟪na.1, f (γ t)⟫_ℝ)
    (h0 : γ 0 ∈ polyRegion faces) {t : ℝ} (ht : 0 ≤ t) :
    r ≤ dist (γ t) 0 := by
  have hmemR : γ t ∈ polyRegion faces :=
    polyRegion_invariant_of_support hγcont hγ hsupp h0 ht
  have hcompl : γ t ∈ (Metric.ball (0 : E) r)ᶜ :=
    polyRegion_subset_compl_ball hmem hn har hmemR
  rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hcompl
  rwa [dist_zero_right]

end ZeroSeparatingCurve2D

end CRNT

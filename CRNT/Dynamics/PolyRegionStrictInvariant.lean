import CRNT.Dynamics.SupportDiniBridge
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Boundary-local invariance of the polygonal zero-separating region (Craciun §4.2)

The closed region `ZeroSeparatingCurve2D.polyRegion faces` is the intersection of the closed
half-planes `{p | aⱼ ≤ ⟪nⱼ, p⟫_ℝ}` over the oriented faces `(nⱼ, aⱼ)`. Its forward invariance for
Craciun's faithful curve is governed by **boundary-local subtangency**: at each point of the region
that lies *on* a face's bounding line, the velocity must point into the region across that face. This
is the `ZeroSeparatingCurve2D.IsSupportFace` condition — subtangency tested only where it is active,
namely at boundary points on the face line.

This module proves invariance directly from that local condition (in its strict form), via a
first-exit argument that never appeals to a global all-faces condition:

* a curve leaving the region has a first-exit time `τ` with `γ τ` on the region's frontier;
* at `τ` each face is either **active** (`⟪n, γ τ⟫_ℝ = a`) or **inactive** (`a < ⟪n, γ τ⟫_ℝ`);
* on an active face, strict boundary subtangency `0 < ⟪n, f (γ τ)⟫_ℝ` makes the per-face slack
  `s ↦ a − ⟪n, γ s⟫_ℝ` strictly decrease through `τ` (negative derivative at a zero), so that face
  stays satisfied just past `τ`;
* on an inactive face, continuity keeps the strict slack just past `τ`;
* over the finite face list these combine: the curve re-enters the region on a right-neighbourhood
  of `τ`, contradicting the right-accumulation of exit points.

Crucially the support condition is evaluated **at the curve's actual position** `γ τ` and only over
the **active** faces there. So distinct segments may carry distinct — even mutually conflicting —
inward normals (the genuine §4.2 chaining of attracting directions): the argument never requires one
velocity to point inward across every face at once. This is the contrast with the convex
per-half-plane route (`ZeroSeparatingCurve2D.polyRegion_invariant_of_support`), whose hypothesis
`∀ na ∈ faces, ∀ t, 0 ≤ ⟪na.1, f (γ t)⟫_ℝ` demands every face inward at every point and so only
covers the regime where a single velocity-cone is simultaneously inward for all faces.

## What this module formalizes (sorry-free)

* `eventually_forall_mem_list` — a finite-conjunction eventually lemma: if each member of a list
  satisfies a predicate eventually along a filter, the whole list does eventually (general).

* `eventually_neg_nhdsGT_of_hasDerivAt` — a real function with negative derivative at `τ` and value
  `0` there is eventually strictly negative just to the right of `τ` (via the slope characterization
  of the derivative).

* `IsStrictSupportFace` / `IsStrictSupportField` — the strict boundary-local subtangency condition:
  at every region-boundary point on the face line the velocity points *strictly* into the region,
  `0 < ⟪n, f p⟫_ℝ`. This is the faithful-curve condition where the attracting direction lies in the
  interior of the admissible slope interval.

* `polyRegion_invariant_of_strictSupport` — **boundary-local forward invariance.** A continuous
  curve solving the field on `(0, ∞)`, started strictly inside every face's half-plane, with the
  strict boundary-local support condition, stays in `polyRegion faces` for all forward time.

* `stays_away_from_zero_of_strictSupport` — **persistence.** With a separating face (unit normal,
  offset `a ≥ r > 0`), the invariant curve keeps a hard distance `r` from the origin.

The strict-interior start hypothesis `∀ nf ∈ faces, nf.2 < ⟪nf.1, γ 0⟫_ℝ` matches the persistence
setting, where the trajectory begins on the far side of the curve, strictly separated from `0`; it
also rules out an instantaneous exit from a starting boundary point, where only a right-derivative
at `0` would be available.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.SupportDiniBridge`,
`Mathlib.Analysis.Calculus.Deriv.Slope`.
-/

namespace CRNT

open Set Filter Topology
open scoped InnerProductSpace

/-! ## Generic eventually lemmas -/

/-- **Finite conjunction of eventually facts over a list.** If every member `b` of a list `L`
satisfies `Q b` eventually along a filter `l`, then eventually along `l` *all* members satisfy it.
A list induction combining the head fact with the tail conjunction. -/
theorem eventually_forall_mem_list {α β : Type*} {l : Filter α} {L : List β}
    {Q : β → α → Prop} (h : ∀ b ∈ L, ∀ᶠ x in l, Q b x) :
    ∀ᶠ x in l, ∀ b ∈ L, Q b x := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
      have h1 : ∀ᶠ x in l, Q hd x := h hd (List.mem_cons.mpr (Or.inl rfl))
      have h2 : ∀ᶠ x in l, ∀ b ∈ tl, Q b x :=
        ih (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))
      filter_upwards [h1, h2] with x hx1 hx2 b hb
      rcases List.mem_cons.mp hb with rfl | h'
      · exact hx1
      · exact hx2 b h'

/-- **Negative derivative ⇒ eventually negative just to the right.** A real function `φ` with
`HasDerivAt φ d τ`, `d < 0`, and `φ τ = 0` satisfies `φ s < 0` for all `s` in a right-neighbourhood
of `τ`. Via `hasDerivAt_iff_tendsto_slope`: the slope `(φ s − φ τ)/(s − τ)` tends to `d < 0`, so it
is eventually negative on `𝓝[≠] τ`, hence on `𝓝[>] τ`; with `φ τ = 0` and `s − τ > 0` this forces
`φ s < 0`. -/
theorem eventually_neg_nhdsGT_of_hasDerivAt {φ : ℝ → ℝ} {τ d : ℝ}
    (hd : HasDerivAt φ d τ) (hneg : d < 0) (h0 : φ τ = 0) :
    ∀ᶠ s in 𝓝[>] τ, φ s < 0 := by
  have hslope : Filter.Tendsto (slope φ τ) (𝓝[≠] τ) (𝓝 d) := hasDerivAt_iff_tendsto_slope.mp hd
  have hyev : ∀ᶠ y in 𝓝 d, y < 0 := eventually_lt_nhds hneg
  have hev : ∀ᶠ s in 𝓝[≠] τ, slope φ τ s < 0 := hslope.eventually hyev
  have hmono : 𝓝[>] τ ≤ 𝓝[≠] τ := nhdsWithin_mono τ (fun x hx => ne_of_gt hx)
  filter_upwards [hev.filter_mono hmono, self_mem_nhdsWithin] with s hs hsmem
  have hsτ : τ < s := hsmem
  rw [slope_def_field, h0, sub_zero] at hs
  rcases div_neg_iff.mp hs with ⟨_, hb⟩ | ⟨hgoal, _⟩
  · exact absurd (sub_pos.mpr hsτ) (not_lt.mpr hb.le)
  · exact hgoal

namespace ZeroSeparatingCurve2D

open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Strict boundary-local subtangency -/

/-- **Strict support face.** A face `(n, a)` is a *strict support face* of `f` on the region cut out
by `faces` when, at every region-boundary point on that face's bounding line, the velocity points
*strictly* into the region side: `0 < ⟪n, f p⟫_ℝ`. This is the faithful-curve condition with the
attracting direction in the interior of the admissible slope interval. -/
def IsStrictSupportFace (f : E → E) (faces : List (E × ℝ)) (n : E) (a : ℝ) : Prop :=
  ∀ p, OnFaceBoundary faces n a p → 0 < ⟪n, f p⟫_ℝ

/-- **Strict support field.** Every face of the list is a strict support face. -/
def IsStrictSupportField (f : E → E) (faces : List (E × ℝ)) : Prop :=
  ∀ nf ∈ faces, IsStrictSupportFace f faces nf.1 nf.2

/-! ## Boundary-local forward invariance -/

/-- **Boundary-local forward invariance of the polygonal region.** Let `γ` be a continuous curve
solving the field on `(0, ∞)` (`HasDerivAt γ (f (γ t)) t`), started strictly inside every face's
half-plane (`nf.2 < ⟪nf.1, γ 0⟫_ℝ`), with the strict boundary-local support condition
(`IsStrictSupportField f faces`). Then `γ t ∈ polyRegion faces` for all `t ≥ 0`.

The proof is a first-exit argument. If `γ` left the region, its first-exit time `τ` would be
positive (the strict-interior start keeps the curve inside on a right-neighbourhood of `0`) with
`γ τ ∈ polyRegion faces`. Each face is active (`⟪n, γ τ⟫_ℝ = a`) or inactive (`a < ⟪n, γ τ⟫_ℝ`) at
`γ τ`. On an active face, strict support `0 < ⟪n, f (γ τ)⟫_ℝ` gives the per-face slack a negative
derivative at its zero, so the face stays satisfied just past `τ`; on an inactive face continuity
does. Over the finite face list these combine to put the curve back in the region on a
right-neighbourhood of `τ`, contradicting the right-accumulation of exit points
(`exit_accumulates_right`).

The support condition is read off the curve's *actual* position `γ τ` and only at the *active*
faces there, so distinct (even conflicting) segment normals are handled without any single velocity
pointing inward across every face simultaneously. -/
theorem polyRegion_invariant_of_strictSupport {faces : List (E × ℝ)} {γ : ℝ → E} {f : E → E}
    (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (hsupp : IsStrictSupportField f faces)
    (hstart : ∀ nf ∈ faces, nf.2 < ⟪nf.1, γ 0⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    γ t ∈ polyRegion faces := by
  by_contra htR
  -- The start point lies in the region (strict interior ⇒ membership).
  have h0R : γ 0 ∈ polyRegion faces := by
    rw [mem_polyRegion]; intro nf hnf; exact (hstart nf hnf).le
  -- Hence the violating time is strictly positive.
  have ht0 : 0 < t := lt_of_le_of_ne ht (fun h => htR (h ▸ h0R))
  have hRcl : IsClosed (polyRegion faces) := isClosed_polyRegion faces
  -- The first-exit time is positive: the strict-interior start keeps the curve inside near `0`.
  have hτpos : 0 < exitTime γ (polyRegion faces) := by
    have hev0 : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ nf ∈ faces, nf.2 < ⟪nf.1, γ s⟫_ℝ := by
      apply eventually_forall_mem_list
      intro nf hnf
      have hcont : Continuous (fun s => ⟪nf.1, γ s⟫_ℝ) := continuous_const.inner hγcont
      exact (hcont.tendsto 0).eventually (eventually_gt_nhds (hstart nf hnf))
    rw [Metric.eventually_nhds_iff] at hev0
    obtain ⟨δ, hδpos, hδ⟩ := hev0
    refine lt_of_lt_of_le hδpos (le_csInf (exitSet_nonempty ht0 htR) ?_)
    intro x hx
    by_contra hxlt
    rw [not_le] at hxlt
    refine hx.2 ?_
    rw [mem_polyRegion]
    intro nf hnf
    have hdx : dist x 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]; exact hxlt
    exact (hδ hdx nf hnf).le
  set τ := exitTime γ (polyRegion faces) with hτdef
  have hτmem : γ τ ∈ polyRegion faces := mem_exitTime hγcont hRcl h0R ht0 htR
  -- Just past `τ` every face stays satisfied, so the curve re-enters the region.
  have hev : ∀ᶠ s in 𝓝[>] τ, ∀ nf ∈ faces, nf.2 ≤ ⟪nf.1, γ s⟫_ℝ := by
    apply eventually_forall_mem_list
    intro nf hnf
    have hge : nf.2 ≤ ⟪nf.1, γ τ⟫_ℝ := (mem_polyRegion.mp hτmem) nf hnf
    rcases eq_or_lt_of_le hge with hactive | hinactive
    · -- Active face: strict subtangency forces the slack down through its zero.
      have hOnF : OnFaceBoundary faces nf.1 nf.2 (γ τ) := ⟨hτmem, hactive.symm⟩
      have hpos : 0 < ⟪nf.1, f (γ τ)⟫_ℝ := hsupp nf hnf (γ τ) hOnF
      have hslack : HasDerivAt (fun s => nf.2 - ⟪nf.1, γ s⟫_ℝ) (-⟪nf.1, f (γ τ)⟫_ℝ) τ :=
        hasDerivAt_halfPlane_slack (hγ τ hτpos)
      have h0v : (fun s => nf.2 - ⟪nf.1, γ s⟫_ℝ) τ = 0 := by
        show nf.2 - ⟪nf.1, γ τ⟫_ℝ = 0; rw [← hactive]; ring
      have hneg := eventually_neg_nhdsGT_of_hasDerivAt hslack (neg_lt_zero.mpr hpos) h0v
      filter_upwards [hneg] with s hs; linarith
    · -- Inactive face: continuity keeps the strict slack.
      have hcont : Continuous (fun s => ⟪nf.1, γ s⟫_ℝ) := continuous_const.inner hγcont
      have hgt : ∀ᶠ s in 𝓝 τ, nf.2 < ⟪nf.1, γ s⟫_ℝ :=
        (hcont.tendsto τ).eventually (eventually_gt_nhds hinactive)
      exact (hgt.filter_mono nhdsWithin_le_nhds).mono (fun s hs => hs.le)
  have hevR : ∀ᶠ s in 𝓝[>] τ, γ s ∈ polyRegion faces := hev.mono (fun s hs => mem_polyRegion.mpr hs)
  obtain ⟨u, huτ, husub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevR
  have huτ' : τ < u := huτ
  obtain ⟨s, hsmem, hsR⟩ :=
    exit_accumulates_right hγcont hRcl h0R ht0 htR (ε := u - τ) (by linarith)
  have hsIoo : s ∈ Set.Ioo τ u := ⟨hsmem.1, by have := hsmem.2; linarith⟩
  exact hsR (husub hsIoo)

/-- **Persistence away from `0` via boundary-local invariance.** With a separating face `(n, a)`
(unit normal, offset `a ≥ r > 0`), the strict-support invariant curve keeps a hard distance `r`
from the origin for all forward time. -/
theorem stays_away_from_zero_of_strictSupport {faces : List (E × ℝ)} {γ : ℝ → E} {f : E → E}
    {n : E} {a r : ℝ}
    (hmem : (n, a) ∈ faces) (hn : ‖n‖ = 1) (har : r ≤ a)
    (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (hsupp : IsStrictSupportField f faces)
    (hstart : ∀ nf ∈ faces, nf.2 < ⟪nf.1, γ 0⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    r ≤ dist (γ t) 0 := by
  have hmemR : γ t ∈ polyRegion faces :=
    polyRegion_invariant_of_strictSupport hγcont hγ hsupp hstart ht
  have hcompl : γ t ∈ (Metric.ball (0 : E) r)ᶜ :=
    polyRegion_subset_compl_ball hmem hn har hmemR
  rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hcompl
  rwa [dist_zero_right]

end ZeroSeparatingCurve2D

end CRNT

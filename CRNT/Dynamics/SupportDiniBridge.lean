import CRNT.Dynamics.ClosedSetNagumo
import CRNT.Geometry.ZeroSeparatingCurve2D
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Support ⇒ distance-nonincreasing bridge for a convex polygonal region

The zero-separating region `ZeroSeparatingCurve2D.polyRegion faces` is a finite intersection
of closed half-planes `{p | a ≤ ⟪n, p⟫_ℝ}`, hence **convex**, and for a unit inward normal the
distance to a single half-plane is fully explicit. Such regions are the zero-separating surfaces of
Craciun, _Toric differential inclusions and a proof of the global attractor conjecture_. This module
discharges the half-plane case of the support ⇒ `infDist`-nonincreasing bridge and assembles it
toward the convex polyhedral region, feeding the distance-based Nagumo invariance of
`ClosedSetNagumo.lean`.

## Contents

* `infDist_dotHalfPlane` — **half-plane distance formula.** For a unit inward normal `‖n‖ = 1`,
  `Metric.infDist x (dotHalfPlane n a) = max 0 (a − ⟪n, x⟫_ℝ)`. The lower bound is Cauchy–Schwarz
  applied to every region point; the upper bound exhibits the orthogonal projection
  `x + (a − ⟪n, x⟫_ℝ) • n` when `x` is outside.

* `infDist_dotHalfPlane_eq_sub_of_notMem` / `infDist_dotHalfPlane_eq_zero_of_mem` — the two regimes
  of the formula: outside the half-plane the distance is the linear slack `a − ⟪n, x⟫_ℝ`; inside it
  is `0`.

* `hasDerivAt_halfPlane_slack` — along a curve `γ` with `HasDerivAt γ (f (γ t)) t`, the half-plane
  slack `t ↦ a − ⟪n, γ t⟫_ℝ` has derivative `−⟪n, f (γ t)⟫_ℝ`.

* `slack_antitoneOn_of_support` — **half-plane Dini monotonicity.** When the support condition
  `0 ≤ ⟪n, f (γ t)⟫_ℝ` holds on `(0, ∞)`, the slack `t ↦ a − ⟪n, γ t⟫_ℝ` has nonpositive derivative
  and is antitone on `[0, ∞)` (`antitoneOn_of_deriv_nonpos_Ici`).

* `infDist_halfPlane_antitoneOn_of_support` — support ⇒ the half-plane distance
  `t ↦ Metric.infDist (γ t) (dotHalfPlane n a)` is antitone on `[0, ∞)`: it is
  `max 0 (slack t)` with `slack` antitone, and `max 0` of an antitone function is antitone.

* `dist_le_infDist_polyRegion` — for the convex polyhedral region, every per-face slack is bounded
  by the distance to the whole region: `a − ⟪n, x⟫_ℝ ≤ Metric.infDist x (polyRegion faces)` for any
  face `(n, a)` with unit normal, since `polyRegion faces ⊆ dotHalfPlane n a`.

* `stays_in_polyRegion_of_support` / `stays_away_from_zero_of_infDist_antitone` — wiring: given that
  `t ↦ Metric.infDist (γ t) (polyRegion faces)` is antitone (the assembled bridge), the genuine
  curve stays in the region for all forward time and a fixed distance `r` from `0`.

## Scope

Established here, sorry-free and axiom-clean: the half-plane distance formula (item 1), the
half-plane Dini monotonicity (item 2) in full, the per-face slack lower bound for the convex region,
and the Nagumo wiring.

The **intersection-distance identity** for the convex polyhedral region — that
`Metric.infDist x (polyRegion faces)` is controlled *above* by the per-face slacks (the reverse of
`dist_le_infDist_polyRegion`), turning per-face support into antitonicity of the region distance —
is taken as a hypothesis, not constructed here. The per-half-plane distances bound the region
distance from below cleanly; the matching upper control is the convex-intersection projection
identity, which enters as the antitonicity hypothesis of `stays_away_from_zero_of_infDist_antitone`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.ClosedSetNagumo`,
`CRNT.Geometry.ZeroSeparatingCurve2D`.
-/

namespace CRNT

namespace ZeroSeparatingCurve2D

open Set Metric
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The half-plane distance formula -/

/-- **Lower bound on the half-plane distance.** For any normal `n` with `‖n‖ = 1`, the linear slack
`a − ⟪n, x⟫_ℝ` is a lower bound for the distance to the closed half-plane `{p | a ≤ ⟪n, p⟫_ℝ}`:
every region point `y` satisfies `a − ⟪n, x⟫_ℝ ≤ ⟪n, y − x⟫_ℝ ≤ ‖y − x‖ = dist x y` by
Cauchy–Schwarz. -/
theorem sub_le_infDist_dotHalfPlane {n : E} {a : ℝ} (hn : ‖n‖ = 1) (x : E) :
    a - ⟪n, x⟫_ℝ ≤ Metric.infDist x (dotHalfPlane n a) := by
  rcases Set.eq_empty_or_nonempty (dotHalfPlane n a) with hempty | hne
  · -- An empty half-plane forces `n = 0`, contradicting `‖n‖ = 1`.
    exfalso
    have : a • n ∈ dotHalfPlane n a := by
      rw [mem_dotHalfPlane, real_inner_smul_right, real_inner_self_eq_norm_sq, hn]
      simp
    rw [hempty] at this
    exact this
  rw [Metric.le_infDist hne]
  intro y hy
  rw [mem_dotHalfPlane] at hy
  have hcs : ⟪n, y - x⟫_ℝ ≤ ‖y - x‖ := by
    have := real_inner_le_norm n (y - x)
    rwa [hn, one_mul] at this
  have hexpand : ⟪n, y - x⟫_ℝ = ⟪n, y⟫_ℝ - ⟪n, x⟫_ℝ := inner_sub_right n y x
  calc a - ⟪n, x⟫_ℝ ≤ ⟪n, y⟫_ℝ - ⟪n, x⟫_ℝ := by linarith
    _ = ⟪n, y - x⟫_ℝ := hexpand.symm
    _ ≤ ‖y - x‖ := hcs
    _ = dist x y := by rw [dist_eq_norm, norm_sub_rev]

/-- **Half-plane distance, outside regime.** For a unit normal and a point strictly outside the
half-plane (`⟪n, x⟫_ℝ < a`), the distance equals the slack `a − ⟪n, x⟫_ℝ`. The upper bound is
witnessed by the orthogonal projection `x + (a − ⟪n, x⟫_ℝ) • n`, which lies on the bounding line
and is at distance exactly the slack. -/
theorem infDist_dotHalfPlane_eq_sub_of_notMem {n : E} {a : ℝ} (hn : ‖n‖ = 1) {x : E}
    (hx : ⟪n, x⟫_ℝ < a) :
    Metric.infDist x (dotHalfPlane n a) = a - ⟪n, x⟫_ℝ := by
  refine le_antisymm ?_ (sub_le_infDist_dotHalfPlane hn x)
  set c := a - ⟪n, x⟫_ℝ with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  set y := x + c • n with hy
  have hymem : y ∈ dotHalfPlane n a := by
    rw [mem_dotHalfPlane, hy, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hn]
    rw [hc]; ring_nf; norm_num
  have hdist : dist x y = c := by
    rw [hy, dist_eq_norm]
    have hrw : x - (x + c • n) = (-c) • n := by rw [neg_smul]; abel
    rw [hrw, norm_smul, hn, mul_one, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (le_of_lt hcpos)]
  calc Metric.infDist x (dotHalfPlane n a) ≤ dist x y := Metric.infDist_le_dist_of_mem hymem
    _ = c := hdist

/-- **Half-plane distance, inside regime.** A point inside the half-plane is at distance `0`. -/
theorem infDist_dotHalfPlane_eq_zero_of_mem {n : E} {a : ℝ} {x : E}
    (hx : x ∈ dotHalfPlane n a) :
    Metric.infDist x (dotHalfPlane n a) = 0 :=
  Metric.infDist_zero_of_mem hx

/-- **The half-plane distance formula.** For a unit inward normal `‖n‖ = 1`,
`Metric.infDist x (dotHalfPlane n a) = max 0 (a − ⟪n, x⟫_ℝ)`. -/
theorem infDist_dotHalfPlane {n : E} {a : ℝ} (hn : ‖n‖ = 1) (x : E) :
    Metric.infDist x (dotHalfPlane n a) = max 0 (a - ⟪n, x⟫_ℝ) := by
  rcases lt_or_ge (⟪n, x⟫_ℝ) a with hlt | hge
  · rw [infDist_dotHalfPlane_eq_sub_of_notMem hn hlt, max_eq_right (by linarith)]
  · have hmem : x ∈ dotHalfPlane n a := by rw [mem_dotHalfPlane]; exact hge
    rw [infDist_dotHalfPlane_eq_zero_of_mem hmem, max_eq_left (by linarith)]

/-! ## Half-plane Dini monotonicity -/

/-- The half-plane slack `t ↦ a − ⟪n, γ t⟫_ℝ` has derivative `−⟪n, f (γ t)⟫_ℝ` along a curve with
`HasDerivAt γ (f (γ t)) t`. -/
theorem hasDerivAt_halfPlane_slack {n : E} {a : ℝ} {γ : ℝ → E} {f : E → E} {t : ℝ}
    (hγ : HasDerivAt γ (f (γ t)) t) :
    HasDerivAt (fun s => a - ⟪n, γ s⟫_ℝ) (-⟪n, f (γ t)⟫_ℝ) t := by
  have hinner : HasDerivAt (fun s => ⟪n, γ s⟫_ℝ) (⟪n, f (γ t)⟫_ℝ) t := by
    have h := (hasDerivAt_const t n).inner ℝ hγ
    simpa using h
  have hsub := (hasDerivAt_const t a).sub hinner
  have heq : (-⟪n, f (γ t)⟫_ℝ) = (0 : ℝ) - ⟪n, f (γ t)⟫_ℝ := by ring
  rw [heq]
  exact hsub

/-- **Half-plane Dini monotonicity.** When the support condition `0 ≤ ⟪n, f (γ t)⟫_ℝ` holds on
`(0, ∞)`, the slack `t ↦ a − ⟪n, γ t⟫_ℝ` is antitone on `[0, ∞)`: its derivative is
`−⟪n, f (γ t)⟫_ℝ ≤ 0`. -/
theorem slack_antitoneOn_of_support {n : E} {a : ℝ} {γ : ℝ → E} {f : E → E}
    (hcont : ContinuousOn (fun s => a - ⟪n, γ s⟫_ℝ) (Set.Ici 0))
    (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (hsupp : ∀ t > 0, 0 ≤ ⟪n, f (γ t)⟫_ℝ) :
    AntitoneOn (fun s => a - ⟪n, γ s⟫_ℝ) (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos_Ici hcont
    (fun t ht => (hasDerivAt_halfPlane_slack (hγ t ht)).differentiableAt)
    (fun t ht => ?_)
  rw [(hasDerivAt_halfPlane_slack (hγ t ht)).deriv]
  exact neg_nonpos.mpr (hsupp t ht)

/-- **Support ⇒ half-plane distance nonincreasing.** Along a curve with the support condition
`0 ≤ ⟪n, f (γ t)⟫_ℝ` on `(0, ∞)`, the half-plane distance
`t ↦ Metric.infDist (γ t) (dotHalfPlane n a)` is antitone on `[0, ∞)`. It equals `max 0 (slack t)`
with `slack` antitone, and `max 0` of an antitone function is antitone. -/
theorem infDist_halfPlane_antitoneOn_of_support {n : E} {a : ℝ} {γ : ℝ → E} {f : E → E}
    (hn : ‖n‖ = 1)
    (hcont : ContinuousOn (fun s => a - ⟪n, γ s⟫_ℝ) (Set.Ici 0))
    (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (hsupp : ∀ t > 0, 0 ≤ ⟪n, f (γ t)⟫_ℝ) :
    AntitoneOn (fun s => Metric.infDist (γ s) (dotHalfPlane n a)) (Set.Ici 0) := by
  have hslack := slack_antitoneOn_of_support hcont hγ hsupp
  intro s hs u hu hsu
  simp only
  rw [infDist_dotHalfPlane hn, infDist_dotHalfPlane hn]
  exact max_le_max le_rfl (hslack hs hu hsu)

/-! ## Toward the convex polyhedral region -/

/-- **Per-face slack lower bound for the convex region.** Since `polyRegion faces` is contained in
each face's half-plane, the per-face slack `a − ⟪n, x⟫_ℝ` is a lower bound for the distance to the
nonempty region: the half-plane distance dominates the slack (`sub_le_infDist_dotHalfPlane`), and
the distance to a nonempty subset dominates the distance to the larger set. -/
theorem sub_le_infDist_polyRegion {faces : List (E × ℝ)} {n : E} {a : ℝ}
    (hmem : (n, a) ∈ faces) (hn : ‖n‖ = 1) (hne : (polyRegion faces).Nonempty) (x : E) :
    a - ⟪n, x⟫_ℝ ≤ Metric.infDist x (polyRegion faces) := by
  have hsub : polyRegion faces ⊆ dotHalfPlane n a := by
    intro p hp
    rw [mem_dotHalfPlane]
    have := hp (n, a) hmem
    simpa [mem_dotHalfPlane] using this
  calc a - ⟪n, x⟫_ℝ ≤ Metric.infDist x (dotHalfPlane n a) := sub_le_infDist_dotHalfPlane hn x
    _ ≤ Metric.infDist x (polyRegion faces) :=
      Metric.infDist_le_infDist_of_subset hsub hne

/-! ## Persistence wiring into the closed-set Nagumo rung -/

/-- **Persistence of the convex region.** Given that `t ↦ Metric.infDist (γ t) (polyRegion faces)`
is antitone on `[0, ∞)` (the assembled support ⇒ distance-nonincreasing bridge) and `γ 0` is in the
region, the genuine curve stays in the region for all forward time. -/
theorem stays_in_polyRegion_of_support {faces : List (E × ℝ)} {γ : ℝ → E}
    (h0 : γ 0 ∈ polyRegion faces)
    (hanti : AntitoneOn (fun t => Metric.infDist (γ t) (polyRegion faces)) (Set.Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    γ t ∈ polyRegion faces :=
  invariant_of_infDist_antitoneOn (isClosed_polyRegion faces) ⟨γ 0, h0⟩ h0 hanti ht

/-- **Persistence away from `0`.** With the region distance antitone and a separating face (unit
normal, offset `a ≥ r > 0`), the genuine curve stays a hard distance `r` from the origin for all
forward time. -/
theorem stays_away_from_zero_of_infDist_antitone {faces : List (E × ℝ)} {γ : ℝ → E}
    {n : E} {a r : ℝ}
    (hmem : (n, a) ∈ faces) (hn : ‖n‖ = 1) (har : r ≤ a)
    (h0 : γ 0 ∈ polyRegion faces)
    (hanti : AntitoneOn (fun t => Metric.infDist (γ t) (polyRegion faces)) (Set.Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    r ≤ dist (γ t) 0 := by
  have hmemR : γ t ∈ polyRegion faces := stays_in_polyRegion_of_support h0 hanti ht
  have hcompl : γ t ∈ (Metric.ball (0 : E) r)ᶜ :=
    polyRegion_subset_compl_ball hmem hn har hmemR
  rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hcompl
  rwa [dist_zero_right]

end ZeroSeparatingCurve2D

end CRNT

import CRNT.Theorems.DeficiencyZero.Lyapunov
import CRNT.Kinetics.Concentration
import CRNT.Dynamics.MassActionField
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Monotone

/-!
# Confinement: coercivity, positivity, and the bounded-Lipschitz cutoff

The analytic inputs to the confinement of mass-action trajectories.

* **Coercivity** (`relEntropy_coord_le`): each per-coordinate relative-entropy term grows
  superlinearly, so a sublevel set `{x ≥ 0 | relEntropy x* x ≤ C}` is bounded
  coordinatewise — trajectories along which `relEntropy` is nonincreasing stay bounded.
* **Positivity** (`pos_of_forward_deriv_ge`): a differentiable `y` with `0 < y 0` and the
  differential inequality `y' ≥ −L·y` (wherever `y > 0`) stays strictly positive on
  `[0, ∞)` — a first-crossing argument (`z = y·exp(L·)` is nondecreasing up to a
  hypothetical first zero, contradicting it). For each species `f_s(x) ≥ −L·x_s` on a
  bounded region, so a confined trajectory never reaches the boundary, keeping the relative
  entropy differentiable and the dissipation descent valid.
* **Cutoff** (`exists_cutoff`): clamping each coordinate to `[-B, B]` (`clampBox`, a
  `1`-Lipschitz retraction) and precomposing the mass-action field yields a globally
  bounded, globally Lipschitz field that agrees with `f` on the box. This is the field the
  `Flow ℝ≥0` construction (`ODE.exists_flow`) applies to; on a `relEntropy`-sublevel set
  contained in the interior of the box it coincides with the genuine dynamics.

-/

open scoped NNReal ENNReal

namespace CRNT

/-- **A solution staying-positive lemma (first crossing).** If a differentiable `y` has
`0 < y 0` and satisfies the differential inequality `y' ≥ −L·y` wherever `y > 0`, then `y`
stays strictly positive on `[0, ∞)`. The argument: at a hypothetical first zero `t₁`, the
function `z = y·exp(L·)` is nondecreasing on `[0, t₁]` (its derivative is
`(y' + L·y)·exp ≥ 0`), so `y t₁ ≥ y 0 · exp(−L t₁) > 0`, a contradiction. -/
theorem pos_of_forward_deriv_ge {y : ℝ → ℝ} {L : ℝ} (hd : ∀ t, HasDerivAt y (deriv y t) t)
    (hineq : ∀ t, 0 < y t → -L * y t ≤ deriv y t) (h0 : 0 < y 0) :
    ∀ t, 0 ≤ t → 0 < y t := by
  have hcont : Continuous y := by
    rw [continuous_iff_continuousAt]; exact fun t => (hd t).continuousAt
  intro T hT
  by_contra hyT
  rw [not_lt] at hyT
  -- the closed, nonempty, bounded-below set of bad times in `[0, T]`
  set A : Set ℝ := Set.Icc 0 T ∩ {t | y t ≤ 0} with hA
  have hAne : A.Nonempty := ⟨T, ⟨hT, le_refl T⟩, hyT⟩
  have hAcl : IsClosed A := isClosed_Icc.inter (isClosed_le hcont continuous_const)
  have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  set t₁ := sInf A with ht₁def
  have ht₁A : t₁ ∈ A := hAcl.csInf_mem hAne hAbdd
  have ht₁0 : 0 ≤ t₁ := ht₁A.1.1
  have hyt₁ : y t₁ ≤ 0 := ht₁A.2
  -- before `t₁` the function is positive
  have hpos_before : ∀ t, 0 ≤ t → t < t₁ → 0 < y t := by
    intro t ht htlt
    by_contra hle
    rw [not_lt] at hle
    exact absurd (csInf_le hAbdd ⟨⟨ht, le_trans htlt.le ht₁A.1.2⟩, hle⟩) (not_le.mpr htlt)
  have ht₁pos : 0 < t₁ := by
    rcases eq_or_lt_of_le ht₁0 with h | h
    · exact absurd (h ▸ h0) (not_lt.mpr hyt₁)
    · exact h
  -- `z = y · exp (L ·)` is nondecreasing on `[0, t₁]`
  set z : ℝ → ℝ := fun t => y t * Real.exp (L * t) with hz
  have hzd : ∀ t, HasDerivAt z ((deriv y t + L * y t) * Real.exp (L * t)) t := by
    intro t
    have he : HasDerivAt (fun s => Real.exp (L * s)) (Real.exp (L * t) * L) t := by
      simpa using (((hasDerivAt_id t).const_mul L)).exp
    have hm := (hd t).mul he
    have hval : deriv y t * Real.exp (L * t) + y t * (Real.exp (L * t) * L)
        = (deriv y t + L * y t) * Real.exp (L * t) := by ring
    rw [hz, ← hval]; exact hm
  have hzcont : Continuous z :=
    hcont.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hmono : MonotoneOn z (Set.Icc 0 t₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t₁) hzcont.continuousOn
      (fun t _ => (hzd t).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
    rw [interior_Icc, Set.mem_Ioo] at ht
    rw [(hzd t).deriv]
    have hyt : 0 < y t := hpos_before t (le_of_lt ht.1) ht.2
    exact mul_nonneg (by linarith [hineq t hyt]) (Real.exp_pos _).le
  have hz01 : z 0 ≤ z t₁ := hmono ⟨le_refl 0, ht₁0⟩ ⟨ht₁0, le_refl t₁⟩ ht₁0
  simp only [hz, mul_zero, Real.exp_zero, mul_one] at hz01
  rcases mul_pos_iff.mp (lt_of_lt_of_le h0 hz01) with ⟨hp, _⟩ | ⟨_, hn⟩
  · exact absurd hp (not_lt.mpr hyt₁)
  · exact absurd hn (not_lt.mpr (Real.exp_pos _).le)

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Superlinear growth of the relative-entropy term: if `t·log(t/a) − t + a ≤ C` (with
`a > 0`, `t ≥ 0`) then `t` is bounded by `max (e²·a) C`. -/
theorem relEntropyTerm_le_bound {a t C : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    (h : t * Real.log (t / a) - t + a ≤ C) : t ≤ max (Real.exp 2 * a) C := by
  rcases le_total t (Real.exp 2 * a) with hle | hge
  · exact le_max_of_le_left hle
  · have hta : Real.exp 2 ≤ t / a := by rw [le_div_iff₀ ha]; linarith
    have hlog : (2 : ℝ) ≤ Real.log (t / a) := by
      have := Real.log_le_log (Real.exp_pos 2) hta
      rwa [Real.log_exp] at this
    have hterm : t ≤ t * Real.log (t / a) - t + a := by
      nlinarith [mul_le_mul_of_nonneg_left hlog ht, ha.le]
    exact le_max_of_le_right (le_trans hterm h)

omit [DecidableEq S] in
/-- **Coercivity (coordinatewise).** On the nonnegative orthant, a sublevel set of the
relative entropy is bounded in each coordinate. -/
theorem relEntropy_coord_le {xstar x : Concentration S} (hxs : xstar.Positive)
    (hx : x.Nonnegative) {C : ℝ} (h : relEntropy xstar x ≤ C) (s : S) :
    x s ≤ max (Real.exp 2 * xstar s) C := by
  refine relEntropyTerm_le_bound (hxs s) (hx s) (le_trans ?_ h)
  exact Finset.single_le_sum (f := fun i => x i * Real.log (x i / xstar i) - x i + xstar i)
    (fun i _ => relEntropyTerm_nonneg (hx i) (hxs i)) (Finset.mem_univ s)

/-- Clamp every coordinate to `[-B, B]` — a `1`-Lipschitz retraction onto the box. -/
noncomputable def clampBox (B : ℝ) (x : S → ℝ) : S → ℝ := fun s => max (-B) (min B (x s))

omit [DecidableEq S] [Fintype S] in
theorem clampBox_mem {B : ℝ} (hB : 0 ≤ B) (x : S → ℝ) (s : S) : clampBox B x s ∈ Set.Icc (-B) B :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_left B (x s))⟩

omit [DecidableEq S] [Fintype S] in
theorem clampBox_eq_of_mem {B : ℝ} {x : S → ℝ} (h : ∀ s, |x s| ≤ B) : clampBox B x = x := by
  funext s
  rw [clampBox, min_eq_right (le_of_abs_le (h s)), max_eq_right (neg_le_of_abs_le (h s))]

omit [DecidableEq S] in
theorem lipschitzWith_clampBox (B : ℝ) : LipschitzWith 1 (clampBox (S := S) B) := by
  have hcl : LipschitzWith 1 (fun t : ℝ => max (-B) (min B t)) :=
    ((LipschitzWith.id (α := ℝ)).const_min B).const_max (-B)
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro s
  refine (hcl.dist_le_mul (x s) (y s)).trans ?_
  rw [NNReal.coe_one, one_mul]; exact dist_le_pi_dist x y s

/-- **Bounded-Lipschitz cutoff of the mass-action field.** Composing the field with the
clamp to `[-B, B]` yields a globally bounded Lipschitz field, agreeing with `f` on the box. -/
theorem exists_cutoff (N : Network S) (κ : RateConstants N) {B : ℝ} (hB : 0 ≤ B) :
    ∃ (K M : ℝ≥0), LipschitzWith K (N.massActionVectorField κ ∘ clampBox B) ∧
      (∀ x, ‖(N.massActionVectorField κ ∘ clampBox B) x‖ ≤ M) := by
  set box : Set (Concentration S) := Set.univ.pi (fun _ : S => Set.Icc (-B : ℝ) B) with hbox
  have hconv : Convex ℝ box := convex_pi fun _ _ => convex_Icc _ _
  have hcpt : IsCompact box := isCompact_univ_pi fun _ => isCompact_Icc
  have hmaps : ∀ x, clampBox B x ∈ box := fun x => Set.mem_univ_pi.2 fun s => clampBox_mem hB x s
  obtain ⟨K, hK⟩ := (N.massActionVectorField_contDiff κ (n := 1)).contDiffOn.exists_lipschitzOnWith
    one_ne_zero hconv hcpt
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn
    (N.massActionVectorField_contDiff κ (n := 1)).continuous.continuousOn
  refine ⟨K, Real.toNNReal C, ?_, fun x => ?_⟩
  · intro x y
    calc edist ((N.massActionVectorField κ ∘ clampBox B) x)
            ((N.massActionVectorField κ ∘ clampBox B) y)
        ≤ K * edist (clampBox B x) (clampBox B y) := hK (hmaps x) (hmaps y)
      _ ≤ K * edist x y := by
          gcongr
          have := lipschitzWith_clampBox B x y
          rwa [ENNReal.coe_one, one_mul] at this
  · calc ‖(N.massActionVectorField κ ∘ clampBox B) x‖
        ≤ C := hC _ (hmaps x)
      _ ≤ (Real.toNNReal C : ℝ) := by rw [Real.coe_toNNReal']; exact le_max_left _ _

end Network

end CRNT

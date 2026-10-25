import CRNT.Stochastic.MinimalSemigroupNonExplosion
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# An exponential drift from a square-root-dissipative Foster function

Let `J` be a jump system on a countable state space with generator
`QV(x) = ∑ᵢ rateᵢ(x) (V(nextᵢ x) − V x)` (`CRNT.JumpSystem.drift`).  A Foster function `V ≥ 0`
with `QV ≤ −f + K` gives positive recurrence; it does not give *geometric* ergodicity unless the
dissipation `f` dominates `V` itself.  This module proves the classical way around that
restriction: if

1. the jumps of `V` are of the order of `√V` (`(V(nextᵢ x) − V x)² ≤ L² (1 + V x)` whenever the
   jump `i` is enabled at `x`),
2. the absolute flux of `V` is controlled by the dissipation
   (`∑ᵢ rateᵢ(x) |V(nextᵢ x) − V x| ≤ M (f x + 1)`), and
3. the dissipation dominates `√V` (`ε² (1 + V) ≤ (f + K₀)²`),

then for a small `a > 0` the tilted function

`W = exp (a √(1 + V))`        (`CRNT.JumpSystem.expSqrt`)

satisfies the **exponential drift** `QW ≤ −c W + K'` with `c > 0`
(`CRNT.JumpSystem.exists_expSqrt_drift`), and `W` has finite sublevel sets whenever `V` does
(`CRNT.JumpSystem.expSqrt_finite`).

## The computation

Write `s = √(1 + V x)`, `s' = √(1 + V y)` for a jump `x → y`, `δ = V y − V x = s'² − s²` and
`Δ = s' − s`.  Then

* `Δ · 2s ≤ δ` (the square root is concave: `δ − 2sΔ = Δ²`),
* `|Δ| · s ≤ |δ|` (because `δ = Δ (s' + s)` and `s' + s ≥ s`), so `|Δ| ≤ L` and `Δ² s ≤ L |δ|`,
* `e^u − 1 ≤ u + e·u²` for `|u| ≤ 1` (`CRNT.exp_sub_one_le_add_sq`), applied to `u = aΔ`.

Hence, with `T = a / (2s)`,

`W y − W x = W x (e^{aΔ} − 1) ≤ W x · T · (δ + 2 e a L |δ|)`,

and summing against the rates,

`QW(x) ≤ W x · T · (QV(x) + 2 e a L ∑ rateᵢ |δᵢ|) ≤ W x · T · (−f/2 + K + 1/2)`

once `4 e a L M ≤ 1`.  The dissipation bound `f ≥ ε s − K₀` turns the right-hand side into
`W x (a B / (2 s) − a ε / 4)`, which is `≤ −(a ε / 8) W x` for `s ≥ 4B/ε` and bounded above
otherwise.

The point of the construction is that it needs only `f ≳ √V`, not `f ≳ V`.  This is exactly
the situation of the antithetic integral controller, where along the line `z₁ = 0` the
piecewise quadratic Lyapunov function grows quadratically while its dissipation grows only
linearly (`CRNT.Antithetic.lyap_no_exponential_drift`); see `CRNT.Design.AntitheticGeometric`.
-/

namespace CRNT

/-- **Second-order bound for the exponential.**  For `|u| ≤ 1`, `e^u − 1 ≤ u + e · u²`.
The proof uses only `x + 1 ≤ eˣ`: it gives `e^u − 1 ≤ u e^u` and `u ≤ e^u − 1`, and
`u (e^u − 1) ≤ u² e^{|u|}`. -/
theorem exp_sub_one_le_add_sq {u : ℝ} (hu : |u| ≤ 1) :
    Real.exp u - 1 ≤ u + Real.exp 1 * u ^ 2 := by
  have hpos := Real.exp_pos u
  have h1 : Real.exp u - 1 ≤ u * Real.exp u := by
    have h := Real.add_one_le_exp (-u)
    have hm : Real.exp (-u) * Real.exp u = 1 := by
      rw [← Real.exp_add]; simp
    have h' := mul_le_mul_of_nonneg_right h hpos.le
    nlinarith
  have h2 : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have hE : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hu1 : u ≤ 1 := (le_abs_self u).trans hu
  rcases le_total 0 u with h0 | h0
  · have h3 : Real.exp u ≤ Real.exp 1 := Real.exp_le_exp.mpr hu1
    have h4 : u * (Real.exp u - 1) ≤ u * (u * Real.exp u) := mul_le_mul_of_nonneg_left h1 h0
    have h5 : u ^ 2 * Real.exp u ≤ u ^ 2 * Real.exp 1 :=
      mul_le_mul_of_nonneg_left h3 (sq_nonneg u)
    nlinarith
  · have h4 : u * (Real.exp u - 1) ≤ u * u := mul_le_mul_of_nonpos_left h2 h0
    have h5 : u ^ 2 ≤ Real.exp 1 * u ^ 2 := by nlinarith [sq_nonneg u]
    nlinarith

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- **The exponential–square-root tilt** `x ↦ exp (a √(1 + V x))` of a function `V`. -/
noncomputable def expSqrt (a : ℝ) (V : α → ℝ) (x : α) : ℝ :=
  Real.exp (a * Real.sqrt (1 + V x))

omit [DecidableEq α] in
theorem expSqrt_pos (a : ℝ) (V : α → ℝ) (x : α) : 0 < expSqrt a V x := Real.exp_pos _

omit [DecidableEq α] in
/-- **Finite sublevel sets.**  If `V ≥ 0` has finite sublevel sets and `a > 0`, so has
`exp (a √(1 + V))`: `W x ≤ R` forces `a √(1 + V x) + 1 ≤ R`, hence `V x ≤ (R/a)²`. -/
theorem expSqrt_finite {V : α → ℝ} {a : ℝ} (ha : 0 < a) (hV : ∀ x, 0 ≤ V x)
    (hfin : ∀ R : ℝ, {x | V x ≤ R}.Finite) (R : ℝ) : {x | expSqrt a V x ≤ R}.Finite := by
  refine (hfin ((R / a) ^ 2)).subset ?_
  intro x hx
  simp only [Set.mem_setOf_eq, expSqrt] at hx ⊢
  have hVx := hV x
  have hs0 : 0 ≤ Real.sqrt (1 + V x) := Real.sqrt_nonneg _
  have hss : Real.sqrt (1 + V x) ^ 2 = 1 + V x := Real.sq_sqrt (by linarith)
  have h1 : a * Real.sqrt (1 + V x) + 1 ≤ R := (Real.add_one_le_exp _).trans hx
  have h2 : Real.sqrt (1 + V x) ≤ R / a := by
    rw [le_div_iff₀ ha]; linarith
  have h3 : Real.sqrt (1 + V x) ^ 2 ≤ (R / a) ^ 2 := pow_le_pow_left₀ hs0 h2 2
  linarith

omit [DecidableEq α] in
/-- **The one-jump estimate.**  If the jump `x → y` changes `V` by `δ` with `δ² ≤ L² (1 + V x)`,
`a L ≤ 1`, and `T = a / (2 √(1 + V x))`, then
`exp (a √(1 + V y)) − exp (a √(1 + V x)) ≤ exp (a √(1 + V x)) · T · (δ + 2 e a L |δ|)`. -/
theorem expSqrt_jump_le {V : α → ℝ} {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (haL : a * L ≤ 1)
    {x y : α} (hVx : 0 ≤ V x) (hVy : 0 ≤ V y)
    (hjump : (V y - V x) ^ 2 ≤ L ^ 2 * (1 + V x)) :
    expSqrt a V y - expSqrt a V x ≤
      expSqrt a V x * (a / (2 * Real.sqrt (1 + V x))) *
        ((V y - V x) + 2 * Real.exp 1 * a * L * |V y - V x|) := by
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (1 + V x) := ⟨_, rfl⟩
  obtain ⟨s', hs'_def⟩ : ∃ s', s' = Real.sqrt (1 + V y) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = V y - V x := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs_def]; exact Real.one_le_sqrt.mpr (by linarith)
  have hs0 : 0 < s := by linarith
  have hsne : s ≠ 0 := hs0.ne'
  have hs'0 : 0 ≤ s' := by rw [hs'_def]; exact Real.sqrt_nonneg _
  have hss : s ^ 2 = 1 + V x := by rw [hs_def]; exact Real.sq_sqrt (by linarith)
  have hss' : s' ^ 2 = 1 + V y := by rw [hs'_def]; exact Real.sq_sqrt (by linarith)
  have hWx : expSqrt a V x = Real.exp (a * s) := by unfold expSqrt; rw [← hs_def]
  have hWy : expSqrt a V y = Real.exp (a * s) * Real.exp (a * (s' - s)) := by
    unfold expSqrt; rw [← hs'_def, ← Real.exp_add]; congr 1; ring
  rw [hWx, hWy, ← hs_def, ← hδ]
  have hδsq : δ = s' ^ 2 - s ^ 2 := by rw [hδ, hss, hss']; ring
  -- concavity of the square root
  have hΔ1 : (s' - s) * (2 * s) ≤ δ := by rw [hδsq]; nlinarith [sq_nonneg (s' - s)]
  have hδfac : δ = (s' - s) * (s' + s) := by rw [hδsq]; ring
  have habsΔ : |s' - s| * s ≤ |δ| := by
    rw [hδfac, abs_mul, abs_of_nonneg (by linarith : 0 ≤ s' + s)]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hδL : |δ| ≤ L * s := by
    have h := hjump
    rw [← hδ, ← hss] at h
    have h2 : |δ| ^ 2 ≤ (L * s) ^ 2 := by rw [sq_abs, mul_pow]; exact h
    exact (sq_le_sq₀ (abs_nonneg δ) (mul_nonneg hL hs0.le)).mp h2
  have hΔL : |s' - s| ≤ L := le_of_mul_le_mul_right (habsΔ.trans hδL) hs0
  have hu : |a * (s' - s)| ≤ 1 := by
    rw [abs_mul, abs_of_pos ha]
    calc a * |s' - s| ≤ a * L := mul_le_mul_of_nonneg_left hΔL ha.le
      _ ≤ 1 := haL
  have hexp := exp_sub_one_le_add_sq hu
  -- the first-order term
  have hfirst : a * (s' - s) ≤ a / (2 * s) * δ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    calc a * (s' - s) * (2 * s) = a * ((s' - s) * (2 * s)) := by ring
      _ ≤ a * δ := mul_le_mul_of_nonneg_left hΔ1 ha.le
  -- the second-order term
  have hsecond : Real.exp 1 * (a * (s' - s)) ^ 2 ≤
      a / (2 * s) * (2 * Real.exp 1 * a * L * |δ|) := by
    have hsq : (s' - s) ^ 2 * s ≤ L * |δ| := by
      calc (s' - s) ^ 2 * s = |s' - s| * (|s' - s| * s) := by rw [← sq_abs]; ring
        _ ≤ L * |δ| := mul_le_mul hΔL habsΔ (by positivity) hL
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have hE0 : 0 ≤ Real.exp 1 * a ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hsq hE0
    nlinarith [h]
  have key : Real.exp (a * (s' - s)) - 1 ≤
      a / (2 * s) * (δ + 2 * Real.exp 1 * a * L * |δ|) := by
    have : a / (2 * s) * (δ + 2 * Real.exp 1 * a * L * |δ|) =
        a / (2 * s) * δ + a / (2 * s) * (2 * Real.exp 1 * a * L * |δ|) := by ring
    rw [this]; linarith
  have hW0 := Real.exp_pos (a * s)
  calc Real.exp (a * s) * Real.exp (a * (s' - s)) - Real.exp (a * s)
      = Real.exp (a * s) * (Real.exp (a * (s' - s)) - 1) := by ring
    _ ≤ Real.exp (a * s) * (a / (2 * s) * (δ + 2 * Real.exp 1 * a * L * |δ|)) :=
      mul_le_mul_of_nonneg_left key hW0.le
    _ = Real.exp (a * s) * (a / (2 * s)) * (δ + 2 * Real.exp 1 * a * L * |δ|) := by ring

/-- **The exponential drift of the exponential–square-root tilt.**  Let `V ≥ 0` satisfy the
Foster drift `QV ≤ −f + K` with `f ≥ 0`, and suppose

* `hjump`: every enabled jump changes `V` by at most `L √(1 + V)` (in squared form),
* `habs`: the absolute flux of `V` is at most `M (f + 1)`,
* `hcoer`: the dissipation dominates `√V`: `ε² (1 + V) ≤ (f + K₀)²`.

Then there are `a > 0`, `c > 0` and `K' ≥ 0` with
`Q (exp (a √(1 + V))) ≤ −c · exp (a √(1 + V)) + K'` everywhere. -/
theorem exists_expSqrt_drift (V f : α → ℝ) {K L M ε K₀ : ℝ}
    (hV : ∀ x, 0 ≤ V x) (hf : ∀ x, 0 ≤ f x) (hK : 0 ≤ K) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hε : 0 < ε) (hK₀ : 0 ≤ K₀)
    (hdrift : ∀ x, J.drift V x ≤ -f x + K)
    (hjump : ∀ i x, 0 < J.rate i x → (V (J.next i x) - V x) ^ 2 ≤ L ^ 2 * (1 + V x))
    (habs : ∀ x, ∑ i, J.rate i x * |V (J.next i x) - V x| ≤ M * (f x + 1))
    (hcoer : ∀ x, ε ^ 2 * (1 + V x) ≤ (f x + K₀) ^ 2) :
    ∃ a : ℝ, 0 < a ∧ ∃ c : ℝ, 0 < c ∧ ∃ K' : ℝ, 0 ≤ K' ∧
      ∀ x, J.drift (expSqrt a V) x ≤ -c * expSqrt a V x + K' := by
  have hE0 : 0 < Real.exp 1 := Real.exp_pos 1
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp 1 := ⟨_, rfl⟩
  have hE0' : 0 < E := by rw [hE]; exact hE0
  have hden : 0 < 1 + L + 4 * E * L * M := by positivity
  obtain ⟨a, ha_def⟩ : ∃ a, a = 1 / (1 + L + 4 * E * L * M) := ⟨_, rfl⟩
  have ha : 0 < a := by rw [ha_def]; positivity
  have hprod : a * (1 + L + 4 * E * L * M) = 1 := by
    rw [ha_def, one_div, inv_mul_cancel₀ hden.ne']
  have hELM : 0 ≤ E * L * M := by positivity
  have haELM : 0 ≤ a * (E * L * M) := mul_nonneg ha.le hELM
  have haL0 : 0 ≤ a * L := mul_nonneg ha.le hL
  have haL : a * L ≤ 1 := by nlinarith
  have haM : 4 * (a * (E * L * M)) ≤ 1 := by nlinarith
  obtain ⟨B, hB_def⟩ : ∃ B, B = K₀ / 2 + K + 1 / 2 := ⟨_, rfl⟩
  have hB : 0 < B := by rw [hB_def]; positivity
  refine ⟨a, ha, a * ε / 8, by positivity, a * B / 2 * Real.exp (a * (4 * B / ε)), by positivity,
    fun x => ?_⟩
  have hVx := hV x
  have hfx := hf x
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (1 + V x) := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs_def]; exact Real.one_le_sqrt.mpr (by linarith)
  have hs0 : 0 < s := by linarith
  have hsne : s ≠ 0 := hs0.ne'
  have hss : s ^ 2 = 1 + V x := by rw [hs_def]; exact Real.sq_sqrt (by linarith)
  have hWx : expSqrt a V x = Real.exp (a * s) := by unfold expSqrt; rw [← hs_def]
  obtain ⟨T, hT⟩ : ∃ T, T = a / (2 * s) := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hTs : T * (2 * s) = a := by rw [hT, div_mul_cancel₀ a (by positivity : (2 * s) ≠ 0)]
  -- the termwise bound
  have hterm : ∀ i, J.rate i x * (expSqrt a V (J.next i x) - expSqrt a V x) ≤
      Real.exp (a * s) * T * (J.rate i x * (V (J.next i x) - V x)) +
      Real.exp (a * s) * T * (2 * E * a * L) * (J.rate i x * |V (J.next i x) - V x|) := by
    intro i
    rcases (J.rate_nonneg i x).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hj := expSqrt_jump_le ha hL haL hVx (hV (J.next i x)) (hjump i x hpos)
      rw [hWx, ← hs_def, ← hT, ← hE] at hj
      rw [hWx]
      calc J.rate i x * (expSqrt a V (J.next i x) - Real.exp (a * s))
          ≤ J.rate i x * (Real.exp (a * s) * T *
              ((V (J.next i x) - V x) + 2 * E * a * L * |V (J.next i x) - V x|)) :=
            mul_le_mul_of_nonneg_left hj hpos.le
        _ = Real.exp (a * s) * T * (J.rate i x * (V (J.next i x) - V x)) +
            Real.exp (a * s) * T * (2 * E * a * L) * (J.rate i x * |V (J.next i x) - V x|) := by
          ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset J.ι)) => hterm i)
  have hdriftW : J.drift (expSqrt a V) x ≤
      Real.exp (a * s) * T * J.drift V x +
      Real.exp (a * s) * T * (2 * E * a * L) * ∑ i, J.rate i x * |V (J.next i x) - V x| := by
    unfold JumpSystem.drift
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact hsum
  have hP0 : 0 ≤ Real.exp (a * s) * T := by positivity
  have hQ0 : 0 ≤ Real.exp (a * s) * T * (2 * E * a * L) := by positivity
  have h1 := mul_le_mul_of_nonneg_left (hdrift x) hP0
  have h2 := mul_le_mul_of_nonneg_left (habs x) hQ0
  -- `2 e a L M (f + 1) ≤ (f + 1) / 2`
  have h3 : 2 * E * a * L * (M * (f x + 1)) ≤ (f x + 1) / 2 := by
    have h3' : 0 ≤ (1 / 2 - 2 * E * a * L * M) * (f x + 1) :=
      mul_nonneg (by nlinarith) (by linarith)
    nlinarith
  have h3P := mul_le_mul_of_nonneg_left h3 hP0
  -- the coercivity `ε s ≤ f + K₀`
  have hcx : ε * s ≤ f x + K₀ := by
    have h := hcoer x
    rw [← hss] at h
    have h2 : (ε * s) ^ 2 ≤ (f x + K₀) ^ 2 := by rw [mul_pow]; exact h
    exact (sq_le_sq₀ (by positivity) (by linarith)).mp h2
  -- assemble: `QW ≤ W T (B − ε s / 2)`
  have hG : J.drift (expSqrt a V) x ≤ Real.exp (a * s) * T * (B - ε * s / 2) := by
    have e1 : Real.exp (a * s) * T * (2 * E * a * L) * (M * (f x + 1)) =
        Real.exp (a * s) * T * (2 * E * a * L * (M * (f x + 1))) := by ring
    have h4 : Real.exp (a * s) * T * (-f x + K) +
        Real.exp (a * s) * T * ((f x + 1) / 2) ≤ Real.exp (a * s) * T * (B - ε * s / 2) := by
      have : -f x + K + (f x + 1) / 2 ≤ B - ε * s / 2 := by rw [hB_def]; linarith
      have := mul_le_mul_of_nonneg_left this hP0
      linarith [this]
    linarith [hdriftW, h1, h2, h3P, e1, h4]
  -- `W T (B − ε s/2) = W (T B) − W (a ε / 4)`
  have hWT : Real.exp (a * s) * T * (B - ε * s / 2) =
      Real.exp (a * s) * (T * B) - Real.exp (a * s) * (a * ε / 4) := by
    have : T * s = a / 2 := by linarith [hTs]
    calc Real.exp (a * s) * T * (B - ε * s / 2)
        = Real.exp (a * s) * (T * B) - Real.exp (a * s) * (ε / 2) * (T * s) := by ring
      _ = Real.exp (a * s) * (T * B) - Real.exp (a * s) * (a * ε / 4) := by rw [this]; ring
  rw [hWx]
  have hW0 := Real.exp_pos (a * s)
  have hK'0 : 0 ≤ a * B / 2 * Real.exp (a * (4 * B / ε)) := by positivity
  rcases le_or_gt (4 * B) (ε * s) with hbig | hsmall
  · -- far from the origin: `T B ≤ a ε / 8`
    have hTB : T * B ≤ a * ε / 8 := by
      have hmul : T * B * (2 * s) ≤ a * ε / 8 * (2 * s) := by
        have e : T * B * (2 * s) = a * B := by rw [mul_right_comm, hTs]
        rw [e]
        have : a * (4 * B) ≤ a * (ε * s) := mul_le_mul_of_nonneg_left hbig ha.le
        linarith
      exact le_of_mul_le_mul_right hmul (by positivity)
    have := mul_le_mul_of_nonneg_left hTB hW0.le
    linarith [hG, hWT, this, hK'0]
  · -- near the origin: everything is bounded
    have hsle : s ≤ 4 * B / ε := by rw [le_div_iff₀ hε]; linarith
    have hWle : Real.exp (a * s) ≤ Real.exp (a * (4 * B / ε)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsle ha.le)
    have hTle : T ≤ a / 2 := by
      have : T * 2 ≤ T * (2 * s) := mul_le_mul_of_nonneg_left (by linarith) hT0
      linarith
    have hTB : T * B ≤ a * B / 2 := by
      have := mul_le_mul_of_nonneg_right hTle hB.le
      linarith
    have hTB0 : 0 ≤ T * B := mul_nonneg hT0 hB.le
    have h5 : Real.exp (a * s) * (T * B) ≤ Real.exp (a * (4 * B / ε)) * (a * B / 2) :=
      mul_le_mul hWle hTB hTB0 (Real.exp_pos _).le
    have h6 : 0 ≤ Real.exp (a * s) * (a * ε / 8) := by positivity
    linarith [hG, hWT, h5, h6]

end JumpSystem

end CRNT

#print axioms CRNT.exp_sub_one_le_add_sq
#print axioms CRNT.JumpSystem.expSqrt_finite
#print axioms CRNT.JumpSystem.expSqrt_jump_le
#print axioms CRNT.JumpSystem.exists_expSqrt_drift

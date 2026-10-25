import CRNT.Dynamics.OmegaLimitOrderConvex
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The comparability hypothesis of `omegaLimit_orderConvex_of_monotone_flow` cannot be dropped

`CRNT.omegaLimit_orderConvex_of_monotone_flow` proves that the ω-limit set of a bounded orbit of a
monotone semiflow is order-convex when it consists of equilibria, the equilibrium set is
order-convex, **and the orbit is order-comparable with every test point** (`hcmp`). This module
shows that the statement without `hcmp` (`GeneralClaim`) is false (`not_generalClaim`).

## The counterexample

On `ℝ⁴ = Concentration (Fin 4)` with the componentwise order:

* `U t x = x / (1 + |x| t)`, the flow of `ẋ = −x|x|`, drives the coordinates `0` and `1`;
* `G σ y = y + |y| σ(−log |y|) / 4` with `σ₁ = sin`, `σ₂ = −cos` is continuous and nondecreasing
  (`G_mono`: `u ↦ u (1 ± σ(−log u)/4)` is nondecreasing because `σ` is `1`-Lipschitz and bounded by
  `1`);
* the coordinates `2, 3` are `zᵢ + ∫₀ᵗ (U s x + G σᵢ (U s y)) ds`.

The semiflow is monotone (`flow_monotone`), its fixed points are the points with vanishing
coordinates `0, 1` (`fixed_of_zero`, `zero_of_fixed`), an order-convex set. From
`x₀ = (1, −1, 0, 0)` the `U`-coordinates are `±1/(1+t)` and the integrands collapse to
`σᵢ(log(1+s)) / (4(1+s))`, so exactly
`z(t) = ((1 − cos θ)/4, −(sin θ)/4)` with `θ = log(1+t)`: the orbit runs around the circle of radius
`1/4` about `(1/4, 0)` forever (`orbit_two`, `orbit_three`). The ω-limit set contains `P = 0` and
`Q = (0, 0, 1/2, 0)` (`P_mem`, `Q_mem`), lies on the circle (`omega_circle`), and so misses the
centre `W = (0, 0, 1/4, 0)`, which is a fixed point between `P` and `Q`.

This is the four-dimensional version of `docs/notes/d14-order-convexity-counterexample.md`, with
the clock `log(1 + t)` of the decay `1/(1+t)` in place of `(t + c)^{1/4}`.
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped NNReal

namespace CRNT
namespace OmegaOrderConvexCounterexample

/-! ## The claim -/

/-- **The order-convexity statement without the comparability hypothesis.** -/
def GeneralClaim : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (ϕ : Flow ℝ≥0 (Concentration S)),
    CRNT.Monotone.IsMonotoneFlow ϕ →
    ∀ (x₀ : Concentration S) (K : Set (Concentration S)), IsCompact K →
    (∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K) →
    (∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ≥0, ϕ t y = y) →
    (∀ p q z : Concentration S, (∀ t : ℝ≥0, ϕ t p = p) → (∀ t : ℝ≥0, ϕ t q = q) →
      p ≤ z → z ≤ q → ∀ t : ℝ≥0, ϕ t z = z) →
    ∀ p q z : Concentration S, p ∈ omegaLimit atTop ϕ {x₀} → q ∈ omegaLimit atTop ϕ {x₀} →
      p ≤ z → z ≤ q → z ∈ omegaLimit atTop ϕ {x₀}

/-! ## The decay `U` -/

/-- `U t x = x / (1 + |x| t)` (time clamped at `0`), the flow of `ẋ = −x|x|`. -/
noncomputable def U (t x : ℝ) : ℝ := x / (1 + |x| * max t 0)

theorem U_den_pos (t x : ℝ) : 0 < 1 + |x| * max t 0 :=
  add_pos_of_pos_of_nonneg one_pos (mul_nonneg (abs_nonneg x) (le_max_right t 0))

theorem U_zero_left (x : ℝ) : U 0 x = x := by
  unfold U; simp

theorem U_zero_right (t : ℝ) : U t 0 = 0 := by
  unfold U; simp

theorem U_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : ℝ) : U s (U t x) = U (s + t) x := by
  unfold U
  rw [max_eq_left hs, max_eq_left ht, max_eq_left (add_nonneg hs ht)]
  have hd : 0 < 1 + |x| * t := add_pos_of_pos_of_nonneg one_pos (mul_nonneg (abs_nonneg x) ht)
  have hdne : 1 + |x| * t ≠ 0 := hd.ne'
  rw [abs_div, abs_of_pos hd, div_div]
  congr 1
  field_simp
  ring

theorem U_mono (t : ℝ) : Monotone (U t) := by
  intro x y hxy
  unfold U
  have hc : 0 ≤ max t 0 := le_max_right t 0
  rw [div_le_div_iff₀ (U_den_pos t x) (U_den_pos t y)]
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]; nlinarith [mul_nonneg hx hc]
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    subst hx0; subst hy0; simp
  · rw [abs_of_nonpos hx, abs_of_nonneg hy]
    nlinarith [mul_nonneg (mul_nonneg hy (neg_nonneg.mpr hx)) hc]
  · rw [abs_of_nonpos hx, abs_of_nonpos hy]; nlinarith [mul_nonneg (neg_nonneg.mpr hy) hc]

theorem U_cont : Continuous (fun q : ℝ × ℝ => U q.1 q.2) := by
  unfold U
  exact continuous_snd.div (continuous_const.add ((continuous_abs.comp continuous_snd).mul
    (continuous_fst.max continuous_const))) (fun q => (U_den_pos q.1 q.2).ne')

theorem U_one {s : ℝ} (hs : 0 ≤ s) : U s 1 = 1 / (1 + s) := by
  unfold U; rw [max_eq_left hs, abs_one, one_mul]

theorem U_neg_one {s : ℝ} (hs : 0 ≤ s) : U s (-1) = -1 / (1 + s) := by
  unfold U; rw [max_eq_left hs, abs_neg, abs_one, one_mul]

theorem U_one_fixed {x : ℝ} (h : U 1 x = x) : x = 0 := by
  unfold U at h
  rw [max_eq_left zero_le_one, mul_one] at h
  have hd : 0 < 1 + |x| := add_pos_of_pos_of_nonneg one_pos (abs_nonneg x)
  rw [div_eq_iff hd.ne'] at h
  have hx : x * |x| = 0 := by linarith
  rcases mul_eq_zero.mp hx with h' | h'
  · exact h'
  · exact abs_eq_zero.mp h'

/-! ## The couplings `G σ` -/

/-- `|sin v| ≤ |v|`. -/
theorem abs_sin_le_abs_self (v : ℝ) : |Real.sin v| ≤ |v| := by
  have key : ∀ w : ℝ, 0 ≤ w → |Real.sin w| ≤ w := by
    intro w hw
    rw [abs_le]
    refine ⟨?_, Real.sin_le hw⟩
    rcases le_or_gt 1 w with h1 | h1
    · linarith [Real.neg_one_le_sin w]
    · have : 0 ≤ Real.sin w :=
        Real.sin_nonneg_of_nonneg_of_le_pi hw (by linarith [Real.pi_gt_three])
      linarith
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]; exact key v hv
  · have := key (-v) (neg_nonneg.mpr hv)
    rw [Real.sin_neg, abs_neg] at this
    rw [abs_of_nonpos hv]; exact this

theorem sin_lipschitz (a b : ℝ) : |Real.sin a - Real.sin b| ≤ |a - b| := by
  rw [Real.sin_sub_sin, abs_mul, abs_mul]
  have h1 := abs_sin_le_abs_self ((a - b) / 2)
  have h2 := Real.abs_cos_le_one ((a + b) / 2)
  have h3 : |(2 : ℝ)| = 2 := abs_of_pos two_pos
  rw [h3]
  have h4 : |(a - b) / 2| = |a - b| / 2 := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [h4] at h1
  calc 2 * |Real.sin ((a - b) / 2)| * |Real.cos ((a + b) / 2)|
      ≤ 2 * (|a - b| / 2) * 1 := by
        apply mul_le_mul (by linarith) h2 (abs_nonneg _) (by positivity)
    _ = |a - b| := by ring

theorem negCos_lipschitz (a b : ℝ) : |-Real.cos a - -Real.cos b| ≤ |a - b| := by
  rw [show -Real.cos a - -Real.cos b = Real.cos b - Real.cos a by ring, Real.cos_sub_cos,
    abs_mul, abs_mul]
  have h1 := abs_sin_le_abs_self ((b - a) / 2)
  have h2 := Real.abs_sin_le_one ((b + a) / 2)
  have h3 : |(-2 : ℝ)| = 2 := by norm_num
  rw [h3]
  have h4 : |(b - a) / 2| = |a - b| / 2 := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm]
  rw [h4] at h1
  calc 2 * |Real.sin ((b + a) / 2)| * |Real.sin ((b - a) / 2)|
      ≤ 2 * 1 * (|a - b| / 2) := by
        apply mul_le_mul (by linarith) h1 (abs_nonneg _) (by positivity)
    _ = |a - b| := by ring

/-- The two oscillators. -/
noncomputable def σ₁ : ℝ → ℝ := Real.sin
noncomputable def σ₂ : ℝ → ℝ := fun θ => -Real.cos θ

theorem σ₁_bound (θ : ℝ) : |σ₁ θ| ≤ 1 := Real.abs_sin_le_one θ
theorem σ₂_bound (θ : ℝ) : |σ₂ θ| ≤ 1 := by
  show |-Real.cos θ| ≤ 1; rw [abs_neg]; exact Real.abs_cos_le_one θ
theorem σ₁_lip (a b : ℝ) : |σ₁ a - σ₁ b| ≤ |a - b| := sin_lipschitz a b
theorem σ₂_lip (a b : ℝ) : |σ₂ a - σ₂ b| ≤ |a - b| := negCos_lipschitz a b
theorem σ₁_cont : Continuous σ₁ := Real.continuous_sin
theorem σ₂_cont : Continuous σ₂ := Real.continuous_cos.neg

/-- **The monotonicity estimate**: for `|κ| ≤ 1/4` and `σ` bounded by `1` and `1`-Lipschitz,
`u ↦ u (1 + κ σ(−log u))` is nondecreasing on `(0, ∞)`. -/
theorem mul_one_add_mono {σ : ℝ → ℝ} (hσ1 : ∀ θ, |σ θ| ≤ 1)
    (hσL : ∀ a b, |σ a - σ b| ≤ |a - b|) {κ : ℝ} (hκ : |κ| ≤ 1 / 4) {u u' : ℝ} (hu : 0 < u)
    (huu : u ≤ u') :
    u * (1 + κ * σ (-Real.log u)) ≤ u' * (1 + κ * σ (-Real.log u')) := by
  have hu' : 0 < u' := hu.trans_le huu
  have hlogle : Real.log u ≤ Real.log u' := Real.log_le_log hu huu
  have hlog : Real.log u' - Real.log u ≤ u' / u - 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hu' hu)
    rwa [Real.log_div hu'.ne' hu.ne'] at this
  have h1 : u * (Real.log u' - Real.log u) ≤ u' - u := by
    have h := mul_le_mul_of_nonneg_left hlog hu.le
    have e : u * (u' / u - 1) = u' - u := by field_simp
    linarith
  have hL : |σ (-Real.log u') - σ (-Real.log u)| ≤ Real.log u' - Real.log u := by
    have h := hσL (-Real.log u') (-Real.log u)
    rwa [show -Real.log u' - -Real.log u = -(Real.log u' - Real.log u) by ring, abs_neg,
      abs_of_nonneg (sub_nonneg.mpr hlogle)] at h
  have e1 : -(1 / 4) ≤ κ * σ (-Real.log u') := by
    have h : |κ * σ (-Real.log u')| ≤ 1 / 4 := by
      rw [abs_mul]
      calc |κ| * |σ (-Real.log u')| ≤ 1 / 4 * 1 :=
            mul_le_mul hκ (hσ1 _) (abs_nonneg _) (by norm_num)
        _ = 1 / 4 := by norm_num
    linarith [neg_abs_le (κ * σ (-Real.log u'))]
  have e2 : -(1 / 4) * (Real.log u' - Real.log u) ≤
      κ * (σ (-Real.log u') - σ (-Real.log u)) := by
    have h : |κ * (σ (-Real.log u') - σ (-Real.log u))| ≤ 1 / 4 * (Real.log u' - Real.log u) := by
      rw [abs_mul]; exact mul_le_mul hκ hL (abs_nonneg _) (by norm_num)
    linarith [neg_abs_le (κ * (σ (-Real.log u') - σ (-Real.log u)))]
  have p1 : 0 ≤ (u' - u) * (κ * σ (-Real.log u') + 1 / 4) :=
    mul_nonneg (sub_nonneg.mpr huu) (by linarith)
  have p2 := mul_le_mul_of_nonneg_left e2 hu.le
  nlinarith [p1, p2, h1, huu]

/-- **The coupling** `G σ y = y + |y| σ(−log |y|) / 4`. -/
noncomputable def G (σ : ℝ → ℝ) (y : ℝ) : ℝ := y + |y| * σ (-Real.log |y|) / 4

theorem G_zero (σ : ℝ → ℝ) : G σ 0 = 0 := by
  unfold G; simp

theorem G_mono {σ : ℝ → ℝ} (hσ1 : ∀ θ, |σ θ| ≤ 1) (hσL : ∀ a b, |σ a - σ b| ≤ |a - b|) :
    Monotone (G σ) := by
  intro y y' hyy
  rcases lt_or_ge 0 y with hy | hy
  · have hy' : 0 < y' := hy.trans_le hyy
    have h := mul_one_add_mono hσ1 hσL (κ := 1 / 4) (le_of_eq (abs_of_pos (by norm_num))) hy hyy
    unfold G
    rw [abs_of_pos hy, abs_of_pos hy']
    linarith
  · rcases lt_or_ge y' 0 with hy' | hy'
    · have hy0 : y < 0 := lt_of_le_of_lt hyy hy'
      have h := mul_one_add_mono hσ1 hσL (κ := -(1 / 4))
        (le_of_eq (by rw [abs_neg]; exact abs_of_pos (by norm_num))) (neg_pos.mpr hy')
        (neg_le_neg hyy)
      unfold G
      rw [abs_of_neg hy0, abs_of_neg hy']
      linarith
    · have hb := abs_le.mp (hσ1 (-Real.log |y|))
      have hb' := abs_le.mp (hσ1 (-Real.log |y'|))
      have g1 : G σ y ≤ 0 := by
        unfold G
        rw [abs_of_nonpos hy]
        have := mul_le_mul_of_nonpos_left (abs_of_nonpos hy ▸ hb.2) hy
        nlinarith [this]
      have g2 : 0 ≤ G σ y' := by
        unfold G
        rw [abs_of_nonneg hy']
        have := mul_le_mul_of_nonneg_left (abs_of_nonneg hy' ▸ hb'.1) hy'
        nlinarith [this]
      linarith

theorem G_cont {σ : ℝ → ℝ} (hσc : Continuous σ) (hσ1 : ∀ θ, |σ θ| ≤ 1) : Continuous (G σ) := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · show Tendsto (G σ) (𝓝 0) (𝓝 (G σ 0))
    rw [G_zero]
    have hbound : ∀ z : ℝ, ‖G σ z‖ ≤ 5 / 4 * |z| := by
      intro z
      rw [Real.norm_eq_abs]
      have hb := abs_le.mp (hσ1 (-Real.log |z|))
      have u1 : |z| * σ (-Real.log |z|) ≤ |z| := by
        have := mul_le_mul_of_nonneg_left hb.2 (abs_nonneg z); linarith
      have u2 : -|z| ≤ |z| * σ (-Real.log |z|) := by
        have := mul_le_mul_of_nonneg_left hb.1 (abs_nonneg z); linarith
      unfold G
      rw [abs_le]
      constructor <;> linarith [neg_abs_le z, le_abs_self z]
    have hlim : Tendsto (fun z : ℝ => 5 / 4 * |z|) (𝓝 0) (𝓝 0) := by
      have := ((continuous_abs.tendsto (0 : ℝ)).const_mul (5 / 4 : ℝ))
      simpa using this
    exact squeeze_zero_norm hbound hlim
  · have hlog : ContinuousAt (fun z : ℝ => Real.log |z|) y :=
      (Real.continuousAt_log (abs_ne_zero.mpr hy)).comp continuous_abs.continuousAt
    have hσ' : ContinuousAt (fun z : ℝ => σ (-Real.log |z|)) y :=
      hσc.continuousAt.comp hlog.neg
    exact continuousAt_id.add ((continuous_abs.continuousAt.mul hσ').div_const 4)

/-! ## The semiflow -/

/-- The integrand of the `z`-coordinates. -/
noncomputable def integrand (σ : ℝ → ℝ) (p : Concentration (Fin 4)) (s : ℝ) : ℝ :=
  U s (p 0) + G σ (U s (p 1))

theorem integrand_cont {σ : ℝ → ℝ} (hσc : Continuous σ) (hσ1 : ∀ θ, |σ θ| ≤ 1) :
    Continuous (fun q : Concentration (Fin 4) × ℝ => integrand σ q.1 q.2) := by
  unfold integrand
  have h0 : Continuous (fun q : Concentration (Fin 4) × ℝ => U q.2 (q.1 0)) :=
    U_cont.comp (continuous_snd.prodMk ((continuous_apply 0).comp continuous_fst))
  have h1 : Continuous (fun q : Concentration (Fin 4) × ℝ => U q.2 (q.1 1)) :=
    U_cont.comp (continuous_snd.prodMk ((continuous_apply 1).comp continuous_fst))
  exact h0.add ((G_cont hσc hσ1).comp h1)

theorem integrand_cont_s {σ : ℝ → ℝ} (hσc : Continuous σ) (hσ1 : ∀ θ, |σ θ| ≤ 1)
    (p : Concentration (Fin 4)) : Continuous (integrand σ p) :=
  (integrand_cont hσc hσ1).comp (continuous_const.prodMk continuous_id)

theorem integrand_zero (σ : ℝ → ℝ) {z : Concentration (Fin 4)} (h0 : z 0 = 0) (h1 : z 1 = 0)
    (s : ℝ) : integrand σ z s = 0 := by
  unfold integrand; rw [h0, h1, U_zero_right, G_zero, add_zero]

/-- The `z`-integral over `[t₂, t₂ + t₁]` is the `z`-integral of the shifted point. -/
theorem integral_shift {σ : ℝ → ℝ} (hσc : Continuous σ) (hσ1 : ∀ θ, |σ θ| ≤ 1)
    (p q : Concentration (Fin 4)) {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (hq0 : q 0 = U t₂ (p 0)) (hq1 : q 1 = U t₂ (p 1)) :
    ∫ s in (0 : ℝ)..(t₁ + t₂), integrand σ p s =
      (∫ s in (0 : ℝ)..t₂, integrand σ p s) + ∫ s in (0 : ℝ)..t₁, integrand σ q s := by
  have hcongr : EqOn (integrand σ q) (fun s => integrand σ p (s + t₂)) (uIcc 0 t₁) := by
    intro s hs
    rw [Set.uIcc_of_le ht₁] at hs
    show U s (q 0) + G σ (U s (q 1)) = U (s + t₂) (p 0) + G σ (U (s + t₂) (p 1))
    rw [hq0, hq1, U_add hs.1 ht₂, U_add hs.1 ht₂]
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_comp_add_right (fun s => integrand σ p s) t₂, zero_add,
    add_comm t₁ t₂]
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((integrand_cont_s hσc hσ1 p).intervalIntegrable _ _)
    ((integrand_cont_s hσc hσ1 p).intervalIntegrable _ _)).symm

/-- The semiflow. -/
noncomputable def flowFun (t : ℝ≥0) (p : Concentration (Fin 4)) : Concentration (Fin 4) :=
  ![U t (p 0), U t (p 1), p 2 + ∫ s in (0 : ℝ)..(t : ℝ), integrand σ₁ p s,
    p 3 + ∫ s in (0 : ℝ)..(t : ℝ), integrand σ₂ p s]

/-- **The semiflow** as a `Flow ℝ≥0 (Concentration (Fin 4))`. -/
noncomputable def flow : Flow ℝ≥0 (Concentration (Fin 4)) where
  toFun := flowFun
  cont' := by
    apply continuous_pi
    intro i
    fin_cases i
    · show Continuous fun q : ℝ≥0 × Concentration (Fin 4) => U (q.1 : ℝ) (q.2 0)
      exact U_cont.comp ((NNReal.continuous_coe.comp continuous_fst).prodMk
        ((continuous_apply 0).comp continuous_snd))
    · show Continuous fun q : ℝ≥0 × Concentration (Fin 4) => U (q.1 : ℝ) (q.2 1)
      exact U_cont.comp ((NNReal.continuous_coe.comp continuous_fst).prodMk
        ((continuous_apply 1).comp continuous_snd))
    · show Continuous fun q : ℝ≥0 × Concentration (Fin 4) =>
        q.2 2 + ∫ s in (0 : ℝ)..(q.1 : ℝ), integrand σ₁ q.2 s
      refine ((continuous_apply 2).comp continuous_snd).add ?_
      exact continuous_parametric_intervalIntegral_of_continuous (a₀ := 0)
        (f := fun (q : ℝ≥0 × Concentration (Fin 4)) (s : ℝ) => integrand σ₁ q.2 s)
        ((integrand_cont σ₁_cont σ₁_bound).comp
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
        (NNReal.continuous_coe.comp continuous_fst)
    · show Continuous fun q : ℝ≥0 × Concentration (Fin 4) =>
        q.2 3 + ∫ s in (0 : ℝ)..(q.1 : ℝ), integrand σ₂ q.2 s
      refine ((continuous_apply 3).comp continuous_snd).add ?_
      exact continuous_parametric_intervalIntegral_of_continuous (a₀ := 0)
        (f := fun (q : ℝ≥0 × Concentration (Fin 4)) (s : ℝ) => integrand σ₂ q.2 s)
        ((integrand_cont σ₂_cont σ₂_bound).comp
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
        (NNReal.continuous_coe.comp continuous_fst)
  map_add' := by
    intro t₁ t₂ p
    have h1 := NNReal.coe_nonneg t₁
    have h2 := NNReal.coe_nonneg t₂
    funext i
    fin_cases i
    · show U ((t₁ + t₂ : ℝ≥0) : ℝ) (p 0) = U (t₁ : ℝ) (U (t₂ : ℝ) (p 0))
      rw [NNReal.coe_add, U_add h1 h2]
    · show U ((t₁ + t₂ : ℝ≥0) : ℝ) (p 1) = U (t₁ : ℝ) (U (t₂ : ℝ) (p 1))
      rw [NNReal.coe_add, U_add h1 h2]
    · show p 2 + ∫ s in (0 : ℝ)..((t₁ + t₂ : ℝ≥0) : ℝ), integrand σ₁ p s =
        (p 2 + ∫ s in (0 : ℝ)..(t₂ : ℝ), integrand σ₁ p s) +
          ∫ s in (0 : ℝ)..(t₁ : ℝ), integrand σ₁ (flowFun t₂ p) s
      rw [NNReal.coe_add, add_assoc,
        integral_shift σ₁_cont σ₁_bound p (flowFun t₂ p) h1 h2 rfl rfl]
    · show p 3 + ∫ s in (0 : ℝ)..((t₁ + t₂ : ℝ≥0) : ℝ), integrand σ₂ p s =
        (p 3 + ∫ s in (0 : ℝ)..(t₂ : ℝ), integrand σ₂ p s) +
          ∫ s in (0 : ℝ)..(t₁ : ℝ), integrand σ₂ (flowFun t₂ p) s
      rw [NNReal.coe_add, add_assoc,
        integral_shift σ₂_cont σ₂_bound p (flowFun t₂ p) h1 h2 rfl rfl]
  map_zero' := by
    intro p
    funext i
    fin_cases i
    · show U ((0 : ℝ≥0) : ℝ) (p 0) = p 0
      rw [NNReal.coe_zero, U_zero_left]
    · show U ((0 : ℝ≥0) : ℝ) (p 1) = p 1
      rw [NNReal.coe_zero, U_zero_left]
    · show p 2 + ∫ s in (0 : ℝ)..((0 : ℝ≥0) : ℝ), integrand σ₁ p s = p 2
      rw [NNReal.coe_zero, intervalIntegral.integral_same, add_zero]
    · show p 3 + ∫ s in (0 : ℝ)..((0 : ℝ≥0) : ℝ), integrand σ₂ p s = p 3
      rw [NNReal.coe_zero, intervalIntegral.integral_same, add_zero]

theorem flow_apply (t : ℝ≥0) (p : Concentration (Fin 4)) : flow t p = flowFun t p := rfl

theorem integral_mono_of_le {σ : ℝ → ℝ} (hσc : Continuous σ) (hσ1 : ∀ θ, |σ θ| ≤ 1)
    (hσL : ∀ a b, |σ a - σ b| ≤ |a - b|) {p q : Concentration (Fin 4)} (hpq : p ≤ q) (t : ℝ≥0) :
    ∫ s in (0 : ℝ)..(t : ℝ), integrand σ p s ≤ ∫ s in (0 : ℝ)..(t : ℝ), integrand σ q s :=
  intervalIntegral.integral_mono_on (NNReal.coe_nonneg t)
    ((integrand_cont_s hσc hσ1 p).intervalIntegrable _ _)
    ((integrand_cont_s hσc hσ1 q).intervalIntegrable _ _)
    (fun s _ => add_le_add (U_mono s (hpq 0)) (G_mono hσ1 hσL (U_mono s (hpq 1))))

/-- **The semiflow is monotone** for the componentwise order. -/
theorem flow_monotone : CRNT.Monotone.IsMonotoneFlow flow := by
  intro t p q hpq i
  fin_cases i
  · exact U_mono _ (hpq 0)
  · exact U_mono _ (hpq 1)
  · show p 2 + ∫ s in (0 : ℝ)..(t : ℝ), integrand σ₁ p s ≤
      q 2 + ∫ s in (0 : ℝ)..(t : ℝ), integrand σ₁ q s
    exact add_le_add (hpq 2) (integral_mono_of_le σ₁_cont σ₁_bound σ₁_lip hpq t)
  · show p 3 + ∫ s in (0 : ℝ)..(t : ℝ), integrand σ₂ p s ≤
      q 3 + ∫ s in (0 : ℝ)..(t : ℝ), integrand σ₂ q s
    exact add_le_add (hpq 3) (integral_mono_of_le σ₂_cont σ₂_bound σ₂_lip hpq t)

/-! ## Fixed points -/

theorem fixed_of_zero {z : Concentration (Fin 4)} (h0 : z 0 = 0) (h1 : z 1 = 0) (t : ℝ≥0) :
    flow t z = z := by
  funext i
  fin_cases i
  · show U (t : ℝ) (z 0) = z 0
    rw [h0, U_zero_right]
  · show U (t : ℝ) (z 1) = z 1
    rw [h1, U_zero_right]
  · show z 2 + ∫ s in (0 : ℝ)..(t : ℝ), integrand σ₁ z s = z 2
    simp only [integrand_zero σ₁ h0 h1, intervalIntegral.integral_zero, add_zero]
  · show z 3 + ∫ s in (0 : ℝ)..(t : ℝ), integrand σ₂ z s = z 3
    simp only [integrand_zero σ₂ h0 h1, intervalIntegral.integral_zero, add_zero]

theorem zero_of_fixed {p : Concentration (Fin 4)} (hp : ∀ t : ℝ≥0, flow t p = p) :
    p 0 = 0 ∧ p 1 = 0 := by
  have e0 := congrFun (hp 1) 0
  have e1 := congrFun (hp 1) 1
  change U ((1 : ℝ≥0) : ℝ) (p 0) = p 0 at e0
  change U ((1 : ℝ≥0) : ℝ) (p 1) = p 1 at e1
  rw [NNReal.coe_one] at e0 e1
  exact ⟨U_one_fixed e0, U_one_fixed e1⟩

/-! ## The orbit of `x₀ = (1, −1, 0, 0)` -/

/-- The initial point. -/
noncomputable def x₀ : Concentration (Fin 4) := ![1, -1, 0, 0]

theorem integrand_x₀ (σ : ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    integrand σ x₀ s = σ (Real.log (1 + s)) / (4 * (1 + s)) := by
  have hd : 0 < 1 + s := by linarith
  show U s 1 + G σ (U s (-1)) = _
  rw [U_one hs, U_neg_one hs]
  unfold G
  have habs : |(-1 : ℝ) / (1 + s)| = 1 / (1 + s) := by
    rw [abs_div, abs_neg, abs_one, abs_of_pos hd]
  have hlog : -Real.log (1 / (1 + s)) = Real.log (1 + s) := by
    rw [one_div, Real.log_inv, neg_neg]
  rw [habs, hlog]
  field_simp
  ring

theorem orbit_zero (t : ℝ≥0) : flow t x₀ 0 = 1 / (1 + t) := by
  show U (t : ℝ) 1 = _
  exact U_one (NNReal.coe_nonneg t)

theorem orbit_one (t : ℝ≥0) : flow t x₀ 1 = -1 / (1 + t) := by
  show U (t : ℝ) (-1) = _
  exact U_neg_one (NNReal.coe_nonneg t)

theorem orbit_two (t : ℝ≥0) : flow t x₀ 2 = (1 - Real.cos (Real.log (1 + t))) / 4 := by
  show (0 : ℝ) + ∫ s in (0 : ℝ)..(t : ℝ), integrand σ₁ x₀ s = _
  rw [zero_add]
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) (t : ℝ),
      HasDerivAt (fun s : ℝ => -Real.cos (Real.log (1 + s)) / 4) (integrand σ₁ x₀ s) s := by
    intro s hs
    rw [Set.uIcc_of_le (NNReal.coe_nonneg t)] at hs
    have hd : 0 < 1 + s := by linarith [hs.1]
    rw [integrand_x₀ σ₁ hs.1]
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 s := (hasDerivAt_id' s).const_add 1
    have h2 := h1.log hd.ne'
    have h3 := h2.cos
    have h4 := h3.neg.div_const 4
    convert h4 using 1
    show Real.sin (Real.log (1 + s)) / (4 * (1 + s)) = _
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((integrand_cont_s σ₁_cont σ₁_bound x₀).intervalIntegrable _ _)]
  simp only [add_zero, Real.log_one, Real.cos_zero]
  ring

theorem orbit_three (t : ℝ≥0) : flow t x₀ 3 = -Real.sin (Real.log (1 + t)) / 4 := by
  show (0 : ℝ) + ∫ s in (0 : ℝ)..(t : ℝ), integrand σ₂ x₀ s = _
  rw [zero_add]
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) (t : ℝ),
      HasDerivAt (fun s : ℝ => -Real.sin (Real.log (1 + s)) / 4) (integrand σ₂ x₀ s) s := by
    intro s hs
    rw [Set.uIcc_of_le (NNReal.coe_nonneg t)] at hs
    have hd : 0 < 1 + s := by linarith [hs.1]
    rw [integrand_x₀ σ₂ hs.1]
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 s := (hasDerivAt_id' s).const_add 1
    have h2 := h1.log hd.ne'
    have h3 := h2.sin
    have h4 := h3.neg.div_const 4
    convert h4 using 1
    show -Real.cos (Real.log (1 + s)) / (4 * (1 + s)) = _
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((integrand_cont_s σ₂_cont σ₂_bound x₀).intervalIntegrable _ _)]
  simp only [add_zero, Real.log_one, Real.sin_zero, neg_zero, zero_div, sub_zero]

/-- The orbit lies on the circle of radius `1/4` about `(1/4, 0)` in the `z`-coordinates. -/
theorem orbit_circle (t : ℝ≥0) : (flow t x₀ 2 - 1 / 4) ^ 2 + (flow t x₀ 3) ^ 2 = 1 / 16 := by
  rw [orbit_two, orbit_three]
  have := Real.sin_sq_add_cos_sq (Real.log (1 + t))
  linear_combination this / 16

/-! ## The ω-limit set -/

/-- A continuous observable converging along the orbit is constant on the ω-limit set. -/
theorem omega_eq_of_tendsto (g : Concentration (Fin 4) → ℝ) (hg : Continuous g) (c : ℝ)
    (h : Tendsto (fun t : ℝ≥0 => g (flow t x₀)) atTop (𝓝 c)) :
    ∀ y ∈ omegaLimit atTop flow {x₀}, g y = c := by
  intro y hy
  by_contra hne
  obtain ⟨V, W, hVo, hWo, hyV, hcW, hVW⟩ := t2_separation hne
  have hn : g ⁻¹' V ∈ 𝓝 y := hg.continuousAt.preimage_mem_nhds (hVo.mem_nhds hyV)
  have hfreq := (mem_omegaLimit_iff_frequently (f := atTop) (ϕ := flow) (s := {x₀}) y).mp hy _ hn
  have hev : ∀ᶠ t in atTop, g (flow t x₀) ∈ W := h (hWo.mem_nhds hcW)
  obtain ⟨t, ⟨z, hz1, hz2⟩, ht⟩ := (hfreq.and_eventually hev).exists
  rw [Set.mem_singleton_iff] at hz1
  subst hz1
  have hz2' : g (flow t x₀) ∈ V := hz2
  exact Set.disjoint_left.mp hVW hz2' ht

theorem tendsto_one_div (f : ℝ≥0 → ℝ) (hf : ∀ t, f t = 1 / (1 + t)) :
    Tendsto f atTop (𝓝 0) := by
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hden : Tendsto (fun t : ℝ≥0 => 1 + (t : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun t => by linarith) hcoe
  have := hden.inv_tendsto_atTop
  rw [show f = fun t : ℝ≥0 => 1 / (1 + (t : ℝ)) from funext hf]
  convert this using 1
  funext t
  simp [one_div]

theorem omega_zero_one {y : Concentration (Fin 4)} (hy : y ∈ omegaLimit atTop flow {x₀}) :
    y 0 = 0 ∧ y 1 = 0 := by
  refine ⟨omega_eq_of_tendsto (fun z => z 0) (continuous_apply 0) 0
    (tendsto_one_div _ orbit_zero) y hy, ?_⟩
  have h := (tendsto_one_div (fun t => flow t x₀ 0) orbit_zero).neg
  rw [neg_zero] at h
  refine omega_eq_of_tendsto (fun z => z 1) (continuous_apply 1) 0 ?_ y hy
  refine h.congr fun t => ?_
  show -(flow t x₀ 0) = flow t x₀ 1
  rw [orbit_zero, orbit_one, neg_div]

theorem omega_circle {y : Concentration (Fin 4)} (hy : y ∈ omegaLimit atTop flow {x₀}) :
    (y 2 - 1 / 4) ^ 2 + (y 3) ^ 2 = 1 / 16 := by
  have hsub := omegaLimit_subset_closure_image2 (f := atTop) (ϕ := flow) (s := {x₀})
    (u := Set.univ) Filter.univ_mem
  have hclosed : IsClosed {z : Concentration (Fin 4) | (z 2 - 1 / 4) ^ 2 + (z 3) ^ 2 = 1 / 16} :=
    isClosed_eq ((((continuous_apply 2).sub continuous_const).pow 2).add
      ((continuous_apply 3).pow 2)) continuous_const
  have himg : Set.image2 flow Set.univ {x₀} ⊆
      {z : Concentration (Fin 4) | (z 2 - 1 / 4) ^ 2 + (z 3) ^ 2 = 1 / 16} := by
    rintro _ ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact orbit_circle t
  exact closure_minimal himg hclosed (hsub hy)

/-- A sequence of times along which the orbit has fixed `z`-coordinates gives an ω-limit point. -/
theorem mem_omega_of_angles (θ : ℕ → ℝ) (hθ : Tendsto θ atTop atTop) (hθ0 : ∀ k, 0 ≤ θ k)
    (c s : ℝ) (hc : ∀ k, Real.cos (θ k) = c) (hs : ∀ k, Real.sin (θ k) = s) :
    (![0, 0, (1 - c) / 4, -s / 4] : Concentration (Fin 4)) ∈ omegaLimit atTop flow {x₀} := by
  -- the times `exp (θ k) − 1`
  have hpos : ∀ k, 0 ≤ Real.exp (θ k) - 1 := fun k => by linarith [Real.one_le_exp (hθ0 k)]
  set τ : ℕ → ℝ≥0 := fun k => ⟨Real.exp (θ k) - 1, hpos k⟩ with hτ
  have hτv : ∀ k, ((τ k : ℝ≥0) : ℝ) = Real.exp (θ k) - 1 := fun k => rfl
  have h1τ : ∀ k, 1 + ((τ k : ℝ≥0) : ℝ) = Real.exp (θ k) := fun k => by rw [hτv]; ring
  have hlog : ∀ k, Real.log (1 + ((τ k : ℝ≥0) : ℝ)) = θ k := fun k => by
    rw [h1τ, Real.log_exp]
  have hexp : Tendsto (fun k => Real.exp (θ k)) atTop atTop := Real.tendsto_exp_atTop.comp hθ
  have hτtop : Tendsto τ atTop atTop := by
    rw [← NNReal.tendsto_coe_atTop]
    refine tendsto_atTop_mono (fun k => ?_) hθ
    rw [hτv]; linarith [Real.add_one_le_exp (θ k)]
  have hinv : Tendsto (fun k => 1 / (1 + ((τ k : ℝ≥0) : ℝ))) atTop (𝓝 0) := by
    have := hexp.inv_tendsto_atTop
    refine this.congr fun k => ?_
    simp [h1τ, one_div, Pi.inv_apply]
  have hconv : Tendsto (fun k => flow (τ k) x₀) atTop
      (𝓝 (![0, 0, (1 - c) / 4, -s / 4] : Concentration (Fin 4))) := by
    rw [tendsto_pi_nhds]
    intro i
    fin_cases i
    · show Tendsto (fun k => flow (τ k) x₀ 0) atTop (𝓝 0)
      exact hinv.congr fun k => (orbit_zero (τ k)).symm
    · show Tendsto (fun k => flow (τ k) x₀ 1) atTop (𝓝 0)
      have := hinv.neg
      rw [neg_zero] at this
      exact this.congr fun k => by rw [orbit_one, neg_div]
    · show Tendsto (fun k => flow (τ k) x₀ 2) atTop (𝓝 ((1 - c) / 4))
      refine tendsto_const_nhds.congr fun k => ?_
      rw [orbit_two, hlog, hc]
    · show Tendsto (fun k => flow (τ k) x₀ 3) atTop (𝓝 (-s / 4))
      refine tendsto_const_nhds.congr fun k => ?_
      rw [orbit_three, hlog, hs]
  rw [mem_omegaLimit_iff_frequently]
  intro n hn
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨k, hk1, hk2⟩ := ((hτtop.eventually_ge_atTop a).and (hconv hn)).exists
  exact ⟨τ k, hk1, x₀, Set.mem_singleton x₀, hk2⟩

theorem angles_tendsto (φ : ℝ) (hφ : 0 ≤ φ) :
    Tendsto (fun k : ℕ => ((k : ℤ) : ℝ) * (2 * Real.pi) + φ) atTop atTop := by
  have h : Tendsto (fun k : ℕ => (k : ℝ) * (2 * Real.pi)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
  refine tendsto_atTop_mono (fun k => ?_) h
  push_cast; linarith

theorem sin_of_cos_one {x : ℝ} (h : Real.cos x = 1) : Real.sin x = 0 := by
  have := Real.sin_sq_add_cos_sq x
  rw [h] at this
  have h2 : Real.sin x ^ 2 = 0 := by linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2

/-- `P = 0` is an ω-limit point (angles `2πk`). -/
theorem P_mem : (![0, 0, 0, 0] : Concentration (Fin 4)) ∈ omegaLimit atTop flow {x₀} := by
  have hc : ∀ k : ℕ, Real.cos (((k : ℤ) : ℝ) * (2 * Real.pi) + 0) = 1 := fun k => by
    rw [add_zero]; exact Real.cos_int_mul_two_pi k
  have h := mem_omega_of_angles (fun k : ℕ => ((k : ℤ) : ℝ) * (2 * Real.pi) + 0)
    (angles_tendsto 0 le_rfl) (fun k => by push_cast; positivity) 1 0 hc
    (fun k => sin_of_cos_one (hc k))
  have e : (![0, 0, (1 - 1) / 4, -0 / 4] : Concentration (Fin 4)) = ![0, 0, 0, 0] := by
    norm_num
  rwa [e] at h

/-- `Q = (0, 0, 1/2, 0)` is an ω-limit point (angles `2πk + π`). -/
theorem Q_mem : (![0, 0, 1 / 2, 0] : Concentration (Fin 4)) ∈ omegaLimit atTop flow {x₀} := by
  have hc0 : ∀ k : ℕ, Real.cos (((k : ℤ) : ℝ) * (2 * Real.pi)) = 1 := fun k =>
    Real.cos_int_mul_two_pi k
  have hc : ∀ k : ℕ, Real.cos (((k : ℤ) : ℝ) * (2 * Real.pi) + Real.pi) = -1 := fun k => by
    rw [Real.cos_add_pi, hc0]
  have hs : ∀ k : ℕ, Real.sin (((k : ℤ) : ℝ) * (2 * Real.pi) + Real.pi) = 0 := fun k => by
    rw [Real.sin_add_pi, sin_of_cos_one (hc0 k), neg_zero]
  have h := mem_omega_of_angles (fun k : ℕ => ((k : ℤ) : ℝ) * (2 * Real.pi) + Real.pi)
    (angles_tendsto Real.pi Real.pi_pos.le) (fun k => by push_cast; positivity) (-1) 0 hc hs
  have e : (![0, 0, (1 - -1) / 4, -0 / 4] : Concentration (Fin 4)) = ![0, 0, 1 / 2, 0] := by
    norm_num
  rwa [e] at h

/-- `W = (0, 0, 1/4, 0)`, the centre of the circle, is not an ω-limit point. -/
theorem W_not_mem : (![0, 0, 1 / 4, 0] : Concentration (Fin 4)) ∉ omegaLimit atTop flow {x₀} := by
  intro h
  have := omega_circle h
  norm_num at this

/-! ## The hypotheses of the claim -/

theorem absorbing : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 flow v {x₀}) ⊆
    Set.Icc (![0, -1, 0, -1 / 4] : Concentration (Fin 4)) ![1, 0, 1 / 2, 1 / 4] := by
  refine ⟨Set.univ, Filter.univ_mem, closure_minimal ?_ isClosed_Icc⟩
  rintro _ ⟨t, -, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at hx
  subst hx
  have ht := NNReal.coe_nonneg t
  have hd : 0 < 1 + (t : ℝ) := by linarith
  have e0 : 0 ≤ 1 / (1 + (t : ℝ)) := by positivity
  have e1 : 1 / (1 + (t : ℝ)) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have c1 := Real.neg_one_le_cos (Real.log (1 + t))
  have c2 := Real.cos_le_one (Real.log (1 + t))
  have s1 := Real.neg_one_le_sin (Real.log (1 + t))
  have s2 := Real.sin_le_one (Real.log (1 + t))
  rw [Set.mem_Icc]
  constructor
  · intro i
    fin_cases i
    · show (0 : ℝ) ≤ flow t x₀ 0
      rw [orbit_zero]; exact e0
    · show (-1 : ℝ) ≤ flow t x₀ 1
      rw [orbit_one, neg_div]; linarith
    · show (0 : ℝ) ≤ flow t x₀ 2
      rw [orbit_two]; linarith
    · show (-1 / 4 : ℝ) ≤ flow t x₀ 3
      rw [orbit_three]; linarith
  · intro i
    fin_cases i
    · show flow t x₀ 0 ≤ (1 : ℝ)
      rw [orbit_zero]; exact e1
    · show flow t x₀ 1 ≤ (0 : ℝ)
      rw [orbit_one, neg_div]; linarith
    · show flow t x₀ 2 ≤ (1 / 2 : ℝ)
      rw [orbit_two]; linarith
    · show flow t x₀ 3 ≤ (1 / 4 : ℝ)
      rw [orbit_three]; linarith

/-- **The order-convexity statement without the comparability hypothesis is false.** -/
theorem not_generalClaim : ¬ GeneralClaim := by
  intro h
  have hΩE : ∀ y ∈ omegaLimit atTop flow {x₀}, ∀ t : ℝ≥0, flow t y = y := fun y hy t =>
    fixed_of_zero (omega_zero_one hy).1 (omega_zero_one hy).2 t
  have hEq : ∀ p q z : Concentration (Fin 4), (∀ t : ℝ≥0, flow t p = p) →
      (∀ t : ℝ≥0, flow t q = q) → p ≤ z → z ≤ q → ∀ t : ℝ≥0, flow t z = z := by
    intro p q z hp hq hpz hzq t
    obtain ⟨hp0, hp1⟩ := zero_of_fixed hp
    obtain ⟨hq0, hq1⟩ := zero_of_fixed hq
    have hz0 : z 0 = 0 := le_antisymm (hq0 ▸ hzq 0) (hp0 ▸ hpz 0)
    have hz1 : z 1 = 0 := le_antisymm (hq1 ▸ hzq 1) (hp1 ▸ hpz 1)
    exact fixed_of_zero hz0 hz1 t
  have hPW : (![0, 0, 0, 0] : Concentration (Fin 4)) ≤ ![0, 0, 1 / 4, 0] := by
    intro i; fin_cases i <;> norm_num
  have hWQ : (![0, 0, 1 / 4, 0] : Concentration (Fin 4)) ≤ ![0, 0, 1 / 2, 0] := by
    intro i; fin_cases i <;> norm_num
  exact W_not_mem (h (Fin 4) flow flow_monotone x₀ _ isCompact_Icc absorbing hΩE hEq
    _ _ _ P_mem Q_mem hPW hWQ)

end OmegaOrderConvexCounterexample
end CRNT

#print axioms CRNT.OmegaOrderConvexCounterexample.not_generalClaim

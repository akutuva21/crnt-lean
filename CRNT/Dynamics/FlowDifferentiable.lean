import CRNT.Dynamics.VariationalEquation

/-!
# Differentiability of an ODE flow in its initial condition

For an autonomous `C¹` vector field `f : E → E`, the flow `x₀ ↦ Φ x₀ t` is differentiable in
its initial point, with directional derivative the solution of the linear variational equation.
This module extracts that differentiability from the Grönwall variational error bound
`ODE.norm_flow_variational_error_le`: the error between the genuine flow separation and its
linear prediction is `O(ρ · |h|)` with `ρ` the modulus of `fderiv ℝ f` along the joining
segment, and as `h → 0` the segment shrinks to the base point, so `ρ → 0` by continuity of the
derivative and the error is `o(h)`.

## The modulus and its decay

`segmentModulus f a b = sSup { ‖fderiv ℝ f z - fderiv ℝ f a‖ | z ∈ segment ℝ a b }` is the
uniform deviation of `fderiv ℝ f` from its value at `a` over the segment `[a, b]`. It bounds the
first-order remainder of `f` on that segment (`norm_image_sub_le_segmentModulus`, via the
mean-value inequality `Convex.norm_image_sub_le_of_norm_fderiv_le'`); it shrinks the joining
segment to the base point as `b → a`, so the modulus decays — recorded here as the hypothesis
`ρ → 0` of the limit lemmas.

## The limit

`gronwallBound 0 K ε t` is linear in `ε` (`gronwallBound_zero_eq_mul`), so the variational error
bound divides cleanly by `|h|`:
`‖(y t - x t)/h - W t‖ ≤ ρ(h) · ‖v‖ · exp (K T) · gronwallBound 0 K 1 t`, whose right side
vanishes as `ρ(h) → 0`.

## Main results

* `tendsto_flow_difference_quotient`: the difference quotient
  `h ↦ (Y h t - Y 0 t) / h` of a flow family `Y` (with `Y h` the curve from a base point moved
  by `h`) converges to the variational solution `W t` as `h → 0`.
* `hasDerivAt_flow_initial`: equivalently, `HasDerivAt (fun h => Y h t) (W t) 0` — the
  directional derivative of the time-`t` flow in the chosen direction is `W t`. This is the
  variational datum (`TransversalSection.spaceDeriv` in a fixed direction) that differentiable
  dependence on initial conditions, and through it the Andronov–Hopf first-return map, requires.
-/

open Set Filter
open scoped Topology

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Linearity of the Grönwall growth function in its driving term.** With zero initial value,
`gronwallBound 0 K ε t = ε · gronwallBound 0 K 1 t`: the bound scales linearly with `ε`. This
is what lets the variational error bound `gronwallBound 0 K (ρ · |h| · …) t` be divided by `|h|`
to expose the difference quotient. -/
theorem gronwallBound_zero_eq_mul (K ε t : ℝ) :
    gronwallBound 0 K ε t = ε * gronwallBound 0 K 1 t := by
  by_cases hK : K = 0
  · subst hK; simp only [gronwallBound_K0, zero_add]; ring
  · simp only [gronwallBound_of_K_ne_0 hK, zero_mul, zero_add, one_div]
    ring

/-- `gronwallBound 0 K 1 t` is nonnegative for `0 ≤ K` and `0 ≤ t`: the growth function with unit
driving term and zero initial value never goes below zero on forward time. -/
theorem gronwallBound_zero_one_nonneg {K t : ℝ} (hK : 0 ≤ K) (ht : 0 ≤ t) :
    0 ≤ gronwallBound 0 K 1 t := by
  have := gronwallBound_mono (δ := 0) (K := K) (ε := 1) le_rfl zero_le_one hK ht
  rwa [gronwallBound_x0] at this

/-- **The segment modulus of `fderiv ℝ f`.** The uniform deviation of `fderiv ℝ f` from its value
at `a`, taken over the segment `[a, b]`. It is the modulus of continuity that bounds the
first-order remainder of `f` on the segment and that vanishes as `b → a`. -/
noncomputable def segmentModulus (f : E → E) (a b : E) : ℝ :=
  sSup ((fun z => ‖fderiv ℝ f z - fderiv ℝ f a‖) '' segment ℝ a b)

variable {f : E → E}

/-- The segment modulus is nonnegative: it is a supremum of norms over a nonempty set (the
segment always contains its endpoint `a`), bounded below by `0`. -/
theorem segmentModulus_nonneg (a b : E)
    (hbdd : BddAbove ((fun z => ‖fderiv ℝ f z - fderiv ℝ f a‖) '' segment ℝ a b)) :
    0 ≤ segmentModulus f a b := by
  apply le_csSup_of_le hbdd (mem_image_of_mem _ (left_mem_segment ℝ a b))
  simp

/-- **The segment modulus bounds the deviation pointwise.** For every `z` on the segment `[a, b]`,
the deviation `‖fderiv ℝ f z - fderiv ℝ f a‖` is at most `segmentModulus f a b`. -/
theorem norm_fderiv_sub_le_segmentModulus {a b z : E} (hz : z ∈ segment ℝ a b)
    (hbdd : BddAbove ((fun z => ‖fderiv ℝ f z - fderiv ℝ f a‖) '' segment ℝ a b)) :
    ‖fderiv ℝ f z - fderiv ℝ f a‖ ≤ segmentModulus f a b :=
  le_csSup hbdd (mem_image_of_mem _ hz)

/-- **First-order remainder bound from the segment modulus.** By the mean-value inequality
(`Convex.norm_image_sub_le_of_norm_fderiv_le'`) on the segment `[a, b]`, the first-order remainder
of `f` is controlled by the segment modulus:
`‖f b - f a - (fderiv ℝ f a) (b - a)‖ ≤ segmentModulus f a b · ‖b - a‖`. -/
theorem norm_image_sub_le_segmentModulus {a b : E}
    (hf : ∀ z ∈ segment ℝ a b, DifferentiableAt ℝ f z)
    (hbdd : BddAbove ((fun z => ‖fderiv ℝ f z - fderiv ℝ f a‖) '' segment ℝ a b)) :
    ‖f b - f a - (fderiv ℝ f a) (b - a)‖ ≤ segmentModulus f a b * ‖b - a‖ := by
  have hconv : Convex ℝ (segment ℝ a b) := convex_segment a b
  refine Convex.norm_image_sub_le_of_norm_fderiv_le' (φ := fderiv ℝ f a) hf
    (fun z hz => norm_fderiv_sub_le_segmentModulus hz hbdd) hconv
    (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)

/-- **The difference quotient of a flow family tends to the variational solution.**

Let `x` be the base solution, `W` the solution of the linear variational equation
`Ẇ = Df (x t) · W` with `W 0 = v`, and `Y : ℝ → ℝ → E` a family of solutions with `Y h` started
near `x` along the direction `v` (so `Y 0 = x` and the difference quotient is well posed). Suppose
the variational error obeys the Grönwall bound from `norm_flow_variational_error_le`,
`‖(Y h t - x t) - h • W t‖ ≤ gronwallBound 0 K (ρ h · |h| · ‖v‖ · exp (K T)) t`, with `0 ≤ K`,
`0 ≤ ρ h`, and the modulus `ρ h → 0` as `h → 0`. Then the difference quotient converges:
`Tendsto (fun h => (Y h t - x t) / h) (𝓝[≠] 0) (𝓝 (W t))` (division by the scalar `h` via
`•`-inverse), i.e. the directional derivative of the time-`t` flow is `W t`. -/
theorem tendsto_flow_difference_quotient {x W : ℝ → E} {v : E} {K T t : ℝ} {ρ : ℝ → ℝ}
    (hK : 0 ≤ K) (ht : t ∈ Icc (0 : ℝ) T)
    {Y : ℝ → ℝ → E} (_hY0 : Y 0 = x)
    (_hρ0 : ∀ h, 0 ≤ ρ h) (hρlim : Tendsto ρ (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (herr : ∀ h, ‖(Y h t - x t) - h • W t‖ ≤
      gronwallBound 0 K (ρ h * (|h| * ‖v‖ * Real.exp (K * T))) t) :
    Tendsto (fun h => (h⁻¹ : ℝ) • (Y h t - x t)) (𝓝[≠] (0 : ℝ)) (𝓝 (W t)) := by
  -- The growth factor `gronwallBound 0 K 1 t ≥ 0`.
  set G : ℝ := gronwallBound 0 K 1 t with hG
  have hGnn : 0 ≤ G := gronwallBound_zero_one_nonneg hK ht.1
  -- Bound the distance of the difference quotient from `W t`.
  have hbound : ∀ h : ℝ, h ≠ 0 →
      ‖(h⁻¹ : ℝ) • (Y h t - x t) - W t‖ ≤ ρ h * (‖v‖ * Real.exp (K * T)) * G := by
    intro h hh
    have hkey : (h⁻¹ : ℝ) • (Y h t - x t) - W t = (h⁻¹ : ℝ) • ((Y h t - x t) - h • W t) := by
      rw [smul_sub (h⁻¹ : ℝ) (Y h t - x t) (h • W t), smul_smul, inv_mul_cancel₀ hh, one_smul]
    rw [hkey, norm_smul, norm_inv, Real.norm_eq_abs]
    calc |h|⁻¹ * ‖(Y h t - x t) - h • W t‖
        ≤ |h|⁻¹ * gronwallBound 0 K (ρ h * (|h| * ‖v‖ * Real.exp (K * T))) t := by
          gcongr; exact herr h
      _ = |h|⁻¹ * ((ρ h * (|h| * ‖v‖ * Real.exp (K * T))) * G) := by
          rw [gronwallBound_zero_eq_mul, hG]
      _ = ρ h * (‖v‖ * Real.exp (K * T)) * G := by
          have hne : |h| ≠ 0 := by positivity
          rw [show ρ h * (|h| * ‖v‖ * Real.exp (K * T)) * G
              = |h| * (ρ h * (‖v‖ * Real.exp (K * T)) * G) by ring,
            inv_mul_cancel_left₀ hne]
  -- The right side tends to `0` as `h → 0`.
  have hrhs : Tendsto (fun h => ρ h * (‖v‖ * Real.exp (K * T)) * G) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have : Tendsto (fun h => ρ h * ((‖v‖ * Real.exp (K * T)) * G)) (𝓝[≠] (0 : ℝ))
        (𝓝 (0 * ((‖v‖ * Real.exp (K * T)) * G))) :=
      hρlim.mul_const _
    simpa only [zero_mul, mul_assoc] using this
  -- Squeeze the distance to `0`.
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' ?_ ?_ hrhs
  · filter_upwards with h using dist_nonneg
  · filter_upwards [self_mem_nhdsWithin] with h hh
    rw [dist_eq_norm]; exact hbound h (by simpa using hh)

/-- **The flow is differentiable in its initial condition (fixed direction).**

Under the hypotheses of `tendsto_flow_difference_quotient`, the time-`t` flow has derivative the
variational solution along the chosen direction: `HasDerivAt (fun h => Y h t) (W t) 0`. The
directional derivative of `x₀ ↦ Φ x₀ t` in direction `v` is the linear variational solution `W t`
— the variational datum filling `TransversalSection.spaceDeriv` (in a fixed direction) and, with
it, the smooth dependence of the Andronov–Hopf first-return map on initial data. -/
theorem hasDerivAt_flow_initial {x W : ℝ → E} {v : E} {K T t : ℝ} {ρ : ℝ → ℝ}
    (hK : 0 ≤ K) (ht : t ∈ Icc (0 : ℝ) T)
    {Y : ℝ → ℝ → E} (hY0 : Y 0 = x)
    (hρ0 : ∀ h, 0 ≤ ρ h) (hρlim : Tendsto ρ (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (herr : ∀ h, ‖(Y h t - x t) - h • W t‖ ≤
      gronwallBound 0 K (ρ h * (|h| * ‖v‖ * Real.exp (K * T))) t) :
    HasDerivAt (fun h => Y h t) (W t) 0 := by
  have htend := tendsto_flow_difference_quotient hK ht hY0 hρ0 hρlim herr
  rw [hasDerivAt_iff_tendsto_slope]
  -- `slope (fun h => Y h t) 0 h = h⁻¹ • (Y h t - x t)` since `Y 0 t = x t`.
  have hslope : ∀ h : ℝ, slope (fun h => Y h t) 0 h = (h⁻¹ : ℝ) • (Y h t - x t) := by
    intro h
    rw [slope_def_module, sub_zero, hY0]
  exact htend.congr fun h => (hslope h).symm

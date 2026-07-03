import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The Horn–Jackson Lyapunov function (relative entropy)

The deficiency-zero theorem's stability and well-posedness rest on the *pseudo-Helmholtz*
/ relative-entropy function

```text
relEntropy x* x = ∑ᵢ (xᵢ log(xᵢ / x*ᵢ) − xᵢ + x*ᵢ).
```

This module establishes its defining property as a Lyapunov function: it is **positive
definite about the reference** `x*` — nonnegative everywhere (Gibbs' inequality, the
nonnegativity of relative entropy), and zero exactly at `x = x*`. These are the
properties used to certify that a complex-balanced equilibrium is a strict local minimum
of the energy, underlying both Birch's well-posedness and Milestone 5 (stability).

-/

namespace CRNT

open scoped BigOperators

/-- **Gibbs' inequality (per coordinate).** `t log(t/a) − t + a ≥ 0` for `t ≥ 0`,
`a > 0`. -/
theorem relEntropyTerm_nonneg {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) :
    0 ≤ t * Real.log (t / a) - t + a := by
  rcases eq_or_lt_of_le ht with h | ht'
  · rw [← h]; simp only [zero_mul]; linarith
  · have hat : 0 < a / t := div_pos ha ht'
    have hlog : Real.log (a / t) = -Real.log (t / a) := by
      rw [Real.log_div ha.ne' ht'.ne', Real.log_div ht'.ne' ha.ne']; ring
    have hle := Real.log_le_sub_one_of_pos hat
    rw [hlog] at hle
    have hta : t * (a / t) = a := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hle ht'.le, hta]

/-- **Strict Gibbs' inequality (per coordinate).** The term is strictly positive when
`t ≠ a`. -/
theorem relEntropyTerm_pos {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) (hne : t ≠ a) :
    0 < t * Real.log (t / a) - t + a := by
  rcases eq_or_lt_of_le ht with h | ht'
  · rw [← h]; simp only [zero_mul]; linarith
  · have hat : 0 < a / t := div_pos ha ht'
    have hne' : a / t ≠ 1 := by
      rw [ne_eq, div_eq_one_iff_eq ht'.ne']; exact fun hh => hne hh.symm
    have hlog : Real.log (a / t) = -Real.log (t / a) := by
      rw [Real.log_div ha.ne' ht'.ne', Real.log_div ht'.ne' ha.ne']; ring
    have hlt := Real.log_lt_sub_one_of_pos hat hne'
    rw [hlog] at hlt
    have hta : t * (a / t) = a := by field_simp
    nlinarith [mul_lt_mul_of_pos_left hlt ht', hta]

/-- The Horn–Jackson / pseudo-Helmholtz Lyapunov function (relative entropy of `x` with
respect to the reference `x*`). -/
noncomputable def relEntropy {ι : Type*} [Fintype ι] (xstar x : ι → ℝ) : ℝ :=
  ∑ i, (x i * Real.log (x i / xstar i) - x i + xstar i)

/-- **Nonnegativity of relative entropy** (Gibbs' inequality). -/
theorem relEntropy_nonneg {ι : Type*} [Fintype ι] {xstar x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hxs : ∀ i, 0 < xstar i) : 0 ≤ relEntropy xstar x :=
  Finset.sum_nonneg fun i _ => relEntropyTerm_nonneg (hx i) (hxs i)

/-- **Positive definiteness.** The Lyapunov function vanishes exactly at the reference. -/
theorem relEntropy_eq_zero_iff {ι : Type*} [Fintype ι] {xstar x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hxs : ∀ i, 0 < xstar i) :
    relEntropy xstar x = 0 ↔ x = xstar := by
  constructor
  · intro h
    funext i
    by_contra hne
    have hsumpos : 0 < relEntropy xstar x :=
      Finset.sum_pos' (fun j _ => relEntropyTerm_nonneg (hx j) (hxs j))
        ⟨i, Finset.mem_univ i, relEntropyTerm_pos (hx i) (hxs i) hne⟩
    linarith
  · intro h
    subst h
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [div_self (hxs i).ne', Real.log_one, mul_zero]
    ring

/-- The Lyapunov function is **strictly positive away from the reference**. -/
theorem relEntropy_pos_of_ne {ι : Type*} [Fintype ι] {xstar x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hxs : ∀ i, 0 < xstar i) (hne : x ≠ xstar) :
    0 < relEntropy xstar x :=
  (relEntropy_nonneg hx hxs).lt_of_ne fun h =>
    hne ((relEntropy_eq_zero_iff hx hxs).mp h.symm)

end CRNT

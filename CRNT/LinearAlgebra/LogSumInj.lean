import CRNT.LinearAlgebra.PowerProductMonoFinset

/-!
# Injectivity of a shifted-monomial log-sum

The deficiency-one uniqueness argument pins its equilibrium parameter `β` as the unique root of
the log-sum

`H(β) = ∑_{c ∈ s ∪ U} G_c · log(β · y*_c + b_c)`,

where `y* > 0` on `s` and `y* = 0` on `U` (with `b > 0` there). Splitting the sum, on `U` the
term is the constant `log b_c`, and on `s` it is `log y*_c + log(β + b_c/y*_c)`; so `H` is a
constant plus the strictly-decreasing log-sum `∑_{c ∈ s} G_c · log(β + q_c)`
(`powerProd_logSum_strictAntiOn`, with `q_c = b_c/y*_c`). Hence `H` is injective on its domain,
and two parameters giving the same value of `H` coincide.

* `eq_of_shiftedLogSum_eq` — `H β₁ = H β₂ ⟹ β₁ = β₂`.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.LinearAlgebra.PowerProductMonoFinset`.
-/

namespace CRNT

open scoped BigOperators

/-- **Injectivity of the shifted-monomial log-sum.** With `y*` positive on `s` and zero on `U`
(where `b > 0`), a positive lump `a₀ = ∑_{c ∈ U} G_c` with `a₀ + ∑_{c ∈ s} G_c = 0`, and the
level-set sign condition, the map `β ↦ ∑_{c ∈ s ∪ U} G_c · log(β · y*_c + b_c)` is injective on
`{β : ∀ c ∈ s, −b_c/y*_c < β}`: two such parameters with equal log-sum coincide. -/
theorem eq_of_shiftedLogSum_eq {ι : Type*} [DecidableEq ι] (s U : Finset ι)
    (hdisj : Disjoint s U) (ystar b G : ι → ℝ)
    (hys : ∀ c ∈ s, 0 < ystar c) (hyU : ∀ c ∈ U, ystar c = 0)
    (ha0 : 0 < ∑ c ∈ U, G c)
    (hsum : (∑ c ∈ U, G c) + ∑ c ∈ s, G c = 0)
    (hlevel : ∀ v : ℝ,
      0 ≤ (∑ c ∈ U, G c) + ∑ c ∈ s.filter (fun c => v < b c / ystar c), G c)
    {β₁ β₂ : ℝ}
    (hd₁ : ∀ c ∈ s, - (b c / ystar c) < β₁) (hd₂ : ∀ c ∈ s, - (b c / ystar c) < β₂)
    (hH : (∑ c ∈ s ∪ U, G c * Real.log (β₁ * ystar c + b c))
        = ∑ c ∈ s ∪ U, G c * Real.log (β₂ * ystar c + b c)) :
    β₁ = β₂ := by
  classical
  set q : ι → ℝ := fun c => b c / ystar c with hq
  -- `s` is nonempty (otherwise the lump would vanish).
  have hsne : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with h | h
    · rw [h] at hsum; simp only [Finset.sum_empty, add_zero] at hsum
      exact absurd hsum ha0.ne'
    · exact h
  obtain ⟨c0, hc0s, hmin⟩ := Finset.exists_min_image s q hsne
  -- Splitting `H` into a constant plus the log-sum `∑_{c ∈ s} G_c · log(β + q_c)`.
  have hsplit : ∀ β : ℝ, - q c0 < β →
      (∑ c ∈ s ∪ U, G c * Real.log (β * ystar c + b c))
        = ((∑ c ∈ U, G c * Real.log (b c)) + ∑ c ∈ s, G c * Real.log (ystar c))
          + ∑ c ∈ s, G c * Real.log (β + q c) := by
    intro β hβ
    rw [Finset.sum_union hdisj]
    have hsterm : ∀ c ∈ s, G c * Real.log (β * ystar c + b c)
        = G c * Real.log (ystar c) + G c * Real.log (β + q c) := by
      intro c hc
      have hyc : 0 < ystar c := hys c hc
      have hqpos : 0 < β + q c := by
        have : q c0 ≤ q c := hmin c hc
        linarith
      have hfac : β * ystar c + b c = ystar c * (β + q c) := by
        rw [hq, mul_add, mul_div_cancel₀ _ hyc.ne']; ring
      rw [hfac, Real.log_mul hyc.ne' hqpos.ne', mul_add]
    have hUterm : ∀ c ∈ U, G c * Real.log (β * ystar c + b c) = G c * Real.log (b c) := by
      intro c hc
      rw [hyU c hc, mul_zero, zero_add]
    rw [Finset.sum_congr rfl hsterm, Finset.sum_congr rfl hUterm, Finset.sum_add_distrib]
    ring
  -- The log-sum is strictly decreasing, hence injective, on `(−q c0, ∞)`.
  have hanti := powerProd_logSum_strictAntiOn s q G (∑ c ∈ U, G c) (q c0) ha0 hsum hmin hlevel
  have hmem₁ : β₁ ∈ Set.Ioi (- q c0) := hd₁ c0 hc0s
  have hmem₂ : β₂ ∈ Set.Ioi (- q c0) := hd₂ c0 hc0s
  have hlog : (∑ c ∈ s, G c * Real.log (β₁ + q c)) = ∑ c ∈ s, G c * Real.log (β₂ + q c) := by
    have e₁ := hsplit β₁ hmem₁
    have e₂ := hsplit β₂ hmem₂
    rw [e₁, e₂] at hH
    linarith [hH]
  exact hanti.injOn hmem₁ hmem₂ hlog

end CRNT

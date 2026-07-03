import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Strict monotonicity of a product of power functions

For real exponents `aᵢ` summing to zero and shifts `q₁ ≥ q₂ ≥ ⋯ ≥ q_k`, the function
`β ↦ ∏ᵢ (β + qᵢ)^{aᵢ}` is strictly decreasing on `(−q_k, ∞)` provided `a₀ > 0` and the
partial sums `∑_{j≤i} aⱼ` are nonnegative wherever the shifts strictly decrease. This is the
analytic linchpin of Feinberg's deficiency-one theorem: the equation pinning the equilibrium
parameter has at most one solution.

The combinatorial heart is an Abel summation (`sum_increment_mul_pos`): for an antitone `d`
with `d 1 < 0`, increments `a` with `a 0 > 0`, `∑ a = 0`, and the partial-sum sign condition,
`∑ᵢ a_{i+1}·d_{i+1} > 0`. Taking `d i = log(β₁ + qᵢ) − log(β₂ + qᵢ)` (which is antitone in
`i` and negative, for `β₁ < β₂`) turns this into the strict monotonicity
(`powerProd_strictAntiOn`).

Depends on:
`Mathlib.Algebra.BigOperators.Module`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`.
-/

namespace CRNT

open scoped BigOperators

/-- **Abel-summation inequality.** Let `d` be antitone on `[1, k]` with `d 1 < 0`, and let `a`
have `a 0 > 0`, `∑_{i ≤ k} a i = 0`, and nonnegative partial sums `∑_{j ≤ i} a j` at every
index where `d` strictly decreases. Then `∑_{i < k} a (i+1) · d (i+1) > 0`. -/
theorem sum_increment_mul_pos {k : ℕ} (hk : 1 ≤ k) {a d : ℕ → ℝ}
    (hd_anti : ∀ i, 1 ≤ i → i < k → d (i + 1) ≤ d i)
    (hd1 : d 1 < 0) (ha0 : 0 < a 0)
    (hsum : ∑ i ∈ Finset.range (k + 1), a i = 0)
    (hpartial : ∀ i, 1 ≤ i → i < k → d (i + 1) < d i → 0 ≤ ∑ j ∈ Finset.range (i + 1), a j) :
    0 < ∑ i ∈ Finset.range k, a (i + 1) * d (i + 1) := by
  -- Abel summation by parts on `∑_{i ≤ k} d i · a i`.
  have hby := Finset.sum_range_by_parts d a (k + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at hby
  rw [hsum, mul_zero, zero_sub, Finset.sum_range_succ' (fun i => d i * a i) k] at hby
  -- hby : (∑ i < k, d (i+1) * a (i+1)) + d 0 * a 0 = - ∑ i < k, (d (i+1) - d i) * G (i+1)
  have hmain : ∑ i ∈ Finset.range k, a (i + 1) * d (i + 1)
      = -(d 0 * a 0) - ∑ i ∈ Finset.range k,
          (d (i + 1) - d i) * ∑ j ∈ Finset.range (i + 1), a j := by
    have : ∑ i ∈ Finset.range k, a (i + 1) * d (i + 1)
        = ∑ i ∈ Finset.range k, d (i + 1) * a (i + 1) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this]; linarith [hby]
  -- Rewrite as `-d 1 · a 0 + ∑ nonnegative`.
  rw [hmain, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  have hsplit : ∑ i ∈ Finset.range k, -((d (i + 1) - d i) * ∑ j ∈ Finset.range (i + 1), a j)
      = (d 0 * a 0 - d 1 * a 0)
        + ∑ i ∈ Finset.range (k - 1),
            (d (i + 1) - d (i + 2)) * ∑ j ∈ Finset.range (i + 2), a j := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel]
    rw [add_comm]
    congr 1
    · simp only [Finset.sum_range_one, zero_add]; ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  have hpos : 0 < -(d 1 * a 0) := by nlinarith [hd1, ha0]
  have hnn : 0 ≤ ∑ i ∈ Finset.range (k - 1),
      (d (i + 1) - d (i + 2)) * ∑ j ∈ Finset.range (i + 2), a j := by
    refine Finset.sum_nonneg fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hi1 : 1 ≤ i + 1 := Nat.le_add_left 1 i
    have hik : i + 1 < k := by omega
    have hdiff : 0 ≤ d (i + 1) - d (i + 2) := by linarith [hd_anti (i + 1) hi1 hik]
    rcases hdiff.lt_or_eq with h | h
    · exact mul_nonneg hdiff (hpartial (i + 1) hi1 hik (by linarith))
    · simp [← h]
  linarith [hpos, hnn]

/-- **Strict monotonicity of a product of power functions (Feinberg's Lemma).** With shifts
`q` antitone on `[1, k]`, exponents `a` summing to zero with `a 0 > 0`, and the partial-sum
sign condition at indices where the shifts strictly decrease, the map
`β ↦ ∏_{i < k} (β + q (i+1)) ^ a (i+1)` is strictly decreasing on `(−q k, ∞)`. -/
theorem powerProd_strictAntiOn {k : ℕ} (hk : 1 ≤ k) {q a : ℕ → ℝ}
    (hq : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → q j ≤ q i)
    (ha0 : 0 < a 0) (hsum : ∑ i ∈ Finset.range (k + 1), a i = 0)
    (hpartial : ∀ i, 1 ≤ i → i < k → q (i + 1) < q i → 0 ≤ ∑ j ∈ Finset.range (i + 1), a j) :
    StrictAntiOn (fun β => ∏ i ∈ Finset.range k, (β + q (i + 1)) ^ a (i + 1))
      (Set.Ioi (- q k)) := by
  intro β₁ hβ₁ β₂ hβ₂ hlt
  simp only [Set.mem_Ioi] at hβ₁ hβ₂
  -- Each shift `q (i+1)` is at least `q k`, so the bases are positive on the domain.
  have hbase : ∀ β, - q k < β → ∀ i, i < k → 0 < β + q (i + 1) := by
    intro β hβ i hi
    have : q k ≤ q (i + 1) := hq (i + 1) k (by omega) (by omega) le_rfl
    linarith
  have hfpos : ∀ β, - q k < β →
      0 < ∏ i ∈ Finset.range k, (β + q (i + 1)) ^ a (i + 1) := by
    intro β hβ
    refine Finset.prod_pos fun i hi => Real.rpow_pos_of_pos (hbase β hβ i ?_) _
    exact Finset.mem_range.mp hi
  have hlog : ∀ β, - q k < β →
      Real.log (∏ i ∈ Finset.range k, (β + q (i + 1)) ^ a (i + 1))
        = ∑ i ∈ Finset.range k, a (i + 1) * Real.log (β + q (i + 1)) := by
    intro β hβ
    rw [Real.log_prod (fun i hi => (Real.rpow_pos_of_pos
      (hbase β hβ i (Finset.mem_range.mp hi)) _).ne')]
    exact Finset.sum_congr rfl fun i hi =>
      Real.log_rpow (hbase β hβ i (Finset.mem_range.mp hi)) _
  -- The coordinatewise log-ratio.
  set d : ℕ → ℝ := fun i => Real.log (β₁ + q i) - Real.log (β₂ + q i) with hd
  -- `d` is increasing in the shift, hence antitone in the index.
  have hdmono : ∀ u v : ℝ, 0 < β₁ + v → v ≤ u →
      Real.log (β₁ + v) - Real.log (β₂ + v) ≤ Real.log (β₁ + u) - Real.log (β₂ + u) := by
    intro u v hv hvu
    have hβ₂v : 0 < β₂ + v := by linarith
    have hβ₁u : 0 < β₁ + u := by linarith
    have hβ₂u : 0 < β₂ + u := by linarith
    rw [sub_le_sub_iff, ← Real.log_mul hv.ne' hβ₂u.ne', ← Real.log_mul hβ₁u.ne' hβ₂v.ne',
      Real.log_le_log_iff (mul_pos hv hβ₂u) (mul_pos hβ₁u hβ₂v)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlt.le) (sub_nonneg.mpr hvu)]
  have hpos1 : ∀ i, 1 ≤ i → i ≤ k → 0 < β₁ + q i := by
    intro i hi1 hik
    have : q k ≤ q i := hq i k hi1 hik le_rfl
    linarith
  have hanti : ∀ i, 1 ≤ i → i < k → d (i + 1) ≤ d i := fun i hi1 hik =>
    hdmono (q i) (q (i + 1)) (hpos1 (i + 1) (by omega) (by omega))
      (hq i (i + 1) hi1 (by omega) (by omega))
  have hd1 : d 1 < 0 := by
    have h1 : 0 < β₁ + q 1 := hpos1 1 le_rfl hk
    have : Real.log (β₁ + q 1) < Real.log (β₂ + q 1) := Real.log_lt_log h1 (by linarith)
    simp only [hd]; linarith
  have hpart : ∀ i, 1 ≤ i → i < k → d (i + 1) < d i →
      0 ≤ ∑ j ∈ Finset.range (i + 1), a j := by
    intro i hi1 hik hdlt
    refine hpartial i hi1 hik ?_
    rcases (hq i (i + 1) hi1 (by omega) (by omega)).lt_or_eq with h | h
    · exact h
    · simp only [hd, h] at hdlt; exact absurd hdlt (lt_irrefl _)
  have hkey : 0 < ∑ i ∈ Finset.range k, a (i + 1) * d (i + 1) :=
    sum_increment_mul_pos hk hanti hd1 ha0 hsum hpart
  have hconv : ∑ i ∈ Finset.range k, a (i + 1) * d (i + 1)
      = (∑ i ∈ Finset.range k, a (i + 1) * Real.log (β₁ + q (i + 1)))
        - ∑ i ∈ Finset.range k, a (i + 1) * Real.log (β₂ + q (i + 1)) := by
    simp only [hd, mul_sub]; rw [Finset.sum_sub_distrib]
  rw [← Real.log_lt_log_iff (hfpos β₂ hβ₂) (hfpos β₁ hβ₁), hlog β₂ hβ₂, hlog β₁ hβ₁]
  linarith [hkey, hconv]

end CRNT

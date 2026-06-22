import CRNT.LinearAlgebra.PerronFrobenius

/-!
# Substochastic matrices with no trapped mass have trivial fixed space

A nonnegative matrix `M` with column sums at most one is **column-substochastic**: each
column distributes at most a unit of mass. A column `ℓ` with `∑ i, M i ℓ < 1` is a **leak**
(mass escapes there). The support digraph of `M` (edge `a → c` iff `M a c ≠ 0`) carries the
flow: positivity at `c` feeds positivity at `a` through `M a c`.

If every index reaches a leak along the support digraph, then `M` has **no nonzero fixed
vector**: `M.mulVec v = v → v = 0`. Equivalently the spectral radius is below one, so
`1 - M` is injective. The proof is a single mass balance. From `M.mulVec v = v` and the
triangle inequality, `∑ i, |v i| ≤ ∑ j, (∑ i, M i j) · |v j| ≤ ∑ j, |v j|`; the ends agree, so
both inequalities are equalities. Equality on the right forces `|v j| > 0 ⇒ ∑ i, M i j = 1`
(the support avoids leaks); equality on the left forces `|v i| = ∑ j, M i j · |v j|`, whence a
support edge into the support keeps its source in the support (the support is closed under the
reverse-flow reachability). A support point would then reach a leak inside the support —
impossible, as the support avoids leaks. Hence the support is empty.

This is the substochastic Perron–Frobenius input behind drainage arguments: a transient block
of a Markov-type generator (mass eventually escaping to absorbing classes) has trivial kernel.

* `mulVec_fixed_eq_zero_of_substochastic` — the fixed-space triviality.

This module is **stable** and `sorry`-free. Depends on: `CRNT.LinearAlgebra.PerronFrobenius`.
-/

namespace CRNT

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- **A column-substochastic matrix whose every index reaches a leak has trivial fixed space.**
If `M ≥ 0` has column sums `≤ 1`, and along the support digraph (`supportReaches`) every index
is reached by some strictly-substochastic column `ℓ` (`∑ i, M i ℓ < 1`), then the only vector
fixed by `M` is zero. -/
theorem mulVec_fixed_eq_zero_of_substochastic
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 ≤ M i j) (hcol : ∀ j, ∑ i, M i j ≤ 1)
    (hreach : ∀ j, ∃ ℓ, supportReaches M ℓ j ∧ ∑ i, M i ℓ < 1)
    {v : ι → ℝ} (hv : M.mulVec v = v) : v = 0 := by
  classical
  have hvi : ∀ i, v i = ∑ j, M i j * v j := by
    intro i
    have hcong := congrFun hv i
    rw [← hcong]; simp [Matrix.mulVec, dotProduct]
  -- The triangle inequality bounds `|v i|` by the support-weighted sum of `|v|`.
  have htri : ∀ i, |v i| ≤ ∑ j, M i j * |v j| := by
    intro i
    rw [hvi i]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (hM i j)]
  -- Reindexing the double sum by columns introduces the column sums.
  have hcolsum : ∑ i, ∑ j, M i j * |v j| = ∑ j, (∑ i, M i j) * |v j| := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
  -- The mass balance pinches to an equality.
  have hsum_eq : ∑ i, |v i| = ∑ i, ∑ j, M i j * |v j| := by
    refine le_antisymm (Finset.sum_le_sum fun i _ => htri i) ?_
    rw [hcolsum]
    refine Finset.sum_le_sum fun j _ => ?_
    calc (∑ i, M i j) * |v j| ≤ 1 * |v j| :=
          mul_le_mul_of_nonneg_right (hcol j) (abs_nonneg _)
      _ = |v j| := one_mul _
  -- Equality on the left: every coordinate triangle inequality is tight.
  have hpt : ∀ i, |v i| = ∑ j, M i j * |v j| := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ (∑ j, M i j * |v j|) - |v i| :=
      fun i _ => by linarith [htri i]
    have hsum0 : ∑ i, ((∑ j, M i j * |v j|) - |v i|) = 0 := by
      rw [Finset.sum_sub_distrib, ← hsum_eq, sub_self]
    have heach := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0
    intro i; linarith [heach i (Finset.mem_univ i)]
  -- Equality on the right: the support avoids leaks.
  have hcol_eq : ∑ j, |v j| = ∑ j, (∑ i, M i j) * |v j| := by
    rw [(rfl : (∑ j, |v j|) = ∑ i, |v i|), hsum_eq, hcolsum]
  have hleak0 : ∀ j, (1 - ∑ i, M i j) * |v j| = 0 := by
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ (1 - ∑ i, M i j) * |v j| :=
      fun j _ => mul_nonneg (by linarith [hcol j]) (abs_nonneg _)
    have hsum0 : ∑ j, (1 - ∑ i, M i j) * |v j| = 0 := by
      rw [Finset.sum_congr rfl (fun j _ => by ring :
          ∀ j ∈ Finset.univ, (1 - ∑ i, M i j) * |v j| = |v j| - (∑ i, M i j) * |v j|),
        Finset.sum_sub_distrib, ← hcol_eq, sub_self]
    exact fun j => (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 j (Finset.mem_univ j)
  -- The support is closed under reverse-flow reachability.
  have hclose : ∀ {i j : ι}, supportReaches M i j → v j ≠ 0 → v i ≠ 0 := by
    intro i j hij hj
    induction hij using Relation.ReflTransGen.head_induction_on with
    | refl => exact hj
    | @head a c e _ ih =>
      have hac : 0 < M a c := (hM a c).lt_of_ne (Ne.symm e)
      have hpos : 0 < |v a| := by
        rw [hpt a]
        exact Finset.sum_pos' (fun k _ => mul_nonneg (hM a k) (abs_nonneg _))
          ⟨c, Finset.mem_univ c, mul_pos hac (abs_pos.mpr ih)⟩
      exact abs_pos.mp hpos
  -- A nonzero coordinate would reach a leak inside its own support.
  by_contra hv0
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
  obtain ⟨ℓ, hℓj, hℓleak⟩ := hreach j
  have hℓ : v ℓ ≠ 0 := hclose hℓj hj
  rcases mul_eq_zero.mp (hleak0 ℓ) with h | h
  · linarith [hℓleak]
  · exact hℓ (abs_eq_zero.mp h)

end CRNT

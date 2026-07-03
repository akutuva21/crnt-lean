import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Birch's theorem: uniqueness

Birch's theorem (the toric / global-injectivity result underlying the deficiency-zero
theorem) states that for a subspace `S ⊆ ℝ^ι` and a positive reference vector, each
positive stoichiometric compatibility class `c + S` contains exactly one positive point
`x` whose log-ratio to the reference is orthogonal to `S`. It has two halves:

* **Uniqueness** (`birch_uniqueness`, proved here): at most one such point. This is the
  elementary, purely order-theoretic half — it uses only the strict monotonicity of
  `Real.log` together with the orthogonality, no convexity machinery. It is the source of
  uniqueness of complex-balanced equilibria in the deficiency-zero theorem.
* **Existence** (open): at least one such point, obtained by minimizing the strictly
  convex relative-entropy `∑ᵢ (xᵢ log(xᵢ/x*ᵢ) − xᵢ + x*ᵢ)` over the compatibility class.
  This is the deep analytic half (strict convexity + coercivity + interior optimality).

-/

namespace CRNT

open scoped BigOperators

/-- **Birch uniqueness / global injectivity.** Two positive vectors lying in the same
coset of a subspace `S` whose log-ratio is orthogonal to `S` are equal.

Concretely: if `x, y` are strictly positive, `x - y ∈ S`, and the vector
`i ↦ log (x i) − log (y i)` is orthogonal to every element of `S` (with respect to the
standard inner product `∑ i, · * ·`), then `x = y`. -/
theorem birch_uniqueness {ι : Type*} [Fintype ι] (S : Submodule ℝ (ι → ℝ))
    {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hxy : x - y ∈ S)
    (horth : ∀ s ∈ S, ∑ i, (Real.log (x i) - Real.log (y i)) * s i = 0) :
    x = y := by
  -- Each coordinate's contribution to ⟨log x − log y, x − y⟩ is nonnegative.
  have hterm_nonneg : ∀ i, 0 ≤ (Real.log (x i) - Real.log (y i)) * (x i - y i) := by
    intro i
    rcases lt_trichotomy (x i) (y i) with h | h | h
    · nlinarith [Real.log_lt_log (hx i) h]
    · simp [h]
    · nlinarith [Real.log_lt_log (hy i) h]
  -- The total is zero, by orthogonality applied to `x − y ∈ S`.
  have h0 : ∑ i, (Real.log (x i) - Real.log (y i)) * (x i - y i) = 0 := by
    simpa using horth (x - y) hxy
  -- A sum of nonnegative terms is zero only if each term is zero.
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm_nonneg i).mp h0
  funext i
  have hz := hall i (Finset.mem_univ i)
  rcases lt_trichotomy (x i) (y i) with h | h | h
  · exact absurd hz (by nlinarith [Real.log_lt_log (hx i) h])
  · exact h
  · exact absurd hz (by nlinarith [Real.log_lt_log (hy i) h])

end CRNT

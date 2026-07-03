import CRNT.Decision.RationalFarkas

/-!
# Deciding rational linear feasibility by Fourier–Motzkin elimination

A finite rational linear system `sys : List (Ineq n)` is feasible when some point `x : Fin n → ℚ`
satisfies every inequality. This module turns the elimination step of `CRNT.RationalFarkas` into an
effective decision procedure for `Feasible sys` in any number of variables `n`.

The procedure recurses on `n`:

* **Base case `n = 0`.** A point of `Fin 0 → ℚ` is unique and every left-hand sum `∑ⱼ coeff j * x j`
  is the empty sum `0`, so a row `coeff · x ≤ bound` holds iff `0 ≤ bound`. Hence a `Fin 0` system is
  feasible iff each row's bound is nonnegative (`feasible_zero_iff`), a decidable condition.
* **Recursion `n + 1 → n`.** `feasible_eliminateLast_iff` states that `sys` is feasible iff the
  Fourier–Motzkin elimination `eliminateLast sys` (in `n` variables) is, so feasibility of `sys`
  reduces to feasibility of a smaller system. Iterating down to `n = 0` decides any system.

* `feasible_zero_iff` — feasibility of a `Fin 0` system is the nonnegativity of every bound.
* `decidableFeasible` — `Decidable (Feasible sys)` for every `n` and `sys`, by recursion on `n`.

This is the decision procedure for rational linear feasibility, the computational content of Farkas'
lemma obtained by iterated Fourier–Motzkin elimination.

The `decide` tactic evaluates the `Fin 0` base case directly, since it only compares each row's
bound against `0`. For `n ≥ 1` the eliminated rows carry products and differences of rationals, and
the kernel does not reduce `ℚ` multiplication during `decide`; such systems are decided by appeal to
the instance rather than by kernel evaluation.

Depends on: `CRNT.Decision.RationalFarkas`.
-/

open scoped BigOperators

namespace CRNT

namespace RationalFarkas

/-- In zero variables every left-hand sum is the empty sum `0`, so a row holds at any point iff its
bound is nonnegative. -/
theorem holds_zero_iff (I : Ineq 0) (x : Fin 0 → ℚ) : I.holds x ↔ 0 ≤ I.bound := by
  rw [Ineq.holds, Ineq.lhs, Fin.sum_univ_zero]

/-- **Base case of the decision procedure.** A `Fin 0` system is feasible iff every row's bound is
nonnegative. The unique point `0 : Fin 0 → ℚ` witnesses feasibility when the condition holds. -/
theorem feasible_zero_iff (sys : List (Ineq 0)) :
    Feasible sys ↔ ∀ row ∈ sys, 0 ≤ row.bound := by
  constructor
  · rintro ⟨x, hx⟩ row hrow
    exact (holds_zero_iff row x).1 (hx row hrow)
  · intro h
    refine ⟨0, fun I hI => ?_⟩
    exact (holds_zero_iff I 0).2 (h I hI)

/-- Feasibility of a `Fin 0` system is decidable: it reduces to the nonnegativity of every bound. -/
instance decidableFeasibleZero (sys : List (Ineq 0)) : Decidable (Feasible sys) :=
  decidable_of_iff _ (feasible_zero_iff sys).symm

/-- **Decision procedure for rational linear feasibility.** `Feasible sys` is decidable for every
number of variables `n` and every system `sys : List (Ineq n)`. The recursion eliminates the last
variable via `feasible_eliminateLast_iff` down to the `Fin 0` base case, the computational content of
Farkas' lemma by Fourier–Motzkin elimination. -/
instance decidableFeasible : ∀ {n : ℕ} (sys : List (Ineq n)), Decidable (Feasible sys)
  | 0, sys => decidableFeasibleZero sys
  | _ + 1, sys =>
    have : Decidable (Feasible (eliminateLast sys)) := decidableFeasible (eliminateLast sys)
    decidable_of_iff _ (feasible_eliminateLast_iff sys)

end RationalFarkas

end CRNT

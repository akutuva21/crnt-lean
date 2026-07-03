import CRNT.Basic.Complex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Concentrations

A concentration vector assigns a real concentration to each species. This module
defines the `Concentration` type, the nonnegativity and positivity predicates used as
explicit hypotheses throughout the kinetics and equilibrium layers, and the mass-
action monomial `x ^ y` associated to a complex.

Depends on: `CRNT.Basic.Complex`.
-/

namespace CRNT

/-- A concentration vector: a real concentration for each species. -/
abbrev Concentration (S : Type) := S → ℝ

namespace Concentration

variable {S : Type}

/-- A concentration vector is nonnegative when every species concentration is `≥ 0`. -/
def Nonnegative (x : Concentration S) : Prop := ∀ s : S, 0 ≤ x s

/-- A concentration vector is positive when every species concentration is `> 0`. -/
def Positive (x : Concentration S) : Prop := ∀ s : S, 0 < x s

/-- A positive concentration is in particular nonnegative. -/
theorem Positive.nonnegative {x : Concentration S} (h : x.Positive) : x.Nonnegative :=
  fun s => (h s).le

end Concentration

namespace Complex

variable {S : Type} [Fintype S]

/-- The mass-action monomial `x ^ y = ∏ s, (x s) ^ (y s)` of a complex `y` at a
concentration `x`. This is the concentration-dependent part of the mass-action rate
of a reaction whose source is `y`. -/
def massActionMonomial (y : Complex S) (x : Concentration S) : ℝ :=
  ∏ s : S, (x s) ^ (y s)

/-- The monomial of the zero complex is `1` (empty product of factors). -/
@[simp] theorem massActionMonomial_zero (x : Concentration S) :
    (Complex.zero : Complex S).massActionMonomial x = 1 := by
  simp [massActionMonomial, Complex.zero]

/-- A mass-action monomial of a nonnegative concentration is nonnegative. -/
theorem massActionMonomial_nonneg {x : Concentration S} (hx : x.Nonnegative)
    (y : Complex S) : 0 ≤ y.massActionMonomial x :=
  Finset.prod_nonneg fun s _ => pow_nonneg (hx s) _

/-- A mass-action monomial of a positive concentration is positive. -/
theorem massActionMonomial_pos {x : Concentration S} (hx : x.Positive)
    (y : Complex S) : 0 < y.massActionMonomial x :=
  Finset.prod_pos fun s _ => pow_pos (hx s) _

end Complex

end CRNT

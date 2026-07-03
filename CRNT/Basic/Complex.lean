import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Complexes

A *complex* is a formal finite linear combination of species with natural-number
coefficients. A complex over a species type `S` is modelled directly as a function
`S → ℕ` assigning a stoichiometric coefficient to each species.

It defines the `Complex` abbreviation together with the
basic algebraic operations (`zero`, `add`, `smul`) and the conversions used by the
stoichiometry and kinetics layers (`support`, `coeff`, `toRealVector`).

Depends on: Mathlib finite types and big operators.
-/

namespace CRNT

/-- A complex is a stoichiometric vector: a coefficient in `ℕ` for each species. -/
abbrev Complex (S : Type) := S → ℕ

namespace Complex

variable {S : Type}

/-- The zero complex, written `0` in informal chemistry. It is the source/target of
inflow, outflow, and degradation reactions. -/
def zero : Complex S := fun _ => 0

/-- The stoichiometric coefficient of a species in a complex. -/
def coeff (c : Complex S) (s : S) : ℕ := c s

/-- Pointwise sum of two complexes. -/
def add (c d : Complex S) : Complex S := fun s => c s + d s

/-- Scalar multiplication of a complex by a natural number. -/
def smul (n : ℕ) (c : Complex S) : Complex S := fun s => n * c s

/-- The species occurring in a complex with nonzero coefficient. -/
def support [Fintype S] [DecidableEq S] (c : Complex S) : Finset S :=
  Finset.univ.filter (fun s => c s ≠ 0)

/-- The real-valued stoichiometric vector of a complex. -/
def toRealVector (c : Complex S) : S → ℝ := fun s => (c s : ℝ)

@[simp] theorem zero_apply (s : S) : (zero : Complex S) s = 0 := rfl

@[simp] theorem coeff_eq (c : Complex S) (s : S) : c.coeff s = c s := rfl

@[simp] theorem add_apply (c d : Complex S) (s : S) : add c d s = c s + d s := rfl

@[simp] theorem smul_apply (n : ℕ) (c : Complex S) (s : S) : smul n c s = n * c s := rfl

@[simp] theorem toRealVector_apply (c : Complex S) (s : S) :
    toRealVector c s = (c s : ℝ) := rfl

end Complex

end CRNT

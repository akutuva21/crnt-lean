import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Subadditivity of `finrank` over a finite supremum of submodules

In a finite-dimensional space the dimension of a finite join of submodules is at most the
sum of their dimensions (`finrank_finset_sup_le`). This is the finite-family form of the
two-submodule bound `finrank (s ⊔ t) ≤ finrank s + finrank t`, itself a consequence of
`finrank_sup_add_finrank_inf_eq`. Mathlib has the two-submodule identity but not this
finite-family subadditivity; it is domain-general and upstreamable.

This module is **stable**.
-/

namespace CRNT

open scoped BigOperators

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The dimension of a join of two submodules is at most the sum of their dimensions. -/
theorem finrank_sup_le (s t : Submodule K V) :
    Module.finrank K (s ⊔ t : Submodule K V) ≤ Module.finrank K s + Module.finrank K t := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq s t
  omega

/-- **Subadditivity of `finrank` over a finite supremum of submodules.** -/
theorem finrank_finset_sup_le {ι : Type*} (s : Finset ι) (f : ι → Submodule K V) :
    Module.finrank K (s.sup f : Submodule K V) ≤ ∑ i ∈ s, Module.finrank K (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha]
    exact (finrank_sup_le (f a) (s.sup f)).trans (by gcongr)

end CRNT

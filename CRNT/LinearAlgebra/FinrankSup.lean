import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Subadditivity of `finrank` over a finite supremum of submodules

In a finite-dimensional space the dimension of a finite join of submodules is at most the
sum of their dimensions (`finrank_finset_sup_le`). This is the finite-family form of the
two-submodule bound `finrank (s ⊔ t) ≤ finrank s + finrank t`, itself a consequence of
`finrank_sup_add_finrank_inf_eq`. When the submodules are independent (`iSupIndep`) the bound is
an equality (`finrank_finset_sup_eq_sum_of_iSupIndep`, and the `Fintype` form
`finrank_iSup_eq_sum_of_iSupIndep`). Mathlib has the two-submodule identity but neither the
finite-family subadditivity nor the independent-family equality; both are domain-general and
upstreamable.

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

/-- **Dimension of a finite supremum of independent submodules is the sum of dimensions.** -/
theorem finrank_finset_sup_eq_sum_of_iSupIndep {ι : Type*} (s : Finset ι)
    (f : ι → Submodule K V) (h : iSupIndep f) :
    Module.finrank K (s.sup f : Submodule K V) = ∑ i ∈ s, Module.finrank K (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha, ← ih]
    have hdis : Disjoint (f a) (s.sup f) := by
      refine (iSupIndep_def.mp h a).mono_right ?_
      refine Finset.sup_le fun j hj => ?_
      exact le_iSup₂ (f := fun j (_ : j ≠ a) => f j) j (fun heq => ha (heq ▸ hj))
    have hadd := Submodule.finrank_sup_add_finrank_inf_eq (f a) (s.sup f)
    rw [hdis.eq_bot, finrank_bot, add_zero] at hadd
    omega

/-- **`Fintype` form:** the dimension of `⨆ i, f i` for an independent family is `∑ i, finrank (f i)`. -/
theorem finrank_iSup_eq_sum_of_iSupIndep {ι : Type*} [Fintype ι]
    (f : ι → Submodule K V) (h : iSupIndep f) :
    Module.finrank K (⨆ i, f i : Submodule K V) = ∑ i, Module.finrank K (f i) := by
  have hsup : (⨆ i, f i : Submodule K V) = Finset.univ.sup f :=
    le_antisymm (iSup_le fun i => Finset.le_sup (Finset.mem_univ i))
      (Finset.sup_le fun i _ => le_iSup f i)
  rw [hsup, finrank_finset_sup_eq_sum_of_iSupIndep Finset.univ f h]

end CRNT

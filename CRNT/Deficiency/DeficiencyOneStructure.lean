import CRNT.Deficiency.LinkageDeficiency

/-!
# Structure of the deficiency-one conditions

Feinberg's deficiency-one conditions force a sharp per-linkage-class picture: every linkage
class has deficiency exactly `0` or `1` (`linkageDeficiency_eq_zero_or_one`), and the number of
*deficient* classes (those with `δ_θ = 1`) equals the network deficiency
(`card_deficientLinkageClasses`). A deficiency-one network therefore has exactly one deficient
linkage class (`existsUnique_deficient_of_deficiencyOne`); every other class is
deficiency-zero. This is the reduction that localizes the deficiency-one steady-state analysis
to a single linkage class.

This module is **stable**. Depends on: `CRNT.Deficiency.LinkageDeficiency`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Classical

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Under the deficiency-one conditions, every linkage class has deficiency `0` or `1`.** -/
theorem linkageDeficiency_eq_zero_or_one (N : Network S) (h : N.DeficiencyOneConditions)
    (q : Quotient N.linkedSetoid) :
    N.linkageDeficiency q = 0 ∨ N.linkageDeficiency q = 1 := by
  have h0 := N.linkageDeficiency_nonneg q
  have h1 := h.linkageDeficiency_le_one q
  omega

/-- **The number of deficient linkage classes equals the network deficiency.** A class is
deficient when `δ_θ = 1`; the count of such classes is `δ`. -/
theorem card_deficientLinkageClasses (N : Network S) (h : N.DeficiencyOneConditions) :
    (Finset.univ.filter (fun q => N.linkageDeficiency q = 1)).card = N.deficiency := by
  have hcast : ((Finset.univ.filter (fun q => N.linkageDeficiency q = 1)).card : ℤ)
      = ∑ q, N.linkageDeficiency q := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    rcases N.linkageDeficiency_eq_zero_or_one h q with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  have : ((Finset.univ.filter (fun q => N.linkageDeficiency q = 1)).card : ℤ)
      = (N.deficiency : ℤ) := by rw [hcast, h.sum_eq, N.deficiencyInt_eq_deficiency]
  exact_mod_cast this

/-- **Condition (ii) is exactly that the per-class stoichiometric ranks sum to the network
stoichiometric rank.** Equivalently, the per-class stoichiometric subspaces are independent (the
join `⨆_θ stoichSubspace_θ = stoichSubspace` is a direct sum). This is the linear-algebraic
content of the tightness condition `∑_θ δ_θ = δ`. -/
theorem sum_linkageStoichRank_eq_stoichRank (N : Network S) (h : N.DeficiencyOneConditions) :
    ∑ q, (N.linkageStoichRank q : ℤ) = (N.stoichRank : ℤ) := by
  have hn : (∑ q, (N.numComplexesIn q : ℤ)) = (N.numComplexes : ℤ) := by
    rw [← Nat.cast_sum, N.sum_numComplexesIn]
  have hexp : ∑ q, N.linkageDeficiency q
      = (∑ q, (N.numComplexesIn q : ℤ)) - (Fintype.card (Quotient N.linkedSetoid) : ℤ)
        - ∑ q, (N.linkageStoichRank q : ℤ) := by
    simp only [linkageDeficiency, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  have hs := h.sum_eq
  rw [hexp, hn, card_quotient_eq, deficiencyInt] at hs
  linarith

/-- **A deficiency-one network satisfying the conditions has exactly one deficient linkage
class.** Every other linkage class is deficiency-zero. -/
theorem existsUnique_deficient_of_deficiencyOne (N : Network S) (hδ : N.DeficiencyOne)
    (h : N.DeficiencyOneConditions) :
    ∃! q : Quotient N.linkedSetoid, N.linkageDeficiency q = 1 := by
  have hcard : (Finset.univ.filter (fun q => N.linkageDeficiency q = 1)).card = 1 := by
    rw [card_deficientLinkageClasses N h, (N.deficiencyOne_iff_deficiency_eq_one).mp hδ]
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
  refine ⟨q, ?_, ?_⟩
  · have : q ∈ Finset.univ.filter (fun q => N.linkageDeficiency q = 1) := by rw [hq]; exact Finset.mem_singleton_self q
    exact (Finset.mem_filter.mp this).2
  · intro q' hq'
    have : q' ∈ Finset.univ.filter (fun q => N.linkageDeficiency q = 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ q', hq'⟩
    rw [hq, Finset.mem_singleton] at this
    exact this

end Network

end CRNT

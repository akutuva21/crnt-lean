import CRNT.Deficiency.DeficiencyOne
import CRNT.Decision.Linkage
import CRNT.LinearAlgebra.FinrankSup

/-!
# Per-linkage-class deficiency and the decomposition inequality

Each linkage class `θ` carries its own deficiency `δ_θ = n_θ − 1 − s_θ`, where `n_θ` is the
number of complexes in the class and `s_θ` the rank of the span of the reaction vectors of
the reactions within it. Feinberg's structural inequality

```text
∑_θ δ_θ ≤ δ
```

(`sum_linkageDeficiency_le_deficiency`) holds because the complexes partition into linkage
classes (`sum_numComplexesIn`), the class count is `ℓ` (`card_quotient_eq`), and the
stoichiometric subspace is the join of the per-class subspaces, so its rank is at most the sum
of the per-class ranks (`stoichRank_le_sum`). Equality is exactly the deficiency-one theorem's
condition `∑_θ δ_θ = δ`.

This module is **stable**. Depends on: `CRNT.Deficiency.DeficiencyOne`, `CRNT.Decision.Linkage`,
`CRNT.LinearAlgebra.FinrankSup`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Classical

variable {S : Type} [DecidableEq S] [Fintype S]

noncomputable instance instFintypeQuotientLinked (N : Network S) :
    Fintype (Quotient N.linkedSetoid) := Fintype.ofFinite _

/-- The linkage class of a complex of the network. -/
def classOf (N : Network S) (c : N.ComplexIdx) : Quotient N.linkedSetoid :=
  Quotient.mk N.linkedSetoid c

/-- The number of complexes in a linkage class. -/
noncomputable def numComplexesIn (N : Network S) (q : Quotient N.linkedSetoid) : ℕ :=
  (Finset.univ.filter (fun c : N.ComplexIdx => N.classOf c = q)).card

/-- The per-linkage-class stoichiometric subspace: the span of the reaction vectors of the
reactions whose source lies in the class. -/
def linkageStoichSubspace (N : Network S) (q : Quotient N.linkedSetoid) :
    Submodule ℝ (S → ℝ) :=
  Submodule.span ℝ {v | ∃ r : N.R, N.classOf (N.sourceIdx r) = q ∧ N.reactionVector r = v}

/-- The per-linkage-class stoichiometric rank. -/
noncomputable def linkageStoichRank (N : Network S) (q : Quotient N.linkedSetoid) : ℕ :=
  Module.finrank ℝ (N.linkageStoichSubspace q)

/-- The deficiency of a single linkage class, `δ_θ = n_θ − 1 − s_θ` (over `ℤ`). -/
noncomputable def linkageDeficiency (N : Network S) (q : Quotient N.linkedSetoid) : ℤ :=
  (N.numComplexesIn q : ℤ) - 1 - (N.linkageStoichRank q : ℤ)

/-- **The complexes partition into linkage classes:** `∑_θ n_θ = n`. -/
theorem sum_numComplexesIn (N : Network S) :
    ∑ q, N.numComplexesIn q = N.numComplexes := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset N.ComplexIdx)) (t := (Finset.univ : Finset (Quotient N.linkedSetoid)))
    (f := N.classOf) (fun c _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_coe] at h
  exact h.symm

/-- The number of linkage classes equals `ℓ`. -/
theorem card_quotient_eq (N : Network S) :
    Fintype.card (Quotient N.linkedSetoid) = N.numLinkageClasses := by
  rw [numLinkageClasses, Nat.card_eq_fintype_card]

/-- Each reaction vector lies in its class's stoichiometric subspace. -/
theorem reactionVector_mem_linkageStoichSubspace (N : Network S) (r : N.R) :
    N.reactionVector r ∈ N.linkageStoichSubspace (N.classOf (N.sourceIdx r)) :=
  Submodule.subset_span ⟨r, rfl, rfl⟩

/-- Each per-class subspace sits inside the stoichiometric subspace. -/
theorem linkageStoichSubspace_le (N : Network S) (q : Quotient N.linkedSetoid) :
    N.linkageStoichSubspace q ≤ N.stoichSubspace := by
  rw [linkageStoichSubspace, Submodule.span_le]
  rintro _ ⟨r, _, rfl⟩
  exact N.reactionVector_mem_stoichSubspace r

/-- **The stoichiometric subspace is the join of the per-class subspaces.** -/
theorem stoichSubspace_eq_sup (N : Network S) :
    N.stoichSubspace = Finset.univ.sup N.linkageStoichSubspace := by
  apply le_antisymm
  · rw [stoichSubspace, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact SetLike.le_def.mp
      (Finset.le_sup (Finset.mem_univ (N.classOf (N.sourceIdx r))))
      (N.reactionVector_mem_linkageStoichSubspace r)
  · exact Finset.sup_le fun q _ => N.linkageStoichSubspace_le q

/-- **The stoichiometric rank is at most the sum of the per-class ranks.** -/
theorem stoichRank_le_sum (N : Network S) :
    N.stoichRank ≤ ∑ q, N.linkageStoichRank q := by
  rw [stoichRank, stoichSubspace_eq_sup]
  exact finrank_finset_sup_le Finset.univ N.linkageStoichSubspace

/-- **The per-linkage-class deficiency decomposition inequality** `∑_θ δ_θ ≤ δ`. Equality is
Feinberg's deficiency-one condition. -/
theorem sum_linkageDeficiency_le_deficiency (N : Network S) :
    ∑ q, N.linkageDeficiency q ≤ N.deficiencyInt := by
  have hn : (∑ q, (N.numComplexesIn q : ℤ)) = (N.numComplexes : ℤ) := by
    rw [← Nat.cast_sum, N.sum_numComplexesIn]
  have hC : (N.stoichRank : ℤ) ≤ ∑ q, (N.linkageStoichRank q : ℤ) := by
    rw [← Nat.cast_sum]; exact_mod_cast N.stoichRank_le_sum
  have hsum : ∑ q, N.linkageDeficiency q
      = (∑ q, (N.numComplexesIn q : ℤ)) - (Fintype.card (Quotient N.linkedSetoid) : ℤ)
        - ∑ q, (N.linkageStoichRank q : ℤ) := by
    simp only [linkageDeficiency, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  rw [hsum, deficiencyInt, hn, card_quotient_eq]
  omega

end Network

end CRNT

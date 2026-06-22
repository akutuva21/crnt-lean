import CRNT.Deficiency.IncidenceBlock
import CRNT.Deficiency.DeficiencyOneStructure
import CRNT.LinearAlgebra.FinrankSup
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Per-linkage-class decomposition of the deficiency subspace

The complexes partition into linkage classes, giving coordinate subspaces `supportedOn q` (the
vectors vanishing off class `q`); these are independent (`iSupIndep_supportedOn`). The per-class
deficiency subspace `linkageDeficiencySubspace q := deficiencySubspace ⊓ supportedOn q` sits
inside the deficiency subspace, and the per-class pieces are independent.

Under the deficiency-one conditions the decomposition is tight: the deficiency subspace is the
join of its per-class parts (`deficiencySubspace_eq_iSup`). Its consequence — that a steady
state is complex-balanced on every deficiency-zero linkage class — localizes the deficiency-one
steady-state analysis to a single linkage class.

This module is **stable**. Depends on: `CRNT.Deficiency.IncidenceBlock`,
`CRNT.Deficiency.DeficiencyOneStructure`, `CRNT.LinearAlgebra.FinrankSup`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The coordinate subspace of vectors supported on a linkage class: those vanishing at every
complex outside the class. -/
def supportedOn (N : Network S) (q : Quotient N.linkedSetoid) :
    Submodule ℝ (N.ComplexIdx → ℝ) where
  carrier := {v | ∀ c, N.classOf c ≠ q → v c = 0}
  add_mem' {v w} hv hw := fun c hc => by simp [hv c hc, hw c hc]
  zero_mem' := fun _ _ => rfl
  smul_mem' a v hv := fun c hc => by simp [hv c hc]

@[simp] theorem mem_supportedOn {N : Network S} {q : Quotient N.linkedSetoid}
    {v : N.ComplexIdx → ℝ} : v ∈ N.supportedOn q ↔ ∀ c, N.classOf c ≠ q → v c = 0 :=
  Iff.rfl

theorem restrictToClass_mem_supportedOn (N : Network S) (q : Quotient N.linkedSetoid)
    (v : N.ComplexIdx → ℝ) : N.restrictToClass q v ∈ N.supportedOn q :=
  fun _ hc => restrictToClass_apply_of_ne N v hc

/-- The coordinate subspace of vectors vanishing *on* a linkage class. -/
def supportedOff (N : Network S) (q : Quotient N.linkedSetoid) :
    Submodule ℝ (N.ComplexIdx → ℝ) where
  carrier := {v | ∀ c, N.classOf c = q → v c = 0}
  add_mem' {v w} hv hw := fun c hc => by simp [hv c hc, hw c hc]
  zero_mem' := fun _ _ => rfl
  smul_mem' a v hv := fun c hc => by simp [hv c hc]

/-- **The per-class coordinate subspaces are independent.** A vector supported on `q` and on the
join of the other classes vanishes everywhere. -/
theorem iSupIndep_supportedOn (N : Network S) : iSupIndep N.supportedOn := by
  rw [iSupIndep_def]
  intro q
  rw [Submodule.disjoint_def]
  intro v hv hv'
  have hle : (⨆ q', ⨆ (_ : q' ≠ q), N.supportedOn q') ≤ N.supportedOff q :=
    iSup₂_le fun q' hq' w hw c hc => hw c (by rw [hc]; exact Ne.symm hq')
  have hon : v ∈ N.supportedOff q := hle hv'
  funext c
  by_cases hcq : N.classOf c = q
  · exact hon c hcq
  · exact hv c hcq

/-- The **per-linkage-class deficiency subspace**: the part of the deficiency subspace supported
on a single linkage class. -/
noncomputable def linkageDeficiencySubspace (N : Network S) (q : Quotient N.linkedSetoid) :
    Submodule ℝ (N.ComplexIdx → ℝ) :=
  N.deficiencySubspace ⊓ N.supportedOn q

theorem linkageDeficiencySubspace_le (N : Network S) (q : Quotient N.linkedSetoid) :
    N.linkageDeficiencySubspace q ≤ N.deficiencySubspace := inf_le_left

/-- **The per-class deficiency subspaces are independent.** -/
theorem iSupIndep_linkageDeficiencySubspace (N : Network S) :
    iSupIndep N.linkageDeficiencySubspace :=
  N.iSupIndep_supportedOn.mono fun _ => inf_le_right

/-- The join of the per-class deficiency subspaces sits inside the deficiency subspace. -/
theorem iSup_linkageDeficiencySubspace_le (N : Network S) :
    (⨆ q, N.linkageDeficiencySubspace q) ≤ N.deficiencySubspace :=
  iSup_le fun q => N.linkageDeficiencySubspace_le q

/-- The complex map sends a class-restricted cut vector into the per-class stoichiometric
subspace. -/
theorem complexMap_restrictToClass_mem_linkageStoichSubspace (N : Network S)
    (q : Quotient N.linkedSetoid) {v : N.ComplexIdx → ℝ}
    (hv : v ∈ LinearMap.range N.incidenceMap) :
    N.complexMap (N.restrictToClass q v) ∈ N.linkageStoichSubspace q := by
  obtain ⟨w, rfl⟩ := hv
  rw [N.incidenceMap_restrictToClass q w, ← LinearMap.comp_apply, complexMap_comp_incidenceMap]
  have hsum : N.stoichMap (fun r => if N.classOf (N.sourceIdx r) = q then w r else 0)
      = ∑ r, (if N.classOf (N.sourceIdx r) = q then w r else 0) • N.reactionVector r := by
    funext s
    rw [stoichMap_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun r _ => by rw [Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  refine Submodule.sum_mem _ fun r _ => ?_
  by_cases hr : N.classOf (N.sourceIdx r) = q
  · rw [if_pos hr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, hr, rfl⟩)
  · rw [if_neg hr, zero_smul]; exact Submodule.zero_mem _

/-- **The per-class stoichiometric subspaces are independent** (under the deficiency-one
conditions): condition (ii) `∑ s_θ = s` is exactly this independence. -/
theorem iSupIndep_linkageStoichSubspace (N : Network S) (h : N.DeficiencyOneConditions) :
    iSupIndep N.linkageStoichSubspace := by
  apply CRNT.iSupIndep_of_finrank_iSup_eq_sum
  have hsup : (⨆ q, N.linkageStoichSubspace q : Submodule ℝ (S → ℝ)) = N.stoichSubspace := by
    rw [N.stoichSubspace_eq_sup]
    exact le_antisymm (iSup_le fun q => Finset.le_sup (Finset.mem_univ q))
      (Finset.sup_le fun q _ => le_iSup _ q)
  rw [hsup]
  have hnat : ∑ q, N.linkageStoichRank q = N.stoichRank := by
    exact_mod_cast N.sum_linkageStoichRank_eq_stoichRank h
  exact hnat.symm

/-- **A deficiency vector restricts to a per-class deficiency vector.** For `v` in the
deficiency subspace, its restriction to any linkage class is again in the deficiency subspace
(supported on that class). -/
theorem restrictToClass_mem_linkageDeficiencySubspace (N : Network S)
    (h : N.DeficiencyOneConditions) {v : N.ComplexIdx → ℝ} (hv : v ∈ N.deficiencySubspace)
    (q : Quotient N.linkedSetoid) :
    N.restrictToClass q v ∈ N.linkageDeficiencySubspace q := by
  have hker : N.complexMap v = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hv).1
  have hrange : v ∈ LinearMap.range N.incidenceMap := (Submodule.mem_inf.mp hv).2
  -- the per-class complex images sum to zero and land in independent subspaces, so each is zero
  have hxmem : ∀ q', N.complexMap (N.restrictToClass q' v) ∈ N.linkageStoichSubspace q' :=
    fun q' => N.complexMap_restrictToClass_mem_linkageStoichSubspace q' hrange
  have hxsum : (∑ q', N.complexMap (N.restrictToClass q' v)) = 0 := by
    rw [← map_sum, N.sum_restrictToClass v, hker]
  have hx0 : N.complexMap (N.restrictToClass q v) = 0 := by
    have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
      (N.iSupIndep_linkageStoichSubspace h)
    exact hind Finset.univ (fun q' => N.complexMap (N.restrictToClass q' v))
      (fun q' _ => hxmem q') hxsum q (Finset.mem_univ q)
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩,
    N.restrictToClass_mem_supportedOn q v⟩
  · exact LinearMap.mem_ker.mpr hx0
  · exact N.restrictToClass_mem_range_incidenceMap q hrange

/-- **The deficiency subspace is the join of its per-linkage-class parts** under the
deficiency-one conditions: the decomposition `∑_θ δ_θ = δ` is tight. -/
theorem deficiencySubspace_eq_iSup (N : Network S) (h : N.DeficiencyOneConditions) :
    N.deficiencySubspace = ⨆ q, N.linkageDeficiencySubspace q := by
  refine le_antisymm (fun v hv => ?_) N.iSup_linkageDeficiencySubspace_le
  rw [← N.sum_restrictToClass v]
  exact Submodule.sum_mem _ fun q _ =>
    Submodule.mem_iSup_of_mem q (N.restrictToClass_mem_linkageDeficiencySubspace h hv q)

end Network

end CRNT

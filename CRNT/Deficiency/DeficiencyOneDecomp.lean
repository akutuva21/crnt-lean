import CRNT.Deficiency.IncidenceBlock
import CRNT.Deficiency.DeficiencyOneStructure
import CRNT.LinearAlgebra.FinrankSup

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

end Network

end CRNT

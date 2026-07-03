import CRNT.Deficiency.KineticBlock
import CRNT.Deficiency.SteadyStateKernel

/-!
# Per-linkage-class conservation of the cut space

Every vector in the cut space `Im ∂` sums to zero over each linkage class
(`sum_restrictToClass_eq_zero_of_mem_range_incidenceMap`): an incidence column
`e_{target r} − e_{source r}` has its two complexes in the same linkage class, so it
contributes nothing to the total over any single class. In particular the deficiency
subspace `ker Y ⊓ Im ∂` inherits this property.

This per-class zero-mean is the conservation behind the deficiency-one sign argument: a
nonzero deficiency vector restricted to a linkage class sums to zero, so it must take both
signs there.

Depends on: `CRNT.Deficiency.KineticBlock`,
`CRNT.Deficiency.SteadyStateKernel`.
-/

namespace CRNT

namespace Network

open scoped Classical

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A cut-space vector has zero sum over each linkage class.** -/
theorem sum_restrictToClass_eq_zero_of_mem_range_incidenceMap (N : Network S)
    {g : N.ComplexIdx → ℝ} (hg : g ∈ LinearMap.range N.incidenceMap)
    (q : Quotient N.linkedSetoid) :
    ∑ c, N.restrictToClass q g c = 0 := by
  obtain ⟨w, rfl⟩ := hg
  set T : Finset N.ComplexIdx := Finset.univ.filter (fun c => N.classOf c = q) with hT
  have hmem : ∀ c : N.ComplexIdx, c ∈ T ↔ N.classOf c = q := by
    intro c; rw [hT, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ c, h⟩⟩
  simp only [restrictToClass, incidenceMap_apply]
  rw [← Finset.sum_filter, ← hT, Finset.sum_comm]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_ite_eq T (N.targetIdx r) (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq T (N.sourceIdx r) (fun _ => (1 : ℝ))]
  have hsrctgt : (N.targetIdx r ∈ T) ↔ (N.sourceIdx r ∈ T) := by
    rw [hmem, hmem, N.classOf_sourceIdx_eq_targetIdx r]
  by_cases h : N.sourceIdx r ∈ T
  · rw [if_pos (hsrctgt.mpr h), if_pos h, sub_self, mul_zero]
  · rw [if_neg (fun hh => h (hsrctgt.mp hh)), if_neg h, sub_self, mul_zero]

/-- The deficiency subspace inherits per-class zero sum. -/
theorem sum_restrictToClass_eq_zero_of_mem_deficiencySubspace (N : Network S)
    {g : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace) (q : Quotient N.linkedSetoid) :
    ∑ c, N.restrictToClass q g c = 0 :=
  N.sum_restrictToClass_eq_zero_of_mem_range_incidenceMap (Submodule.mem_inf.mp hg).2 q

end Network

end CRNT

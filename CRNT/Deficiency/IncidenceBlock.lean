import CRNT.Deficiency.KineticBlock
import CRNT.Deficiency.KernelDimension

/-!
# Block structure of the incidence image over linkage classes

No reaction crosses a linkage class, so the incidence map `∂` is block diagonal: restricting an
incidence image to a single linkage class is again an incidence image, of the reactions kept
inside that class (`incidenceMap_restrictToClass`). Hence the cut space `Im ∂` is invariant
under per-class restriction (`restrictToClass_mem_range_incidenceMap`).

This is the incidence-side companion of the kinetic block structure, and a step toward
decomposing the deficiency subspace `ker Y ⊓ Im ∂` over linkage classes.

Depends on: `CRNT.Deficiency.KineticBlock`,
`CRNT.Deficiency.KernelDimension`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The incidence map is block diagonal over linkage classes.** Restricting an incidence
image to a linkage class is the incidence image of the reactions whose source lies in that
class. -/
theorem incidenceMap_restrictToClass (N : Network S) (q : Quotient N.linkedSetoid)
    (w : N.R → ℝ) :
    N.restrictToClass q (N.incidenceMap w)
      = N.incidenceMap (fun r => if N.classOf (N.sourceIdx r) = q then w r else 0) := by
  funext c
  by_cases hc : N.classOf c = q
  · rw [restrictToClass_apply_of_eq _ _ hc, incidenceMap_apply, incidenceMap_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : N.classOf (N.sourceIdx r) = q
    · rw [if_pos hr]
    · have hsrc : N.sourceIdx r ≠ c := fun h => hr (by rw [h]; exact hc)
      have htgt : N.targetIdx r ≠ c := fun h => hr (by
        rw [N.classOf_sourceIdx_eq_targetIdx r, h]; exact hc)
      rw [if_neg hr, zero_mul, if_neg htgt, if_neg hsrc, sub_zero, mul_zero]
  · rw [restrictToClass_apply_of_ne _ _ hc, incidenceMap_apply]
    refine (Finset.sum_eq_zero fun r _ => ?_).symm
    by_cases hr : N.classOf (N.sourceIdx r) = q
    · have hsrc : N.sourceIdx r ≠ c := fun h => hc (by rw [← h]; exact hr)
      have htgt : N.targetIdx r ≠ c := fun h => hc (by
        rw [← h, ← N.classOf_sourceIdx_eq_targetIdx r]; exact hr)
      rw [if_pos hr, if_neg htgt, if_neg hsrc, sub_zero, mul_zero]
    · rw [if_neg hr, zero_mul]

/-- **The cut space is invariant under per-class restriction.** -/
theorem restrictToClass_mem_range_incidenceMap (N : Network S) (q : Quotient N.linkedSetoid)
    {v : N.ComplexIdx → ℝ} (hv : v ∈ LinearMap.range N.incidenceMap) :
    N.restrictToClass q v ∈ LinearMap.range N.incidenceMap := by
  obtain ⟨w, rfl⟩ := hv
  exact ⟨_, (N.incidenceMap_restrictToClass q w).symm⟩

end Network

end CRNT

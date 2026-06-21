import CRNT.Deficiency.LinkageDeficiency
import CRNT.Dynamics.MassActionAlgebra

/-!
# Block structure of the kinetic map over linkage classes

No reaction crosses a linkage class, so the kinetic Laplacian `A_k` is block diagonal with
one block per linkage class. Two consequences are recorded:

* **Locality** (`kineticMap_apply_eq_of_eqOn_class`): the value of `A_k v` at a complex `c`
  depends only on the entries of `v` on the linkage class of `c`.
* **Commutation with restriction** (`kineticMap_restrictToClass`): restricting a vector to a
  single linkage class and then applying `A_k` is the same as applying `A_k` and then
  restricting. Equivalently, each linkage-class coordinate subspace is `A_k`-invariant.

This block decomposition is what lets the deficiency-one argument treat each linkage class
independently.

This module is **stable**. Depends on: `CRNT.Deficiency.LinkageDeficiency`,
`CRNT.Dynamics.MassActionAlgebra`.
-/

namespace CRNT

namespace Network

open scoped Classical

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Source and target of a reaction lie in the same linkage class. -/
theorem classOf_sourceIdx_eq_targetIdx (N : Network S) (r : N.R) :
    N.classOf (N.sourceIdx r) = N.classOf (N.targetIdx r) :=
  Quotient.sound (N.linked_of_reaction r)

/-- **Locality of the kinetic map.** The value of `A_k v` at `c` depends only on the entries
of `v` on the linkage class of `c`: if `v` and `w` agree there, the values agree. -/
theorem kineticMap_apply_eq_of_eqOn_class (N : Network S) (κ : RateConstants N)
    {v w : N.ComplexIdx → ℝ} {c : N.ComplexIdx}
    (h : ∀ d : N.ComplexIdx, N.classOf d = N.classOf c → v d = w d) :
    N.kineticMap κ v c = N.kineticMap κ w c := by
  rw [kineticMap_apply, kineticMap_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hterm : N.targetIdx r = c
  · have hclass : N.classOf (N.sourceIdx r) = N.classOf c := by
      rw [N.classOf_sourceIdx_eq_targetIdx r, hterm]
    rw [h _ hclass]
  · by_cases hsrc : N.sourceIdx r = c
    · rw [h (N.sourceIdx r) (by rw [hsrc])]
    · rw [if_neg hterm, if_neg hsrc]; ring

/-- The restriction of a vector to a linkage class: keep the entries on `q`, zero elsewhere. -/
noncomputable def restrictToClass (N : Network S) (q : Quotient N.linkedSetoid)
    (v : N.ComplexIdx → ℝ) : N.ComplexIdx → ℝ :=
  fun c => if N.classOf c = q then v c else 0

@[simp] theorem restrictToClass_apply_of_eq (N : Network S) {q : Quotient N.linkedSetoid}
    (v : N.ComplexIdx → ℝ) {c : N.ComplexIdx} (hc : N.classOf c = q) :
    N.restrictToClass q v c = v c := if_pos hc

@[simp] theorem restrictToClass_apply_of_ne (N : Network S) {q : Quotient N.linkedSetoid}
    (v : N.ComplexIdx → ℝ) {c : N.ComplexIdx} (hc : N.classOf c ≠ q) :
    N.restrictToClass q v c = 0 := if_neg hc

/-- **The kinetic map is block diagonal over linkage classes.** Restricting to a linkage
class commutes with the kinetic map, so each linkage-class coordinate subspace is
`A_k`-invariant. -/
theorem kineticMap_restrictToClass (N : Network S) (κ : RateConstants N)
    (q : Quotient N.linkedSetoid) (v : N.ComplexIdx → ℝ) :
    N.kineticMap κ (N.restrictToClass q v) = N.restrictToClass q (N.kineticMap κ v) := by
  funext c
  by_cases hc : N.classOf c = q
  · rw [restrictToClass_apply_of_eq _ _ hc]
    exact N.kineticMap_apply_eq_of_eqOn_class κ
      fun d hd => restrictToClass_apply_of_eq N v (hd.trans hc)
  · rw [restrictToClass_apply_of_ne _ _ hc]
    rw [show (0 : ℝ) = N.kineticMap κ 0 c by rw [map_zero]; rfl]
    exact N.kineticMap_apply_eq_of_eqOn_class κ
      fun d hd => restrictToClass_apply_of_ne N v (by rw [hd]; exact hc)

/-- **The per-class restrictions of a vector reassemble it:** the linkage classes partition
the complexes, so `∑_q (restriction to q) = v`. -/
theorem sum_restrictToClass (N : Network S) (v : N.ComplexIdx → ℝ) :
    ∑ q, N.restrictToClass q v = v := by
  funext c
  rw [Finset.sum_apply]
  simp only [restrictToClass]
  rw [Finset.sum_ite_eq Finset.univ (N.classOf c) (fun _ => v c)]
  simp

/-- **The kernel of the kinetic map decomposes over linkage classes.** A vector is killed by
`A_k` iff each of its per-class restrictions is — the block-diagonal kernel decomposition that
lets the deficiency-one argument solve `A_k v = 0` one linkage class at a time. -/
theorem kineticMap_eq_zero_iff_forall_restrictToClass (N : Network S) (κ : RateConstants N)
    (v : N.ComplexIdx → ℝ) :
    N.kineticMap κ v = 0 ↔ ∀ q, N.kineticMap κ (N.restrictToClass q v) = 0 := by
  constructor
  · intro h q
    rw [kineticMap_restrictToClass, h]
    funext c
    simp [restrictToClass]
  · intro h
    rw [← sum_restrictToClass N v, map_sum]
    exact Finset.sum_eq_zero fun q _ => h q

end Network

end CRNT

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic

/-!
# The excess function on a weighted finite digraph

For a finite digraph with arc set `E`, endpoints `src tgt : E → V`, and an arc weight
`z : E → ℝ`, the **excess** of a vertex `i` is the outgoing weight minus the incoming weight,
and the **excess of a set** `U` is the weight crossing out of `U` minus the weight crossing
into `U`. The fundamental identity is that excess is additive over vertices:
`excessSet U = ∑ i ∈ U, excessVertex i` — the net boundary flux of `U` equals the sum of the
per-vertex net fluxes, the internal arcs cancelling.

This is the combinatorial backbone of Feinberg's deficiency-one kernel analysis: applied to
the flux `z e = κ e · v (src e)`, the per-vertex excess is `−(A_k v)` at that complex, and the
set identity turns the kinetic equations into balance statements across complex subsets.

* `excessVertex`, `excessSet` — the vertex and set excess.
* `excessSet_eq_sum_excessVertex` — additivity over vertices.

This module is **stable** and `sorry`-free. Depends on:
`Mathlib.Algebra.BigOperators.Group.Finset.Basic`.
-/

namespace CRNT

open scoped BigOperators

variable {V E : Type*} [DecidableEq V] [Fintype E]

/-- The **excess of a vertex**: total weight on arcs leaving `i` minus that on arcs entering
`i`. -/
def excessVertex (src tgt : E → V) (z : E → ℝ) (i : V) : ℝ :=
  (∑ e, if src e = i then z e else 0) - ∑ e, if tgt e = i then z e else 0

/-- The **excess of a set** `U`: total weight on arcs leaving `U` (source in `U`, target out)
minus that on arcs entering `U` (source out, target in). -/
def excessSet (src tgt : E → V) (z : E → ℝ) (U : Finset V) : ℝ :=
  (∑ e, if src e ∈ U ∧ tgt e ∉ U then z e else 0)
    - ∑ e, if src e ∉ U ∧ tgt e ∈ U then z e else 0

/-- **Excess is additive over vertices.** The net boundary flux of a set equals the sum of the
per-vertex net fluxes; arcs internal to `U` cancel between the two endpoints. -/
theorem excessSet_eq_sum_excessVertex (src tgt : E → V) (z : E → ℝ) (U : Finset V) :
    excessSet src tgt z U = ∑ i ∈ U, excessVertex src tgt z i := by
  have key : ∀ f : E → V, (∑ i ∈ U, ∑ e, if f e = i then z e else 0)
      = ∑ e, if f e ∈ U then z e else 0 := by
    intro f
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : f e ∈ U
    · rw [Finset.sum_eq_single_of_mem (f e) h
        (fun i _ hi => if_neg fun heq => hi heq.symm), if_pos rfl, if_pos h]
    · rw [Finset.sum_eq_zero fun i hi => if_neg fun heq => h (by rw [← heq] at hi; exact hi),
        if_neg h]
  have hRHS : (∑ i ∈ U, excessVertex src tgt z i)
      = (∑ e, if src e ∈ U then z e else 0) - ∑ e, if tgt e ∈ U then z e else 0 := by
    simp only [excessVertex, Finset.sum_sub_distrib, key src, key tgt]
  rw [excessSet, hRHS, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hs : src e ∈ U <;> by_cases ht : tgt e ∈ U <;> simp [hs, ht]

end CRNT

import CRNT.Combinatorics.DigraphExcess
import CRNT.Dynamics.MassActionAlgebra

/-!
# The kinetic map as a digraph excess

The reaction graph of a network is the finite digraph with the complexes as vertices and the
reactions as arcs, each reaction `r` running from `sourceIdx r` to `targetIdx r`. Weighting an
arc `r` by `z r = κ_r · v (sourceIdx r)` — the mass-action flux carried by reaction `r` under
the complex-space vector `v` — the per-vertex excess of this flux is exactly the negative of the
kinetic map: `excessVertex c = −(A_k v)_c`. Outflow minus inflow on the digraph is outflow minus
inflow of `A_k`, with the orientation reversed.

Consequently the excess of a set of complexes is the negated total of `A_k v` over that set
(`excessSet_eq_neg_sum_kineticMap`), so the additivity of excess over vertices turns statements
about `A_k v` summed over complex subsets into boundary-flux statements across those subsets. This
is the link that lets the deficiency-one kernel analysis read partial sums of `A_k v` off the
combinatorics of the reaction graph.

* `excessVertex_eq_neg_kineticMap` — `excessVertex c = −(A_k v)_c` (the flux/excess identity).
* `excessSet_eq_neg_sum_kineticMap` — `excessSet U = −∑_{c ∈ U} (A_k v)_c`.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Combinatorics.DigraphExcess`, `CRNT.Dynamics.MassActionAlgebra`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The mass-action flux carried by each reaction under a complex-space vector `v`:
`kineticFlux κ v r = κ_r · v (sourceIdx r)`. This is the arc weight on the reaction graph whose
excess recovers the kinetic map. -/
def kineticFlux (N : Network S) (κ : RateConstants N) (v : N.ComplexIdx → ℝ) (r : N.R) : ℝ :=
  κ.k r * v (N.sourceIdx r)

/-- **The kinetic map is the negative excess (Feinberg–Boros Prop II.5).** On the reaction graph,
the per-vertex excess of the mass-action flux equals `−(A_k v)` at that complex: outflow minus
inflow of the flux is the reverse of the kinetic map's inflow minus outflow. -/
theorem excessVertex_eq_neg_kineticMap (N : Network S) (κ : RateConstants N)
    (v : N.ComplexIdx → ℝ) (c : N.ComplexIdx) :
    excessVertex N.sourceIdx N.targetIdx (N.kineticFlux κ v) c = - N.kineticMap κ v c := by
  rw [excessVertex, kineticMap_apply, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [kineticFlux]
  by_cases hs : N.sourceIdx r = c <;> by_cases ht : N.targetIdx r = c <;> simp [hs, ht]

/-- **The excess of a complex set is the negated kinetic-map total (Prop II.5, set form).** The
boundary flux of a set of complexes equals `−∑_{c ∈ U} (A_k v)_c`; via additivity of excess this
turns sums of `A_k v` over complex subsets into net boundary fluxes. -/
theorem excessSet_eq_neg_sum_kineticMap (N : Network S) (κ : RateConstants N)
    (v : N.ComplexIdx → ℝ) (U : Finset N.ComplexIdx) :
    excessSet N.sourceIdx N.targetIdx (N.kineticFlux κ v) U
      = - ∑ c ∈ U, N.kineticMap κ v c := by
  rw [excessSet_eq_sum_excessVertex, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun c _ => N.excessVertex_eq_neg_kineticMap κ v c

end Network

end CRNT

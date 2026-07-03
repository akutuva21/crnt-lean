import CRNT.Deficiency.KineticExcess
import CRNT.Graph.Crossing

/-!
# Net inflow into a vanishing set

When a complex-space vector `v` vanishes on a set `U` of complexes, every reaction leaving `U`
carries zero mass-action flux, so the `A_k`-total over `U` reduces to the pure inflow — the flux
of reactions entering `U` from outside. That inflow is a sum of nonnegative terms `κ_r · v(source
r)`, hence nonnegative, and it is strictly positive as soon as one reaction enters `U` from a
complex where `v` is positive (Feinberg–Boros Prop II.8).

This is the sign engine of the deficiency-one assembly: applied to the kernel/preimage vectors of
`A_k`, it converts strong connectivity of the terminal strong linkage class — which supplies an
entering reaction across any proper boundary — into the strict sign conditions feeding the
power-product monotonicity lemma.

* `sum_kineticMap_eq_inflow_of_vanishing` — `∑_{c ∈ U} (A_k v)_c = inflow` when `v = 0` on `U`.
* `sum_kineticMap_nonneg_of_vanishing` — the `A_k`-total over `U` is nonnegative.
* `sum_kineticMap_pos_of_inflow` — it is positive given one entering reaction with `v(source) > 0`.

Depends on:
`CRNT.Deficiency.KineticExcess`, `CRNT.Graph.Crossing`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The `A_k`-total over a vanishing set is its inflow.** If `v` is zero on every complex of
`U`, the reactions leaving `U` carry no flux, so the kinetic-map total over `U` is exactly the
flux entering `U` from outside. -/
theorem sum_kineticMap_eq_inflow_of_vanishing (N : Network S) (κ : RateConstants N)
    (v : N.ComplexIdx → ℝ) (U : Finset N.ComplexIdx) (hv : ∀ c ∈ U, v c = 0) :
    ∑ c ∈ U, N.kineticMap κ v c
      = ∑ r, if N.sourceIdx r ∉ U ∧ N.targetIdx r ∈ U then N.kineticFlux κ v r else 0 := by
  have h := N.excessSet_eq_neg_sum_kineticMap κ v U
  simp only [excessSet] at h
  have hzero : (∑ r, if N.sourceIdx r ∈ U ∧ N.targetIdx r ∉ U then N.kineticFlux κ v r else 0)
      = 0 := by
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hc : N.sourceIdx r ∈ U ∧ N.targetIdx r ∉ U
    · rw [if_pos hc]; simp only [kineticFlux, hv _ hc.1, mul_zero]
    · rw [if_neg hc]
  rw [hzero, zero_sub] at h
  exact (neg_injective h).symm

/-- The inflow into a vanishing set is **nonnegative**: it is a sum of nonnegative fluxes. -/
theorem sum_kineticMap_nonneg_of_vanishing (N : Network S) (κ : RateConstants N)
    (v : N.ComplexIdx → ℝ) (U : Finset N.ComplexIdx) (hvnn : ∀ c, 0 ≤ v c)
    (hv : ∀ c ∈ U, v c = 0) :
    0 ≤ ∑ c ∈ U, N.kineticMap κ v c := by
  rw [N.sum_kineticMap_eq_inflow_of_vanishing κ v U hv]
  refine Finset.sum_nonneg fun r _ => ?_
  by_cases hc : N.sourceIdx r ∉ U ∧ N.targetIdx r ∈ U
  · rw [if_pos hc]; exact mul_nonneg (κ.positive r).le (hvnn _)
  · rw [if_neg hc]

/-- The inflow into a vanishing set is **strictly positive** once some reaction enters `U` from a
complex where `v` is positive. -/
theorem sum_kineticMap_pos_of_inflow (N : Network S) (κ : RateConstants N)
    (v : N.ComplexIdx → ℝ) (U : Finset N.ComplexIdx) (hvnn : ∀ c, 0 ≤ v c)
    (hv : ∀ c ∈ U, v c = 0) {r₀ : N.R}
    (hsrc : N.sourceIdx r₀ ∉ U) (htgt : N.targetIdx r₀ ∈ U) (hpos : 0 < v (N.sourceIdx r₀)) :
    0 < ∑ c ∈ U, N.kineticMap κ v c := by
  rw [N.sum_kineticMap_eq_inflow_of_vanishing κ v U hv]
  refine Finset.sum_pos' (fun r _ => ?_) ⟨r₀, Finset.mem_univ r₀, ?_⟩
  · by_cases hc : N.sourceIdx r ∉ U ∧ N.targetIdx r ∈ U
    · rw [if_pos hc]; exact mul_nonneg (κ.positive r).le (hvnn _)
    · rw [if_neg hc]
  · rw [if_pos ⟨hsrc, htgt⟩]; exact mul_pos (κ.positive r₀) hpos

end Network

end CRNT

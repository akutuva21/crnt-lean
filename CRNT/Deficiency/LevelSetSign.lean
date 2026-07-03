import Mathlib.Tactic.Linarith
import CRNT.Deficiency.KineticExcess

/-!
# A level-set sign for the kinetic map

For a kernel vector `b` of `A_k` and any `y*`, the `A_k y*`-total over the super-level set
`{c : v · y*_c < b_c}` is nonnegative whenever `v > 0`. The reason is a flux comparison across
the boundary of the set `D = {b − v·y* > 0}`: every reaction entering `D` has its source outside
`D`, where `b ≤ v·y*`, so its `b`-flux is at most `v` times its `y*`-flux; every reaction leaving
`D` has its source inside `D`, where `b ≥ v·y*`, so its `b`-flux is at least `v` times its
`y*`-flux. Since the `b`-fluxes net to zero over `D` (the column-sum form of `A_k b = 0`), the
`y*`-net inflow has the sign of `v`.

These are exactly the partial-sum sign inequalities feeding the order-free power-product
monotonicity lemma in the deficiency-one uniqueness proof: the level set `{v · y* < b}` is the
down-set of complexes whose ratio `b/y*` exceeds the threshold `v`.

A companion records the boundary case: over a **reaction-closed** (absorbing) set of complexes —
no reaction leaves it — the `A_k w`-total is pure inflow, hence nonnegative for any `w ≥ 0`.

* `sum_kineticMap_superlevel_nonneg` — `0 ≤ ∑_{c : v·y*_c < b_c} (A_k y*)_c` for `v > 0`.
* `sum_kineticMap_closed_nonneg` — `0 ≤ ∑_{c ∈ U} (A_k w)_c` for `U` reaction-closed and `w ≥ 0`.

Depends on: `CRNT.Deficiency.KineticExcess`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Level-set sign of the kinetic map.** If `b` is a kernel vector of `A_k` and `v > 0`, then
the `A_k y*`-total over the super-level set `{c : v · y*_c < b_c}` is nonnegative. -/
theorem sum_kineticMap_superlevel_nonneg (N : Network S) (κ : RateConstants N)
    (b ystar : N.ComplexIdx → ℝ) {v : ℝ} (hv : 0 < v) (hb : N.kineticMap κ b = 0) :
    0 ≤ ∑ c ∈ Finset.univ.filter (fun c => v * ystar c < b c), N.kineticMap κ ystar c := by
  classical
  set D : Finset N.ComplexIdx := Finset.univ.filter (fun c => v * ystar c < b c) with hD
  have hmemD : ∀ c, c ∈ D ↔ v * ystar c < b c := by
    intro c; rw [hD, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ c, h⟩⟩
  -- The `A_k w`-total over `D` as inflow minus outflow.
  have key : ∀ w : N.ComplexIdx → ℝ, (∑ c ∈ D, N.kineticMap κ w c)
      = (∑ r, if N.sourceIdx r ∉ D ∧ N.targetIdx r ∈ D then κ.k r * w (N.sourceIdx r) else 0)
        - ∑ r, if N.sourceIdx r ∈ D ∧ N.targetIdx r ∉ D then κ.k r * w (N.sourceIdx r) else 0 := by
    intro w
    have h := N.excessSet_eq_neg_sum_kineticMap κ w D
    simp only [excessSet, kineticFlux] at h
    linarith [h]
  -- The `b`-net over `D` is zero.
  have hbzero : (∑ r, if N.sourceIdx r ∉ D ∧ N.targetIdx r ∈ D then κ.k r * b (N.sourceIdx r) else 0)
      - (∑ r, if N.sourceIdx r ∈ D ∧ N.targetIdx r ∉ D then κ.k r * b (N.sourceIdx r) else 0)
      = 0 := by
    rw [← key b]
    simp only [hb, Pi.zero_apply, Finset.sum_const_zero]
  -- Inflow comparison: on entering reactions the source is outside `D`, so `b ≤ v · y*`.
  have hin : (∑ r, if N.sourceIdx r ∉ D ∧ N.targetIdx r ∈ D then κ.k r * b (N.sourceIdx r) else 0)
      ≤ v * (∑ r, if N.sourceIdx r ∉ D ∧ N.targetIdx r ∈ D
          then κ.k r * ystar (N.sourceIdx r) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    by_cases hc : N.sourceIdx r ∉ D ∧ N.targetIdx r ∈ D
    · rw [if_pos hc, if_pos hc]
      have hsrc : ¬ v * ystar (N.sourceIdx r) < b (N.sourceIdx r) := by
        rw [← hmemD]; exact hc.1
      nlinarith [κ.positive r, not_lt.mp hsrc]
    · rw [if_neg hc, if_neg hc, mul_zero]
  -- Outflow comparison: on leaving reactions the source is inside `D`, so `b ≥ v · y*`.
  have hout : v * (∑ r, if N.sourceIdx r ∈ D ∧ N.targetIdx r ∉ D
          then κ.k r * ystar (N.sourceIdx r) else 0)
      ≤ (∑ r, if N.sourceIdx r ∈ D ∧ N.targetIdx r ∉ D then κ.k r * b (N.sourceIdx r) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    by_cases hc : N.sourceIdx r ∈ D ∧ N.targetIdx r ∉ D
    · rw [if_pos hc, if_pos hc]
      have hsrc : v * ystar (N.sourceIdx r) < b (N.sourceIdx r) := (hmemD _).mp hc.1
      nlinarith [κ.positive r, hsrc]
    · rw [if_neg hc, if_neg hc, mul_zero]
  -- Combine: `0 = b-net ≤ v · (y*-net)`, so `y*-net ≥ 0`.
  set inY := (∑ r, if N.sourceIdx r ∉ D ∧ N.targetIdx r ∈ D
    then κ.k r * ystar (N.sourceIdx r) else 0) with hinY
  set outY := (∑ r, if N.sourceIdx r ∈ D ∧ N.targetIdx r ∉ D
    then κ.k r * ystar (N.sourceIdx r) else 0) with houtY
  have hcancel : v * outY ≤ v * inY := by linarith [hin, hout, hbzero]
  have hle : outY ≤ inY := le_of_mul_le_mul_left hcancel hv
  rw [key ystar, ← hinY, ← houtY]
  linarith [hle]

/-- **Nonnegativity of the `A_k`-total over an absorbing set.** If no reaction leaves `U`
(`source ∈ U → target ∈ U`) and `w ≥ 0`, then the `A_k w`-total over `U` is the inflow into `U`,
hence nonnegative. -/
theorem sum_kineticMap_closed_nonneg (N : Network S) (κ : RateConstants N)
    (w : N.ComplexIdx → ℝ) (U : Finset N.ComplexIdx)
    (hclosed : ∀ r, N.sourceIdx r ∈ U → N.targetIdx r ∈ U) (hw : ∀ c, 0 ≤ w c) :
    0 ≤ ∑ c ∈ U, N.kineticMap κ w c := by
  classical
  have h := N.excessSet_eq_neg_sum_kineticMap κ w U
  simp only [excessSet, kineticFlux] at h
  -- the outflow term vanishes: no reaction leaves `U`
  have hout : (∑ r, if N.sourceIdx r ∈ U ∧ N.targetIdx r ∉ U
      then κ.k r * w (N.sourceIdx r) else 0) = 0 := by
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [if_neg]; rintro ⟨hs, ht⟩; exact ht (hclosed r hs)
  -- the inflow term is nonnegative
  have hin : 0 ≤ ∑ r, if N.sourceIdx r ∉ U ∧ N.targetIdx r ∈ U
      then κ.k r * w (N.sourceIdx r) else 0 := by
    refine Finset.sum_nonneg fun r _ => ?_
    by_cases hc : N.sourceIdx r ∉ U ∧ N.targetIdx r ∈ U
    · rw [if_pos hc]; exact mul_nonneg (κ.positive r).le (hw _)
    · rw [if_neg hc]
  rw [hout] at h
  linarith [h, hin]

end Network

end CRNT

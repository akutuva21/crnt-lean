import CRNT.Stochastic.KernelNormalized

/-!
# Support of the normalized invariant jump-chain probability measure

`CRNT.Stochastic.KernelNormalized` builds the normalized invariant probability measure of the
embedded jump chain on a finite closed enabled region `T`: the support-restricted stationary measure
divided by its total mass. This module identifies the support of that distribution. The stationary
distribution of the Anderson–Craciun–Kurtz embedded jump chain is concentrated on the region `T`,
strictly positive on every count inside `T` and null on every count outside it.

The singleton mass scales the restricted measure's singleton mass by the reciprocal total mass. On a
member of `T` both factors are positive — the reciprocal is positive because the finite region gives
a finite, nonzero total mass (`restrictedStationaryMeasure_isFiniteMeasure`,
`restrictedStationaryMeasure_univ_pos`), and the restricted singleton mass is the lifted stationary
weight `ofReal (jumpStationaryMass κ c m)`, positive on the region by `jumpStationaryMass_pos`. Off
the region the restricted singleton mass is the zero indicator, and the complement of `T` meets `T`
in the empty set, so the whole complement carries no mass.

## Main results

* `jumpKernel_invariantProb_singleton_pos` — strict positivity on every singleton inside the region.
* `jumpKernel_invariantProb_singleton_eq_zero` — null on every count outside the region.
* `jumpKernel_invariantProb_compl_eq_zero` — null on the complement: the distribution is supported in
  the region.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Stochastic.KernelNormalized`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- The normalized invariant probability measure of a nonempty finite closed enabled region is
strictly positive on every singleton inside the region. -/
theorem jumpKernel_invariantProb_singleton_pos (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Positive) {T : Set (S → ℕ)}
    (hT : N.ClosedEnabledRegion κ T) (hTfin : T.Finite) (_hne : T.Nonempty) {m : S → ℕ} (hm : m ∈ T) :
    0 < ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) {m} := by
  haveI hfin : IsFiniteMeasure (N.restrictedStationaryMeasure κ c T) :=
    N.restrictedStationaryMeasure_isFiniteMeasure κ c hTfin
  rw [Measure.smul_apply, smul_eq_mul]
  refine ENNReal.mul_pos ?_ ?_
  · refine ENNReal.inv_ne_zero.mpr ?_
    exact measure_ne_top (N.restrictedStationaryMeasure κ c T) Set.univ
  · rw [N.restrictedStationaryMeasure_singleton κ c T m, Set.indicator_of_mem hm]
    exact (ENNReal.ofReal_pos.mpr (N.jumpStationaryMass_pos κ c hc hT hm)).ne'

/-- Null on every count outside the region. -/
theorem jumpKernel_invariantProb_singleton_eq_zero (N : Network S) (κ : RateConstants N)
    (c : Concentration S) {T : Set (S → ℕ)} {m : S → ℕ} (hm : m ∉ T) :
    ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) {m} = 0 := by
  rw [Measure.smul_apply, smul_eq_mul, N.restrictedStationaryMeasure_singleton κ c T m,
    Set.indicator_of_notMem hm, mul_zero]

/-- Null on the complement of the region: the stationary distribution is supported in the region. -/
theorem jumpKernel_invariantProb_compl_eq_zero (N : Network S) (κ : RateConstants N)
    (c : Concentration S) {T : Set (S → ℕ)} :
    ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) Tᶜ = 0 := by
  rw [Measure.smul_apply, smul_eq_mul]
  have hμ : N.restrictedStationaryMeasure κ c T Tᶜ = 0 := by
    rw [restrictedStationaryMeasure,
      Measure.restrict_apply' (MeasurableSpace.measurableSet_top (s := T)),
      Set.compl_inter_self, measure_empty]
  rw [hμ, mul_zero]

end Network

end CRNT

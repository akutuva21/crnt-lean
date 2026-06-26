import CRNT.Stochastic.KernelSupport

/-!
# Product-form proportionality of the invariant jump-chain singleton masses

`CRNT.Stochastic.KernelSupport` identifies the support of the normalized invariant probability
measure of the embedded jump chain on a finite closed enabled region `T`. This module records the
proportionality that relates its singleton masses inside `T`: each singleton mass is the common
reciprocal total mass times the lifted jump-chain stationary weight `ofReal (jumpStationaryMass κ c
m)`. Cross-multiplying two such singletons cancels the shared reciprocal factor and leaves the
weights symmetric, the discrete shadow of the Anderson–Craciun–Kurtz product form for the
stationary distribution of the embedded jump chain.

## Main results

* `jumpKernel_invariantProb_singleton_ratio` — the cross-multiplied proportionality of two singleton
  masses inside the region by the jump-chain stationary weights.
* `jumpKernel_invariantProb_singleton_ne_zero_iff` — the normalized invariant measure is nonzero on a
  singleton exactly when the count lies in the region.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Stochastic.KernelSupport`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- Product-form proportionality: the normalized invariant measure's singleton masses on the
region are related through the jump-chain stationary weight (the discrete shadow of the
Anderson–Craciun–Kurtz product form). Cross-multiplied (no division, no positivity). -/
theorem jumpKernel_invariantProb_singleton_ratio (N : Network S) (κ : RateConstants N)
    (c : Concentration S) {T : Set (S → ℕ)} {m m' : S → ℕ} (hm : m ∈ T) (hm' : m' ∈ T) :
    ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) {m}
        * ENNReal.ofReal (N.jumpStationaryMass κ c m')
      = ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) {m'}
        * ENNReal.ofReal (N.jumpStationaryMass κ c m) := by
  rw [Measure.smul_apply, smul_eq_mul, N.restrictedStationaryMeasure_singleton κ c T m,
    Set.indicator_of_mem hm, Measure.smul_apply, smul_eq_mul,
    N.restrictedStationaryMeasure_singleton κ c T m', Set.indicator_of_mem hm']
  ac_rfl

/-- Support biconditional: the normalized invariant measure is nonzero on a singleton iff the
count lies in the region. -/
theorem jumpKernel_invariantProb_singleton_ne_zero_iff (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Positive) {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T)
    (hTfin : T.Finite) (hne : T.Nonempty) (m : S → ℕ) :
    ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) {m} ≠ 0
      ↔ m ∈ T := by
  constructor
  · intro hpos
    by_contra hm
    exact hpos (N.jumpKernel_invariantProb_singleton_eq_zero κ c hm)
  · intro hm
    exact (N.jumpKernel_invariantProb_singleton_pos κ c hc hT hTfin hne hm).ne'

end Network

end CRNT

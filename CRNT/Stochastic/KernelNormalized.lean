import CRNT.Stochastic.KernelIrreducible

/-!
# Normalizing the support-restricted invariant measure to a probability measure

`CRNT.Stochastic.KernelIrreducible` proves the embedded jump kernel leaves the support-restricted
density measure `restrictedStationaryMeasure κ c T` invariant over any closed enabled region `T`.
For a *finite* region that measure is finite, so it normalizes to a genuine **invariant probability
measure** — the stationary distribution of the jump chain on the region. This module supplies the
normalization layer named as the next dependency of the kernel ladder (`IsProbabilityMeasure`).

The core is general measure theory: scaling an invariant measure by a constant preserves invariance
(`invariant_smul`, since `Measure.bind` is linear), so dividing a finite nonzero invariant measure
by its total mass gives an invariant probability measure (`invariant_normalize`). Applied to the
restricted stationary measure of a finite closed enabled region — finite by
`restrictedStationaryMeasure_isFiniteMeasure` — this yields
`jumpKernel_normalized_isInvariant_probabilityMeasure`: the normalized restricted stationary measure
is both `Kernel.Invariant` under the jump kernel and an `IsProbabilityMeasure`.

The total mass being nonzero (`hpos`) stays a hypothesis: it is the network-and-region-dependent
fact that some count in `T` carries positive product-Poisson weight, not derivable from the closure
structure alone. Likewise the *existence* of a finite closed enabled region for a given network —
the canonical communicating-class characterization — remains the deeper outstanding dependency of
this ladder.

## Main results

* `invariant_smul` — scaling an invariant measure preserves kernel invariance.
* `invariant_normalize` — a finite nonzero invariant measure normalizes to an invariant probability
  measure.
* `restrictedStationaryMeasure_isFiniteMeasure` — the restricted stationary measure is finite over a
  finite region.
* `jumpKernel_normalized_isInvariant_probabilityMeasure` — the normalized restricted stationary
  measure is an invariant probability measure for the embedded jump kernel.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Stochastic.KernelIrreducible`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CRNT

variable {α : Type*} [MeasurableSpace α]

/-- **Scaling preserves invariance.** If `μ` is invariant under the kernel `κ`, so is `a • μ` for
any constant `a`, because `Measure.bind` is linear in the measure. -/
theorem invariant_smul {κ : Kernel α α} {μ : Measure α} (h : Kernel.Invariant κ μ) (a : ℝ≥0∞) :
    Kernel.Invariant κ (a • μ) := by
  unfold Kernel.Invariant at h ⊢
  rw [Measure.bind_smul, h]

/-- **Normalization to a probability measure.** A finite, nonzero invariant measure, divided by its
total mass, is an invariant probability measure. -/
theorem invariant_normalize {κ : Kernel α α} {μ : Measure α} (h : Kernel.Invariant κ μ)
    (hne : μ Set.univ ≠ 0) (hlt : μ Set.univ ≠ ∞) :
    Kernel.Invariant κ ((μ Set.univ)⁻¹ • μ) ∧ IsProbabilityMeasure ((μ Set.univ)⁻¹ • μ) := by
  refine ⟨invariant_smul h _, ⟨?_⟩⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hne hlt]

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- **Finiteness over a finite region.** The support-restricted stationary measure has finite total
mass when the region `T` is finite: its mass is the finite sum, over `T`, of the lifted stationary
weights, each of which is a finite `ENNReal`. -/
theorem restrictedStationaryMeasure_isFiniteMeasure (N : Network S) (κ : RateConstants N)
    (c : Concentration S) {T : Set (S → ℕ)} (hTfin : T.Finite) :
    IsFiniteMeasure (N.restrictedStationaryMeasure κ c T) := by
  refine ⟨?_⟩
  rw [restrictedStationaryMeasure, Measure.restrict_apply_univ, jumpStationaryMeasure,
    Measure.sum_apply _ (MeasurableSpace.measurableSet_top (s := T))]
  have hzero : ∀ n ∉ hTfin.toFinset,
      (ENNReal.ofReal (N.jumpStationaryMass κ c n) • Measure.dirac n) T = 0 := by
    intro n hn
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' n (MeasurableSpace.measurableSet_top (s := T)),
      Set.indicator_of_notMem (fun hT => hn (hTfin.mem_toFinset.mpr hT)), mul_zero]
  rw [tsum_eq_sum hzero]
  refine ENNReal.sum_lt_top.mpr (fun n _ => ?_)
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top (Measure.dirac n) T)

/-- **The normalized restricted stationary measure is an invariant probability measure.** Over a
finite closed enabled region `T` with positive total mass, normalizing the support-restricted
stationary measure by its mass produces a measure that is both invariant under the embedded jump
kernel and a probability measure — the stationary distribution of the embedded jump chain on `T`. -/
theorem jumpKernel_normalized_isInvariant_probabilityMeasure (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) (hTfin : T.Finite)
    (hpos : N.restrictedStationaryMeasure κ c T Set.univ ≠ 0) :
    Kernel.Invariant (N.jumpKernel κ)
        ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) ∧
      IsProbabilityMeasure
        ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) := by
  haveI hfin : IsFiniteMeasure (N.restrictedStationaryMeasure κ c T) :=
    N.restrictedStationaryMeasure_isFiniteMeasure κ c hTfin
  have hinv : Kernel.Invariant (N.jumpKernel κ) (N.restrictedStationaryMeasure κ c T) :=
    N.jumpKernel_invariant_restrictedStationaryMeasure κ c hc hcb T hT
  have hlt : N.restrictedStationaryMeasure κ c T Set.univ ≠ ∞ :=
    measure_ne_top (N.restrictedStationaryMeasure κ c T) Set.univ
  exact invariant_normalize hinv hpos hlt

end Network

end CRNT

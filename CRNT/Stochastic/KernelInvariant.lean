import CRNT.Stochastic.Kernel
import CRNT.Stochastic.JumpKernel
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Candidate stationary measure and bind-to-sum identity for the embedded jump chain

The embedded discrete-time jump chain of the chemical master equation is a genuine Markov
kernel `jumpKernel κ` on the species-count lattice `S → ℕ` (`CRNT.Stochastic.Kernel`). Its
real-arithmetic stationary weight is `jumpStationaryMass κ c = productPoissonPMF c · exitRate`
(`CRNT.Stochastic.JumpKernel`), the product-Poisson density reweighted by the holding rate at
a complex-balanced concentration. This module lifts that weight to a genuine measure on the
discrete count lattice and computes how it pushes forward under the kernel.

The candidate stationary measure is the `ℝ≥0∞`-density measure on the countable count lattice

`jumpStationaryMeasure κ c = Measure.sum (fun n => ofReal (jumpStationaryMass κ c n) • dirac n)`,

an explicit countable superposition of weighted point masses (equivalently the counting
measure with this density). Under the discrete `⊤` σ-algebra on `S → ℕ` every set is
measurable, every singleton is measurable, and every function out of the lattice is
measurable, so all measurability obligations are discharged by `measurable_from_top` /
`MeasurableSpace.measurableSet_top`.

The exported content is the *predecessor-indexed* `bind`-to-sum identity that the kernel
module names as its honest gap: the singleton weight `jumpStationaryMeasure_singleton`, the
pushforward of an arbitrary measurable set `jumpStationaryMeasure_bind_apply`,

`(μ.bind (jumpKernel κ)) s = ∑' n, ofReal (jumpStationaryMass κ c n) · jumpKernel κ n s`,

and the singleton specialization `jumpStationaryMeasure_bind_singleton` exposing the reaction
sum via `jumpKernel_apply'`. This is the bridge from the complex-indexed real-arithmetic
global balance to a measure-theoretic statement indexed by the *source* counts whose mass
flows into each target.

The honest ceiling is full `Kernel.Invariant (jumpKernel κ) (jumpStationaryMeasure κ c)`,
equivalently `μ.bind (jumpKernel κ) = μ`, which is **deliberately not stated as proved**: it
is not soundly reachable from the committed assets. Two independent obstructions remain.
First, an **index mismatch**: `jumpGlobalBalance_of_complexBalanced` is complex/reaction
indexed with a downward shift (inflow weighted by the density at the reaction target), whereas
invariance needs the predecessor tsum `∑' n, ofReal (jumpStationaryMass κ c n) · jumpKernel κ
n {m} = ofReal (jumpStationaryMass κ c m)` over all source counts `n` with `jumpNextCount n r
= m`, weighted by the ratio `jumpProb = stochasticRate / exitRate`; reindexing the lattice
tsum over the finite reaction fibers and cancelling the `exitRate` denominator is new
mathematics. Second, a **boundary / `Enabled` gap**: the global balance is gated by `∀ r,
Enabled n r`, and the `exitRate = 0` holding states are absorbing, so strict pointwise balance
fails on the boundary, which the product-Poisson support does not avoid. The single clean
theorem the downstream process-level Anderson–Craciun–Kurtz stationarity needs is exactly that
predecessor-summation lemma; combined with `jumpStationaryMeasure_bind_singleton` exported here
it yields `μ.bind (jumpKernel κ) = μ` by `Measure.ext` on singletons.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Stochastic.Kernel`,
`CRNT.Stochastic.JumpKernel`, `Mathlib.Probability.Kernel.Invariance`,
`Mathlib.MeasureTheory.Integral.Lebesgue.Countable`, `Mathlib.MeasureTheory.Measure.Dirac`.
-/

open MeasureTheory ProbabilityTheory

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

-- The discrete σ-algebra on the species-count lattice `S → ℕ`: every set is measurable.
-- Re-activated identically to `CRNT.Stochastic.Kernel` (whose instance is module-local) so
-- that `jumpKernel` and the point masses of this module resolve against the same
-- `MeasurableSpace` instance.
attribute [local instance] instMeasurableSpaceCount

/-- The candidate stationary measure of the embedded jump chain at a complex-balanced
concentration: the countable superposition of point masses on the count lattice weighted by
the jump-chain stationary mass `jumpStationaryMass κ c = productPoissonPMF c · exitRate`. This
is the `ℝ≥0∞`-density measure on the discrete lattice corresponding to the real-arithmetic
stationary weight. -/
noncomputable def jumpStationaryMeasure (N : Network S) (κ : RateConstants N)
    (c : Concentration S) : Measure (S → ℕ) :=
  Measure.sum (fun n => ENNReal.ofReal (N.jumpStationaryMass κ c n) • Measure.dirac n)

/-- The singleton mass of the candidate stationary measure is exactly the lifted stationary
weight at that count: the superposition collapses to its diagonal term because each Dirac
contributes to `{m}` only at its own atom. -/
theorem jumpStationaryMeasure_singleton (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (m : S → ℕ) :
    N.jumpStationaryMeasure κ c {m} = ENNReal.ofReal (N.jumpStationaryMass κ c m) := by
  rw [jumpStationaryMeasure,
    Measure.sum_apply _ (MeasurableSpace.measurableSet_top (s := ({m} : Set (S → ℕ))))]
  rw [tsum_eq_single m]
  · rw [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top (s := ({m} : Set (S → ℕ)))),
      Set.indicator_of_mem (Set.mem_singleton m), Pi.one_apply, mul_one]
  · intro n hn
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top (s := ({m} : Set (S → ℕ)))),
      Set.indicator_of_notMem (by simpa [eq_comm] using hn), mul_zero]

/-- The predecessor-indexed `bind`-to-sum identity for the candidate stationary measure: its
pushforward under the embedded jump kernel evaluates on every measurable set as the countable
sum, over source counts, of stationary weight times the kernel's per-set transition mass. This
is the final result of the embedded-chain kernel development — the bridge from the
complex-indexed real-arithmetic global balance to a source-indexed measure statement. -/
theorem jumpStationaryMeasure_bind_apply (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (s : Set (S → ℕ)) :
    (N.jumpStationaryMeasure κ c).bind (N.jumpKernel κ) s =
      ∑' n : S → ℕ, ENNReal.ofReal (N.jumpStationaryMass κ c n) * N.jumpKernel κ n s := by
  rw [Measure.bind_apply (MeasurableSpace.measurableSet_top (s := s))
        (N.jumpKernel κ).aemeasurable,
    jumpStationaryMeasure, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- The singleton specialization of the `bind`-to-sum identity, with each source count's
transition mass into `{m}` expanded via `jumpKernel_apply'` into the holding-Dirac indicator
on the boundary and the reaction-indexed jump-probability sum off the boundary. This is the
exact predecessor-tsum a stationarity proof must equate to
`ofReal (jumpStationaryMass κ c m)`. -/
theorem jumpStationaryMeasure_bind_singleton (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (m : S → ℕ) :
    (N.jumpStationaryMeasure κ c).bind (N.jumpKernel κ) {m} =
      ∑' n : S → ℕ, ENNReal.ofReal (N.jumpStationaryMass κ c n) *
        (if N.exitRate κ n = 0 then ({m} : Set (S → ℕ)).indicator 1 n
          else ∑ r : N.R,
            ENNReal.ofReal (N.jumpProb κ n r) *
              ({m} : Set (S → ℕ)).indicator 1 (N.jumpNextCount n r)) := by
  rw [jumpStationaryMeasure_bind_apply]
  refine tsum_congr fun n => ?_
  rw [N.jumpKernel_apply' κ n ({m} : Set (S → ℕ))]

end Network

end CRNT

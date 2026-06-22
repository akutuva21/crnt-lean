import CRNT.Stochastic.JumpKernel
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Measurable embedded-jump-chain kernel of the chemical master equation

The continuous-time Markov chain of stochastic mass-action kinetics on the species-count
lattice `ℕ^S` carries an embedded discrete-time *jump chain*: from a count `n` the next
reaction to fire is `r` with probability `jumpProb κ n r` (`CRNT.Stochastic.JumpKernel`),
landing on the post-firing count `jumpNextCount n r`. This module lifts that real-valued
jump chain to a genuine measure-theoretic `ProbabilityTheory.Kernel` on the count lattice.

The count lattice `S → ℕ` is equipped with its discrete `⊤` `MeasurableSpace`, under which
every set is measurable, every singleton is measurable (`MeasurableSingletonClass`), and
every function out of the lattice is measurable. The kernel is

`jumpKernel κ n = if exitRate κ n = 0 then dirac n
                 else ∑_r ENNReal.ofReal (jumpProb κ n r) • dirac (jumpNextCount n r)`,

with a *holding* (self-loop Dirac) convention at the absorbing/empty counts where the exit
rate vanishes — the genuine boundary of the embedded chain, where the real-valued jump row
is identically zero. The measurability obligation is discharged instantly by
`measurable_from_top` since the domain σ-algebra is `⊤`.

The load-bearing result is `instIsMarkovKernel_jumpKernel`: the kernel is a Markov kernel
*everywhere on the lattice*, including the boundary. On the positive-exit part each row mass
is `∑_r ENNReal.ofReal (jumpProb κ n r) = 1` via `sum_jumpProb_eq_one`; on the boundary the
holding Dirac is itself a probability measure. The total mass `jumpKernel_univ_eq_one`
records `(jumpKernel κ n) univ = 1`, and `jumpKernel_apply'` gives the explicit per-set mass.

The honest ceiling is full-lattice measure invariance `Kernel.Invariant (jumpKernel κ) μ`
(equivalently `μ.bind (jumpKernel κ) = μ`): it is **not** reachable from these assets and is
deliberately not stated as proved. The proved global balance
`jumpGlobalBalance_of_complexBalanced` is complex/reaction-indexed with a downward shift and
gated by an enabled-everywhere hypothesis, whereas measure invariance requires a
predecessor-indexed `bind`-to-sum identity over source counts landing on each target, plus a
σ-finiteness/`IsFiniteMeasure` proof for the reweighted ACK density `jumpStationaryMass`; the
exitRate = 0 holding states are absorbing, so strict invariance fails there unless the
support avoids the boundary. `Kernel.IsReversible` additionally needs network reversibility.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Stochastic.JumpKernel`,
`Mathlib.Probability.Kernel.Basic`, `Mathlib.Probability.Kernel.Invariance`,
`Mathlib.MeasureTheory.Measure.Dirac`.
-/

open MeasureTheory ProbabilityTheory

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The discrete σ-algebra on the species-count lattice `S → ℕ`: every set is measurable.
Local to this module so the kernel codomain has measurable singletons and computable Dirac
masses without imposing a global instance on the count lattice. -/
local instance instMeasurableSpaceCount : MeasurableSpace (S → ℕ) := ⊤

/-- The post-firing count: firing reaction `r` at the count `n` removes its source complex
and adds its target complex, species by species. This is the count the embedded jump chain
lands on when reaction `r` fires from `n`. -/
def jumpNextCount (N : Network S) (n : S → ℕ) (r : N.R) : S → ℕ :=
  fun s => n s - (N.reaction r).source s + (N.reaction r).target s

/-- The measurable embedded-jump-chain kernel on the count lattice. From a count `n` with
positive exit rate it sends mass `jumpProb κ n r` to each post-firing count
`jumpNextCount n r`; at an absorbing count with vanishing exit rate it holds (self-loop
Dirac). The measurability obligation is trivial under the discrete σ-algebra. -/
noncomputable def jumpKernel (N : Network S) (κ : RateConstants N) :
    Kernel (S → ℕ) (S → ℕ) where
  toFun n :=
    if N.exitRate κ n = 0 then Measure.dirac n
    else ∑ r : N.R, ENNReal.ofReal (N.jumpProb κ n r) • Measure.dirac (N.jumpNextCount n r)
  measurable' := measurable_from_top

/-- Unfolding of the kernel as a measure at a count `n`. -/
theorem jumpKernel_apply (N : Network S) (κ : RateConstants N) (n : S → ℕ) :
    N.jumpKernel κ n =
      (if N.exitRate κ n = 0 then Measure.dirac n
        else ∑ r : N.R, ENNReal.ofReal (N.jumpProb κ n r) • Measure.dirac (N.jumpNextCount n r)) :=
  rfl

/-- The explicit per-set mass of the kernel: every set is measurable under the discrete
σ-algebra, so the Dirac masses compute as indicators. On the boundary the holding Dirac
contributes `s.indicator 1 n`; off the boundary each reaction contributes
`ofReal (jumpProb κ n r) * s.indicator 1 (jumpNextCount n r)`. -/
theorem jumpKernel_apply' (N : Network S) (κ : RateConstants N) (n : S → ℕ) (s : Set (S → ℕ)) :
    N.jumpKernel κ n s =
      (if N.exitRate κ n = 0 then s.indicator 1 n
        else ∑ r : N.R,
          ENNReal.ofReal (N.jumpProb κ n r) * s.indicator 1 (N.jumpNextCount n r)) := by
  rw [jumpKernel_apply]
  by_cases h : N.exitRate κ n = 0
  · simp only [h, if_true]
    exact Measure.dirac_apply' n (MeasurableSpace.measurableSet_top (s := s))
  · simp only [h, if_false]
    rw [Measure.finsetSum_apply]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top (s := s))]

/-- The total mass of every row of the kernel is one: the kernel is row-stochastic
everywhere on the lattice. On the positive-exit part this is `∑_r jumpProb κ n r = 1` lifted
to `ℝ≥0∞`; on the boundary it is the unit mass of the holding Dirac. -/
theorem jumpKernel_univ_eq_one (N : Network S) (κ : RateConstants N) (n : S → ℕ) :
    N.jumpKernel κ n Set.univ = 1 := by
  rw [jumpKernel_apply']
  by_cases h : N.exitRate κ n = 0
  · simp [h]
  · simp only [h, if_false, Set.indicator_univ, Pi.one_apply, mul_one]
    have hpos : 0 < N.exitRate κ n := lt_of_le_of_ne (N.exitRate_nonneg κ n) (Ne.symm h)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => N.jumpProb_nonneg κ n r),
      N.sum_jumpProb_eq_one κ n hpos, ENNReal.ofReal_one]

/-- The embedded jump kernel is a genuine Markov kernel on the whole count lattice: every
row is a probability measure, via `jumpKernel_univ_eq_one`. This is the load-bearing
measure-theoretic content — a row-stochastic measurable kernel over `S → ℕ` ready for
Mathlib's `Kernel.Invariant`/`Kernel.IsReversible`/composition API. -/
instance instIsMarkovKernel_jumpKernel (N : Network S) (κ : RateConstants N) :
    IsMarkovKernel (N.jumpKernel κ) :=
  ⟨fun n => ⟨N.jumpKernel_univ_eq_one κ n⟩⟩

/-- The absorbing/boundary states are holding: at a count with vanishing exit rate the kernel
keeps all its mass on `{n}`, the honest boundary defect of the embedded chain at the
measure-theoretic level. -/
theorem jumpKernel_self_eq_one_of_exitRate_zero (N : Network S) (κ : RateConstants N)
    (n : S → ℕ) (h : N.exitRate κ n = 0) :
    N.jumpKernel κ n {n} = 1 := by
  rw [jumpKernel_apply', if_pos h, Set.indicator_of_mem (Set.mem_singleton n), Pi.one_apply]

/-- Measure-level reading of the kernel's per-set mass on the positive-exit part of the
lattice as a single finite sum over reactions of lifted jump probabilities, exposing the
link between the kernel's Dirac masses and the real-valued jump chain. Each measurable target
set `s` receives `∑_r ofReal (jumpProb κ n r)` restricted to the reactions whose post-firing
count lands in `s`. The honest gap above this rung is a *predecessor*-indexed
`bind`-to-sum identity matching the complex-indexed `jumpGlobalBalance_of_complexBalanced`. -/
theorem jumpKernel_apply_of_exitRate_pos (N : Network S) (κ : RateConstants N) (n : S → ℕ)
    (h : N.exitRate κ n ≠ 0) (s : Set (S → ℕ)) :
    N.jumpKernel κ n s =
      ∑ r : N.R, ENNReal.ofReal (N.jumpProb κ n r) * s.indicator 1 (N.jumpNextCount n r) := by
  rw [jumpKernel_apply', if_neg h]

end Network

end CRNT

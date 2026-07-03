import CRNT.Stochastic.CTMC

/-!
# Embedded discrete-time jump chain of the chemical master equation

The continuous-time Markov chain of stochastic mass-action kinetics on the species-count
lattice `ℕ^S` carries an embedded discrete-time *jump chain*: when the process leaves a
count `n`, the next reaction to fire is `r` with probability equal to that reaction's
propensity divided by the holding rate (exit rate) of `n`. This module renders that jump
chain at the elementary real-valued level of `CRNT.Stochastic.CTMC`'s generator, before any
measure-theoretic kernel layer.

The transition probability is `jumpProb κ n r = stochasticMassActionRate κ n r / exitRate κ n`.
On the positive-exit-rate part of the lattice these probabilities form a stochastic row,
`∑_r jumpProb κ n r = 1`, since the numerators sum to the exit rate by definition. The
honest boundary statement is that every `jumpProb κ n r` vanishes when `exitRate κ n = 0`:
such absorbing/empty counts have a sub-stochastic (identically-zero) row rather than a
stochastic one, the genuine boundary defect of the embedded chain.

The jump chain's stationary mass is `jumpStationaryMass c n = productPoissonPMF c n · exitRate κ n`
— the product-Poisson density reweighted by the holding rate, *not* the density itself. On
the fully-enabled part of the lattice this mass equals the complex-indexed total
generator-outflow sum (the holding-rate departure flux of `CRNT.Stochastic.CTMC`), and at a
complex-balanced concentration the generator stationarity `πQ = 0` upgrades this to global
balance for the embedded chain: total inflow equals total outflow equals the stationary
mass. This is the discrete-time invariance statement at the real-arithmetic level matching the
elementary generator; the measure-theoretic `Kernel.Invariant`/`Kernel.IsReversible` layer is
built on top of it in `CRNT.Stochastic.Kernel` and `CRNT.Stochastic.KernelInvariant`.

Depends on: `CRNT.Stochastic.CTMC`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The embedded jump-chain transition probability from the count `n`: the probability that
the next reaction to fire is `r`, namely that reaction's stochastic mass-action propensity
divided by the holding rate `exitRate κ n`. -/
noncomputable def jumpProb (N : Network S) (κ : RateConstants N) (n : S → ℕ) (r : N.R) :
    ℝ :=
  N.stochasticMassActionRate κ n r / N.exitRate κ n

/-- Every jump probability is nonnegative: a nonnegative propensity divided by the
nonnegative exit rate. -/
theorem jumpProb_nonneg (N : Network S) (κ : RateConstants N) (n : S → ℕ) (r : N.R) :
    0 ≤ N.jumpProb κ n r :=
  div_nonneg (N.stochasticMassActionRate_nonneg κ n r) (N.exitRate_nonneg κ n)

/-- At an absorbing/empty count where the exit rate vanishes, every jump probability is
zero: the row of the embedded kernel is identically zero (sub-stochastic), the boundary
defect of the jump chain. -/
theorem jumpProb_eq_zero_of_exitRate_zero (N : Network S) (κ : RateConstants N) (n : S → ℕ)
    (r : N.R) (h : N.exitRate κ n = 0) : N.jumpProb κ n r = 0 := by
  unfold jumpProb
  rw [h, div_zero]

/-- On the positive-exit-rate part of the lattice the jump chain is row-stochastic: the
transition probabilities out of `n` sum to one, because their numerators are exactly the
reaction-indexed propensities whose sum is the exit rate. -/
theorem sum_jumpProb_eq_one (N : Network S) (κ : RateConstants N) (n : S → ℕ)
    (h : 0 < N.exitRate κ n) : (∑ r : N.R, N.jumpProb κ n r) = 1 := by
  unfold jumpProb
  rw [← Finset.sum_div, ← exitRate]
  exact div_self h.ne'

/-- The stationary mass of the embedded jump chain: the product-Poisson density reweighted
by the holding rate. This is the invariant mass of the discrete-time chain corresponding to
the continuous-time stationary density `productPoissonPMF c`. -/
noncomputable def jumpStationaryMass (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (n : S → ℕ) : ℝ :=
  productPoissonPMF c n * N.exitRate κ n

/-- On the fully-enabled part of the lattice the jump-chain stationary mass equals the
complex-indexed total generator-outflow sum: the product-Poisson density times the exit rate
is the holding-rate departure flux, repackaged onto the jump layer from
`stochasticTotalOutflow_eq_generatorOutflow`. -/
theorem jumpStationaryMass_eq_generatorOutflowSum (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (n : S → ℕ) (hn : ∀ r, N.Enabled n r) :
    N.jumpStationaryMass κ c n = ∑ r : N.R, N.generatorOutflow κ c n r := by
  unfold jumpStationaryMass
  exact N.stochasticTotalOutflow_eq_generatorOutflow κ c n hn

/-- Global balance for the embedded jump chain at a complex-balanced concentration. On the
fully-enabled part of the lattice the total complex-indexed inflow equals the jump-chain
stationary mass, since generator stationarity `πQ = 0` forces total inflow to equal total
outflow and the latter is the stationary mass. This is the discrete-time invariance statement at
the elementary real-arithmetic level. -/
theorem jumpGlobalBalance_of_complexBalanced (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (n : S → ℕ) (hcb : N.IsComplexBalanced κ c)
    (hn : ∀ r, N.Enabled n r) :
    (∑ r : N.R, N.generatorInflow κ c n r) = N.jumpStationaryMass κ c n := by
  have hstat : N.cmeGenerator κ c n = 0 :=
    N.productPoisson_isGeneratorStationary_of_complexBalanced κ c hcb n
  rw [cmeGenerator, sub_eq_zero] at hstat
  rw [hstat, jumpStationaryMass_eq_generatorOutflowSum N κ c n hn]

end Network

end CRNT

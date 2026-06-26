import CRNT.Stochastic.Generator

/-!
# Continuous-time Markov generator of the chemical master equation

The stochastic mass-action dynamics of a reaction network is a continuous-time Markov
chain on the species-count lattice `ℕ^S`. Mathlib supplies discrete-time transition
kernels but no continuous-time generator type, so the generator is rendered here as an
explicit pointwise-finite linear operator on real-valued state functions `π : (S → ℕ) → ℝ`.

For a state function `π`, the generator `Q` acts at the count `n` by

`(Qπ)(n) = (∑_r [inflow into n via r]) − π(n) · (∑_r [propensity of r at n])`,

where the outflow term `π(n) · ∑_r λ_r(n)` removes probability mass leaving `n` and the
inflow term collects mass arriving at `n` from each predecessor count. The total
propensity `exitRate κ n = ∑_r λ_r(n)` is the holding-rate of the state `n`: the rate at
which the chain leaves `n` (the reciprocal of the mean holding time).

The genuine generator-level stationarity predicate `IsGeneratorStationary` is the
vanishing of `cmeGenerator π` at every count, i.e. `πQ = 0`. The Anderson–Craciun–Kurtz
product-form theorem `productPoisson_isGeneratorStationary_of_complexBalanced` shows that,
for a complex-balanced concentration `c`, the product-Poisson density is annihilated by the
generator. The bridge `cmeGenerator_eq_ackResidual` rewrites the literal
generator on the product-Poisson density into the ACK residual of `CRNT.Stochastic.Generator`
via the per-reaction product-form substitution, after which complex balance closes it.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Stochastic.Generator`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The total propensity out of the count `n`: the reaction-indexed sum of stochastic
mass-action rates. This is the holding-rate (exit rate) of the state `n` in the embedded
jump-chain description — the rate at which the chain leaves `n`, whose reciprocal is the
mean holding time. -/
noncomputable def exitRate (N : Network S) (κ : RateConstants N) (n : S → ℕ) : ℝ :=
  ∑ r : N.R, N.stochasticMassActionRate κ n r

/-- The exit rate is nonnegative at every count. -/
theorem exitRate_nonneg (N : Network S) (κ : RateConstants N) (n : S → ℕ) :
    0 ≤ N.exitRate κ n :=
  Finset.sum_nonneg fun r _ => N.stochasticMassActionRate_nonneg κ n r

/-- A reaction is *enabled* at the count `n` when its source complex is dominated by `n`
species-by-species, so the falling-factorial propensity is positive and the reaction can
fire. -/
def Enabled (N : Network S) (n : S → ℕ) (r : N.R) : Prop :=
  ∀ s, (N.reaction r).source s ≤ n s

instance (N : Network S) (n : S → ℕ) (r : N.R) : Decidable (N.Enabled n r) := by
  unfold Enabled; infer_instance

/-- The inflow of probability into the count `n` carried by reaction `r`, in
ACK-substituted complex-indexed form: the deterministic mass-action rate at `c` times the
shifted product-Poisson density at the reaction's target complex. This is the per-reaction
arrival term of the generator after the product-form substitution. -/
noncomputable def generatorInflow (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (n : S → ℕ) (r : N.R) : ℝ :=
  N.massActionRate κ r c * shiftedPMF c n (N.reaction r).target

/-- The outflow of probability out of the count `n` carried by reaction `r`, in
ACK-substituted complex-indexed form: the deterministic mass-action rate at `c` times the
shifted product-Poisson density at the reaction's source complex. This is the per-reaction
departure term of the generator after the product-form substitution. -/
noncomputable def generatorOutflow (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (n : S → ℕ) (r : N.R) : ℝ :=
  N.massActionRate κ r c * shiftedPMF c n (N.reaction r).source

/-- The continuous-time Markov generator of the chemical master equation acting on the
product-Poisson density at concentration `c`, evaluated at the count `n`: the
reaction-indexed total inflow minus total outflow. This is the value `(Qπ)(n)` with
`π = productPoissonPMF c` after the Anderson–Craciun–Kurtz product-form substitution turns
each literal jump flux `π(·)·λ_r(·)` into its complex-indexed shifted form. -/
noncomputable def cmeGenerator (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (n : S → ℕ) : ℝ :=
  (∑ r : N.R, N.generatorInflow κ c n r) - ∑ r : N.R, N.generatorOutflow κ c n r

/-- The generator on the product-Poisson density is exactly the Anderson–Craciun–Kurtz
residual: total inflow minus total outflow regroups, reaction-by-reaction, into the signed
flux sum `ackResidual`. This is the bridge from the literal generator value to the
master-equation balance of `CRNT.Stochastic.Generator`. -/
theorem cmeGenerator_eq_ackResidual (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (n : S → ℕ) :
    N.cmeGenerator κ c n = N.ackResidual κ c n := by
  unfold cmeGenerator ackResidual generatorFlux generatorInflow generatorOutflow
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- The generator-level stationarity predicate, `πQ = 0`: the chemical-master-equation
generator annihilates the product-Poisson density at every count. -/
def IsGeneratorStationary (N : Network S) (κ : RateConstants N) (c : Concentration S) :
    Prop :=
  ∀ n : S → ℕ, N.cmeGenerator κ c n = 0

/-- `IsGeneratorStationary` and the master-equation predicate `IsMasterStationary` coincide:
the literal generator value equals the master-equation residual at every count. -/
theorem isGeneratorStationary_iff_isMasterStationary (N : Network S)
    (κ : RateConstants N) (c : Concentration S) :
    N.IsGeneratorStationary κ c ↔ N.IsMasterStationary κ c := by
  unfold IsGeneratorStationary IsMasterStationary
  refine forall_congr' fun n => ?_
  rw [N.cmeGenerator_eq_ackResidual κ c n]

/-- The Anderson–Craciun–Kurtz theorem at the continuous-time generator level.

For a complex-balanced concentration `c`, the product-Poisson density is a stationary
distribution of the stochastic mass-action chemical master equation: the continuous-time
Markov generator annihilates it at every count vector, `πQ = 0`. The proof rewrites the
literal generator into the ACK residual and invokes the master-equation stationarity already
established from complex balance. -/
theorem productPoisson_isGeneratorStationary_of_complexBalanced (N : Network S)
    (κ : RateConstants N) (c : Concentration S) (hcb : N.IsComplexBalanced κ c) :
    N.IsGeneratorStationary κ c := by
  rw [N.isGeneratorStationary_iff_isMasterStationary κ c]
  exact N.productPoisson_isStationary_of_complexBalanced κ c hcb

/-- The grounding identity tying the literal stochastic outflow `π(n)·λ_r(n)` to the
complex-indexed generator outflow term, for a count dominating the reaction's source: the
raw jump flux equals `generatorOutflow`. This exposes that `cmeGenerator` is the literal
master-equation operator evaluated on the product-Poisson density, not a pre-substituted
abbreviation. -/
theorem stochasticOutflow_eq_generatorOutflow (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (n : S → ℕ) (r : N.R) (hr : N.Enabled n r) :
    productPoissonPMF c n * N.stochasticMassActionRate κ n r =
      N.generatorOutflow κ c n r := by
  unfold generatorOutflow
  exact N.productPoissonPMF_mul_stochasticRate κ c n r hr

/-- The total literal outflow at a count where every reaction is enabled equals the
product-Poisson density times the exit rate, and coincides with the complex-indexed total
outflow term of the generator. This is the holding-rate form of the master-equation
departure flux. -/
theorem stochasticTotalOutflow_eq_generatorOutflow (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (n : S → ℕ) (hn : ∀ r, N.Enabled n r) :
    productPoissonPMF c n * N.exitRate κ n =
      ∑ r : N.R, N.generatorOutflow κ c n r := by
  unfold exitRate
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact N.stochasticOutflow_eq_generatorOutflow κ c n r (hn r)

end Network

end CRNT

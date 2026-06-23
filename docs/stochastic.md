# Stochastic CRN

This document describes the discrete-molecule regime of the `CRNT` library: the
chemical master equation of stochastic mass-action kinetics and the Anderson–Craciun–Kurtz
product-form stationary distribution for complex-balanced networks. It is one of the
per-area documents linked from [`architecture.md`](architecture.md).

When molecule counts are small, concentrations are not a faithful description: the state is
a vector of nonnegative integer counts, one per species, and each reaction firing is a
discrete jump that shifts the count by the reaction's net stoichiometry. The state space is
the count lattice `ℕ^S`, modelled here as `S → ℕ`. The dynamics is a continuous-time Markov
chain: reaction `r` fires from a count `n` at the *stochastic mass-action propensity*
`κ r · ∏ s (n s)^{(source r s)}`, the falling-factorial counting law, the combinatorial
analogue of the deterministic monomial. The evolution of the law of the chain is the
**chemical master equation** `π̇ = πQ`, with generator `Q` assembling the inflow into and
outflow out of each count.

The headline result is that for a **complex-balanced** network the stationary law is a
product of independent Poissons, one per species, with rate the complex-balanced equilibrium
concentration `c`. This is the discrete-state counterpart of the deterministic
deficiency-zero theory: complex balancing is the same notion `IsComplexBalanced`
(`CRNT.Equilibria.ComplexBalanced`) that controls the deterministic equilibria (see
[`deficiency.md`](deficiency.md)), and the equilibrium concentration that solves
`A_k(Ψ x) = 0` is exactly the Poisson parameter here. The literature is Anderson, Craciun &
Kurtz, *Product-form stationary distributions for deficiency zero chemical reaction
networks* (2010).

The development is built bottom-up: the product-Poisson density and its algebra, the
master-equation generator and generator-level stationarity, the embedded discrete-time jump
kernel and its measure invariance, and the restriction of that invariant measure to a closed
communicating region. Every result below is machine-checked, `sorry`-free, and axiom-clean.

## The product-form density

`CRNT/Stochastic/ProductForm.lean` supplies the measure-theoretic candidate and the
algebraic identity at the heart of the theorem.

- **`productPoisson c hc`**: the product-of-Poissons measure on `S → ℕ`, the `Measure.pi` of
  one Poisson factor per species, with rate `c s`. It is a probability measure
  (`IsProbabilityMeasure` instance).
- **`productPoissonPMF c n`**: the explicit density `∏ s, exp(-(c s))·(c s)^(n s)/(n s)!`.
  `productPoissonPMF_nonneg` records nonnegativity; `productPoisson_singleton` identifies the
  measure of a single count vector `{n}` with `ENNReal.ofReal (productPoissonPMF c n)`.
- **`stochasticMassActionRate κ n r`**: the stochastic propensity of reaction `r` at count
  `n`, the rate constant times the falling-factorial counting law `∏ s (n s)^{(source r s)}`
  (via `Nat.descFactorial`). `stochasticMassActionRate_nonneg` gives nonnegativity.

The load-bearing algebra is the **product-form identity**. Per species,
`poissonFactor_mul_descFactorial` proves
`(exp(-c)·c^m/m!) · m^{(k)} = c^k · (exp(-c)·c^{m-k}/(m-k)!)` for `k ≤ m`. Taking the product
over all species, **`productPoissonPMF_mul_descFactorial`** gives, for a count `n` dominating
the source complex of `r`,

```
productPoissonPMF c n · ∏ s (n s)^{(source r s)}
  = (∏ s (c s)^{source r s}) · productPoissonPMF c (n − source r).
```

This is `π(n)·n^{(k)} = c^k·π(n − k)`: multiplying the density by a falling-factorial
propensity reproduces the density at the shifted count weighted by a power of the rate. It
is the exact content that lets the stochastic flux balance reduce to the deterministic
complex-balance equation.

## The CME generator and generator-level ACK stationarity

Mathlib has no continuous-time Markov generator type, so the generator is rendered as an
explicit pointwise-finite algebraic operator on real-valued state functions over `ℕ^S`. This
is done in two layers.

`CRNT/Stochastic/Generator.lean` works at the global-balance level. For a complex-balanced
concentration `c`, the per-reaction product-form substitution turns each literal jump flux
into the complex-indexed quantity `massActionRate κ r c · (π(n − target r) − π(n − source r))`,
where `shiftedPMF c n y = productPoissonPMF c (n − y)`. Their reaction-indexed sum is the
**`ackResidual`**, and **`IsMasterStationary`** is its vanishing at every count (the global
balance `πQ = 0`, i.e. `∑ inflow = ∑ outflow` at each `n`).

- **`sum_target_flux_eq_inflow`** / **`sum_source_flux_eq_outflow`** regroup the
  reaction-indexed inflow and outflow sums over the finite set of complexes, producing the
  complex-indexed `inflow`/`outflow` of the network.
- **`productPoisson_isStationary_of_complexBalanced`**: the Anderson–Craciun–Kurtz theorem
  at the master-equation level: for `c` complex-balanced (`IsComplexBalanced`), `ackResidual`
  vanishes at every count. The proof regroups inflow and outflow by complex and collapses the
  balance termwise via complex balance `inflow = outflow` at each complex.
  `ackResidual_eq_zero_of_complexBalanced` is the pointwise restatement.
- **`productPoissonPMF_mul_stochasticRate`** is the grounding bridge: for a count dominating
  the source complex, the raw outflow flux `π(n)·λ_r(n)` equals the complex-indexed
  `massActionRate κ r c · π(n − source r)`.

`CRNT/Stochastic/CTMC.lean` exhibits the literal generator. **`cmeGenerator κ c n`** is
`(∑_r inflow) − (∑_r outflow)` in the complex-indexed `generatorInflow`/`generatorOutflow`
form, the value `(Qπ)(n)` with `π = productPoissonPMF c`. The exit/holding rate of a state,
**`exitRate κ n = ∑_r stochasticMassActionRate κ n r`** (nonnegative by `exitRate_nonneg`),
is the rate at which the chain leaves `n`. A reaction is **`Enabled`** at `n` when `n`
dominates its source complex (decidable instance provided).

- **`cmeGenerator_eq_ackResidual`** rewrites the literal generator into the master-equation
  residual reaction-by-reaction, and **`isGeneratorStationary_iff_isMasterStationary`** shows
  the two stationarity predicates coincide.
- **`productPoisson_isGeneratorStationary_of_complexBalanced`** is ACK at the generator
  level: for `c` complex-balanced, **`IsGeneratorStationary`** holds: the generator
  annihilates the product-Poisson density at every count, `πQ = 0`.
- **`stochasticTotalOutflow_eq_generatorOutflow`** identifies the holding-rate departure flux
  `π(n)·exitRate κ n` with the total complex-indexed outflow on the fully-enabled part of the
  lattice.

## The jump kernel and `Kernel.Invariant`

The continuous-time chain carries an embedded discrete-time **jump chain**: when the process
leaves a count `n`, the next reaction to fire is `r` with probability proportional to its
propensity. This is rendered first at the real-arithmetic level, then lifted to a Mathlib
`ProbabilityTheory.Kernel`.

`CRNT/Stochastic/JumpKernel.lean` is the real-valued layer. The transition probability is
**`jumpProb κ n r = stochasticMassActionRate κ n r / exitRate κ n`** (`jumpProb_nonneg`). On
the positive-exit part of the lattice the row is stochastic, `sum_jumpProb_eq_one`; at an
absorbing count where `exitRate κ n = 0` every `jumpProb` is zero
(`jumpProb_eq_zero_of_exitRate_zero`), the genuine boundary defect. The jump chain's
stationary weight is **`jumpStationaryMass κ c n = productPoissonPMF c n · exitRate κ n`**,
the product-Poisson density reweighted by the holding rate. `jumpGlobalBalance_of_complexBalanced`
is the embedded global balance: on the fully-enabled part, generator stationarity forces the
total complex-indexed inflow to equal this stationary mass.

`CRNT/Stochastic/Kernel.lean` lifts the jump chain to a measure-theoretic kernel. The count
lattice is given the discrete `⊤` `MeasurableSpace` (a module-local instance
`instMeasurableSpaceCount`), under which every set, singleton, and function out of the
lattice is measurable, discharging all measurability obligations. The post-firing count is
**`jumpNextCount n r = n − source r + target r`**, and the kernel is

```
jumpKernel κ n = if exitRate κ n = 0 then dirac n
                 else ∑_r ofReal (jumpProb κ n r) • dirac (jumpNextCount n r),
```

holding (self-loop Dirac) at absorbing counts. **`instIsMarkovKernel_jumpKernel`** proves it
is a Markov kernel everywhere on the lattice (`jumpKernel_univ_eq_one`), and `jumpKernel_apply'`
gives the explicit per-set mass.

`CRNT/Stochastic/KernelInvariant.lean` builds the candidate stationary measure
**`jumpStationaryMeasure κ c = Measure.sum (fun n => ofReal (jumpStationaryMass κ c n) • dirac n)`**,
the `ℝ≥0∞`-density measure on the countable lattice. Its singleton mass is
`jumpStationaryMeasure_singleton`, and `jumpStationaryMeasure_bind_apply` computes the
pushforward `μ.bind (jumpKernel κ)` on any set as the predecessor-indexed tsum
`∑' n, ofReal (jumpStationaryMass κ c n) · jumpKernel κ n s`.

`CRNT/Stochastic/KernelStationary.lean` closes this into genuine measure invariance. The
unique source-dominating **`predecessorCount r m = m + source r − target r`** is the only
count that fires `r` to land on `m` while dominating the source; every other count landing on
`m` has vanishing propensity. The key cancellation
`jumpStationaryMass_mul_jumpProb_eq_generatorOutflow` removes the holding-rate denominator,
and **`predecessor_sum_eq`** proves the predecessor summation
`∑' n, ofReal (jumpStationaryMass κ c n) · jumpKernel κ n {m} = ofReal (jumpStationaryMass κ c m)`.
This yields **`jumpKernel_invariant_jumpStationaryMeasure`**:
`Kernel.Invariant (jumpKernel κ) (jumpStationaryMeasure κ c)` for `c` complex-balanced, under
explicit **no-boundary** hypotheses: every count has positive exit rate (`hexit`) and
dominates every reaction's target complex (`htarget`, `henabled`). These are needed because
the `exitRate = 0` holding states are absorbing, where strict pointwise balance fails.

## The closed-enabled-region restriction

The global no-boundary hypotheses fail on the genuine lattice: small counts are absorbing or
under-resource a reaction. `CRNT/Stochastic/KernelIrreducible.lean` removes them by
restricting the invariant measure to a self-contained region.

A **`ClosedEnabledRegion κ T`** is a set of counts that is closed and boundary-free for the
jump chain: no member is absorbing (`exit_ne`), every member is `Enabled` for and dominates
every reaction (`enabled`, `target_le`), and both the post-firing count (`forward`) and the
source-dominating predecessor (`backward`) of any member stay in `T`. These are the
membership-gated readings of the global hypotheses; `closedEnabledRegion_univ` recovers them
at `T = Set.univ`, so the structure is a strict weakening.

The exported result is **unconditional** support-restricted invariance,
**`jumpKernel_invariant_restrictedStationaryMeasure`**:
`Kernel.Invariant (jumpKernel κ) ((jumpStationaryMeasure κ c).restrict T)` for any closed
enabled region `T` at a complex-balanced concentration, with no global `hexit`/`htarget`. The
two measures agree on singletons: equal to the lifted stationary weight inside `T`
(`restricted_predecessor_sum_eq`) and zero outside it (`restricted_predecessor_sum_eq_zero`,
since closure admits no inbound mass).

`CRNT/Stochastic/KernelMaximalRegion.lean` makes the region canonical. The family of closed
enabled regions is closed under arbitrary union (`sUnion_closedEnabledRegion`), so the union
of all of them, **`maximalClosedEnabledRegion`**, is itself a closed enabled region
(`closedEnabledRegion_maximal`) containing every other (`subset_maximalClosedEnabledRegion`).
**`jumpKernel_invariant_maximalRegion`** carries the invariant measure on this canonical
region with no region supplied by hand.

`CRNT/Stochastic/KernelNormalized.lean` normalizes to a probability measure. Scaling an
invariant measure preserves invariance (`invariant_smul`), so a finite nonzero invariant
measure divided by its total mass is an invariant probability measure (`invariant_normalize`).
The restricted stationary measure is finite over a finite region
(`restrictedStationaryMeasure_isFiniteMeasure`), so
**`jumpKernel_normalized_isInvariant_probabilityMeasure`** delivers, for a finite closed
enabled region of positive mass, a measure that is both `Kernel.Invariant` under the jump
kernel and an `IsProbabilityMeasure`, the stationary distribution of the embedded jump chain
on the region.

## What is not here

The coverage is deliberately bounded, and the following are simply not part of the current
library:

- **No continuous-time process layer.** Mathlib has no continuous-time Markov generator or
  semigroup type, so the generator is an explicit pointwise-finite operator and the
  probabilistic kernel content lives in the *embedded discrete-time jump chain*, not a
  continuous-time semigroup or a path-space process. The statement "the semigroup
  `e^{tQ}` preserves the law" is not phrased.
- **No Kurtz scaling limits.** The relation between the stochastic chain and the
  deterministic mass-action ODE in the large-volume limit (Kurtz, scaling limits) is not
  formalized.
- **Unconditional invariance on the full lattice** is not proved. Measure invariance
  (`jumpKernel_invariant_jumpStationaryMeasure`) requires global no-boundary hypotheses,
  because absorbing low-count states break strict pointwise balance. Removing them is done
  only by restricting to a closed enabled region; pinning the maximal closed enabled region
  down to a concrete count set for a given network, the communicating-class characterization,
  is not part of the library, and the positive-total-mass condition (`hpos`) feeding
  normalization stays a hypothesis. `Kernel.IsReversible` (which also needs network
  reversibility) is not established.

# Kinetics and dynamics

This document describes the second layer of the `CRNT` library: the passage from the discrete
reaction-network structure of [`foundations.md`](foundations.md) to continuous dynamics. A
network plus a rate law gives a vector field `ẋ = f(x)`; this layer builds that field, factors it
through the complex space, packages its solutions as a forward semiflow, and studies the
asymptotics of that semiflow: Lyapunov descent, LaSalle invariance, local asymptotic stability,
time-scale separation, and the stability of linearizations.

Where this sits: the rate-law abstraction and mass-action field are the inputs to everything
downstream. The equilibrium-existence and deficiency theory (Birch, complex balancing, the
deficiency-zero and deficiency-one theorems) lives in [`deficiency.md`](deficiency.md); the
global-attractor / persistence theory (siphons, the global attractor conjecture) lives in
[`persistence-gac.md`](persistence-gac.md). The overall picture and theorem dependency graph are
in [`architecture.md`](architecture.md).

As everywhere in the library, every result below is machine-checked, `sorry`-free, and clean of
axioms beyond Mathlib's.

## Kinetics: the rate-law abstraction

A **concentration** (`CRNT.Concentration S = S → ℝ`) assigns a real number to each species, with
predicates `Concentration.Nonnegative` and `Concentration.Positive`. The concentration-dependent
part of a rate is the **mass-action monomial** `Complex.massActionMonomial y x = ∏ s, (x s) ^ (y s)`,
nonnegative on the nonnegative orthant (`massActionMonomial_nonneg`) and positive on the positive
orthant (`massActionMonomial_pos`).

### Mass action

`Network.RateConstants N` is a choice of strictly positive rate constant per reaction. The
**mass-action rate** of reaction `r` is `massActionRate κ r x = κ.k r * (source r).massActionMonomial x`,
nonnegative at nonnegative concentrations (`massActionRate_nonneg`), strictly positive at positive
ones (`massActionRate_pos`). The **mass-action vector field**

```text
massActionVectorField κ x s = ∑ r, massActionRate κ r x * reactionVector r s
```

is the right-hand side of the induced polynomial ODE. This is the bridge from discrete CRN
structure to continuous dynamics.

### The general `Kinetics` abstraction

`Network.Kinetics N` makes the rate law a parameter. It bundles a map
`rate : N.R → Concentration S → ℝ` together with Feinberg's admissibility hypotheses:

- `rate_nonneg`: nonnegativity at nonnegative concentrations;
- `rate_vanishing`: the rate vanishes when a species required by the source complex is absent;
- `rate_supportDep`: the rate depends only on the concentrations of the source species;
- `rate_mono`: weak monotonicity, each rate is nondecreasing in the species concentrations on the
  nonnegative orthant.

A kinetics induces `Kinetics.vectorField K x s = ∑ r, K.rate r x * reactionVector r s`, the
right-hand side of `ẋ = f(x)`. Two structural facts about it are **kinetics-agnostic**: they hold
for every admissible kinetics, not just mass action:

- `Kinetics.vectorField_nonneg_of_zero`, **boundary non-attraction**: at a nonnegative
  concentration with `x_s = 0` the `s`-component of the field is `≥ 0` (any reaction that would
  decrease `x_s` consumes `s`, so its rate vanishes there). The orthant face `{x_s = 0}` is
  non-attracting.
- `Kinetics.vectorField_mem_stoichSubspace`, **conservation**: the field always lies in the
  stoichiometric subspace, so every solution stays in the compatibility class of its initial
  condition.

A concentration is a steady state when the field vanishes componentwise (`IsKineticSteadyState`).

Mass action is recovered as the instance `Network.massActionKinetics κ`: its four admissibility
proofs are exactly the mass-action lemmas, and its induced field is the mass-action field
*definitionally* (`massActionKinetics_vectorField : (massActionKinetics κ).vectorField = massActionVectorField κ`).
Mass-action steady states are exactly its kinetic steady states (`isMassActionSteadyState_iff_kinetic`).

### Generalized mass action

Müller–Regensburger generalized mass-action kinetics separates two subspaces of `ι → ℝ`: the
**stoichiometric** subspace `S` and the **kinetic-order** subspace `T`. A positive `x` is a
generalized equilibrium relative to a positive reference when `x − c ∈ S` and the log-ratio
`log(x/x*)` lies in `orthSum T`. The Müller–Regensburger **sign condition** `SignCompatible S T`
(via `SameSign`) is the hypothesis under which such equilibria are unique:

- `gen_birch_uniqueness`: under `SignCompatible S (orthSum T)`, two positive vectors in the same
  `S`-coset with log-ratio orthogonal to `T` are equal;
- `signCompatible_self`: `SignCompatible S (orthSum S)` holds unconditionally, the bridge showing
  the framework subsumes the classical case;
- `birch_uniqueness_of_self`: the `T = S` specialization, recovering classical complex-balanced
  uniqueness;
- `gen_birch_existence`: the single-subspace specialization of generalized existence.

(The genuinely two-subspace existence, `S ≠ T`, is beyond this module's scope.)

## The complex-space factorization

The mass-action field factors through the finite-dimensional **complex space** indexed by
`Network.ComplexIdx` (the vertices of the reaction graph). Writing `Y` for the complex matrix
(`complexMap`), `A_k` for the kinetic Laplacian (`kineticMap`), and `Ψ` for the monomial map
(`complexMonomialVector`), the induced ODE is the standard Feinberg–Horn–Jackson factorization

```text
ẋ = Y (A_k (Ψ x))            massActionVectorField_eq
```

- `complexMap` (`Y`) is the linear map `v ↦ (s ↦ ∑_c v_c · c_s)` combining complexes with given
  coefficients.
- `kineticMap` (`A_k`) is the kinetic Laplacian: at each complex it is inflow minus outflow, each
  reaction contributing its rate constant times the value at its source. Its columns sum to zero
  (`kineticMap_sum_eq_zero`), the Laplacian property that the Perron–Frobenius / Matrix-Tree
  argument later builds on to produce a positive kernel vector for weakly reversible networks.
- `complexMonomialVector` (`Ψ`) sends `x` to the vector of complex monomials.

Consequences:

- `isComplexBalanced_iff_kineticMap`: a concentration is complex-balanced **iff** `A_k(Ψ x) = 0`;
- `IsComplexBalanced.isMassActionSteadyState`: every complex-balanced concentration is a steady
  state (complex balancing kills `A_k`, and `Y` sends `0` to `0`).

## Regularity and the forward semiflow `Flow ℝ≥0`

Before any flow can be built, the field must be regular and the orthant must be non-attracting:

- `massActionVectorField_contDiff`: the field is `C^∞` (it is a polynomial map), the regularity
  hypothesis of Picard–Lindelöf;
- `massActionVectorField_nonneg_of_zero`: the mass-action specialization of boundary
  non-attraction;
- `exists_local_solution`: local existence of solutions through every starting point.

The general (chemistry-free) ODE-to-flow construction lives in the `ODE` namespace and is written
Mathlib-style for upstreaming:

- `ODE.dist_le_of_isIntegralCurve`, **continuous dependence**: two global solutions of the same
  autonomous Lipschitz ODE diverge at most exponentially in forward time (Grönwall);
- `ODE.eqOn_Ici_of_isIntegralCurve`, **uniqueness on `[0, ∞)`**: a solution is determined on
  forward time by its initial value;
- `ODE.exists_isIntegralCurve`, **global existence** for a *bounded* Lipschitz field: because the
  field is globally bounded, the Picard–Lindelöf radius can be taken arbitrarily large, giving a
  solution on `[−T, T]` for every `T`; interval solutions are glued by uniqueness (the step the
  Mathlib ODE library otherwise lacks);
- `ODE.exists_flow`, **the flow**: a bounded Lipschitz autonomous field generates a forward
  semiflow `Flow ℝ≥0 E` whose orbits are its solutions. Existence supplies the orbits, uniqueness
  the semigroup law, continuous dependence the joint continuity.

A forward semiflow is exactly `Flow ℝ≥0` (the `Flow` structure only requires the time monoid to be
an additive monoid). Mass-action dynamics is genuinely *forward only*: solutions stay positive and
are confined forward, but the backward flow can leave the orthant in finite time, so there is no
two-sided `Flow ℝ`.

### Monotone / order-preserving flows

The order-preserving fragment of monotone dynamical systems (Hirsch, Smith; Angeli–Sontag for the
I/O variant):

- `Monotone.IsMonotoneFlow`: a forward semiflow each of whose time-`t` maps is order preserving,
  with `IsMonotoneFlow.le` (orbits from ordered points stay ordered forward) and
  `IsMonotoneFlow.forwardInvariant_Icc` (an order interval bracketed by two equilibria is forward
  invariant); `isMonotoneFlow_id` witnesses non-vacuity;
- `Monotone.scalar_comparison` and `Monotone.traj_le`, the one-dimensional differential-inequality
  engine: if `u 0 ≤ v 0` and `u`'s right derivative is dominated by `v`'s, then `u ≤ v`.

The vector Kamke–Müller comparison principle and the full Angeli–Sontag input/output theory are not
formalized (Mathlib lacks cooperative-field flows and quasimonotone vector ODE comparison).

## The relative-entropy Lyapunov function and local asymptotic stability

The strict Lyapunov function is the Horn–Jackson relative entropy (pseudo-Helmholtz free energy)

```text
relEntropy x* x = ∑ i, (x_i · log(x_i / x*_i) − x_i + x*_i)
```

with `relEntropy_nonneg` (Gibbs' inequality), `relEntropy_eq_zero_iff` (vanishes exactly at `x*`),
and `relEntropy_pos_of_ne` (strictly positive away from `x*`).

**Dissipation.** Pairing the field against the log-ratio gives the dissipation rate, which is
nonpositive and vanishes exactly at complex balancing:

- `dissipation_nonpos`: relative to a complex-balanced positive reference, the dissipation
  `∑_s (log(x_s) − log(x*_s)) · f_s(x) ≤ 0`;
- `complexBalanced_of_dissipation_eq_zero`: vanishing dissipation in a positive class forces
  complex balancing;
- `dissipation_eq_zero_of_complexBalanced`: and conversely.

**Descent along solutions.** Via the chain rule `relEntropy_hasDerivAt`
(`d/dt relEntropy x* (γ t) = ∑_s (log γ_s − log x*_s) γ'_s`):

- `relEntropy_antitone_along_solution`: along any positive solution of `ẋ = f(x)`, relative to a
  complex-balanced reference, `t ↦ relEntropy x* (γ t)` is nonincreasing.

This descent statement needs no flow: it holds for any differentiable positive solution.

**LaSalle's invariance principle** (general, chemistry-free, Mathlib-style):

- `Flow.laSalle`: for a forward semiflow `ϕ` and continuous `V` that is nonincreasing along the
  forward orbit of `x` and whose orbit is eventually absorbed by a compact set, the ω-limit set
  `ω(x)` is nonempty, invariant, and `V` is **constant** on it.

**Local asymptotic stability** assembles these. Because Mathlib's flow theory needs a globally
bounded Lipschitz field, the genuine field is replaced by its bounded-Lipschitz cutoff
(`clampBox`, `exists_cutoff`); confinement and positivity of the cutoff orbit, compactness and
positive-confinement of relative-entropy sublevel sets, and a field lower bound (`exists_cutoff`,
`orbit_pos`, `orbit_relEntropy_le`, `isCompact_relEntropy_sublevel`, `positive_of_relEntropy_lt`,
`sub_mem_stoichSubspace_of_solution`, `exists_field_lower_bound`) feed into:

- `omegaLimit_eq_singleton_of_local`: for a weakly reversible network with complex-balanced
  positive equilibrium `x*`, starting from a positive `x₀` in the same compatibility class and
  sufficiently close to `x*` (the relative-entropy locality bound `relEntropy x* x₀ < x*_s` for all
  `s`), the mass-action semiflow has `ω(x₀) = {x*}`.

LaSalle forces the relative entropy constant on `ω(x₀)`, so the dissipation vanishes there, forcing
each ω-point complex-balanced, hence equal to `x*` by the deficiency-zero uniqueness of the
complex-balanced equilibrium in a positive class. That uniqueness input is the Birch / deficiency
material documented in [`deficiency.md`](deficiency.md).

## Time-scale separation and Michaelis–Menten

This is the quasi-steady-state / singular-perturbation development. It is honest about its ceiling:
the error estimates are **compact-time** and the small parameter `ε` is *not* fully quantified:
the slaving defect is supplied as a hypothesis (or derived as a slow-drift magnitude), and the
Grönwall bounds diverge as the horizon `T → ∞`. There is no infinite-horizon shadowing.

**Compact-time QSSA error bound** (Tikhonov-style, chemistry-free, in `ODE`). The
`ODE.qssaDefect f γᵣ γᵣ' a b εf` predicate is the slaving defect: the reduced curve satisfies the
full field up to a residual `εf`.

- `ODE.qssa_error_bound`: the exact-versus-reduced gap is bounded by `gronwallBound δ K εf (t − a)`
  on `[a, b]` (initial mismatch `δ`, defect `εf`);
- `ODE.qssa_exact_of_zero_defect`: zero defect and zero mismatch recover exact coincidence;
- `ODE.qssa_error_tendsto_zero`: on a fixed horizon `[0, T]` the bound is monotone, and
  `gronwallBound δ K εf T → 0` as `(δ, εf) → (0, 0)`: the reduced trajectory converges uniformly to
  the exact one on compact time as the mismatch and defect vanish.

**Boundary-layer attraction** (the fast side, supplying the defect as a derived quantity).
`ODE.OneSidedContraction f zstar lam` is the dissipativity condition for a contracting fast fibre.

- `ODE.norm_sub_le_exp_neg_mul`: an integral curve of a one-sided-contracting field decays to its
  equilibrium at the explicit rate `‖z t − zstar‖ ≤ ‖z 0 − zstar‖ · exp(−lam·t)`;
- `ODE.norm_sub_tendsto_zero`: for `lam > 0` the layer collapses onto the fast equilibrium;
- `ODE.FastSubsystem` bundles a fast field, its equilibrium, and a positive rate, with
  `FastSubsystem.attraction_bound` / `tendsto_equil` re-exporting the estimate;
- `ODE.qssaDefect_of_fastSubsystem`: for a full field `fast + slow`, the constant reduced curve at
  the fast equilibrium has slaving defect exactly the slow-drift magnitude, composable with
  `qssa_error_tendsto_zero`.

**Fenichel slow manifold (reachable rung).** `ODE.SlowManifold` lifts the flat fibre to a
slow-variable-dependent fast equilibrium `z = h y`, the graph of a manifold map. The three defining
geometric properties are proved:

- `SlowManifold.attraction_bound` / `tendsto_fiber`: per-fibre exponential attraction;
- `SlowManifold.eq_of_stationary` / `fiber_eq_singleton`: per-fibre uniqueness of the equilibrium,
  so `h` is the *only* graph of fast equilibria;
- `SlowManifold.const_isIntegralCurve` / `invariant_graph`: invariance of the graph under the
  frozen layer flow.

`FenichelManifold` derives `manifoldMap` as data with proven uniqueness (`manifoldMap_unique`) and,
under a contraction-rate bound, Lipschitz continuity and continuity (`manifoldMap_lipschitzWith`,
`continuous_manifoldMap`); `FenichelSlowDrift` records the `O(ε)` slow-drift bounds
(`manifoldMap_slowDrift_le`, `manifoldMap_slowDrift_tendsto_zero`). The full Fenichel theorem,
smoothness/existence of `h` from data via a parametrised implicit-function theorem and ε-positive
persistence of the perturbed invariant manifold, is **not formalized** (the invariance here is
exact only for the layer `ε = 0` flow).

**Michaelis–Menten** instantiates this machinery on the enzyme system `E + S ⇌ ES → E + P`:

- `MichaelisMenten.linearFastField` and `enzymeFastSubsystem`: the linear inward fast field, its
  one-sided contraction (`linearFastField_oneSidedContraction`), and its boundary-layer collapse
  `michaelisMenten_boundaryLayer`;
- `michaelisMenten_qssa_error`: the compact-time error theorem against the flat complex-equilibrium
  fibre;
- `MichaelisMentenManifold`: the substrate-dependent complex equilibrium `mmComplexEquil`
  `= Vmax·s/(Km+s)`, its manifold map (`mmManifoldMap_eq`, `continuousOn_mmManifoldMap`), and the
  substrate-dependent error theorems (`michaelisMenten_manifold_qssa_error`,
  `michaelisMenten_manifold_qssa_error_const`);
- `MichaelisMentenReduced`: the reduced scalar Michaelis–Menten field `mmReducedField`
  `= −Vmax·s/(Km+s)` on `s ≥ 0` (extended by `0`), which is `(Vmax/Km)`-Lipschitz
  (`mmReducedField_lipschitz`) and bounded (`mmReducedField_abs_le`); the **constructed** substrate
  curve `mmSubstrate` from `ODE.exists_isIntegralCurve`, its forward positivity
  (`mmSubstrate_nonneg`), and the closed compact-time error theorem
  `michaelisMenten_reduced_qssa_error`;
- `MichaelisMentenDepletion`: the qualitative dynamics of the reduced flow: the substrate is
  monotonically depleted (`mmSubstrate_antitone`), stays in `[0, s₀]` (`mmSubstrate_le_init`,
  `mmSubstrate_nonneg_all`), and settles to a limit as `t → ∞` (`mmSubstrate_tendsto_atTop`).

Everything stated is fully proved on compact time; the reduction's `ε`-dependence and
infinite-horizon behavior are out of scope.

## Routh–Hurwitz and the Hopf crossing gate

The stability of linearizations, in low degree. A real polynomial is **Hurwitz**
(`CRNT.IsHurwitz`) when all complex roots lie in the open left half-plane: exactly the
characteristic polynomial of a linear system whose every mode decays.

- `hurwitz_quadratic_iff` / `hurwitz_quadratic_root_iff`, the **degree-2** Routh–Hurwitz criterion:
  `z² + a₁z + a₀` is Hurwitz iff `0 < a₁` and `0 < a₀`;
- `hurwitz_cubic_necessary`, the **degree-3 necessity** direction: a Hurwitz monic real cubic
  satisfies `0 < a₂`, `0 < a₁`, `0 < a₀`, and `a₀ < a₂·a₁`;
- `hurwitz_cubic_sufficient_allReal` / `hurwitz_cubic_sufficient_conjPair` and
  `hurwitz_cubic_root_iff`, the **degree-3 sufficiency** cores and the full degree-3 criterion as a
  root-predicate `iff` (given the Vieta identities and the real-coefficient conjugation dichotomy);
- `hurwitzMatrix` / `hurwitzDet`, the general Hurwitz matrix and its leading principal minors, with
  `hurwitzDet_two_cubic : hurwitzDet a 3 2 _ = a₂·a₁ − a₀` tying the `2×2` minor to the determinant
  condition;
- `cubic_conj_dichotomy` and `hurwitz_cubic_root_iff_coeff` discharge the conjugation dichotomy
  from the reality of the coefficients alone, giving the **coefficient-only** degree-3 criterion
  (no structural hypothesis).

**The Hopf crossing gate.** On the boundary of the Hurwitz region, where the penultimate Hurwitz
determinant vanishes (`a₂·a₁ = a₀`) while the lower data stay positive:

- `hopf_crossing_gate` (with core `hopf_crossing_core`): the cubic carries a **purely imaginary
  conjugate eigenvalue pair** (two roots with zero real part and nonzero imaginary part) and the
  remaining real root is negative. This is the algebraic eigenvalue-crossing condition under which a
  Hopf bifurcation can occur.

The full Hopf bifurcation theorem (limit-cycle existence, center-manifold reduction) and the
general-degree Routh–Hurwitz converse (positivity of all `n` Hurwitz determinants implies Hurwitz,
via Hermite–Biehler / Routh-array continued fractions) are **not formalized**: the gate states only
the algebraic crossing condition, and the criterion is complete only through degree 3.

## Modules

Kinetics:
- `CRNT/Kinetics/Concentration.lean`: concentrations, nonnegativity/positivity, mass-action
  monomial.
- `CRNT/Kinetics/MassAction.lean`: rate constants, mass-action rate and vector field.
- `CRNT/Kinetics/General.lean`: the `Kinetics` abstraction; boundary non-attraction and
  conservation; mass action as an instance.
- `CRNT/Kinetics/Generalized.lean`: generalized (Müller–Regensburger) mass action.

Dynamics:
- `CRNT/Dynamics/MassActionAlgebra.lean`: the `ẋ = Y(A_k(Ψ x))` factorization.
- `CRNT/Dynamics/MassActionField.lean`: smoothness, boundary non-attraction, local existence.
- `CRNT/Dynamics/FlowConstruction.lean`: the `Flow ℝ≥0` of a bounded Lipschitz field.
- `CRNT/Dynamics/LaSalle.lean`: LaSalle's invariance principle for forward semiflows.
- `CRNT/Dynamics/Monotone.lean`: order-preserving flows and scalar comparison.
- `CRNT/Dynamics/QSSA.lean`: the compact-time quasi-steady-state error bound.
- `CRNT/Dynamics/Tikhonov.lean`: boundary-layer exponential attraction; the derived defect.
- `CRNT/Dynamics/Fenichel.lean`, `FenichelManifold.lean`, `FenichelSlowDrift.lean`: the slow
  manifold, its manifold map, and slow-drift bounds.
- `CRNT/Dynamics/MichaelisMenten.lean`, `MichaelisMentenManifold.lean`, `MichaelisMentenReduced.lean`,
  `MichaelisMentenDepletion.lean`: the Michaelis–Menten reduction and depletion.
- `CRNT/Dynamics/RouthHurwitz.lean`, `Hurwitz.lean`, `HopfGate.lean`: the Routh–Hurwitz criterion
  and the Hopf crossing gate.

Lyapunov / stability stack:
- `CRNT/Theorems/DeficiencyZero/Lyapunov.lean`: `relEntropy` and its positive definiteness.
- `CRNT/Theorems/DeficiencyZero/Dissipation.lean`: the dissipation rate and its sign.
- `CRNT/Theorems/DeficiencyZero/Stability.lean`: descent along solutions.
- `CRNT/Theorems/DeficiencyZero/Confinement.lean`: the `clampBox` cutoff and coercivity.
- `CRNT/Theorems/DeficiencyZero/AsymptoticStability.lean`: `omegaLimit_eq_singleton_of_local`.

## Related documents

- [`architecture.md`](architecture.md): the layered organization and theorem dependency graph.
- [`deficiency.md`](deficiency.md): equilibrium existence, complex balancing, Birch, and the
  deficiency theorems (the uniqueness input to local asymptotic stability).
- [`persistence-gac.md`](persistence-gac.md): global dynamics, siphons, persistence, and the global
  attractor conjecture.
</content>
</invoke>

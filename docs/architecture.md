# Mathematical architecture

This document describes how the `CRNT` library is organized as mathematics: the layers it is built
in, the core abstractions each layer introduces, and how the major theorems depend on one another.
It is the hub for the per-area documents, each of which articulates one area's definitions and
proven results in detail.

- **What is here and what works** is documented here and in the per-area docs below.
- **What is ahead** (the roadmap and open strategy) lives in the project's working plan, not in
  the committed docs.
- **Why the code is shaped the way it is** (representation choices) is in [`design.md`](design.md).
- **How external tools emit checkable Lean** is in
  [`generated-certificates.md`](generated-certificates.md).

The default import `import CRNT` is `sorry`-free and introduces no axioms beyond Mathlib's; every
result reported as proven is machine-checked.

## The layers

The library is built bottom-up; each layer depends only on those above it.

1. **Foundations**: finite chemical reaction networks as data, the reaction graph, and
   stoichiometry. Species, complexes, reactions, the `Network` structure; directed reachability,
   weak reversibility, linkage and strong-linkage classes; reaction vectors, the stoichiometric
   subspace, and rank. See [`foundations.md`](foundations.md).

2. **Kinetics and dynamics**: rate laws and the resulting differential equations. The general
   `Kinetics` abstraction and mass-action as its instance; the Feinberg–Horn–Jackson factorization
   `ẋ = Y(A_k(Ψ x))` through complex space; the relative-entropy Lyapunov function and LaSalle's
   invariance principle; the forward semiflow `Flow ℝ≥0` of the genuine dynamics; local asymptotic
   stability; and the reduced models (quasi-steady-state / Michaelis–Menten, Routh–Hurwitz). See
   [`dynamics.md`](dynamics.md).

3. **Equilibria and deficiency**: existence, uniqueness, and the structural theory that controls
   them. Complex balancing and the toric structure of equilibria; Birch's theorem; Perron–Frobenius
   for column-stochastic matrices; deficiency as a kernel dimension; the deficiency-zero theorem and
   the deficiency-one uniqueness theorem (single and multi-class). See [`deficiency.md`](deficiency.md).

4. **Global dynamics**: behavior in the large: whether trajectories avoid extinction and converge.
   Petri-net siphons and persistence; the global attractor conjecture, its reduction to persistence,
   the unconditional no-critical-siphon case, and the toric-differential-inclusion development. See
   [`persistence-gac.md`](persistence-gac.md).

5. **Multistationarity, robustness, and composition**: when multiple equilibria are possible, when
   an output is robust, and how networks compose. Injectivity / species–reaction graph / P-matrix
   criteria; absolute concentration robustness and antithetic integral feedback; open (CFSTR)
   extensions; network interconnection. See [`multistationarity-robustness.md`](multistationarity-robustness.md).

6. **Stochastic CRN**: the discrete-molecule regime. The chemical master equation's generator on
   `ℕ^S` and the Anderson–Craciun–Kurtz product-form stationary distribution for complex-balanced
   networks. See [`stochastic.md`](stochastic.md).

7. **Decidability and certificates**: computable companions. Decidable reachability, weak
   reversibility, and linkage; the `crnt_check` tactic; exact rational rank and deficiency
   certificates; and the contract by which external tools emit checkable Lean. See
   [`decidability.md`](decidability.md) and [`generated-certificates.md`](generated-certificates.md).

## Core abstractions

A few types carry the whole development:

- **`Network S`**: a finite reaction network over a `Fintype` of species `S`: a finite reaction
  index `R` and, per reaction, source and target `Complex S` (a `Complex` is a function `S → ℕ` of
  stoichiometric coefficients, with `toRealVector` the bridge into real space). Everything structural,
  the reaction graph, linkage, and deficiency, is read off this.
- **`Kinetics`**: the rate-law abstraction (a rate function with admissibility: nonnegativity,
  support-vanishing, weak monotonicity). Mass-action is the canonical instance and recovers the
  mass-action vector field definitionally; the stoichiometry/deficiency/linkage algebra is
  kinetics-agnostic over it.
- **The mass-action vector field** and its factorization `ẋ = Y(A_k(Ψ x))`: the dynamics expressed
  through the complex space, where `Y` is the complex matrix, `A_k` the (Laplacian) kinetic matrix,
  and `Ψ` the monomial map. Complex balancing is exactly `A_k(Ψ x) = 0`.
- **`Flow ℝ≥0`**: the forward semiflow of the genuine dynamics, constructed from a bounded-Lipschitz
  cutoff of the field via Picard–Lindelöf with continuous dependence and uniqueness; the substrate
  for every dynamical statement (`Flow.laSalle`, ω-limit theory).
- **`relEntropy x* ·`**: the Horn–Jackson relative entropy (pseudo-Helmholtz free energy), the
  strict Lyapunov function whose dissipation vanishes exactly at complex-balanced equilibria.

## Theorem dependency structure

The headline results and what they rest on:

```
Network / reaction graph / stoichiometry  (foundations)
        │
        ├── mass-action field  ─► factorization ẋ = Y(A_k(Ψ x))  ─► complex balancing = A_k(Ψ x)=0
        │                                                              │
        │                                                              ▼
        │   Perron–Frobenius (column-stochastic)  ─► WR ⇒ positive kernel of A_k
        │   Birch (existence + uniqueness per positive class)   ─────────────┐
        │                                                                    ▼
        ├── deficiency = dim(ker Y ∩ Im ∂)  ─► deficiency-zero theorem  ─► (unique complex-balanced eq.)
        │                                   └► deficiency-one uniqueness (single + multi-class)
        │
        ├── relEntropy Lyapunov + dissipation  ─► Flow ℝ≥0  ─► LaSalle
        │            │                                          │
        │            ▼                                          ▼
        │   local asymptotic stability (deficiency-zero)   ω-limit machinery
        │                                                       │
        └── siphons / boundary ω-points ──────────────────────► GAC ⟺ persistence
                                                                 │
                                          no-critical-siphon ⇒ GAC ; one positive ω-point ⇒ GAC
```

The Lyapunov/LaSalle stack reduces the global attractor conjecture to **persistence** (no boundary
ω-limit points). Persistence is proven for the no-critical-siphon class and is otherwise the open
frontier. Stochastic ACK product-form reuses the same complex-balancing notion as the
deficiency-zero theorem, with the complex-balanced equilibrium as the Poisson parameter.

## Conventions

- **Sorry-free and axiom-clean.** The stable library uses no `sorry` and no `native_decide`; every
  headline result is `[propext, Classical.choice, Quot.sound]`-clean.
- **Two axes of completeness.** Where applicable each notion has both a propositional definition and
  a decidable computable companion related by a theorem (see [`decidability.md`](decidability.md)).
- **Each abstraction is exercised** by at least one worked example network (`CRNT/Examples/`).
- Module docstrings describe the mathematics as present fact and cite the source literature by
  author and title; they do not reference internal plans or paper section numbers.

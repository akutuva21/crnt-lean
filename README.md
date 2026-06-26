# Chemical Reaction Network Theory in Lean 4

A Lean 4 formalization of **Chemical Reaction Network Theory**, oriented toward synthetic biology,
molecular programming, and biochemical design automation.

A chemical reaction network is a set of chemical species together with the reactions among them: the
model behind gene regulatory circuits, metabolic pathways, and cell-signaling cascades. Chemical
Reaction Network Theory studies how that structure (which species react, and into what) constrains the
dynamics a network can produce, often independent of the reaction rates.

That makes the theory valuable to anyone engineering biochemical systems. When you design a circuit such
as a genetic toggle switch or a biochemical oscillator, the rate constants are usually unknown and can
drift, so the guarantees worth having are the ones that depend only on the wiring. From the structure
alone, the theory can often settle whether the network has a unique steady state, whether it can be
bistable or oscillate, whether it returns to equilibrium from any starting point, and whether some
species holds steady while others vary. You can rule a behavior out, or guarantee it, before you build the circuit.

This library makes that theory machine-checked. Every result is verified by Lean's kernel, and the
structural criteria carry decidable procedures and exact certificates, so a design tool can hand it a
candidate network and get back a checkable answer instead of a heuristic.

Underneath, the library is built in two layers. The CRN layer formalizes the classical structural and
dynamical theory over a small composable core: species, complexes, reactions, stoichiometry,
mass-action kinetics, linkage classes, deficiency. The mathematics layer beneath it supplies general
results Mathlib lacks as of v4.31 (Sperner's lemma and Brouwer's theorem in every dimension, Gale–Nikaido
univalence, forward semiflows with LaSalle).

- **Package:** `crnt-lean` · **Namespace:** `CRNT`
- **Lean:** 4.31.0 · **Mathlib:** v4.31.0
- The default import (`import CRNT`) is **`sorry`-free** and introduces **no axioms beyond Mathlib's**
  (`[propext, Classical.choice, Quot.sound]`).

## Highlights

- Feinberg's deficiency-zero and deficiency-one theorems: network structure alone pins down the
  equilibria, for any rate constants.
- Unconditional global convergence for no-critical-siphon networks: a decidable sufficient condition
  for the global attractor property.
- The Anderson–Craciun–Kurtz product form: the exact stationary distribution of a complex-balanced
  stochastic network.
- Concordance forces at most one steady state per class, for every weakly-monotonic kinetics,
  independent of the rate constants.
- Gale–Nikaido univalence without topological degree: a P-matrix Jacobian on a box is injective,
  resting on n-dimensional Sperner and Brouwer theorems formalized here.
- A decidable, certificate-emitting core: check deficiency, reachability, and siphons, with
  kernel-checked certificates and a stable JSON contract for external tools.

## What's proven

Grouped by area; the precise statements and module names are in each linked doc.

**[Foundations & decidability](docs/foundations.md)**
- the network, reaction-graph, and stoichiometry core
- decidable reachability, weak reversibility, and linkage, plus the `crnt_check` tactic
- exact rational-rank and deficiency certificates, and a versioned `analyze` JSON contract

**[Equilibria & deficiency](docs/deficiency.md)**
- complex balancing and the toric structure of steady states
- Birch's theorem, and Perron–Frobenius for column-stochastic matrices
- the deficiency-zero theorem, and deficiency-one uniqueness (single- and multi-class)

**[Dynamics & stability](docs/dynamics.md)**
- the complex-space factorization `ẋ = Y(A_k(Ψ x))` and the forward semiflow
- the relative-entropy Lyapunov function, LaSalle's invariance principle, and local asymptotic stability
- a Michaelis–Menten quasi-steady-state reduction

**[Persistence & global attraction](docs/persistence-gac.md)**
- the reduction GAC ⟺ persistence, and unconditional convergence for the no-critical-siphon class
- the sharp "one positive ω-limit point ⇒ convergence" reduction
- a development of the toric-differential-inclusion approach

**[Stochastic CRN](docs/stochastic.md)**
- the chemical-master-equation generator on `ℕ^S`
- the Anderson–Craciun–Kurtz product-form stationary distribution

**[Multistationarity & robustness](docs/multistationarity-robustness.md)**
- degree-free Gale–Nikaido univalence, bound to class injectivity
- concordance ⇒ kinetics-independent monostationarity
- the signed species–reaction graph and the determinant cycle-cover expansion
- absolute concentration robustness, antithetic integral feedback, open (CFSTR) systems, and composition

Every abstraction is exercised by at least one worked example network in `CRNT/Examples/`.

### General mathematics (not in Mathlib v4.31)

The CRN results above rest on general-purpose mathematics built here.

**[Fixed-point theory](CRNT/Analysis)**
- Sperner's lemma in every dimension, via the Kuhn (Freudenthal) triangulation and a parity/handshake
  involution on door incidences
- Brouwer's fixed-point theorem for the standard `n`-simplex in every dimension, from Sperner by mesh
  refinement

**[Univalence & matrices](CRNT/Multistationarity)**
- Gale–Nikaido global univalence, degree-free: Stiemke's alternative, an order-monotonicity theorem,
  and ±1 sign-conjugation over a P-matrix calculus (Schur complements, signature invariance)
- computable exact rational matrix rank with a nonsingular-minor certificate

**[Dynamical systems](CRNT/Dynamics)**
- forward semiflows, Lyapunov stability, and LaSalle's principle, with the flow of a bounded Lipschitz
  field and backward invariance of ω-limit sets
- single-valued Nagumo invariance (subtangency ⇒ forward invariance) via first-exit arguments

## Scope & open problems

The library proves the classical canon and a large decidable fraction of the design-relevant criteria.
What remains is of two kinds: established mathematics Mathlib does not yet have, where building it
unlocks the CRN results noted, and questions where the mathematics itself is still open.

**General mathematics still to build**
- topological degree: unconditional steady-state existence and the multistationarity converse (the
  switch verdict)
- persistence theory (facet repulsion, Butler–McGehee): global attraction for broad weakly-reversible
  classes
- Fenichel / singular-perturbation theory: error-quantified, infinite-horizon time-scale reduction
- continuous-time Markov chains: process-level stochastics and the deterministic (Kurtz) scaling limit
- center-manifold reduction and Hopf bifurcation: sustained oscillation (the clock verdict)

**Open research**
- the global attractor conjecture in full generality (Horn's 1974 conjecture, still open; proven here
  for the no-critical-siphon class and reduced to persistence in all cases)
- the correctness of the higher-deficiency (Deficiency One and Advanced Deficiency) algorithms
- unconditional absolute concentration robustness

## Getting started

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build           # build the library and examples
lake test            # build and run the smoke tests
```

```lean
import CRNT
open CRNT

inductive Species | A | B deriving DecidableEq, Fintype, Repr
open Species

def cA : Complex Species := fun s => match s with | A => 1 | B => 0
def cB : Complex Species := fun s => match s with | A => 0 | B => 1

inductive Rxn | fwd | bwd deriving DecidableEq, Fintype, Repr

def rxn : Rxn → Reaction Species
  | .fwd => { source := cA, target := cB }
  | .bwd => { source := cB, target := cA }

def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

example : N.numComplexes = 2 := by decide
example : N.WeaklyReversible := by
  intro r; cases r
  · exact Network.Reaches.single ⟨Rxn.bwd, rfl, rfl⟩
  · exact Network.Reaches.single ⟨Rxn.fwd, rfl, rfl⟩
```

`Complex S` is `S → ℕ` (stoichiometric coefficients). See
[`docs/foundations.md`](docs/foundations.md) for the data model and
[`docs/decidability.md`](docs/decidability.md) for `decide` / `crnt_check` and certificates.

## Documentation

[`docs/architecture.md`](docs/architecture.md) is the hub: the mathematical layering, core
abstractions, and theorem dependency structure. From there:

| Doc | Covers |
|---|---|
| [`foundations.md`](docs/foundations.md) | networks, the reaction graph, stoichiometry |
| [`dynamics.md`](docs/dynamics.md) | kinetics, complex-space factorization, the semiflow, Lyapunov/LaSalle, local stability, reduced models |
| [`deficiency.md`](docs/deficiency.md) | complex balancing, Birch, Perron–Frobenius, the deficiency-zero and deficiency-one theorems |
| [`persistence-gac.md`](docs/persistence-gac.md) | siphons, persistence, the global attractor conjecture (proven vs. open) |
| [`stochastic.md`](docs/stochastic.md) | the chemical master equation and Anderson–Craciun–Kurtz product form |
| [`multistationarity-robustness.md`](docs/multistationarity-robustness.md) | injectivity, the SR-graph, concordance, ACR, adaptation, open systems, composition |
| [`decidability.md`](docs/decidability.md) | decision procedures, `crnt_check`, rational rank/deficiency certificates |
| [`generated-certificates.md`](docs/generated-certificates.md) · [`analyze-contract.md`](docs/analyze-contract.md) | the contract for external tools that emit checkable Lean |
| [`design.md`](docs/design.md) | implementation and representation decisions |

## Contributing

- Keep the default import (`CRNT`) `sorry`-free and axiom-clean (`[propext, Classical.choice,
  Quot.sound]`); no `native_decide` (`decide` is fine).
- Provide both a propositional definition and, where feasible, a decidable computable companion,
  related by a theorem.
- Exercise every new abstraction with at least one example network and a `test/Smoke.lean` entry.
- Module docstrings describe the mathematics as present fact and cite source literature by author and
  title; place unfinished proofs in clearly named modules that `CRNT.lean` does not re-export.

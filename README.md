# Chemical Reaction Network Theory (CRNT) in Lean 4

A Lean 4 formalization of **Chemical Reaction Network Theory**, oriented toward synthetic biology,
molecular programming, and biochemical design automation.

The library provides a rigorous, composable core for finite chemical reaction networks (species,
complexes, reactions, the reaction graph, stoichiometry, mass-action kinetics, linkage classes,
weak reversibility, deficiency) and builds on it the classical structural and dynamical theory:
the deficiency-zero and deficiency-one theorems, the Horn–Jackson Lyapunov/LaSalle stability theory,
persistence and the global attractor conjecture, the Anderson–Craciun–Kurtz stochastic product form,
multistationarity and robustness criteria, and decidable companions with exact certificates. It is
designed so external tools can emit Lean files that *check* network properties against a stable API.

- **Package:** `crnt-lean` · **Namespace:** `CRNT`
- **Lean:** 4.31.0 · **Mathlib:** v4.31.0
- The default import (`import CRNT`) is **`sorry`-free** and introduces **no axioms beyond Mathlib's**.

## Build

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build           # build the library and examples
lake test            # build and run the smoke tests
```

## Minimal example

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

The mathematics is documented by area. Start with the architecture overview, then read the area you
need.

- [`docs/architecture.md`](docs/architecture.md): the **mathematical architecture**: layers, core
  abstractions, and the dependency structure of the major theorems (the hub for everything below).
- [`docs/foundations.md`](docs/foundations.md): networks, the reaction graph, stoichiometry.
- [`docs/dynamics.md`](docs/dynamics.md): kinetics, the complex-space factorization, the semiflow,
  the relative-entropy Lyapunov function, LaSalle, local stability, and reduced models.
- [`docs/deficiency.md`](docs/deficiency.md): complex balancing, Birch, Perron–Frobenius, and the
  deficiency-zero and deficiency-one theorems.
- [`docs/persistence-gac.md`](docs/persistence-gac.md): siphons, persistence, and the global
  attractor conjecture (what is proven, and what remains open).
- [`docs/stochastic.md`](docs/stochastic.md): the chemical master equation and Anderson–Craciun–Kurtz
  product-form stationarity.
- [`docs/multistationarity-robustness.md`](docs/multistationarity-robustness.md): injectivity,
  the species–reaction graph, absolute concentration robustness, adaptation, open systems, composition.
- [`docs/decidability.md`](docs/decidability.md): decision procedures, the `crnt_check` tactic, and
  exact rational rank/deficiency certificates.
- [`docs/generated-certificates.md`](docs/generated-certificates.md): the contract for external
  tools that emit checkable Lean.
- [`docs/design.md`](docs/design.md): the implementation/representation decisions behind the code.

## What is proven (at a glance)

Headline machine-checked results, by area (see the area docs for the precise statements and module
names):

- **Foundations & decidability:** the network/graph/stoichiometry core; decidable reachability,
  weak reversibility, and linkage; the `crnt_check` tactic; exact rational rank and deficiency
  certificates via verified Gaussian elimination.
- **Equilibria & deficiency:** complex balancing and the toric structure of equilibria; Birch's
  theorem (existence and uniqueness per positive class); Perron–Frobenius for column-stochastic
  matrices; deficiency as a kernel dimension; the **Feinberg–Horn–Jackson deficiency-zero theorem**;
  and the **deficiency-one uniqueness theorem** (single- and multi-deficient-class).
- **Dynamics & stability:** the factorization `ẋ = Y(A_k(Ψ x))`; the forward semiflow `Flow ℝ≥0`;
  the relative-entropy Lyapunov function with its dissipation inequality; **LaSalle's invariance
  principle**; **local asymptotic stability** of the complex-balanced equilibrium; and a compact-time
  Michaelis–Menten quasi-steady-state reduction.
- **Persistence & the global attractor conjecture:** the reduction *GAC ⟺ persistence*;
  **unconditional global convergence for the no-critical-siphon class**; the sharp "one positive
  ω-limit point ⇒ convergence" reduction; and a machine-checked development of the
  toric-differential-inclusion approach. The conjecture is open in general; see the area doc for what
  is proven versus assumed.
- **Stochastic CRN:** the chemical-master-equation generator on `ℕ^S` and the
  **Anderson–Craciun–Kurtz product-form** stationary distribution for complex-balanced networks.
- **Multistationarity & robustness:** injectivity and species–reaction-graph fragments; the P-matrix
  layer; absolute concentration robustness; antithetic integral feedback (perfect adaptation); open
  (CFSTR) extensions; network interconnection.

Each abstraction is exercised by at least one worked example network in `CRNT/Examples/`.

## Contributing

- Keep the default import (`CRNT`) `sorry`-free and axiom-clean (`[propext, Classical.choice,
  Quot.sound]`); no `native_decide` (`decide` is fine).
- Provide both a propositional definition and, where feasible, a decidable computable companion,
  related by a theorem.
- Exercise every new abstraction with at least one example network and a `test/Smoke.lean` entry.
- Module docstrings describe the mathematics as present fact and cite source literature by author and
  title; place unfinished proofs in clearly named modules that `CRNT.lean` does not re-export.

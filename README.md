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

- **Package:** `crnt-lean`
- **Namespace:** `CRNT`
- **Lean:** 4.31.0
- **Mathlib:** v4.31.0
- The default import (`import CRNT`) is **`sorry`-free** and introduces **no axioms beyond Mathlib's**
  (`[propext, Classical.choice, Quot.sound]`).

## Highlights

- Feinberg's deficiency-zero and deficiency-one theorems: network structure alone pins down the
  equilibria, for any rate constants.
- Unconditional global convergence for no-critical-siphon networks: a decidable sufficient condition
  for the global attractor property.
- The global attractor conjecture reduced to a single explicit hypothesis: for weakly-reversible
  complex-balanced networks, global convergence follows from one geometric predicate (a bounded region
  that confines the orbit a fixed distance away from every species facet), with every step from that
  predicate to convergence machine-checked.
- The Anderson–Craciun–Kurtz product form: the exact stationary distribution of a complex-balanced
  stochastic network.
- Concordance forces at most one steady state per class, for every weakly-monotonic kinetics,
  independent of the rate constants.
- Gale–Nikaido univalence without topological degree: a P-matrix Jacobian on a box is injective,
  resting on n-dimensional Sperner and Brouwer theorems formalized here.
- A decidable, certificate-emitting core: check deficiency, reachability, and siphons, with
  kernel-checked certificates and a stable JSON contract for external tools.

## What's Proven

Grouped by area; the precise statements and module names are in each linked doc.

**[Foundations & decidability](docs/foundations.md)**
- The network, reaction-graph, and stoichiometry core
- Decidable reachability, weak reversibility, and linkage, plus the `crnt_check` tactic
- Exact rational-rank and deficiency certificates, and a versioned `analyze` JSON contract

**[Equilibria & deficiency](docs/deficiency.md)**
- Complex balancing and the toric structure of steady states
- Birch's theorem, and Perron–Frobenius for column-stochastic matrices
- The deficiency-zero theorem, and deficiency-one uniqueness (single- and multi-class)

**[Dynamics & stability](docs/dynamics.md)**
- The complex-space factorization `ẋ = Y(A_k(Ψ x))` and the forward semiflow
- The relative-entropy Lyapunov function, LaSalle's invariance principle, and local asymptotic stability
- A Michaelis–Menten quasi-steady-state reduction, error-quantified in time: the full trajectory tracks
  the slow-manifold reduction within an O(ε) Grönwall bound on compact time, and within a
  horizon-uniform O(ε) ceiling for all time under a coupled contraction hypothesis (ε the timescale
  separation)
- Routh–Hurwitz stability to degree 4 (Liénard–Chipart) with the degree-3 and degree-4 Hopf crossing
  gates, and a dimension-free Gershgorin test certifying mass-action Jacobian stability (so oscillation
  is excluded)
- The planar Poincaré normal form with its first Lyapunov coefficient, and the closed-form limit cycle
  of the truncated normal form; the sustained-oscillation verdict for the full field is reduced to
  explicit center-manifold, averaging, and smooth-flow-dependence hypotheses (see Scope & Open Problems)

**[Persistence & global attraction](docs/persistence-gac.md)**
- The reduction GAC ⟺ persistence, and unconditional convergence for the no-critical-siphon class
- The sharp "one positive ω-limit point ⇒ convergence" reduction
- The global attractor conjecture for weakly-reversible complex-balanced networks reduced to a single
  predicate, `SeparatingConfinement` (a bounded, forward-invariant region holding the orbit off every
  facet), proven sufficient for global convergence end to end; the affine separating surface is built
  in every dimension
- That predicate shown equivalent to persistence and constructed outright on two classes — near
  equilibrium, and the entire decidable no-critical-siphon class — so it is realized, not only assumed;
  the construction supplies the no-critical-siphon persistence certificate as a by-product
- A development of the toric-differential-inclusion approach

**[Stochastic CRN](docs/stochastic.md)**
- The chemical-master-equation generator on `ℕ^S`
- The Anderson–Craciun–Kurtz product-form stationary distribution
- A normalized invariant probability measure on any finite closed enabled region, with product-form
  singleton ratios
- The Kurtz density-dependent generator-convergence estimate: the volume-scaled generator of a
  differentiable observable converges to its derivative along the deterministic mass-action field

**[Multistationarity & robustness](docs/multistationarity-robustness.md)**
- Degree-free Gale–Nikaido univalence, bound to class injectivity
- Concordance ⇒ kinetics-independent monostationarity
- The signed species–reaction graph and the determinant cycle-cover expansion
- Topological-degree steady-state existence (a nonzero reduced degree forces a steady state in the
  compatibility class) and a multistationarity-capacity test from a sign-indefinite reduced Jacobian
- Absolute concentration robustness, antithetic integral feedback, open (CFSTR) systems, and composition

Every abstraction is exercised by at least one worked example network in [`CRNT/Examples/`](./CRNT/Examples/).

### General Mathematics (not in Mathlib v4.31)

The CRN results above rest on general-purpose mathematics built here.

**[Fixed-point theory](CRNT/Analysis)**
- Sperner's lemma in every dimension, via the Kuhn (Freudenthal) triangulation and a parity/handshake
  involution on door incidences
- Brouwer's fixed-point theorem for the standard `n`-simplex in every dimension, from Sperner by mesh
  refinement

**[Univalence & matrices](CRNT/Multistationarity)**
- Gale–Nikaido global univalence, degree-free: Stiemke's alternative, an order-monotonicity theorem,
  and ±1 sign-conjugation over a P-matrix calculus (Schur complements, signature invariance)
- Computable exact rational matrix rank with a nonsingular-minor certificate

**[Topological degree](CRNT/Multistationarity)**
- The Brouwer degree at a regular value, built as a finite signed sum of Jacobian-determinant signs:
  Sard's theorem (critical values are null, regular values dense), degree additivity over disjoint
  regions, homotopy invariance, and local constancy of the degree for proper maps

**[Dynamical systems](CRNT/Dynamics)**
- Forward semiflows, Lyapunov stability, and LaSalle's principle, with the flow of a bounded Lipschitz
  field and backward invariance of ω-limit sets
- Single-valued Nagumo invariance (subtangency ⇒ forward invariance) via first-exit arguments

## Scope & Open Problems

The library proves the classical canon and a large decidable fraction of the design-relevant criteria.
What remains is of two kinds: established mathematics Mathlib does not yet have, where building it
unlocks the CRN results noted, and questions where the mathematics itself is still open.

**General mathematics still to build.** The apparatus in each of these areas is in place; what
remains is a specific missing piece.
- The nonzero-degree input for topological-degree existence. The Brouwer degree, Sard's theorem, and
  homotopy invariance are built, and a nonzero reduced degree forces a steady state; what is missing is
  a theorem forcing the degree to be nonzero for a network class, which would make steady-state
  existence unconditional and settle the multistationarity converse (the switch verdict)
- Critical-siphon facet repulsion. The Butler–McGehee lemma and non-siphon (codimension-1) facet
  repulsion are proven, as is the Anderson–Shiu influx estimate for a singleton critical siphon (a
  linear lower bound on the mass-action field at the facet). From that bound together with a near-facet
  relative-entropy dissipation bound, a uniform positive facet floor follows. What remains is the
  dissipation bound itself, carried as a hypothesis, and its assembly into a persistence conclusion;
  discharging it would extend unconditional global attraction past the no-critical-siphon class
- Fenichel normally-hyperbolic invariant-manifold persistence. The O(ε) quasi-steady-state reduction
  holds on compact time and lifts to the infinite horizon: all-time invariance of the substrate-varying
  slow manifold with an O(ε) ceiling is proven for the closed-form contracting field, and a
  horizon-uniform O(ε) tracking ceiling for the genuine coupled Michaelis–Menten trajectory is proven by
  a dissipative (log-norm) Grönwall estimate. The latter assumes a coupled transverse contraction bound;
  deriving that bound from the enzyme field itself is what remains
- The stochastic process layer. The chemical-master-equation generator, the uniformized transition
  semigroup, and the deterministic (Kurtz) scaling skeleton (the generator-convergence estimate and a
  conditional fluid-limit bound) are built, together with a Poisson probability space (an independent
  scaled-Poisson clock family) and an in-probability law of large numbers for the aggregate scaled
  fluctuation. What remains is the continuous-time sample-path process itself, a time-indexed random
  trajectory with its filtration, and the process-level (Skorokhod) law of large numbers, which rest on
  the compensated-Poisson martingale theory Mathlib lacks
- The center-manifold gaps behind sustained oscillation. The Hopf crossing gates, the planar normal
  form, and the truncated-normal-form limit cycle are proven, and the full-field "clock verdict" is
  reduced to three explicit inputs: center-manifold existence, center-manifold averaging, and C¹
  dependence of the flow on initial data (a return-map construction). Two of the three are discharged
  independently: the center manifold is constructed as a Lyapunov–Perron fixed point, and the flow's C¹
  dependence on its initial data is proven through the variational equation. The clock verdict still
  consumes all three as inputs, and center-manifold averaging is the one piece Mathlib lacks and no
  module yet supplies

**Open research**
- The global attractor conjecture (Horn's 1974 conjecture, open in general):
  - Proven unconditionally for the no-critical-siphon class of complex-balanced networks, and reduced
    to persistence in all cases (GAC ⟺ persistence)
  - For weakly-reversible complex-balanced networks the persistence requirement is reduced to a single
    explicit predicate, `SeparatingConfinement`: the genuine mass-action orbit is forward-invariant in
    a bounded region that stays a fixed positive distance above every species facet. The implication
    `SeparatingConfinement ⇒ global convergence` is machine-checked end to end, and the affine
    (half-plane) zero-separating surface that realizes it is constructed in every dimension
  - `SeparatingConfinement` is proven equivalent to the persistence certificate `PersistentFrom`, and
    constructed outright on two classes: near equilibrium (relative entropy of the start below every
    reference coordinate) and the entire decidable no-critical-siphon class (where the orbit may touch
    a facet at finite times, but its closure stays interior). The no-critical-siphon construction also
    discharges the `PersistentFrom` certificate that the ω-limit argument leaves implicit. The
    genuine-orbit inputs — positivity, relative-entropy descent, and box uniqueness for the unclamped
    field — are proven once and reused
  - Craciun's toric-differential-inclusion architecture is formalized sorry-free, with the steps it
    rests on isolated as explicit hypotheses: set-valued viability, the n-dimensional surface
    construction, the weak-reversibility cycle cover, the polyhedral-fan axioms, and arbitrary-fan
    faithful-curve existence
  - Constructing `SeparatingConfinement` for the curved mass-action case is the open content: the
    toric zero-separating surface, refereed in the literature only for stoichiometric dimension at most
    three. No theorem constructs it in general
- The correctness of the higher-deficiency (Deficiency One and Advanced Deficiency) algorithms:
  - The apparatus is formalized (network consistency via Stiemke, cut pairs, regularity, confluence
    vectors with their proven antisymmetry, shelves, signatures, colinearity classes), and the
    exclusion direction is proven: an injective network has no capacity for multiple steady states
  - The correctness equivalences themselves (a network has that capacity iff the algorithm affirms it)
    are stated as propositions but proved in neither direction; this is the Feinberg 1995 content,
    including the forward step from a sign-compatible log-ratio to a full shelf signature
- Unconditional absolute concentration robustness (Shinar–Feinberg):
  - The discrete reduction is proven, including that the monomial ratio is constant on each linkage
    class, which narrows the whole question to forcing one scalar to zero (the robust species' log-ratio
    between two positive steady states)
  - That scalar is supplied as a hypothesis today; the natural algebraic route through the deficiency
    mode is vacuous, so closing it needs the deficiency-one sign argument from the steady-state
    equations at the non-terminal cut, which is not yet formalized and likely needs new infrastructure

## Getting Started

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

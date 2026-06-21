# CRNT in Lean 4

A Lean 4 formalization of **Chemical Reaction Network Theory** (CRNT), oriented toward
synthetic biology, molecular programming, and biochemical design automation.

The library provides a rigorous, composable core for finite chemical reaction
networks: species, complexes, reactions, the reaction graph, stoichiometry, mass-
action kinetics, linkage classes, weak reversibility, and deficiency. It is designed
so external tools can emit Lean files that *check* structural network properties
against a stable API.

- **Package:** `lean-crnt`
- **Namespace:** `CRNT`
- **Lean:** 4.31.0 · **Mathlib:** v4.31.0

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

See [`docs/tutorial.md`](docs/tutorial.md) for a step-by-step walkthrough and
[`docs/generated-certificates.md`](docs/generated-certificates.md) for the external-tool
emission contract.

## What is proven

The stable library (`import CRNT`) is `sorry`-free and introduces no axioms beyond
Mathlib's. It defines and proves, among others:

- finite CRN data structures: `Complex`, `Reaction`, `Network`;
- the reaction graph: directed reachability (`Reaches`), weak reversibility
  (`WeaklyReversible`), and linkage (`Linked`, `numLinkageClasses`);
- stoichiometry: reaction vectors, the stoichiometric subspace, and rank
  (`stoichRank ≤ card S`);
- mass-action kinetics: monomials, rates, and the vector field, with nonnegativity and
  positivity lemmas;
- equilibria: steady states, stoichiometric compatibility (an equivalence relation),
  and complex balancing;
- the Feinberg–Horn–Jackson algebraic factorization of the dynamics through the complex
  space, `ẋ = Y (A_k (Ψ x))` (`massActionVectorField_eq`), the characterization of
  complex balancing as `A_k (Ψ x) = 0`, and the theorem that **every complex-balanced
  concentration is a steady state** (`IsComplexBalanced.isMassActionSteadyState`);
- the stoichiometric and incidence maps with the factorization `stoichMap = Y ∘ ∂`,
  the incidence-rank identity `rank(∂) = n − ℓ`, and hence **deficiency as a kernel
  dimension** `δ = dim(ker Y ∩ Im ∂)` (`deficiencyInt_eq_finrank_deficiencySubspace`)
  with the deficiency-zero theorem's structural input
  `DeficiencyZero ⟺ ker Y ∩ Im ∂ = ⊥` (`deficiencyZero_iff_deficiencySubspace_eq_bot`);
- the Laplacian/conservation property of the kinetic matrix `A_k` — its columns sum to
  zero (`kineticMap_sum_eq_zero`) — and that reactions stay within linkage classes
  (`linked_of_reaction`);
- **Perron–Frobenius for column-stochastic matrices**, built from primitives (Mathlib
  has no Brouwer/Perron–Frobenius/Matrix-Tree): existence of a nonnegative fixed vector
  by a Cesàro/Markov–Kakutani argument (`exists_nonneg_mulVec_fixed_of_colStochastic`),
  the combinatorial positivity upgrade under strong connectivity
  (`pos_of_nonneg_mulVec_fixed_of_stronglyConnected`), and the combined strictly-positive
  fixed vector (`exists_pos_mulVec_fixed_of_stronglyConnected`);
- the theorem that **a weakly reversible network's kinetic matrix has a strictly positive
  kernel vector** (`PositiveKernel.weaklyReversible_exists_positive_kernelVector`) — the
  existence of complex-balanced reference states, obtained by applying Perron–Frobenius
  per linkage class;
- **Birch's theorem** (`birch`): relative to a positive reference `x*`, every positive
  stoichiometric compatibility class `c + S` contains a **unique** point with
  `S`-orthogonal log-ratio — the existence and uniqueness of the complex-balanced
  equilibrium in each positive class. Uniqueness (`birch_uniqueness`) is the strict
  monotonicity of `log`; existence (`birch_existence`) comes from minimizing the dual
  objective (below) and the double-complement identity `(Sᗮ)ᗮ = S` (`orthSum_orthSum`,
  by transporting Mathlib's `Submodule.orthogonal_orthogonal` across
  `ι → ℝ ≃ EuclideanSpace ℝ ι`);
- the **Horn–Jackson Lyapunov function** (`relEntropy`, the relative entropy) and its
  positive-definiteness about a reference equilibrium (Gibbs' inequality):
  `relEntropy_nonneg`, `relEntropy_eq_zero_iff`, `relEntropy_pos_of_ne`;
- that `relEntropy` is a **strict Lyapunov function** for the dynamics: the dissipation
  inequality `∑_s (log x_s − log x*_s) f(x)_s ≤ 0` (`dissipation_nonpos`), vanishing exactly
  at complex-balanced points (`complexBalanced_of_dissipation_eq_zero`), and hence the
  **Lyapunov descent** `relEntropy_antitone_along_solution` — `relEntropy` is nonincreasing
  along every positive mass-action solution (chain rule `relEntropy_hasDerivAt`);
- **LaSalle's invariance principle for forward semiflows** (`Flow.laSalle`), general
  dynamical-systems content built on Mathlib's `Flow`/`omegaLimit`: a continuous Lyapunov
  function with precompact orbit is constant on the ω-limit set;
- the **ODE foundations** of the mass-action dynamics: the vector field is `C^∞`
  (`massActionVectorField_contDiff`), the orthant's boundary faces are non-attracting
  (`massActionVectorField_nonneg_of_zero`), and solutions exist locally from every start
  (`exists_local_solution`, via Picard–Lindelöf);
- general flow-construction infrastructure (CRN-free, upstream-targeted): **continuous
  dependence** on initial conditions (`ODE.dist_le_of_isIntegralCurve`), uniqueness on
  `[0,∞)` (`ODE.eqOn_Ici_of_isIntegralCurve`), and **global existence** for a bounded
  Lipschitz autonomous field (`ODE.exists_isIntegralCurve`) — the analytic core of building
  a flow from an ODE, which Mathlib otherwise lacks;
- the analytic chain behind Birch existence: the **Fenchel–Young inequality**
  (`birchDualTerm_ge`, convex conjugate dual to Gibbs), the boundedness below of the Birch
  dual objective (`birchDual_ge`), its **coercivity** (`birchDual_coercive`, bounded
  sublevel sets), the existence of a **minimizer over any finite-dimensional subspace**
  (`birchDual_exists_isMinOn`), and the **first-order optimality** of that minimizer
  (`birchDual_firstOrder`: the gradient `x* ⊙ exp(ŵ) − c` is orthogonal to the subspace);
- **Perron–Frobenius uniqueness** (`mulVec_fixed_unique_of_stronglyConnected`): on a
  strongly connected nonnegative matrix, a positive fixed vector is unique up to scaling
  (a min-ratio argument feeding the localized positivity-spreading lemma);
- the **toric structure of complex-balanced equilibria**: the monomial vector scales as
  `Ψ(x)_c = Ψ(x*)_c · exp(⟨c, log(x/x*)⟩)` (`complexMonomialVector_eq_mul_exp`); the
  **toric inclusion** (`complexBalanced_of_logRatio_orthogonal`) — relative to a
  complex-balanced reference `x*`, any positive `x` with `log(x/x*)` orthogonal to the
  stoichiometric subspace is itself complex-balanced — and its **converse** for weakly
  reversible networks (`logRatio_orthogonal_of_complexBalanced`, via Perron–Frobenius
  uniqueness per linkage class); hence **given one complex-balanced equilibrium, every
  positive compatibility class contains exactly one** — existence
  (`exists_isComplexBalanced_in_positiveClass`, via Birch existence) and uniqueness
  (`isComplexBalanced_unique_in_positiveClass`, via Birch uniqueness);
- existence of a complex-balanced equilibrium from weak reversibility + deficiency zero
  (`exists_isComplexBalanced`): the strictly positive kernel vector of `A_k` is realized as
  a monomial vector `Ψ x` because deficiency zero collapses the stoichiometric and incidence
  row spaces (`range_stoichTranspose_eq`) — this is where `δ = 0` is consumed;
- **the Feinberg–Horn–Jackson deficiency-zero theorem** (`deficiencyZeroTheorem`): for a
  weakly reversible network of deficiency zero, every positive choice of rate constants and
  positive starting concentration determines a *unique* complex-balanced equilibrium in the
  positive compatibility class of the start;
- deficiency over `ℤ` (`deficiencyInt`, `DeficiencyZero`), with no natural-number
  truncated-subtraction pitfall;
- a sound, computable directed-walk certificate checker (`reaches_of_walk`).

Worked example networks (each `sorry`-free):

| Network | Proven properties |
|---|---|
| `Examples.Minimal` (`A → B`) | complex count; **not** weakly reversible |
| `Examples.ReversiblePair` (`A ⇌ B`) | `n=2`, `ℓ=1`, `s=1`; weakly reversible; **deficiency zero** |
| `Examples.IrreversibleChain` (`A → B → C`) | complex count; **not** weakly reversible |
| `Examples.GeneExpression` | complex count; DNA conservation `d[DNA]/dt = 0` |
| `Examples.Enzyme` (`E + S ⇌ ES → E + P`) | complex count; total-enzyme conservation |

## What is not yet proven

These are stated or deferred, not asserted (see [`docs/roadmap.md`](docs/roadmap.md)):

- local asymptotic stability of the complex-balanced equilibrium — the Lyapunov function,
  its strict dissipation, the descent along solutions, the abstract LaSalle invariance
  principle, and the ODE foundations (smoothness, boundary invariance, local existence) are
  all proved (above), as are the general flow-construction inputs — global existence,
  continuous dependence, and uniqueness for bounded Lipschitz fields. The remaining step to
  a literal `x(t) → x*` is now **assembly**: package these into a `Flow ℝ≥0` (semigroup +
  joint continuity) and apply it to mass action after a cutoff to a bounded field with the
  `relEntropy` confinement, then invoke LaSalle. This is bookkeeping on top of the proved
  pieces rather than missing infrastructure;
- a verified computable Boolean decision procedure for reachability / weak
  reversibility (and the corresponding `..._iff` equivalence). Concrete examples are
  established by explicit proof or by the walk-certificate checker;
- computable linkage-class enumeration and exact rational rank certificates;
- a `crnt_check` tactic.

## Contributing

- Keep the default import (`CRNT`) `sorry`-free and axiom-free.
- Provide both a propositional definition and, where feasible, a computable companion,
  related by a theorem.
- Exercise every new abstraction with at least one example network.
- Place unfinished proofs in clearly named experimental modules that `CRNT.lean` does
  not re-export.


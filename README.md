# lean-crnt

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

- the deficiency-zero theorem itself — its hypotheses and conclusion are exposed as a
  statement interface (`SatisfiesDeficiencyZeroHypotheses`, `DeficiencyZeroConclusion`)
  but the implication is not yet assembled. Its structural inputs are proved (deficiency
  as a kernel dimension, and the strictly positive kernel vector above); the remaining
  ingredient is **Birch's theorem** — realizing the positive kernel vector as a monomial
  vector `Ψ x`, uniquely in each positive stoichiometric compatibility class;
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


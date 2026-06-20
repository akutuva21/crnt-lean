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
  but the implication is not proved;
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


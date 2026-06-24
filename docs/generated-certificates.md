# Generated certificates

External tools (CRN compilers, SBML/SBOL exporters, AI design systems) verify network
claims by emitting a Lean file that imports `CRNT`, reconstructs the network with
finite types, and checks properties. Lean *verifies* the certificate rather than
trusting it. A complete worked file is
[`CRNT/Interop/CodegenExamples.lean`](../CRNT/Interop/CodegenExamples.lean).

## Emission contract

A generated file declares, in order:

1. a `Species` inductive type deriving `DecidableEq, Fintype, Repr`;
2. one `def` per complex, of type `Complex Species`;
3. a `Rxn` inductive type (one constructor per reaction channel) deriving
   `DecidableEq, Fintype, Repr`;
4. a `reaction : Rxn → Reaction Species` map;
5. the `Network` value with `decEqR := inferInstance`, `fintypeR := inferInstance`;
6. the property checks.

```lean
import CRNT
open CRNT

inductive Species | A | B deriving DecidableEq, Fintype, Repr
open Species

def cA : Complex Species := fun s => match s with | A => 1 | B => 0
def cB : Complex Species := fun s => match s with | A => 0 | B => 1

inductive Rxn | r1 | r2 deriving DecidableEq, Fintype, Repr

def reaction : Rxn → Reaction Species
  | .r1 => { source := cA, target := cB }
  | .r2 => { source := cB, target := cA }

def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := reaction }
```

## Checkable claims

- **Complex count**: `example : N.numComplexes = 2 := by decide`.
- **Directed reachability**: emit a walk (a list of complexes) and check it:
  `N.reaches_of_walk c d walk (by decide) (by decide) : N.Reaches c d`. The first
  `decide` confirms the walk ends at `d`; the second confirms each step is a reaction.
- **Weak reversibility**: supply a return walk per reaction:

  ```lean
  example : N.WeaklyReversible := by
    intro r; cases r
    · exact N.reaches_of_walk cB cA [cA] (by decide) (by decide)
    · exact N.reaches_of_walk cA cB [cB] (by decide) (by decide)
  ```

## JSON interchange schema

The recommended pipeline is *codegen*, not in-Lean parsing: a tool consumes JSON/SBML
and emits the Lean file above. A minimal JSON network:

```json
{
  "species": ["A", "B"],
  "complexes": [
    {"id": "A", "stoich": {"A": 1}},
    {"id": "B", "stoich": {"B": 1}}
  ],
  "reactions": [
    {"id": "r1", "source": "A", "target": "B"},
    {"id": "r2", "source": "B", "target": "A"}
  ]
}
```

Each `species` entry becomes a `Species` constructor, each `complexes` entry a complex
`def`, and each `reactions` entry a `Rxn` constructor and a `reaction` arm.

## Throughput path: the `analyze` contract

Codegen is the *provenance* path: Lean kernel-checks each emitted network. For bulk scoring where a
stable JSON contract matters more than a per-network kernel certificate, the `analyze` executable
reads a `NetworkData` (or array) and returns its structural invariants as JSON at native speed, with
no per-network elaboration. It uses compiled evaluation (a labeled trust boundary), with library
bridges relating each field to its propositional definition. See
[`analyze-contract.md`](analyze-contract.md).

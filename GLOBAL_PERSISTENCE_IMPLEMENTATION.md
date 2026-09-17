# Global persistence implementation status

## Implemented as proofs

- global quantifier layer for `PersistentFrom` and boundary-omega persistence;
- global GAC specialization from `StructurallyPersistent`;
- global no-critical-siphon boundary exclusion;
- **weak reversibility implies endotacticity**;
- compatibility bridge from the legacy source-triggered strong-endotactic predicate to the standard
  stoichiometric trigger on weakly reversible networks;
- a single-linkage class implies every occurring complex is linked;
- weak reversibility + single linkage gives directed reachability between every pair of occurring
  complexes;
- **weak reversibility + deficiency zero + no critical siphon implies `StructurallyPersistent`**;
- proof-carrying global persistence, boundary-omega, and permanence certificate wrappers;
- analyzer bridge: `persistenceCertified = true` constructs `GlobalPersistenceCertificate`.

## Implemented definitions / theorem interfaces

- standard stoichiometrically triggered `StronglyEndotacticStd`;
- flow/rate/network-level permanence quantifiers;
- exact finite enabled reaction pathways;
- drainable and self-replicable species sets/siphons;
- minimal critical siphons;
- tier monomials, tier comparisons, proper/transversal tier sequences, top source tier, and
  `TierDescending`;
- explicit proposition contracts for:
  - strong-endotactic permanence;
  - single-linkage strong endotacticity;
  - single-linkage structural persistence;
  - strong-endotactic ↔ tier-descending;
  - tier-descending → structural permanence;
  - minimal-critical-siphon drainable/self-replicable dichotomy;
  - no-drainable-siphon persistence;
  - non-autocatalytic weakly-reversible persistence;
  - the general Persistence Conjecture at strong-certificate and omega-limit levels.

These contracts are ordinary `Prop` definitions. They are not axioms and cannot be used without an
actual proof.

## Validation limitation in this environment

The supplied archive contains no `.lake` dependency cache, and this execution environment has no
`lean`, `lake`, or `elan` executable. Consequently the new code could not be elaborated against Lean
4.31/Mathlib here. Static checks performed before packaging:

- every local `CRNT.*` import resolves to a source file;
- the local CRNT import graph is acyclic;
- newly added modules contain no `sorry`, `admit`, or `axiom` command;
- `test/GlobalPersistenceSmoke.lean` checks the intended public names when run in a configured Lean
  environment.

The first action on a normal development machine should therefore be `lake update`/cache setup
followed by `lake build` and `lake env lean test/GlobalPersistenceSmoke.lean`; any elaboration errors
should be treated as integration issues, not papered over with assumptions.

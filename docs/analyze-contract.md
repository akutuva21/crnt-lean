# The `analyze` JSON contract

The `analyze` executable computes a network's structural invariants from data, at native speed, with
no per-network elaboration. It is the bulk-scoring counterpart to the codegen certificate workflow
([`generated-certificates.md`](generated-certificates.md)): where codegen emits a kernel-checked Lean
file per network, `analyze` reads a network as JSON and returns its invariants as JSON. The contract
is owned here and versioned, so external consumers depend on a stable shape rather than internal
symbol names.

## Trust boundary

`analyze` uses **compiled evaluation** (compiler trust), so it sits outside the `CRNT` library's
axiom-clean guarantee. Each reported field is a computable companion of the library theory, and the
library carries a bridge relating it to the propositional definition: `analyze_deficiency_eq`,
`analyze_stoichRank_eq`, `analyze_numLinkageClasses_eq`, `analyze_conservationLawDim_eq`,
`analyze_weaklyReversible_eq`, `analyze_acrSpecies_eq`, and `analyze_hasSiphon_eq`
(`CRNT/Interop/Analysis.lean`). When a result needs an axiom-clean kernel certificate for a specific
network, use the codegen contract instead.

## Input: `NetworkData`

A network as a species count and a list of reactions, each a pair of nonnegative integer coefficient
vectors indexed by species position. A coefficient vector shorter than `numSpecies` is zero-padded; a
longer one is truncated — reconstruction (to `Network (Fin numSpecies)`) is total.

```json
{
  "numSpecies": 2,
  "reactions": [
    {"source": [1, 0], "target": [0, 1]},
    {"source": [0, 1], "target": [1, 0]}
  ]
}
```

The input may also be a JSON **array** of such objects, in which case the output is the array of
their analyses (the bulk path: one process invocation scores many networks).

## Output: `Analysis`

```json
{
  "version": 3,
  "numSpecies": 2,
  "numComplexes": 2,
  "numReactions": 2,
  "numLinkageClasses": 1,
  "numStrongLinkageClasses": 1,
  "stoichRank": 1,
  "conservationLawDim": 1,
  "deficiency": 0,
  "weaklyReversible": true,
  "acrSpecies": [],
  "hasSiphon": true
}
```

| Field | Type | Meaning | Companion |
|---|---|---|---|
| `version` | int | contract version (`analysisVersion`) | — |
| `numSpecies` | int | species count (the `Fin n` carrier size) | — |
| `numComplexes` | int | distinct complexes `n` | `numComplexes` |
| `numReactions` | int | reaction channels | `numReactions` |
| `numLinkageClasses` | int | linkage classes `ℓ` | `computeNumLinkageClasses` |
| `numStrongLinkageClasses` | int | strong linkage classes | `numStrongLinkageClasses` |
| `stoichRank` | int | stoichiometric rank `s` | `computeRank stoichMatrixQ` |
| `conservationLawDim` | int | conservation laws `numSpecies − s` (cokernel dim) | `finrank (orthSum stoichSubspace)` |
| `deficiency` | int | `δ = n − ℓ − s` | `computableDeficiency` |
| `weaklyReversible` | bool | weak reversibility | `decide WeaklyReversible` |
| `acrSpecies` | int[] | species with a structural Shinar–Feinberg ACR witness | `acrSpecies` (`HasShinarFeinbergPair`) |
| `hasSiphon` | bool | a nonempty siphon exists | `IsSiphon` (powerset search) |

`acrSpecies` reports the decidable structural fragment of Shinar–Feinberg ACR (two non-terminal
complexes in distinct linkage classes differing in exactly one species). The deficiency-one side
condition is not a finite decision and is asserted by the consuming objective, not by `analyze`.

`hasSiphon` enumerates the species powerset (`2^numSpecies`, fine for small networks) and reports
whether any nonempty siphon exists. It is one-sided: `false` soundly excludes any *critical* siphon
(`analyze_hasNoCriticalSiphon_of_hasSiphon_false`), hence — with weak reversibility and complex
balancing — persistence; `true` is inconclusive. The exclusion is narrow in practice: for a closed
network the full species set is always a siphon, so `hasSiphon = false` arises only with a synthesis
reaction (`0 → y`). Deciding *criticality* directly is Farkas-blocked (sign-restricted kernel
feasibility, absent in Mathlib v4.31), so `hasCriticalSiphon` is not offered; the minimal-siphon
structure (next) is the actionable signal — the consumer runs its own feasibility check per siphon.

The deficiency assembly `δ = n − ℓ − s` is owned by the library (`computableDeficiency`), not the
consumer: `computeNumLinkageClasses` supplies a computable `ℓ` (the quotient `numLinkageClasses` does
not evaluate), and `deficiency_eq_computableDeficiency` bridges the assembly to the propositional
`deficiency`.

## Versioning

`version` tags the field set. It is bumped whenever fields are added or their meaning changes, so a
consumer can detect a contract it does not understand. New per-property companions (multistationarity
capacity, ACR, deficiency-one) join the record as they land, raising the version.

## Usage

```shell
echo '{"numSpecies":2,"reactions":[{"source":[1,0],"target":[0,1]},
      {"source":[0,1],"target":[1,0]}]}' | lake exe analyze
```

Invalid input is reported on stderr with a nonzero exit; the trust boundary means a malformed network
never yields a structural verdict.

## Modules

- `CRNT/Interop/NetworkData.lean`: `NetworkData`/`ReactionData`, `FromJson`/`ToJson`, and `toNetwork`.
- `CRNT/Interop/Analysis.lean`: `Analysis`, `analyze`, and the field bridges.
- `CRNT/Decision/ComputableDeficiency.lean`: `computeNumLinkageClasses`, `computableDeficiency`, and
  `deficiency_eq_computableDeficiency`.
- `CRNT/Decision/ACRCheck.lean`: `HasShinarFeinbergPair`, `acrSpecies`, and `mem_acrSpecies`.
- `CRNT/Dynamics/Siphon.lean`: `IsSiphon`, `HasNoCriticalSiphon`, and the exclusion lemma
  `hasNoCriticalSiphon_of_forall_not_isSiphon`.
- `CRNT/LinearAlgebra/OrthogonalComplement.lean`: `orthSum` and `finrank_orthSum` (conservation laws).
- `Analyze.lean`: the `lake exe analyze` entry point.

## Related documents

- [`generated-certificates.md`](generated-certificates.md): the per-network kernel-checked codegen
  contract — the provenance path, complementary to this throughput path.
- [`decidability.md`](decidability.md): the decision procedures and computable companions the fields
  rest on.

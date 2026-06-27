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
derived fields each have a bridge in `CRNT/Interop/Analysis.lean` relating the reported value to its
propositional definition: `analyze_deficiency_eq`, `analyze_stoichRank_eq`,
`analyze_numLinkageClasses_eq`, `analyze_conservationLawDim_eq`, `analyze_weaklyReversible_eq`,
`analyze_acrSpecies_eq`, `analyze_hasSiphon_eq`, `mem_analyze_minimalSiphons`,
`analyze_srSignConsistent_eq`, and `analyze_hasCriticalSiphon_eq`. The one-sided
exclusion `analyze_hasNoCriticalSiphon_of_hasSiphon_false` is proved there too. When a result needs an
axiom-clean kernel certificate for a specific network, use the codegen contract instead.

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

`analyze` writes the record with `Json.compress`, which sorts the object keys alphabetically:

```json
{"acrSpecies":[],"conservationLawDim":1,"deficiency":0,"hasCriticalSiphon":false,
 "hasSiphon":true,"minimalSiphons":[[0,1]],"numComplexes":2,"numLinkageClasses":1,
 "numReactions":2,"numSpecies":2,"numStrongLinkageClasses":1,"srSignConsistent":false,
 "stoichRank":1,"version":7,"weaklyReversible":true}
```

The fields, in their declaration order on the `Analysis` structure:

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
| `minimalSiphons` | int[][] | support-minimal siphons, each an ascending index array | `IsMinimalSiphon` |
| `srSignConsistent` | bool | consistent signed species–reaction cover condition holds | `decide ConsistentSRSign` |
| `hasCriticalSiphon` | bool | a critical siphon exists (no positive conservation law on its support) | `decide HasCriticalSiphon` |

`Analysis` derives `FromJson, ToJson, Repr, DecidableEq`; the `ToJson` instance is what serializes the
record.

`acrSpecies` reports the decidable structural fragment of Shinar–Feinberg ACR (two non-terminal
complexes in distinct linkage classes differing in exactly one species). The deficiency-one side
condition is not a finite decision and is asserted by the consuming objective, not by `analyze`.

`hasSiphon` enumerates the species powerset (`2^numSpecies`, fine for small networks) and reports
whether any nonempty siphon exists. It is one-sided: `false` soundly excludes any *critical* siphon
(`analyze_hasNoCriticalSiphon_of_hasSiphon_false`), hence — with weak reversibility and complex
balancing — persistence; `true` is inconclusive. The exclusion is narrow in practice: for a closed
network the full species set is always a siphon, so `hasSiphon = false` arises only with a synthesis
reaction (`0 → y`).

`hasCriticalSiphon` is `decide HasCriticalSiphon`: the full critical-siphon verdict. A siphon is
critical iff it carries no positive conservation law on its exact support; `hasCriticalSiphon` reports
whether any nonempty siphon is critical. Each candidate's criticality reduces to a rational linear
feasibility problem (sign-restricted conservation-cone membership), decided by Fourier–Motzkin
elimination — the constructive content of Farkas' lemma. A species enumeration is drawn computably
from the `Fintype` and the decision lifted through the subsingleton of `Decidable`, so the verdict is
computable. It is two-sided: `false` soundly establishes the absence of a critical siphon, hence —
with weak reversibility and complex balancing — persistence.

`minimalSiphons` lists the support-minimal siphons (each as an ascending species-index array). These
are the candidate critical siphons: a siphon is critical iff it carries no positive conservation law
on its support. Enumeration tests minimality across the powerset (`~4^numSpecies` in the worst case —
fine for the small networks evaluated here).

`srSignConsistent` is `decide ConsistentSRSign`: the consistent signed species–reaction cover
condition, the decidable sign fragment of the Craciun–Feinberg species–reaction graph injectivity
criterion. Over every restricted species set, every reaction-choice cover carries a nonnegative
signed-incidence weight, read in `ℤ` where the order is decidable. It is **not** a full injectivity
verdict: discharging mass-action injectivity (and monostationarity) on a positive compatibility
class additionally requires the chart-box, positivity, positive-diagonal, and coordinate-selection
hypotheses, which the consumer supplies. When `true`, the network satisfies the verdict's sign
hypothesis (`hweight_of_consistentSRSign`).

The deficiency assembly `δ = n − ℓ − s` is owned by the library (`computableDeficiency`), not the
consumer: `computeNumLinkageClasses` supplies a computable `ℓ` (the quotient `numLinkageClasses` does
not evaluate), and `deficiency_eq_computableDeficiency` bridges the assembly to the propositional
`deficiency`.

## Versioning

`version` is the value of `analysisVersion` (`CRNT/Interop/Analysis.lean`), currently `7`. It tags the
field set and increments whenever a field is added or its meaning changes, so a consumer can detect a
contract it does not understand. A new per-property companion raises the version when it joins the
record.

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
- `CRNT/Dynamics/Siphon.lean`: `IsSiphon`, `IsMinimalSiphon`, `minimalSiphons`, `HasNoCriticalSiphon`,
  and the exclusion lemma `hasNoCriticalSiphon_of_forall_not_isSiphon`.
- `CRNT/Multistationarity/SRSignDecidable.lean`: `ConsistentSRSign`, its `Decidable` instance, and
  `hweight_of_consistentSRSign` (the SR-sign injectivity fragment).
- `CRNT/Decision/CriticalSiphonDecide.lean`: `HasCriticalSiphon`, its computable `Decidable`
  instance (rational feasibility by Fourier–Motzkin elimination), and `supportedFeasSystem`.
- `CRNT/LinearAlgebra/OrthogonalComplement.lean`: `orthSum` and `finrank_orthSum` (conservation laws).
- `Analyze.lean`: the `lake exe analyze` entry point.

## Related documents

- [`generated-certificates.md`](generated-certificates.md): the per-network kernel-checked codegen
  contract — the provenance path, complementary to this throughput path.
- [`decidability.md`](decidability.md): the decision procedures and computable companions the fields
  rest on.

import CRNT.Interop.NetworkData
import CRNT.Decision.ComputableDeficiency
import CRNT.Decision.DirectedReachability
import CRNT.Decision.ACRCheck
import CRNT.Dynamics.Siphon
import CRNT.LinearAlgebra.OrthogonalComplement
import CRNT.Multistationarity.SRSignDecidable

/-!
# One-call structural analysis

`analyze` maps a `NetworkData` to an `Analysis`: the network's structural invariants in one
computable record, ready to serialize as JSON. It is the stable contract an external evaluator
consumes — every field is a computable companion of the library theory, so a compiled analyzer
produces them at native speed with no per-network elaboration, and the library (not the consumer)
owns the `δ = n − ℓ − s` assembly.

Each numeric field has a bridge back to its propositional definition: `analyze_deficiency_eq`
(`δ`), `analyze_stoichRank_eq` (`s`), `analyze_numLinkageClasses_eq` (`ℓ`), and
`analyze_conservationLawDim_eq` (the dimension of the conservation-law space, `orthSum` of the
stoichiometric subspace). The `weaklyReversible` flag is `decide N.WeaklyReversible`, sound by the
`Decidable` instance. `acrSpecies` lists the species carrying the structural Shinar–Feinberg ACR
witness (`analyze_acrSpecies_eq`), the decidable fragment; the deficiency-one side condition is
supplied by the consumer. `hasSiphon` flags the existence of a nonempty siphon
(`analyze_hasSiphon_eq`); when `false` it soundly excludes any critical siphon
(`analyze_hasNoCriticalSiphon_of_hasSiphon_false`), the Farkas-free persistence design filter.
`minimalSiphons` lists the support-minimal siphons as ascending species-index arrays
(`mem_analyze_minimalSiphons`) — the species sets a consumer's criticality feasibility check tests.
`srSignConsistent` is `decide N.ConsistentSRSign` (`analyze_srSignConsistent_eq`), the decidable
signed species–reaction cover fragment of the Craciun–Feinberg injectivity criterion; it is not a
full injectivity verdict, which additionally needs the consumer's chart-box, positivity, and
positive-diagonal hypotheses.

`version` tags the JSON contract; bump it whenever the field set changes.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Interop.NetworkData`,
`CRNT.Decision.ComputableDeficiency`, `CRNT.Decision.DirectedReachability`.
-/

namespace CRNT

open Lean (FromJson ToJson)
open CRNT.GaussianRank

/-- The version of the `Analysis` JSON contract. Bump on any field-set change. -/
def analysisVersion : Nat := 6

/-- The structural invariants of a network, as a JSON-serializable record. The numeric fields are
the computable companions of the library theory; `deficiency` is `n − ℓ − s` assembled here. -/
structure Analysis where
  /-- The contract version (`analysisVersion`). -/
  version : Nat
  /-- The number of species. -/
  numSpecies : Nat
  /-- The number of distinct complexes `n`. -/
  numComplexes : Nat
  /-- The number of reaction channels. -/
  numReactions : Nat
  /-- The number of linkage classes `ℓ`. -/
  numLinkageClasses : Nat
  /-- The number of strong linkage classes. -/
  numStrongLinkageClasses : Nat
  /-- The stoichiometric rank `s`. -/
  stoichRank : Nat
  /-- The dimension of the conservation-law space, `numSpecies − stoichRank`: the number of
  independent linear conservation laws (the cokernel of the stoichiometric map). -/
  conservationLawDim : Nat
  /-- The deficiency `δ = n − ℓ − s`. -/
  deficiency : Nat
  /-- Whether the network is weakly reversible. -/
  weaklyReversible : Bool
  /-- The species indices carrying a structural Shinar–Feinberg ACR witness (decidable fragment;
  the deficiency-one side condition is supplied by the consumer). -/
  acrSpecies : Array Nat
  /-- Whether the network has a nonempty siphon. When `false`, the network has no critical siphon,
  so (weakly reversible and complex balanced) it is persistent — a sound design filter. -/
  hasSiphon : Bool
  /-- The support-minimal siphons, each as an ascending array of species indices. These are the
  candidate critical siphons a persistence/extinction analysis tests for feasibility. -/
  minimalSiphons : Array (Array Nat)
  /-- Whether the network satisfies the consistent signed species–reaction cover condition
  (`ConsistentSRSign`): the decidable sign fragment of the Craciun–Feinberg species–reaction graph
  injectivity criterion. When `true`, the network discharges the verdict's sign hypothesis; a full
  injectivity verdict additionally needs the chart-box, positivity, and positive-diagonal
  hypotheses the consumer supplies. -/
  srSignConsistent : Bool
  deriving FromJson, ToJson, Repr, DecidableEq

namespace NetworkData

/-- **Analyze a data-driven network**: compute its structural invariants in one record. -/
def analyze (d : NetworkData) : Analysis :=
  let N := d.toNetwork
  { version := analysisVersion
    numSpecies := d.numSpecies
    numComplexes := N.numComplexes
    numReactions := N.numReactions
    numLinkageClasses := N.computeNumLinkageClasses
    numStrongLinkageClasses := N.numStrongLinkageClasses
    stoichRank := computeRank N.stoichMatrixQ
    conservationLawDim := d.numSpecies - computeRank N.stoichMatrixQ
    deficiency := N.computableDeficiency
    weaklyReversible := decide N.WeaklyReversible
    acrSpecies := (((List.finRange d.numSpecies).filter
      (fun s => decide (N.HasShinarFeinbergPair s))).map Fin.val).toArray
    hasSiphon := decide (∃ P : Finset (Fin d.numSpecies), P.Nonempty ∧ N.IsSiphon P)
    minimalSiphons := (((List.finRange d.numSpecies).sublists.filter
      (fun l => decide (N.IsMinimalSiphon l.toFinset))).map
      (fun l => (l.map Fin.val).toArray)).toArray
    srSignConsistent := decide N.ConsistentSRSign }

/-- The reported deficiency is the network's deficiency. -/
theorem analyze_deficiency_eq (d : NetworkData) :
    (d.analyze).deficiency = d.toNetwork.deficiency :=
  (d.toNetwork.deficiency_eq_computableDeficiency).symm

/-- The reported stoichiometric rank is the network's stoichiometric rank. -/
theorem analyze_stoichRank_eq (d : NetworkData) :
    (d.analyze).stoichRank = d.toNetwork.stoichRank :=
  (d.toNetwork.stoichRank_eq_computeRank).symm

/-- The reported conservation-law dimension is the dimension of the conservation-law space:
the `orthSum` (dot-product complement) of the stoichiometric subspace. -/
theorem analyze_conservationLawDim_eq (d : NetworkData) :
    (d.analyze).conservationLawDim
      = Module.finrank ℝ (orthSum d.toNetwork.stoichSubspace) := by
  show d.numSpecies - computeRank d.toNetwork.stoichMatrixQ
    = Module.finrank ℝ (orthSum d.toNetwork.stoichSubspace)
  rw [finrank_orthSum, Fintype.card_fin, ← d.toNetwork.stoichRank_eq_computeRank]
  simp only [Network.stoichRank]

/-- The reported linkage-class count is the network's linkage-class count. -/
theorem analyze_numLinkageClasses_eq (d : NetworkData) :
    (d.analyze).numLinkageClasses = d.toNetwork.numLinkageClasses :=
  d.toNetwork.computeNumLinkageClasses_eq_numLinkageClasses

/-- The reported weak-reversibility flag is `true` exactly when the network is weakly reversible. -/
theorem analyze_weaklyReversible_eq (d : NetworkData) :
    (d.analyze).weaklyReversible = true ↔ d.toNetwork.WeaklyReversible :=
  decide_eq_true_iff

/-- A species index is reported in `acrSpecies` exactly when that species carries a structural
Shinar–Feinberg ACR witness. -/
theorem analyze_acrSpecies_eq (d : NetworkData) (s : Fin d.numSpecies) :
    s.val ∈ (d.analyze).acrSpecies ↔ d.toNetwork.HasShinarFeinbergPair s := by
  show s.val ∈ (((List.finRange d.numSpecies).filter
      (fun t => decide (d.toNetwork.HasShinarFeinbergPair t))).map Fin.val).toArray ↔ _
  simp only [List.mem_toArray, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, hav⟩
    rwa [Fin.val_injective hav] at ha
  · intro h
    exact ⟨s, h, rfl⟩

/-- The reported siphon flag is `true` exactly when the network has a nonempty siphon. -/
theorem analyze_hasSiphon_eq (d : NetworkData) :
    (d.analyze).hasSiphon = true ↔
      ∃ P : Finset (Fin d.numSpecies), P.Nonempty ∧ d.toNetwork.IsSiphon P :=
  decide_eq_true_iff

/-- **Sound persistence filter.** When the siphon flag is `false`, the network has no critical
siphon (every critical siphon is a nonempty siphon), so with weak reversibility and complex
balancing it is persistent. The exclusion is Farkas-free — only the decidable `IsSiphon` is used. -/
theorem analyze_hasNoCriticalSiphon_of_hasSiphon_false (d : NetworkData)
    (h : (d.analyze).hasSiphon = false) : d.toNetwork.HasNoCriticalSiphon := by
  apply Network.hasNoCriticalSiphon_of_forall_not_isSiphon
  intro P hP hsiph
  have htrue : (d.analyze).hasSiphon = true := (analyze_hasSiphon_eq d).mpr ⟨P, hP, hsiph⟩
  simp [htrue] at h

/-- An entry of `minimalSiphons` is exactly the ascending index image of a minimal siphon: it is
present iff some subset list `l` of the species whose underlying set `l.toFinset` is a minimal
siphon maps to it. -/
theorem mem_analyze_minimalSiphons (d : NetworkData) (arr : Array Nat) :
    arr ∈ (d.analyze).minimalSiphons ↔
      ∃ l : List (Fin d.numSpecies), l ∈ (List.finRange d.numSpecies).sublists ∧
        d.toNetwork.IsMinimalSiphon l.toFinset ∧ arr = (l.map Fin.val).toArray := by
  show arr ∈ (((List.finRange d.numSpecies).sublists.filter
      (fun l => decide (d.toNetwork.IsMinimalSiphon l.toFinset))).map
      (fun l => (l.map Fin.val).toArray)).toArray ↔ _
  simp only [List.mem_toArray, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨l, ⟨hl, hmin⟩, harr⟩
    exact ⟨l, hl, hmin, harr.symm⟩
  · rintro ⟨l, hl, hmin, harr⟩
    exact ⟨l, ⟨hl, hmin⟩, harr.symm⟩

/-- The reported SR-sign-consistency flag is `true` exactly when the network satisfies the
consistent signed species–reaction cover condition. It exposes only the decidable sign fragment of
the Craciun–Feinberg injectivity criterion; the chart-box, positivity, and positive-diagonal
hypotheses for a full injectivity verdict are supplied by the consumer. -/
theorem analyze_srSignConsistent_eq (d : NetworkData) :
    (d.analyze).srSignConsistent = true ↔ d.toNetwork.ConsistentSRSign :=
  decide_eq_true_iff

end NetworkData

end CRNT

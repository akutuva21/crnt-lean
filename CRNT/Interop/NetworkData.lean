import CRNT.Basic.Network
import Mathlib.Lean.Json

/-!
# Data-driven networks

A `Network S` carries its reactions as a map out of an abstract index type, which an external tool
reconstructs by emitting fresh Lean inductives (the codegen contract in
`docs/generated-certificates.md`). For bulk analysis it is cheaper to build the network from *data*:
`NetworkData` is a plain, JSON-serializable description — a species count and a list of reactions,
each a pair of nonnegative coefficient vectors — and `toNetwork` reconstructs a concrete
`Network (Fin numSpecies)` from it.

The generic decision procedures hold for the `Fin n` carrier, so a network built this way supports
every computable companion (`numComplexes`, `computeNumLinkageClasses`, `computeRank`,
`computableDeficiency`, `WeaklyReversible`, …) with no per-network elaboration. The `FromJson`/
`ToJson` instances give a stable interchange format owned by the library.

Coefficient arrays are read with `Array.getD … 0`, so a reaction shorter than `numSpecies` pads with
zeros and a longer one is truncated; reconstruction is therefore total.

Depends on: `CRNT.Basic.Network`, `Mathlib.Lean.Json`.
-/

namespace CRNT

open Lean (FromJson ToJson)

/-- One reaction as data: the source and target complexes as nonnegative coefficient vectors,
indexed by species position. -/
structure ReactionData where
  /-- Source-complex coefficients, by species index. -/
  source : Array ℕ
  /-- Target-complex coefficients, by species index. -/
  target : Array ℕ
  deriving FromJson, ToJson, Repr, DecidableEq

/-- A chemical reaction network as JSON-serializable data: a species count and a list of reactions.
`toNetwork` reconstructs a concrete `Network (Fin numSpecies)`. -/
structure NetworkData where
  /-- The number of species; the carrier is `Fin numSpecies`. -/
  numSpecies : ℕ
  /-- The reaction channels, in order. -/
  reactions : Array ReactionData
  deriving FromJson, ToJson, Repr, DecidableEq

namespace NetworkData

/-- The complex with the given coefficient vector over `Fin n`, padding missing entries with `0`. -/
def toComplex (n : ℕ) (coeffs : Array ℕ) : Complex (Fin n) :=
  fun s => coeffs.getD s.val 0

/-- **Reconstruct a concrete network from the data.** The carrier is `Fin numSpecies` and the
reaction index type is `Fin reactions.size`; each channel's source and target are read off its
coefficient vectors. -/
def toNetwork (d : NetworkData) : Network (Fin d.numSpecies) where
  R := Fin d.reactions.size
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction r :=
    { source := toComplex d.numSpecies d.reactions[r].source
      target := toComplex d.numSpecies d.reactions[r].target }

/-- The reconstructed network has one reaction channel per entry of `reactions`. -/
@[simp] theorem toNetwork_numReactions (d : NetworkData) :
    d.toNetwork.numReactions = d.reactions.size :=
  Fintype.card_fin d.reactions.size

end NetworkData

end CRNT

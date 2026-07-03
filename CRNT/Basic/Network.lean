import CRNT.Basic.Reaction
import Mathlib.Data.Fintype.Card

/-!
# Networks

A finite chemical reaction network over a species type `S`. Reactions are indexed by
a finite type `R` so that parallel reactions (distinct reaction channels with the same
source and target) are representable and duplicate-erasure is avoided.

It defines `Network`, exposes the reaction index type's
`Fintype`/`DecidableEq` instances, and computes the finite set of complexes
together with its cardinality.

Depends on: `CRNT.Basic.Reaction`.
-/

namespace CRNT

/-- A finite chemical reaction network: a finite index type `R` of reactions, each
mapped to a `Reaction` over the species type `S`. The `decEqR` and `fintypeR`
fields carry the finiteness data so that `Network` is a plain structure (no
instance-implicit fields). -/
structure Network (S : Type) [DecidableEq S] [Fintype S] where
  /-- The reaction index type. -/
  R : Type
  /-- Decidable equality on the reaction index type. -/
  decEqR : DecidableEq R
  /-- Finiteness of the reaction index type. -/
  fintypeR : Fintype R
  /-- The reaction associated to each index. -/
  reaction : R → Reaction S

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [instance] Network.decEqR Network.fintypeR

/-- The finite set of complexes appearing as a source or target of some reaction. -/
def complexes (N : Network S) : Finset (Complex S) :=
  (Finset.univ.image fun r : N.R => (N.reaction r).source) ∪
  (Finset.univ.image fun r : N.R => (N.reaction r).target)

/-- The number of distinct complexes in the network, written `n` in `δ = n - ℓ - s`. -/
def numComplexes (N : Network S) : ℕ := N.complexes.card

/-- The number of reactions (counting parallel reactions separately). -/
def numReactions (N : Network S) : ℕ := Fintype.card N.R

/-- A source complex of a reaction is a complex of the network. -/
theorem source_mem_complexes (N : Network S) (r : N.R) :
    (N.reaction r).source ∈ N.complexes := by
  apply Finset.mem_union_left
  exact Finset.mem_image_of_mem _ (Finset.mem_univ r)

/-- A target complex of a reaction is a complex of the network. -/
theorem target_mem_complexes (N : Network S) (r : N.R) :
    (N.reaction r).target ∈ N.complexes := by
  apply Finset.mem_union_right
  exact Finset.mem_image_of_mem _ (Finset.mem_univ r)

end Network

end CRNT

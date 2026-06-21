import CRNT.Stoich.Subspace

/-!
# Interconnection of reaction networks

Two reaction networks over a common species type `S` are *interconnected* by forming the
disjoint union of their reaction channels, indexed by the sum `N₁.R ⊕ N₂.R`. The
interconnection shares the species pool: a reaction from either component acts on the same
concentration vector.

The stoichiometric subspace composes as a join: the span of all reaction vectors of the
interconnection is the supremum of the two component subspaces, so each component's
stoichiometric subspace embeds into the interconnection's.

This module is **stable**. Depends on: `CRNT.Stoich.Subspace`, Mathlib linear algebra.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The interconnection** of two networks over a shared species type: the reactions are
the disjoint union of the components' reactions, indexed by `N₁.R ⊕ N₂.R`, acting on the
common species pool. -/
def interconnect (N₁ N₂ : Network S) : Network S where
  R := N₁.R ⊕ N₂.R
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := Sum.elim N₁.reaction N₂.reaction

@[simp] theorem interconnect_reaction_inl (N₁ N₂ : Network S) (r : N₁.R) :
    (N₁.interconnect N₂).reaction (Sum.inl r) = N₁.reaction r := rfl

@[simp] theorem interconnect_reaction_inr (N₁ N₂ : Network S) (r : N₂.R) :
    (N₁.interconnect N₂).reaction (Sum.inr r) = N₂.reaction r := rfl

@[simp] theorem interconnect_reactionVector_inl (N₁ N₂ : Network S) (r : N₁.R) :
    (N₁.interconnect N₂).reactionVector (Sum.inl r) = N₁.reactionVector r := rfl

@[simp] theorem interconnect_reactionVector_inr (N₁ N₂ : Network S) (r : N₂.R) :
    (N₁.interconnect N₂).reactionVector (Sum.inr r) = N₂.reactionVector r := rfl

/-- The reaction vectors of the interconnection are the union of the components' reaction
vectors. -/
theorem interconnect_reactionVectors (N₁ N₂ : Network S) :
    (N₁.interconnect N₂).reactionVectors = N₁.reactionVectors ∪ N₂.reactionVectors := by
  unfold reactionVectors
  ext v
  constructor
  · rintro ⟨r | r, rfl⟩
    · exact Or.inl ⟨r, rfl⟩
    · exact Or.inr ⟨r, rfl⟩
  · rintro (⟨r, rfl⟩ | ⟨r, rfl⟩)
    · exact ⟨Sum.inl r, rfl⟩
    · exact ⟨Sum.inr r, rfl⟩

/-- **The stoichiometric subspace of an interconnection is the join** of the components'
stoichiometric subspaces. -/
theorem stoichSubspace_interconnect (N₁ N₂ : Network S) :
    (N₁.interconnect N₂).stoichSubspace = N₁.stoichSubspace ⊔ N₂.stoichSubspace := by
  unfold stoichSubspace
  rw [interconnect_reactionVectors, Submodule.span_union]

/-- The first component's stoichiometric subspace embeds into the interconnection's. -/
theorem stoichSubspace_le_interconnect_left (N₁ N₂ : Network S) :
    N₁.stoichSubspace ≤ (N₁.interconnect N₂).stoichSubspace := by
  rw [stoichSubspace_interconnect]
  exact le_sup_left

/-- The second component's stoichiometric subspace embeds into the interconnection's. -/
theorem stoichSubspace_le_interconnect_right (N₁ N₂ : Network S) :
    N₂.stoichSubspace ≤ (N₁.interconnect N₂).stoichSubspace := by
  rw [stoichSubspace_interconnect]
  exact le_sup_right

/-- A two-reaction example: over `S = Fin 2`, `N₁` is the single reaction `A → B` and `N₂`
is the single reaction `B → A`. Their interconnection carries both, and `N₁`'s
stoichiometric subspace embeds into the interconnection's. -/
example :
    let A : Complex (Fin 2) := Pi.single 0 1
    let B : Complex (Fin 2) := Pi.single 1 1
    let N₁ : Network (Fin 2) :=
      { R := Unit, decEqR := inferInstance, fintypeR := inferInstance,
        reaction := fun _ => { source := A, target := B } }
    let N₂ : Network (Fin 2) :=
      { R := Unit, decEqR := inferInstance, fintypeR := inferInstance,
        reaction := fun _ => { source := B, target := A } }
    N₁.stoichSubspace ≤ (N₁.interconnect N₂).stoichSubspace :=
  stoichSubspace_le_interconnect_left _ _

end Network

end CRNT

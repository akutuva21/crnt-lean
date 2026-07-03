import CRNT.Compose.Interconnect
import CRNT.Dynamics.Siphon

/-!
# Siphons of an interconnection

A species set is a siphon of an interconnection exactly when it is a siphon of each
component. The interconnection's reactions are the disjoint union of the components'
reactions acting on the shared species pool, so the reactant and product relations of a
summand index `Sum.inl r` or `Sum.inr r` coincide with those of the component reaction.
The siphon condition — every reaction producing a species of `P` consumes a species of
`P` — therefore quantifies over both components' reactions independently, splitting as a
conjunction of the two component siphon conditions.

Depends on: `CRNT.Compose.Interconnect`,
`CRNT.Dynamics.Siphon`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S] {N₁ N₂ : Network S}

@[simp] theorem interconnect_isReactant_inl (r : N₁.R) (s : S) :
    (N₁.interconnect N₂).IsReactant (Sum.inl r) s ↔ N₁.IsReactant r s := Iff.rfl

@[simp] theorem interconnect_isReactant_inr (r : N₂.R) (s : S) :
    (N₁.interconnect N₂).IsReactant (Sum.inr r) s ↔ N₂.IsReactant r s := Iff.rfl

@[simp] theorem interconnect_isProduct_inl (r : N₁.R) (s : S) :
    (N₁.interconnect N₂).IsProduct (Sum.inl r) s ↔ N₁.IsProduct r s := Iff.rfl

@[simp] theorem interconnect_isProduct_inr (r : N₂.R) (s : S) :
    (N₁.interconnect N₂).IsProduct (Sum.inr r) s ↔ N₂.IsProduct r s := Iff.rfl

/-- **A set is a siphon of an interconnection iff it is a siphon of each component.** The
interconnection's reactions are the disjoint union of the components', so the universal
siphon condition over `N₁.R ⊕ N₂.R` splits as a conjunction of the two component
conditions. -/
theorem interconnect_isSiphon_iff (N₁ N₂ : Network S) (P : Finset S) :
    (N₁.interconnect N₂).IsSiphon P ↔ N₁.IsSiphon P ∧ N₂.IsSiphon P := by
  constructor
  · intro h
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · obtain ⟨s, hsP, ht⟩ := h (Sum.inl r) hr
      exact ⟨s, hsP, ht⟩
    · obtain ⟨s, hsP, ht⟩ := h (Sum.inr r) hr
      exact ⟨s, hsP, ht⟩
  · rintro ⟨h₁, h₂⟩ (r | r) hr
    · exact h₁ r hr
    · exact h₂ r hr

end Network

end CRNT

import CRNT.Compose.InterconnectKinetics
import CRNT.Multistationarity.Injectivity

/-!
# Monostationarity of an interconnection

The stoichiometric subspace of an interconnection is the join of the components', so each
component's positive stoichiometric compatibility class embeds into the interconnection's:
a displacement that keeps a concentration within a component's subspace keeps it within
the larger interconnection subspace.

The monostationarity payoff lifts to the composed kinetics. When the combined vector field
`(K₁.sum K₂).vectorField` is injective on a positive compatibility class of the
interconnection, any two steady states of the combined kinetics lying in that class
coincide: at most one positive steady state of the interconnection per class. This is the
component-level injectivity-implies-monostationarity argument applied to the interconnection.

Depends on:
`CRNT.Compose.InterconnectKinetics`, `CRNT.Multistationarity.Injectivity`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S] {N₁ N₂ : Network S}

/-- The first component's positive compatibility class embeds into the interconnection's:
a displacement in `N₁`'s stoichiometric subspace is a displacement in the (larger)
interconnection subspace. -/
theorem positiveCompatibilityClass_subset_interconnect_left
    (N₁ N₂ : Network S) (x₀ : Concentration S) :
    N₁.positiveCompatibilityClass x₀ ⊆ (N₁.interconnect N₂).positiveCompatibilityClass x₀ := by
  rintro x ⟨hc, hp⟩
  exact ⟨stoichSubspace_le_interconnect_left N₁ N₂ hc, hp⟩

/-- The second component's positive compatibility class embeds into the interconnection's. -/
theorem positiveCompatibilityClass_subset_interconnect_right
    (N₁ N₂ : Network S) (x₀ : Concentration S) :
    N₂.positiveCompatibilityClass x₀ ⊆ (N₁.interconnect N₂).positiveCompatibilityClass x₀ := by
  rintro x ⟨hc, hp⟩
  exact ⟨stoichSubspace_le_interconnect_right N₁ N₂ hc, hp⟩

namespace Kinetics

/-- **Monostationarity of an interconnection.** If the combined vector field is injective
on the positive compatibility class of `x₀` in the interconnection, then any two steady
states of the combined kinetics lying in that class coincide: at most one positive steady
state of the interconnection per compatibility class. -/
theorem InjectiveOnClass.sum_subsingleton_steadyState
    {K₁ : Kinetics N₁} {K₂ : Kinetics N₂} {x₀ : Concentration S}
    (h : (K₁.sum K₂).InjectiveOnClass x₀)
    {x y : Concentration S}
    (hx : x ∈ (N₁.interconnect N₂).positiveCompatibilityClass x₀)
    (hy : y ∈ (N₁.interconnect N₂).positiveCompatibilityClass x₀)
    (hsx : (N₁.interconnect N₂).IsKineticSteadyState (K₁.sum K₂) x)
    (hsy : (N₁.interconnect N₂).IsKineticSteadyState (K₁.sum K₂) y) : x = y :=
  h.subsingleton_steadyState hx hy hsx hsy

end Kinetics

end Network

end CRNT

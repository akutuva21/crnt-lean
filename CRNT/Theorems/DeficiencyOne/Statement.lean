import CRNT.Deficiency.DeficiencyOneHypotheses
import CRNT.Equilibria.SteadyState
import CRNT.Equilibria.CompatibilityClass
import CRNT.Graph.WeakReversibility

/-!
# Deficiency-one theorem: statement interface

This module exposes the hypotheses and the conclusions of Feinberg's deficiency-one
theorem as named definitions, giving downstream tools and proofs a stable API. The
theorem itself is not asserted here: each conclusion is a `Prop`-valued definition that
a future proof — or an explicit, clearly marked experimental hypothesis — can target.

The hypotheses are `N.DeficiencyOneHypotheses` (`CRNT.Deficiency.DeficiencyOneHypotheses`):
each linkage class has deficiency at most one, the class deficiencies sum to the network
deficiency, and each linkage class contains exactly one terminal strong linkage class.

Two conclusions are packaged:

* `DeficiencyOneUniqueness` — the distinctive content. Under the deficiency-one
  hypotheses, for *any* positive rate constants a positive stoichiometric compatibility
  class contains **at most one** mass-action steady state. This requires neither weak
  reversibility nor complex balancing, which is what sharpens it past the deficiency-zero
  theorem.
* `DeficiencyOneExistence` — for weakly reversible networks the class contains
  **exactly one** positive steady state.

Depends on the deficiency-one hypotheses,
the steady-state, compatibility-class, and weak-reversibility layers.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Uniqueness conclusion of the deficiency-one theorem.** For every positive choice of
rate constants and every positive starting concentration, the positive stoichiometric
compatibility class of the start contains at most one mass-action steady state.

This is a `Prop`-valued *statement*, not an asserted theorem:
`∀ N, N.DeficiencyOneHypotheses → N.DeficiencyOneUniqueness` is not proved here. -/
def DeficiencyOneUniqueness (N : Network S) : Prop :=
  ∀ (κ : RateConstants N) (x₀ : Concentration S), x₀.Positive →
    ∀ ⦃x y : Concentration S⦄,
      x ∈ N.positiveCompatibilityClass x₀ → N.IsMassActionSteadyState κ x →
      y ∈ N.positiveCompatibilityClass x₀ → N.IsMassActionSteadyState κ y →
      x = y

/-- **Existence-and-uniqueness conclusion for weakly reversible networks.** For every
positive choice of rate constants and every positive starting concentration, the positive
stoichiometric compatibility class of the start contains exactly one mass-action steady
state.

This is a `Prop`-valued *statement*, not an asserted theorem:
`∀ N, N.WeaklyReversible → N.DeficiencyOneHypotheses → N.DeficiencyOneExistence` — the
weakly reversible form of the deficiency-one theorem — is not proved here. -/
def DeficiencyOneExistence (N : Network S) : Prop :=
  ∀ (κ : RateConstants N) (x₀ : Concentration S), x₀.Positive →
    ∃! x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x

/-- The existence form refines the uniqueness form: a class with a unique positive steady
state has at most one. -/
theorem deficiencyOneUniqueness_of_existence (N : Network S)
    (h : N.DeficiencyOneExistence) : N.DeficiencyOneUniqueness := by
  intro κ x₀ hx0 x y hxmem hxss hymem hyss
  obtain ⟨_, _, huniq⟩ := h κ x₀ hx0
  rw [huniq x ⟨hxmem, hxss⟩, huniq y ⟨hymem, hyss⟩]

end Network

end CRNT

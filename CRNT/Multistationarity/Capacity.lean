import CRNT.Multistationarity.Injectivity

/-!
# Capacity for multiple steady states

A network **has the capacity for multiple steady states** (is *multistationary*) when some choice
of positive rate constants admits two distinct positive steady states in a single stoichiometric
compatibility class. This is the property that the deficiency-one, advanced-deficiency, and
species–reaction-graph algorithms are designed to decide: each either affirms the capacity or rules
it out, independently of the particular rate constants.

Following Feinberg, the capacity is a property of the network alone — the rate constants are
existentially quantified — and the two steady states are required to lie in one compatibility class,
since steady states of distinct classes carry no comparison.

* `HasMultistationarityCapacity` — the existence of `κ` and two distinct positive steady states in
  one positive compatibility class;
* `not_hasMultistationarityCapacity_of_injective` — **injectivity rules out multistationarity**: if
  the mass-action kinetics is injective for every choice of rate constants, the network has no
  capacity for multiple steady states. This is the Craciun–Feinberg exclusion direction, the easy
  half on which the injectivity and SR-graph criteria rest.

The converse — *affirming* the capacity by exhibiting the witnessing rate constants and steady
states, which the deficiency algorithms accomplish through a parameter-independent linear
feasibility test — is a separate development.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Multistationarity.Injectivity`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The capacity for multiple steady states.** For some choice of positive rate constants `κ`
there are two distinct positive concentrations, lying in one positive stoichiometric compatibility
class, that are both mass-action steady states. -/
def HasMultistationarityCapacity (N : Network S) : Prop :=
  ∃ (κ : RateConstants N) (x₀ x y : Concentration S),
    x ∈ N.positiveCompatibilityClass x₀ ∧ y ∈ N.positiveCompatibilityClass x₀ ∧
      N.IsMassActionSteadyState κ x ∧ N.IsMassActionSteadyState κ y ∧ x ≠ y

/-- **Injectivity rules out the capacity for multiple steady states.** If the mass-action kinetics
is injective (Craciun–Feinberg) for every choice of rate constants, then any two steady states in a
common compatibility class coincide, so no `κ` can witness multistationarity. -/
theorem not_hasMultistationarityCapacity_of_injective (N : Network S)
    (h : ∀ κ : RateConstants N, (N.massActionKinetics κ).Injective) :
    ¬ N.HasMultistationarityCapacity := by
  rintro ⟨κ, x₀, x, y, hx, hy, hsx, hsy, hne⟩
  exact hne (massAction_subsingleton_steadyState_of_injective (h κ) hx hy hsx hsy)

end Network

end CRNT

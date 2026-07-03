import CRNT.Kinetics.General
import CRNT.Equilibria.CompatibilityClass

/-!
# Injectivity and monostationarity

A kinetics is **injective** (in the sense of Craciun–Feinberg) when its induced vector
field is injective on every positive stoichiometric compatibility class. Injectivity is
the structural property that rules out multiple positive steady states: two steady states
lying in one positive compatibility class are both zeros of the field, so injectivity on
that class forces them to coincide.

This module defines the per-class and global injectivity predicates over an arbitrary
`Kinetics` and proves the monostationarity payoff — at most one positive steady state per
compatibility class — together with its mass-action corollary. The Jacobian-determinant
sign criterion that *establishes* injectivity is a separate development.

Depends on: `CRNT.Kinetics.General`,
`CRNT.Equilibria.CompatibilityClass`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

namespace Kinetics

/-- A kinetics is **injective on the positive compatibility class** of `x₀` when its
induced vector field is injective (in the `Set.InjOn` sense) on that class. -/
def InjectiveOnClass (K : Kinetics N) (x₀ : Concentration S) : Prop :=
  Set.InjOn K.vectorField (N.positiveCompatibilityClass x₀)

/-- A kinetics is **injective** (Craciun–Feinberg) when its induced vector field is
injective on every positive compatibility class. -/
def Injective (K : Kinetics N) : Prop :=
  ∀ x₀ : Concentration S, K.InjectiveOnClass x₀

example (K : Kinetics N) (x₀ : Concentration S) :
    K.InjectiveOnClass x₀ ↔ Set.InjOn K.vectorField (N.positiveCompatibilityClass x₀) :=
  Iff.rfl

/-- **Easy direction.** If `K` is injective on the positive compatibility class of `x₀`,
then any two steady states of `K` lying in that class coincide: at most one positive
steady state per class. -/
theorem InjectiveOnClass.subsingleton_steadyState
    {K : Kinetics N} {x₀ : Concentration S} (h : K.InjectiveOnClass x₀)
    {x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsKineticSteadyState K x) (hsy : N.IsKineticSteadyState K y) : x = y := by
  have ex : K.vectorField x = 0 := funext fun s => hsx s
  have ey : K.vectorField y = 0 := funext fun s => hsy s
  exact h hx hy (ex.trans ey.symm)

/-- The same uniqueness for a globally injective kinetics. -/
theorem Injective.subsingleton_steadyState
    {K : Kinetics N} (h : K.Injective) {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsKineticSteadyState K x) (hsy : N.IsKineticSteadyState K y) : x = y :=
  (h x₀).subsingleton_steadyState hx hy hsx hsy

end Kinetics

/-- Mass-action corollary: at most one positive mass-action steady state per compatibility
class, for an injective mass-action system. -/
theorem massAction_subsingleton_steadyState_of_injective
    {N : Network S} {κ : RateConstants N} (h : (N.massActionKinetics κ).Injective)
    {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsMassActionSteadyState κ x) (hsy : N.IsMassActionSteadyState κ y) : x = y :=
  h.subsingleton_steadyState hx hy
    ((N.isMassActionSteadyState_iff_kinetic κ x).mp hsx)
    ((N.isMassActionSteadyState_iff_kinetic κ y).mp hsy)

end Network

end CRNT

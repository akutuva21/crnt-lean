import CRNT.Kinetics.MassAction

/-!
# Steady states

A steady state of a vector field is a concentration at which the field vanishes
componentwise. This module defines the general predicate and its mass-action
specialization.

Depends on: `CRNT.Kinetics.MassAction`.
-/

namespace CRNT

/-- A concentration `x` is a steady state of the vector field `f` when `f x` is zero
in every species coordinate. -/
def IsSteadyState {S : Type} (f : Concentration S → S → ℝ) (x : Concentration S) : Prop :=
  ∀ s : S, f x s = 0

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A concentration is a mass-action steady state when it is a steady state of the
network's mass-action vector field. -/
def IsMassActionSteadyState (N : Network S) (κ : RateConstants N)
    (x : Concentration S) : Prop :=
  IsSteadyState (N.massActionVectorField κ) x

theorem isMassActionSteadyState_iff (N : Network S) (κ : RateConstants N)
    (x : Concentration S) :
    N.IsMassActionSteadyState κ x ↔
      ∀ s : S, (∑ r : N.R, N.massActionRate κ r x * N.reactionVector r s) = 0 :=
  Iff.rfl

end Network

end CRNT

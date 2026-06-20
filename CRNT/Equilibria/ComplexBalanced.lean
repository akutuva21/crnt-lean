import CRNT.Kinetics.MassAction

/-!
# Complex balancing

A concentration is *complex-balanced* when, at every complex, the total mass-action
inflow equals the total outflow. Complex-balanced equilibria are the equilibria
delivered by the deficiency-zero theorem.

This module is **stable**. Depends on: `CRNT.Kinetics.MassAction`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The total mass-action flow into complex `c`: the sum of rates of reactions whose
target is `c`. -/
def inflow (N : Network S) (κ : RateConstants N) (x : Concentration S)
    (c : Complex S) : ℝ :=
  ∑ r : N.R, if (N.reaction r).target = c then N.massActionRate κ r x else 0

/-- The total mass-action flow out of complex `c`: the sum of rates of reactions whose
source is `c`. -/
def outflow (N : Network S) (κ : RateConstants N) (x : Concentration S)
    (c : Complex S) : ℝ :=
  ∑ r : N.R, if (N.reaction r).source = c then N.massActionRate κ r x else 0

/-- `x` is complex-balanced when inflow equals outflow at every complex of the
network. -/
def IsComplexBalanced (N : Network S) (κ : RateConstants N) (x : Concentration S) :
    Prop :=
  ∀ c ∈ N.complexes, N.inflow κ x c = N.outflow κ x c

end Network

end CRNT

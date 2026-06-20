import CRNT.Kinetics.Concentration
import CRNT.Stoich.Vector

/-!
# Mass-action kinetics

Under mass-action kinetics each reaction fires at a rate proportional to the product
of the concentrations of its source species, with a positive rate constant. Summing
the reaction vectors weighted by these rates gives the mass-action vector field — the
polynomial ODE induced by the network. This module is the bridge from discrete CRN
structure to continuous dynamics.

This module is **stable**. Rate constants are `ℝ`-valued with an explicit positivity
proof. Depends on: `CRNT.Kinetics.Concentration`, `CRNT.Stoich.Vector`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A choice of positive rate constant for each reaction of a network. -/
structure RateConstants (N : Network S) where
  /-- The rate constant of each reaction. -/
  k : N.R → ℝ
  /-- Every rate constant is strictly positive. -/
  positive : ∀ r, 0 < k r

/-- The mass-action rate of reaction `r` at concentration `x`: the rate constant
times the monomial of the source complex. -/
def massActionRate (N : Network S) (κ : RateConstants N) (r : N.R)
    (x : Concentration S) : ℝ :=
  κ.k r * (N.reaction r).source.massActionMonomial x

/-- At a nonnegative concentration, every mass-action rate is nonnegative. -/
theorem massActionRate_nonneg (N : Network S) (κ : RateConstants N) (r : N.R)
    {x : Concentration S} (hx : x.Nonnegative) : 0 ≤ N.massActionRate κ r x :=
  mul_nonneg (κ.positive r).le (Complex.massActionMonomial_nonneg hx _)

/-- At a positive concentration, every mass-action rate is strictly positive. -/
theorem massActionRate_pos (N : Network S) (κ : RateConstants N) (r : N.R)
    {x : Concentration S} (hx : x.Positive) : 0 < N.massActionRate κ r x :=
  mul_pos (κ.positive r) (Complex.massActionMonomial_pos hx _)

/-- The mass-action vector field: for each species, the net rate of change is the sum
over reactions of the reaction rate times the species' entry in the reaction vector.
This is the right-hand side of the induced polynomial ODE `ẋ = f(x)`. -/
def massActionVectorField (N : Network S) (κ : RateConstants N)
    (x : Concentration S) : S → ℝ :=
  fun s => ∑ r : N.R, N.massActionRate κ r x * N.reactionVector r s

@[simp] theorem massActionVectorField_apply (N : Network S) (κ : RateConstants N)
    (x : Concentration S) (s : S) :
    N.massActionVectorField κ x s =
      ∑ r : N.R, N.massActionRate κ r x * N.reactionVector r s :=
  rfl

end Network

end CRNT

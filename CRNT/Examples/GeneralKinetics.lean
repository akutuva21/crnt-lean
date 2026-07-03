import CRNT.Kinetics.General
import CRNT.Examples.ReversiblePair

/-!
# General kinetics on the reversible pair `A ⇌ B`

Exercises the `Kinetics` abstraction on the canonical network: mass action arises as the
instance `massActionKinetics`, its induced field is the mass-action vector field, and the
kinetics-agnostic stoichiometry lemmas (conservation, boundary non-attraction) apply.
-/

namespace CRNT.Examples.GeneralKinetics

open CRNT CRNT.Examples.ReversiblePair

/-- Unit rate constants for `A ⇌ B`. -/
def κ : Network.RateConstants N where
  k := fun _ => 1
  positive := fun _ => one_pos

/-- Mass action as a kinetics on the reversible pair. -/
def K : Network.Kinetics N := N.massActionKinetics κ

/-- The kinetics' rate is the mass-action rate. -/
example : K.rate = N.massActionRate κ := rfl

/-- The induced field is the mass-action vector field — the API is recovered
definitionally. -/
example : K.vectorField = N.massActionVectorField κ :=
  N.massActionKinetics_vectorField κ

/-- Conservation: the induced field lies in the stoichiometric subspace. -/
example (x : Concentration Species) : K.vectorField x ∈ N.stoichSubspace :=
  K.vectorField_mem_stoichSubspace x

/-- Boundary non-attraction: on the face `{x_A = 0}` the `A`-component of the field is
nonnegative. -/
example {x : Concentration Species} (hx : x.Nonnegative) (hA : x Species.A = 0) :
    0 ≤ K.vectorField x Species.A :=
  K.vectorField_nonneg_of_zero hx hA

end CRNT.Examples.GeneralKinetics

import CRNT.Theorems.DeficiencyOne.Statement
import CRNT.Examples.ReversiblePair

/-!
# The deficiency-one statement interface on `A ⇌ B`

This exercises the statement-level conclusions of the deficiency-one theorem on the
reversible pair: the existence form refines the uniqueness form (`deficiencyOneUniqueness_of_existence`),
and each conclusion unfolds to the expected quantified statement about positive steady
states in a positive compatibility class.
-/

namespace CRNT.Examples.DeficiencyOneStatementExample

open CRNT CRNT.Examples.ReversiblePair

/-- The existence form of the conclusion implies the uniqueness form. -/
example : N.DeficiencyOneExistence → N.DeficiencyOneUniqueness :=
  N.deficiencyOneUniqueness_of_existence

/-- The uniqueness conclusion unfolds to: positive steady states in a positive
compatibility class coincide. -/
example : N.DeficiencyOneUniqueness ↔
    ∀ (κ : Network.RateConstants N) (x₀ : Concentration Species), x₀.Positive →
      ∀ ⦃x y : Concentration Species⦄,
        x ∈ N.positiveCompatibilityClass x₀ → N.IsMassActionSteadyState κ x →
        y ∈ N.positiveCompatibilityClass x₀ → N.IsMassActionSteadyState κ y →
        x = y :=
  Iff.rfl

end CRNT.Examples.DeficiencyOneStatementExample

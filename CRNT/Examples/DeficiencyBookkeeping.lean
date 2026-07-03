import CRNT.Deficiency.DeficiencyOne
import CRNT.Examples.ReversiblePair

/-!
# Deficiency bookkeeping for `A ⇌ B`

The reversible pair has `n = 2` complexes, `ℓ = 1` linkage class, stoichiometric rank `s = 1`,
and deficiency `δ = 0`. This exercises the natural-number deficiency and the structural
identity `n = ℓ + s + δ`, and confirms the network is not of deficiency one.
-/

namespace CRNT.Examples.DeficiencyBookkeeping

open CRNT CRNT.Examples.ReversiblePair

/-- The natural-number deficiency of `A ⇌ B` is zero. -/
theorem deficiency_eq : N.deficiency = 0 :=
  (N.deficiencyZero_iff_deficiency_eq_zero).mp deficiencyZero

/-- The structural identity `n = ℓ + s + δ` holds: `2 = 1 + 1 + 0`. -/
example : N.numComplexes = N.numLinkageClasses + N.stoichRank + N.deficiency :=
  N.numComplexes_eq_add

/-- The reversible pair is not of deficiency one. -/
example : ¬ N.DeficiencyOne :=
  fun h => N.not_deficiencyZero_of_deficiencyOne h deficiencyZero

end CRNT.Examples.DeficiencyBookkeeping

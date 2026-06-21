import CRNT.Decision.Tactic
import CRNT.Examples.ReversiblePair

/-!
# Closing structural goals with `crnt_check`

The decidable structural core lets concrete networks discharge their properties by reflection.
For the reversible pair, weak reversibility and the strong-linkage-class count are closed by
`crnt_check`.

This module is **stable** (example/test). It contains no `sorry`.
-/

namespace CRNT.Examples.CrntCheck

open CRNT CRNT.Examples.ReversiblePair

/-- Weak reversibility of `A ⇌ B`, closed by reflection. -/
theorem weaklyReversible : N.WeaklyReversible := by crnt_check

/-- The single strong linkage class, closed by reflection. -/
theorem numStrongLinkageClasses_eq : N.numStrongLinkageClasses = 1 := by crnt_check

end CRNT.Examples.CrntCheck

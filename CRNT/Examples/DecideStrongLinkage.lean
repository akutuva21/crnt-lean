import CRNT.Decision.StrongLinkage
import CRNT.Examples.ReversiblePair

/-!
# Strong linkage of `A ⇌ B`

The reversible pair is strongly connected: `A` and `B` are mutually reachable in one step,
so they are strongly linked, discharged by `decide` on the bounded companion. The single
strong linkage class is terminal — no reaction leaves it.

This module is **stable** (example/test). It contains no `sorry`.
-/

namespace CRNT.Examples.DecideStrongLinkage

open CRNT CRNT.Examples.ReversiblePair

/-- `A` and `B` are mutually reachable within one reaction. -/
theorem stronglyLinkedWithin_one : N.StronglyLinkedWithin 1 cA cB := by decide

/-- Hence `A` and `B` are strongly linked. -/
theorem stronglyLinked_AB : N.StronglyLinked cA cB :=
  N.stronglyLinked_of_within stronglyLinkedWithin_one

end CRNT.Examples.DecideStrongLinkage

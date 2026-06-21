import CRNT.Decision.Linkage
import CRNT.Examples.ReversiblePair

/-!
# Computing the linkage-class count of `A ⇌ B`

The reversible pair has a single linkage class. With the simple-graph model of the undirected
reaction graph the count `ℓ` is the number of connected components, which is computable; the
abstract identity then transports it to `numLinkageClasses`.

This module is **stable** (example/test). It contains no `sorry`.
-/

namespace CRNT.Examples.DecideLinkage

open CRNT CRNT.Examples.ReversiblePair

/-- The undirected reaction graph of `A ⇌ B` has one connected component. -/
theorem card_connectedComponent : Fintype.card N.linkageGraph.ConnectedComponent = 1 := by
  decide

/-- Hence `ℓ = 1`, obtained by reduction through the computable component count. -/
theorem numLinkageClasses_eq : N.numLinkageClasses = 1 := by
  rw [N.numLinkageClasses_eq_card_connectedComponent, card_connectedComponent]

end CRNT.Examples.DecideLinkage

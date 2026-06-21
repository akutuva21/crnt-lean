import CRNT.Decision.DirectedReachability
import CRNT.Examples.ReversiblePair

/-!
# Deciding directed reachability and strong linkage of `A ⇌ B`

With reachability restricted to the finite vertex type of complexes, full (unbounded)
directed reachability is decidable, as is the strong-linkage-class count. The reversible
pair is strongly connected: `A` and `B` reach each other, forming a single strong linkage
class, all discharged by `decide`.

This module is **stable** (example/test). It contains no `sorry`.
-/

namespace CRNT.Examples.DecideDirectedReachability

open CRNT CRNT.Examples.ReversiblePair

/-- `A` as a vertex of the finite complex graph. -/
def vA : {c : Complex Species // c ∈ N.complexes} := ⟨cA, by decide⟩

/-- `B` as a vertex of the finite complex graph. -/
def vB : {c : Complex Species // c ∈ N.complexes} := ⟨cB, by decide⟩

/-- Full, unbounded directed reachability is decidable — no depth bound needed. -/
example : N.Reaches vA.val vB.val := by decide

example : N.Reaches vB.val vA.val := by decide

/-- The reversible pair forms a single strong linkage class. -/
theorem numStrongLinkageClasses_eq : N.numStrongLinkageClasses = 1 := by decide

end CRNT.Examples.DecideDirectedReachability

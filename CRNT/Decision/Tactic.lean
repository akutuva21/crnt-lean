import CRNT.Decision.DirectedReachability

/-!
# The `crnt_check` tactic

`crnt_check` closes a decidable structural goal about a concrete network by reflection. The
decision procedures of `CRNT.Decision.*` make the standard structural predicates — directed
and undirected reachability, weak reversibility, strong linkage, linkage- and
strong-linkage-class counts — decidable, so a goal stating such a property of a concrete
network reduces to `Bool` evaluation.

The tactic closes the goal by kernel reduction (`decide`), so it stays on the axiom-clean path
(`[propext, Classical.choice, Quot.sound]`). Concrete networks whose structural `Bool` check
the kernel can evaluate are settled directly.

This module is **stable**. Depends on: `CRNT.Decision.DirectedReachability`.
-/

namespace CRNT

/-- Close a decidable structural goal about a concrete network by reflection. -/
macro "crnt_check" : tactic => `(tactic| decide)

end CRNT

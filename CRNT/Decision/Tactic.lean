import CRNT.Decision.DirectedReachability

/-!
# The `crnt_check` tactic

`crnt_check` closes a decidable structural goal about a concrete network by reflection. The
decision procedures of `CRNT.Decision.*` make the standard structural predicates — directed
and undirected reachability, weak reversibility, strong linkage, linkage- and
strong-linkage-class counts — decidable, so a goal stating such a property of a concrete
network reduces to `Bool` evaluation.

The tactic tries kernel reduction (`decide`) first and falls back to compiled evaluation
(`native_decide`) for larger networks. The fallback introduces the compiler-trust axiom; for
the axiom-clean path use goals that `decide` settles directly.

This module is **stable**. Depends on: `CRNT.Decision.DirectedReachability`.
-/

namespace CRNT

/-- Close a decidable structural goal about a concrete network by reflection. -/
macro "crnt_check" : tactic => `(tactic| first | decide | native_decide)

end CRNT

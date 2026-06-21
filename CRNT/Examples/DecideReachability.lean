import CRNT.Decision.Reachability
import CRNT.Examples.ReversiblePair

/-!
# Discharging reachability and weak reversibility by `decide`

The reversible pair `A ⇌ B` is weakly reversible: each reaction's source is reachable from
its target in one step. With the decidable bounded-reachability companion this is closed by
`decide` on `WeaklyReversibleWithin 1`, instead of building the return paths by hand.

This module is **stable** (example/test). It contains no `sorry`.
-/

namespace CRNT.Examples.DecideReachability

open CRNT CRNT.Examples.ReversiblePair

/-- `B` is reachable from `A` within one reaction. -/
example : N.ReachesWithin 1 cA cB := by decide

/-- Both return paths have length one, so the network is weakly reversible within depth 1. -/
theorem weaklyReversibleWithin_one : N.WeaklyReversibleWithin 1 := by decide

/-- Weak reversibility of `A ⇌ B`, discharged by reduction. -/
theorem weaklyReversible : N.WeaklyReversible :=
  N.weaklyReversible_of_within weaklyReversibleWithin_one

end CRNT.Examples.DecideReachability

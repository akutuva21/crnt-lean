import CRNT.Graph.Reachability

/-!
# Weak reversibility

A network is *weakly reversible* when every reaction lies on a directed cycle:
for each reaction `y → y'` there is a directed path from `y'` back to `y`.
Weak reversibility is a central hypothesis of the deficiency-zero theorem.

Weak reversibility is defined propositionally; example
networks are shown weakly reversible (or not) by explicit witnesses. Depends on:
`CRNT.Graph.Reachability`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- `N.WeaklyReversible` holds when, for every reaction `y → y'`, the source `y` is
reachable from the target `y'`. Equivalently, each reaction lies on a directed
cycle. -/
def WeaklyReversible (N : Network S) : Prop :=
  ∀ r : N.R, N.Reaches (N.reaction r).target (N.reaction r).source

/-- To prove weak reversibility it suffices to exhibit, for each reaction, a return
path from its target to its source. -/
theorem weaklyReversible_iff (N : Network S) :
    N.WeaklyReversible ↔
      ∀ r : N.R, N.Reaches (N.reaction r).target (N.reaction r).source :=
  Iff.rfl

/-- In a weakly reversible network the source and target of every reaction reach each
other: weak reversibility makes the reaction-graph adjacency relation symmetric up to
reachability. -/
theorem WeaklyReversible.reaches_symm {N : Network S} (h : N.WeaklyReversible)
    (r : N.R) :
    N.Reaches (N.reaction r).source (N.reaction r).target ∧
      N.Reaches (N.reaction r).target (N.reaction r).source :=
  ⟨N.reaches_of_reaction r, h r⟩

end Network

end CRNT

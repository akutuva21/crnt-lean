import CRNT.Graph.Reachability

/-!
# Crossing reactions along a directed path

A directed path that starts outside a set of complexes and ends inside it must traverse a
reaction whose source lies outside the set and whose target lies inside — the path crosses the
boundary. This is the elementary boundary argument underlying the excess/sign analysis of the
reaction graph: it produces, from reachability into a set, an explicit in-crossing reaction.

* `exists_crossing_reaction` — a reaction crossing into a set, from `Reaches` into it.

Depends on: `CRNT.Graph.Reachability`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A path into a set crosses its boundary.** If `c` reaches `d`, `c` is outside the predicate
`P`, and `d` is inside it, then some reaction runs from outside `P` to inside `P`. -/
theorem exists_crossing_reaction {N : Network S} (P : Complex S → Prop)
    {c d : Complex S} (h : N.Reaches c d) (hc : ¬ P c) (hd : P d) :
    ∃ r : N.R, ¬ P (N.reaction r).source ∧ P (N.reaction r).target := by
  revert hc
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun h => absurd hd h
  | @head a b hab _ ih =>
    intro hna
    by_cases hpb : P b
    · obtain ⟨r, hrs, hrt⟩ := hab
      exact ⟨r, by rw [hrs]; exact hna, by rw [hrt]; exact hpb⟩
    · exact ih hpb

end Network

end CRNT

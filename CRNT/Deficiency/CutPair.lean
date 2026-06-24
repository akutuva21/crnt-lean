import CRNT.Decision.Linkage
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Cut pairs

In the undirected reaction graph, a pair of directly linked complexes `y, y'` is a **cut pair**
when the reaction(s) between them form a *bridge* of their linkage class: deleting that edge
disconnects `y` from `y'`, splitting the linkage class into the two pieces `W(y) ∋ y` and
`W(y') ∋ y'`. Cut pairs are the third ingredient of a *regular* network underlying Feinberg's
Deficiency One Algorithm (Ji, *Uniqueness of equilibria for complex chemical reaction networks*,
Ohio State University, 2011, §1.6).

The undirected reaction graph is `linkageGraph`, whose simple edge between two complexes collapses
all reactions between them; deleting that single edge therefore removes *all* reactions between `y`
and `y'`, and the cut condition is the resulting non-reachability.

* `CutPair y y'` — `y, y'` are adjacent and become unreachable once the edge `s(y, y')` is deleted;
* `CutPair.symm` — the relation is symmetric (the deleted edge and reachability are both symmetric).

This module is **stable** and `sorry`-free. Depends on: `CRNT.Decision.Linkage`,
`Mathlib.Combinatorics.SimpleGraph.DeleteEdges`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Cut pair.** Directly linked complexes `y, y'` whose connecting edge is a bridge of the
linkage graph: after deleting `s(y, y')` they are no longer reachable from one another, so the
linkage class splits into the component of `y` and the component of `y'`. -/
def CutPair (N : Network S) (y y' : {c : Complex S // c ∈ N.complexes}) : Prop :=
  N.linkageGraph.Adj y y' ∧ ¬ (N.linkageGraph.deleteEdges {s(y, y')}).Reachable y y'

/-- **Cut pairs are symmetric.** Adjacency and reachability are symmetric, and the deleted edge
`s(y', y) = s(y, y')` is the same. -/
theorem CutPair.symm {N : Network S} {y y' : {c : Complex S // c ∈ N.complexes}}
    (h : N.CutPair y y') : N.CutPair y' y := by
  obtain ⟨hadj, hcut⟩ := h
  refine ⟨hadj.symm, ?_⟩
  intro hr
  have hset : ({s(y', y)} : Set (Sym2 {c : Complex S // c ∈ N.complexes})) = {s(y, y')} := by
    rw [Sym2.eq_swap]
  rw [hset] at hr
  exact hcut hr.symm

end Network

end CRNT

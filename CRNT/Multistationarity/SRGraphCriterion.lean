import CRNT.Multistationarity.SRGraph
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Combinatorics.SimpleGraph.Girth

/-!
# Bipartite alternation in the species–reaction graph

The Craciun–Feinberg species–reaction-graph criterion for injectivity of the
mass-action vector field is *stated over* the cycle structure of the SR-graph: it
counts cycles by parity and intersects even cycles sharing terminal edges. The
combinatorial substrate underlying that bookkeeping is the bipartite alternation of
the SR-graph — every walk strictly alternates between the species side and the
reaction side, so every cycle has even length and the graph has no odd cycle.

This module records that substrate.

* `srGraph_getVert_isLeft_succ` — consecutive vertices of a walk lie on opposite
  sides of the species/reaction bipartition.
* `srGraph_getVert_isLeft` — closed form for the side of the `i`-th vertex of a walk
  in terms of the parity of `i` and the side of the start vertex.
* `srGraph_even_length_of_closed` — every closed walk has even length.
* `srGraph_even_length_of_isCycle` — every cycle has even length.
* `srGraph_not_isCycle_of_odd_length` — contrapositively, an odd-length closed walk
  is not a cycle (the SR-graph has no odd cycle).
* `srGraph_four_le_egirth` — the SR-graph has no triangle, so its edge-girth is at
  least four (combining the general girth bound of three with the evenness of
  cycles).

The SR-graph here is the *unlabeled, unsigned* incidence graph: edges record only
that a species occurs in a reaction, carrying no stoichiometric sign. Consequently
these results are purely combinatorial parity facts about cycles. They are the
foundation the Craciun–Feinberg criterion is built on; relating cycle parity to a
Jacobian determinant sign condition requires the signed/labeled SR-graph and a
determinant-via-matchings expansion, which this module does not provide.

Depends on:
`CRNT.Multistationarity.SRGraph`, `Mathlib.Combinatorics.SimpleGraph.Paths`,
`Mathlib.Combinatorics.SimpleGraph.Walk.Traversal`,
`Mathlib.Combinatorics.SimpleGraph.Girth`.
-/

namespace CRNT

namespace Network

open SimpleGraph

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Consecutive vertices of a walk in the SR-graph lie on opposite sides of the
species/reaction bipartition: the `isLeft` flag flips at each step. -/
theorem srGraph_getVert_isLeft_succ (N : Network S) {u v : N.SRVertex S}
    (w : N.srGraph.Walk u v) {i : ℕ} (hi : i < w.length) :
    (w.getVert (i + 1)).isLeft = !(w.getVert i).isLeft := by
  have hadj := w.adj_getVert_succ hi
  cases hx : w.getVert i <;> cases hy : w.getVert (i + 1) <;> simp_all [srGraph]

/-- The side of the `i`-th vertex of a walk is determined by the parity of `i` and
the side of the start vertex: it equals `u.isLeft` for even `i` and its negation for
odd `i`. -/
theorem srGraph_getVert_isLeft (N : Network S) {u v : N.SRVertex S}
    (w : N.srGraph.Walk u v) (i : ℕ) (hi : i ≤ w.length) :
    (w.getVert i).isLeft = xor (i % 2 = 1) u.isLeft := by
  induction i with
  | zero => simp [w.getVert_zero]
  | succ k ih =>
    have hk : k < w.length := hi
    rw [srGraph_getVert_isLeft_succ N w hk, ih (le_of_lt hk)]
    rcases Nat.even_or_odd k with he | ho
    · have hk1 : (k + 1) % 2 = 1 := by
        rw [Nat.even_iff] at he; omega
      have hk0 : ¬ k % 2 = 1 := by
        rw [Nat.even_iff] at he; omega
      simp [hk1, hk0, Bool.xor]
    · have hk0 : (k + 1) % 2 = 0 := by
        rw [Nat.odd_iff] at ho; omega
      have hk1 : k % 2 = 1 := by
        rw [Nat.odd_iff] at ho; exact ho
      simp [hk0, hk1, Bool.xor]

/-- **Every closed walk in the SR-graph has even length.** The end vertex equals the
start vertex, so the side flag at step `length` must agree with the side flag at
step `0`; by the alternation formula this forces the length to be even. -/
theorem srGraph_even_length_of_closed (N : Network S) {u : N.SRVertex S}
    (w : N.srGraph.Walk u u) : Even w.length := by
  have h := srGraph_getVert_isLeft N w w.length le_rfl
  rw [w.getVert_length] at h
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hlen : w.length % 2 = 1 := Nat.odd_iff.mp hodd
  rw [hlen] at h
  simp [Bool.xor] at h
  cases u <;> simp_all

/-- **Every cycle in the SR-graph has even length:** the SR-graph has no odd cycle.
Evenness holds for any closed walk, in particular for any cycle. -/
theorem srGraph_even_length_of_isCycle (N : Network S) {u : N.SRVertex S}
    {w : N.srGraph.Walk u u} (_h : w.IsCycle) : Even w.length :=
  srGraph_even_length_of_closed N w

/-- **Contrapositive:** an odd-length closed walk in the SR-graph is not a cycle. -/
theorem srGraph_not_isCycle_of_odd_length (N : Network S) {u : N.SRVertex S}
    {w : N.srGraph.Walk u u} (h : Odd w.length) : ¬ w.IsCycle := by
  intro hcyc
  exact (Nat.not_even_iff_odd.mpr h) (srGraph_even_length_of_isCycle N hcyc)

/-- **The SR-graph has no triangle:** its edge-girth is at least four. A cycle has
length at least three in any simple graph, and length an even number in the
SR-graph; the smallest even number that is at least three is four. -/
theorem srGraph_four_le_egirth (N : Network S) : 4 ≤ N.srGraph.egirth := by
  refine le_egirth.mpr ?_
  intro u w hcyc
  have h3 : 3 ≤ w.length := hcyc.three_le_length
  have heven : Even w.length := srGraph_even_length_of_isCycle N hcyc
  have h4 : 4 ≤ w.length := by
    rw [Nat.even_iff] at heven; omega
  exact_mod_cast h4

section Example

/-- A two-species, single-reaction network `A → B`: species `Fin 2` and one reaction
with source the unit complex on `0` and target the unit complex on `1`. -/
private def exampleNetwork : Network (Fin 2) where
  R := Unit
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ =>
    { source := fun s => if s = 0 then 1 else 0
      target := fun s => if s = 1 then 1 else 0 }

/-- The species `0` occurs in the reaction, giving an edge from `Sum.inl 0` to
`Sum.inr ()` in the SR-graph. -/
private theorem exampleNetwork_adj :
    exampleNetwork.srGraph.Adj (Sum.inl 0) (Sum.inr ()) := by decide

/-- The closed walk `Sum.inl 0 → Sum.inr () → Sum.inl 0` of length two, exercising
the even-length result on a concrete network. -/
private def exampleClosedWalk :
    exampleNetwork.srGraph.Walk (Sum.inl 0) (Sum.inl 0) :=
  .cons exampleNetwork_adj (.cons exampleNetwork_adj.symm .nil)

/-- The concrete closed walk has even length, as guaranteed by
`srGraph_even_length_of_closed`. -/
example : Even exampleClosedWalk.length :=
  srGraph_even_length_of_closed exampleNetwork exampleClosedWalk

end Example

end Network

end CRNT

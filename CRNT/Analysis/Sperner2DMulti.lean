import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.BigOperators
import CRNT.Analysis.Sperner2D

/-!
# Multi-outer-vertex door-graph handshaking

This module generalizes the abstract handshaking conclusion `Sperner2D.doorGraph_odd_rainbow` from a
door graph with a *single* outer region `none : Option Cell` to one whose outer region is split into
*many* outer vertices `Outer`, over the vertex type `Cell ⊕ Outer`.

The single-outer-vertex framing collapses a boundary cell's multiple `{0, 1}`-doors into one
adjacency: in a `SimpleGraph (Option Cell)` the cell `some t` and the outer region `none` share at
most one edge, so a triangle with two boundary doors cannot reach door degree `2`. Splitting the
outer region into one outer vertex per boundary sub-edge removes the collapse — each boundary door is
a distinct simple edge to a distinct outer vertex — while keeping the whole argument inside Mathlib's
`SimpleGraph` handshaking lemma `even_card_odd_degree_vertices`.

The handshaking count then partitions over the sum type (`Fintype.sum_sum_type`): the odd-degree
vertices split into the odd-degree cells and the odd-degree outer vertices. With each cell's
odd-degree characterization matching a `rainbow` predicate (`hcell`) and an *odd number of
odd-degree outer vertices* (`houter`, the multi-vertex analogue of "the outer region has odd
degree"), the rainbow-triangle count is forced odd.

This is the abstract backbone of the door-incidence redesign the concrete multi-triangle lattice
grid needs; the single-outer-vertex `Sperner2D.doorGraph_odd_rainbow` is the special case
`Outer := Unit` with `houter` reading off the lone outer vertex's odd degree.

## Main results

* `multiDoorGraph_odd_rainbow` — the multi-outer-vertex handshaking conclusion (odd rainbow count).
* `multiDoorGraph_exists_rainbow` — the existence corollary.

This module is **stable** and `sorry`-free. Depends on:
`Mathlib.Combinatorics.SimpleGraph.DegreeSum`, `Mathlib.Data.Fintype.BigOperators`,
`CRNT.Analysis.Sperner2D`.
-/

namespace CRNT.Analysis.Sperner2D

open Finset SimpleGraph

variable {Cell Outer : Type*} [Fintype Cell] [Fintype Outer]

/-- **Multi-outer-vertex handshaking conclusion.** Given a door graph `G : SimpleGraph (Cell ⊕ Outer)`
— with `Sum.inl x` a triangle and `Sum.inr o` a boundary outer vertex — in which each triangle's
odd-degree characterization matches the `rainbow` predicate (`hcell`) and the number of odd-degree
outer vertices is odd (`houter`), the number of rainbow triangles is odd. The handshaking lemma
`even_card_odd_degree_vertices` is split across `Fintype.sum_sum_type` into the cell and outer parts
and the cell part is transported to `rainbow`. -/
theorem multiDoorGraph_odd_rainbow
    (G : SimpleGraph (Cell ⊕ Outer)) [DecidableRel G.Adj]
    (rainbow : Cell → Prop) [DecidablePred rainbow]
    (hcell : ∀ x : Cell, Odd (G.degree (Sum.inl x)) ↔ rainbow x)
    (houter : Odd #{o : Outer | Odd (G.degree (Sum.inr o))}) :
    Odd #{x : Cell | rainbow x} := by
  classical
  have hHand := G.even_card_odd_degree_vertices
  have key : #{v : Cell ⊕ Outer | Odd (G.degree v)}
      = #{x : Cell | Odd (G.degree (Sum.inl x))} + #{o : Outer | Odd (G.degree (Sum.inr o))} := by
    simp only [Finset.card_filter, Fintype.sum_sum_type]
  rw [key] at hHand
  have hcells : Odd #{x : Cell | Odd (G.degree (Sum.inl x))} := by
    rcases hHand with ⟨k, hk⟩
    rcases houter with ⟨m, hm⟩
    exact ⟨k - m - 1, by omega⟩
  have hcard : #{x : Cell | Odd (G.degree (Sum.inl x))} = #{x : Cell | rainbow x} := by
    apply Finset.card_bij (fun x _ => x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (hcell x).mp hx
    · intro x _ y _ h; exact h
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨x, (hcell x).mpr hx, rfl⟩
  rwa [hcard] at hcells

/-- **Existence corollary.** Under the multi-outer-vertex door-graph hypotheses there is at least one
rainbow triangle. -/
theorem multiDoorGraph_exists_rainbow
    (G : SimpleGraph (Cell ⊕ Outer)) [DecidableRel G.Adj]
    (rainbow : Cell → Prop) [DecidablePred rainbow]
    (hcell : ∀ x : Cell, Odd (G.degree (Sum.inl x)) ↔ rainbow x)
    (houter : Odd #{o : Outer | Odd (G.degree (Sum.inr o))}) :
    ∃ x : Cell, rainbow x := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (multiDoorGraph_odd_rainbow G rainbow hcell houter).pos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact ⟨x, hx⟩

end CRNT.Analysis.Sperner2D

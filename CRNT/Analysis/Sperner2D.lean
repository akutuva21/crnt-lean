import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Option

/-!
# Two-dimensional Sperner lemma: the door-graph handshaking framework

This module provides the door-graph handshaking framework for the two-dimensional Sperner lemma
over a triangulation, on top of the one-dimensional parity double-count in
`CRNT.Analysis.Sperner`. The classical proof of two-dimensional Sperner counts *doors* — triangle edges
colored `{0, 1}` — and runs the handshaking lemma on the *door graph* whose vertices are the
triangles (plus one outer region) and whose edges join two triangles sharing a door. A triangle
has odd door-degree exactly when it is *rainbow* (sees all three colors), and the outer region has
odd door-degree by the one-dimensional Sperner condition on the colored boundary side; handshaking
then forces an odd, hence positive, number of rainbow triangles.

This module proves the two combinatorial pillars of that argument, with the geometry abstracted
away as hypotheses:

* the **local door-count parity** `doorCount_odd_iff`: a single triangle with vertex colors
  `a b c` has an odd number of `{0, 1}`-doors among its three edges iff it is rainbow. This is the
  finite case analysis at the heart of the lemma (`27` color triples), discharged by `decide`.
* the **abstract handshaking conclusion** `doorGraph_odd_rainbow`: for *any* door graph
  `G : SimpleGraph (Option Cell)` (`none` = the outer region, `some x` = a triangle) in which each
  triangle's odd-degree characterization matches a `rainbow` predicate and the outer region has odd
  degree, the number of rainbow triangles is odd. The proof is `even_card_odd_degree_vertices`
  (handshaking) split across `Fintype.sum_option`, transported to the `rainbow` predicate by a
  bijection.

These compose into the door-graph/handshaking *framing* of two-dimensional Sperner, with the parity
conclusion fully proved at the abstract level and the per-triangle rainbow⟺odd-door equivalence
fully proved at the combinatorial level.

## Main definitions

* `CRNT.Analysis.Sperner2D.isDoor` — whether two vertex colors form a `{0, 1}` edge.
* `CRNT.Analysis.Sperner2D.doorCount` — the number of `{0, 1}`-doors among a triangle's three edges.
* `CRNT.Analysis.Sperner2D.isRainbow` — whether a triangle's three colors are exactly `{0, 1, 2}`.

## Main results

* `doorCount_odd_iff` — the local door-count parity.
* `doorGraph_odd_rainbow` — the abstract handshaking conclusion (odd rainbow count).
* `doorGraph_exists_rainbow` — the existence corollary.

## Scope

`hcell` and `houter` remain hypotheses here. The full two-dimensional Sperner lemma over a
*concrete* triangulated grid requires a concrete triangulation datatype with a sub-edge incidence
relation, a proof that every interior `{0, 1}` sub-edge is shared by exactly two triangles (the
geometric crux), the bridge `G.degree (some t) = doorCount …` discharging `hcell` via
`doorCount_odd_iff`, and the bridge discharging `houter` by reducing the boundary door count to
`CRNT.Analysis.Sperner.sperner_odd_rainbowEdges` along the colored boundary side.

Depends on:
`Mathlib.Combinatorics.SimpleGraph.DegreeSum`, `Mathlib.Data.Fintype.Option`.
-/

namespace CRNT.Analysis.Sperner2D

open Finset SimpleGraph

/-- The three Sperner colors `0, 1, 2`. -/
abbrev Color := Fin 3

/-- Two vertex colors form a *door* when they are `{0, 1}` as an unordered pair. -/
def isDoor (x y : Color) : Bool := (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)

/-- The number of `{0, 1}`-doors among a triangle's three edges `{a,b}`, `{b,c}`, `{a,c}`. -/
def doorCount (a b c : Color) : ℕ :=
  (if isDoor a b then 1 else 0) + (if isDoor b c then 1 else 0) + (if isDoor a c then 1 else 0)

/-- A triangle is *rainbow* when its three vertex colors are exactly `{0, 1, 2}`. -/
def isRainbow (a b c : Color) : Bool :=
  ({a, b, c} : Finset Color) = {0, 1, 2}

/-- **Local door-count parity.** A triangle with vertex colors `a b c` has an odd number of
`{0, 1}`-doors among its three edges iff it is rainbow. Proved by finite case analysis over the
`27` color triples. -/
theorem doorCount_odd_iff (a b c : Color) : Odd (doorCount a b c) ↔ isRainbow a b c := by
  revert a b c; decide

variable {Cell : Type*} [Fintype Cell]

/-- **Abstract handshaking conclusion for the door graph.** Given a door graph
`G : SimpleGraph (Option Cell)` — with `none` the outer region and `some x` a triangle — in which
each triangle's odd-degree characterization matches the `rainbow` predicate (`hcell`) and the outer
region has odd degree (`houter`), the number of rainbow triangles is odd. This is the handshaking
lemma `even_card_odd_degree_vertices` split across `Fintype.sum_option` and transported to
`rainbow`. -/
theorem doorGraph_odd_rainbow
    (G : SimpleGraph (Option Cell)) [DecidableRel G.Adj]
    (rainbow : Cell → Prop) [DecidablePred rainbow]
    (hcell : ∀ x : Cell, Odd (G.degree (some x)) ↔ rainbow x)
    (houter : Odd (G.degree none)) :
    Odd #{x : Cell | rainbow x} := by
  classical
  have hHand := G.even_card_odd_degree_vertices
  set p : Option Cell → Prop := fun v => Odd (G.degree v) with hp
  have key : (#{v : Option Cell | p v} : ℕ)
      = (if p none then 1 else 0) + #{x : Cell | p (some x)} := by
    rw [Finset.card_filter, Finset.card_filter]
    rw [Fintype.sum_option]
  rw [key] at hHand
  have hnone : (if p none then (1 : ℕ) else 0) = 1 := by
    rw [if_pos]; exact houter
  rw [hnone] at hHand
  have hodd : Odd #{x : Cell | p (some x)} := by
    rcases hHand with ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    omega
  have hcard : #{x : Cell | p (some x)} = #{x : Cell | rainbow x} := by
    apply Finset.card_bij (fun x _ => x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (hcell x).mp hx
    · intro x _ y _ h; exact h
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨x, (hcell x).mpr hx, rfl⟩
  rwa [hcard] at hodd

/-- **Existence corollary.** Under the door-graph hypotheses there is at least one rainbow
triangle. -/
theorem doorGraph_exists_rainbow
    (G : SimpleGraph (Option Cell)) [DecidableRel G.Adj]
    (rainbow : Cell → Prop) [DecidablePred rainbow]
    (hcell : ∀ x : Cell, Odd (G.degree (some x)) ↔ rainbow x)
    (houter : Odd (G.degree none)) :
    ∃ x : Cell, rainbow x := by
  have hpos : 0 < #{x : Cell | rainbow x} :=
    (doorGraph_odd_rainbow G rainbow hcell houter).pos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact ⟨x, hx⟩

end CRNT.Analysis.Sperner2D

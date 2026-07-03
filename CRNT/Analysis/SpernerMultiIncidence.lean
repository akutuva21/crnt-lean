import CRNT.Analysis.Sperner2DMulti

/-!
# The multi-outer-vertex door-incidence interface

This module bundles the multi-outer-vertex handshaking conclusion `Sperner2D.multiDoorGraph_odd_rainbow`
into a `MultiDoorIncidence` structure — a variant of `CRNT.Analysis.SpernerTriangulation.DoorIncidence`
that supports a boundary cell with *several* `{0, 1}`-doors. Where `DoorIncidence` carries a door graph
on `Option Cell` (one collapsing outer region `none`), `MultiDoorIncidence` carries a door graph on
`Cell ⊕ Outer`, with one outer vertex per boundary sub-edge, so each boundary door is a distinct
adjacency and a cell's door degree can genuinely exceed one.

The structure packages the same two geometric incidence facts, now in the uncollapsed form:

* `cell_degree`: each triangle's door degree equals its local `{0, 1}`-door count — unchanged, but no
  longer capped by the single-outer-vertex collapse;
* `outer_odd`: the number of odd-degree outer vertices is odd. With one outer vertex per boundary
  sub-edge, each such vertex has degree `0` or `1`, so this counts the rainbow boundary edges — odd by
  the one-dimensional Sperner lemma. This replaces `DoorIncidence.outer_degree` (the lone outer
  region's degree) by the multi-vertex parity that `multiDoorGraph_odd_rainbow` consumes.

From these the module derives the **two-dimensional Sperner conclusion** for the uncollapsed door graph:
`odd_rainbow` (the rainbow-triangle count is odd) and `exists_rainbow` (a rainbow triangle exists).

## Scope

`MultiDoorIncidence` takes `cell_degree` and `outer_odd` as hypothesis fields. Constructing them over
a concrete multi-triangle lattice grid requires the lattice-edge incidence lemma (every interior
`{0,1}` sub-edge borders exactly two triangles; every boundary `{0,1}` sub-edge borders exactly one),
which discharges `cell_degree`, and the boundary-side reduction, which discharges `outer_odd` via the
one-dimensional `Sperner.sperner_odd_rainbowEdges`.

## Main results

* `MultiDoorIncidence` — the uncollapsed door-incidence interface over `Cell ⊕ Outer`.
* `MultiDoorIncidence.exists_rainbow` — the two-dimensional Sperner conclusion from the bundled facts.

Depends on: `CRNT.Analysis.Sperner2DMulti`.
-/

namespace CRNT.Analysis.SpernerTriangulation

open SimpleGraph Finset CRNT.Analysis CRNT.Analysis.Sperner2D

/-- A **multi-outer-vertex door-incidence datum** over abstract finite triangle and boundary-vertex
types `Cell`, `Outer`. It bundles a door graph `G : SimpleGraph (Cell ⊕ Outer)` (`Sum.inl t` a
triangle, `Sum.inr o` a boundary outer vertex), the vertex colors `col t` of each triangle, and the
two geometric incidence facts: each triangle's door degree equals its local `{0,1}`-door count
(`cell_degree`), and the number of odd-degree outer vertices is odd (`outer_odd`). Unlike
`DoorIncidence`, a cell may have several boundary doors, since each lands on a distinct outer vertex. -/
structure MultiDoorIncidence (Cell Outer : Type*) [Fintype Cell] [Fintype Outer] where
  /-- The door graph: `Sum.inl t` a triangle, `Sum.inr o` a boundary outer vertex. -/
  G : SimpleGraph (Cell ⊕ Outer)
  /-- Adjacency of the door graph is decidable. -/
  [decAdj : DecidableRel G.Adj]
  /-- The three vertex colors of each triangle. -/
  col : Cell → Sperner2D.Color × Sperner2D.Color × Sperner2D.Color
  /-- **Geometric incidence fact (cells).** Each triangle's door degree equals its local
  `{0,1}`-door count. -/
  cell_degree : ∀ t : Cell,
    G.degree (Sum.inl t) = Sperner2D.doorCount (col t).1 (col t).2.1 (col t).2.2
  /-- **Geometric incidence fact (boundary).** The number of odd-degree outer vertices is odd — the
  multi-vertex form of "the outer region has odd degree", counting the rainbow boundary edges. -/
  outer_odd : Odd #{o : Outer | Odd (G.degree (Sum.inr o))}

attribute [instance] MultiDoorIncidence.decAdj

variable {Cell Outer : Type*} [Fintype Cell] [Fintype Outer]

/-- A triangle is *rainbow* when its three vertex colors are exactly `{0, 1, 2}`. -/
def MultiDoorIncidence.IsRainbowCell (D : MultiDoorIncidence Cell Outer) (t : Cell) : Prop :=
  Sperner2D.isRainbow (D.col t).1 (D.col t).2.1 (D.col t).2.2

instance decidablePredMultiIsRainbowCell (D : MultiDoorIncidence Cell Outer) :
    DecidablePred D.IsRainbowCell := fun _ =>
  inferInstanceAs (Decidable (Sperner2D.isRainbow _ _ _ = true))

/-- **Cell parity bridge.** A triangle has odd door degree iff it is rainbow, via the local
door-count parity. -/
theorem MultiDoorIncidence.hcell (D : MultiDoorIncidence Cell Outer) :
    ∀ t : Cell, Odd (D.G.degree (Sum.inl t)) ↔ D.IsRainbowCell t := by
  intro t
  rw [D.cell_degree]
  exact Sperner2D.doorCount_odd_iff _ _ _

/-- **Two-dimensional Sperner parity.** The number of rainbow triangles is odd. -/
theorem MultiDoorIncidence.odd_rainbow (D : MultiDoorIncidence Cell Outer) :
    Odd #{t : Cell | D.IsRainbowCell t} :=
  Sperner2D.multiDoorGraph_odd_rainbow D.G D.IsRainbowCell D.hcell D.outer_odd

/-- **The two-dimensional Sperner lemma (uncollapsed door graph).** A Sperner-colored triangulation
whose boundary doors are encoded by distinct outer vertices has a rainbow triangle. -/
theorem MultiDoorIncidence.exists_rainbow (D : MultiDoorIncidence Cell Outer) :
    ∃ t : Cell, D.IsRainbowCell t :=
  Sperner2D.multiDoorGraph_exists_rainbow D.G D.IsRainbowCell D.hcell D.outer_odd

end CRNT.Analysis.SpernerTriangulation

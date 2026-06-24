import CRNT.Analysis.SpernerLatticeCellColor

/-!
# The cell adjacency of the door graph

This module begins the assembly of the door graph for the `N`-subdivision: the relation `CellDoor`
recording when two triangles **share a `{0,1}` door edge**. It is the cell–cell part of the door
graph whose degrees the eventual `cell_degree` bijection equates to `doorCount`.

`CellDoor κ t t'` holds when `t ≠ t'` and `t, t'` share two distinct vertices `u, v` whose colors form
a door (`isDoor (κ.color u) (κ.color v)`). Quantifying over the vertices of the triangles — rather
than over a precomputed edge list — keeps the relation defined directly from `triVerts` and the
coloring, so the lattice-edge incidence lemmas of `CRNT.Analysis.SpernerLatticeIncidence` and
`CRNT.Analysis.SpernerLatticeIncidenceHV` can later identify the unique partner across each door edge.

The relation is decidable (a bounded search over the finite vertex sets), symmetric (the shared-edge
witness is symmetric in the two triangles), and irreflexive (it requires `t ≠ t'`). These are the
structural facts the `SimpleGraph` packaging and the neighbor-finset count build on.

## Main definitions

* `CellDoor` — two triangles share a `{0,1}` door edge.

## Main results

* `cellDoor_symm`, `cellDoor_irrefl` — symmetry and irreflexivity of the cell adjacency.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.SpernerLatticeCellColor`.
-/

namespace CRNT.Analysis.SpernerLattice

open CRNT.Analysis.Sperner2D

variable {N : ℕ}

/-- Two triangles **share a `{0,1}` door edge**: they are distinct and have two common distinct
vertices whose colors form a door. This is the cell–cell adjacency of the door graph. -/
def CellDoor (κ : SpernerColoring N) (t t' : Cell N) : Prop :=
  t ≠ t' ∧ ∃ u ∈ triVerts t, ∃ v ∈ triVerts t,
    u ≠ v ∧ u ∈ triVerts t' ∧ v ∈ triVerts t' ∧ isDoor (κ.color u) (κ.color v) = true

instance (κ : SpernerColoring N) : DecidableRel (CellDoor κ) := fun t t' => by
  unfold CellDoor; infer_instance

/-- The cell adjacency is symmetric: a shared door edge of `t` and `t'` is equally a shared door
edge of `t'` and `t`. -/
theorem cellDoor_symm (κ : SpernerColoring N) {t t' : Cell N} (h : CellDoor κ t t') :
    CellDoor κ t' t := by
  obtain ⟨hne, u, hut, v, hvt, huv, hut', hvt', hd⟩ := h
  exact ⟨hne.symm, u, hut', v, hvt', huv, hut, hvt, hd⟩

/-- The cell adjacency is irreflexive. -/
theorem cellDoor_irrefl (κ : SpernerColoring N) (t : Cell N) : ¬ CellDoor κ t t :=
  fun h => h.1 rfl

end CRNT.Analysis.SpernerLattice

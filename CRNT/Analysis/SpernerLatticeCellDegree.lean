import CRNT.Analysis.SpernerLatticeFullGraph
import CRNT.Analysis.SpernerLatticeNeighbor
import CRNT.Analysis.SpernerLatticeIncidence
import CRNT.Analysis.SpernerLatticeIncidenceHV

/-!
# Locating and constructing the cell neighbours of the door graph

Scaffolding toward the `cell_degree` obligation of `MultiDoorIncidence` (that each cell's door-graph
degree equals its local `doorCount`). The two directions of the eventual neighbour-finset bijection:

* **Locators** — `up_cellDoor_partner` / `down_cellDoor_partner`: a door-neighbour of a triangle has
  index pinned to one of the three lattice partners (diagonal, horizontal-shifted, vertical-shifted),
  by `up_down_share_two`.
* **Constructions** — `down_diagonal_cellDoor`: when an interior diagonal carries a door, the down-
  and up-triangle sharing it are door-adjacent (the template for the remaining five edge cases).
* `down_not_adj_outer`: a down-triangle is never adjacent to an outer vertex (only up-triangles reach
  the hypotenuse), so a down-triangle's degree counts cell-neighbours only.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.SpernerLatticeFullGraph`,
`CRNT.Analysis.SpernerLatticeNeighbor`, `CRNT.Analysis.SpernerLatticeIncidence`,
`CRNT.Analysis.SpernerLatticeIncidenceHV`.
-/

namespace CRNT.Analysis.SpernerLattice

open CRNT.Analysis.Sperner2D

variable {N : ℕ}

/-- A door-neighbour `d` of an up-triangle `u` has its index at one of `u`'s three lattice partners. -/
theorem up_cellDoor_partner (κ : SpernerColoring N) {u : Up N} {d : Down N}
    (h : CellDoor κ (Sum.inl u) (Sum.inr d)) :
    (d.1.1 = u.1.1 ∧ d.1.2 = u.1.2) ∨ (d.1.1 = u.1.1 ∧ d.1.2 + 1 = u.1.2) ∨
      (d.1.1 + 1 = u.1.1 ∧ d.1.2 = u.1.2) := by
  obtain ⟨_, p, hpu, q, hqu, hpq, hpd, hqd, _⟩ := h
  exact up_down_share_two hpu hpd hqu hqd hpq

/-- A door-neighbour `u` of a down-triangle `d` has its index at one of `d`'s three lattice partners. -/
theorem down_cellDoor_partner (κ : SpernerColoring N) {d : Down N} {u : Up N}
    (h : CellDoor κ (Sum.inr d) (Sum.inl u)) :
    (d.1.1 = u.1.1 ∧ d.1.2 = u.1.2) ∨ (d.1.1 = u.1.1 ∧ d.1.2 + 1 = u.1.2) ∨
      (d.1.1 + 1 = u.1.1 ∧ d.1.2 = u.1.2) := by
  obtain ⟨_, p, hpd, q, hqd, hpq, hpu, hqu, _⟩ := h
  exact up_down_share_two hpu hpd hqu hqd hpq

/-- A down-triangle is never adjacent to an outer vertex: outer vertices attach only to up-triangles
(the hypotenuse diagonals). -/
theorem down_not_adj_outer (κ : SpernerColoring N) (d : Down N) (k : Outer N) :
    ¬ (fullDoorGraph κ).Adj (Sum.inl (Sum.inr d)) (Sum.inr k) := by
  rw [fullDoorGraph_adj_inl_inr]; rintro ⟨h, _⟩; exact absurd h (by simp [outerTri])

/-- **Construction template (diagonal).** When an interior diagonal carries a door, the down- and
up-triangle sharing it are door-adjacent. -/
theorem down_diagonal_cellDoor (κ : SpernerColoring N) (a b : ℕ) (hd : a + b + 2 ≤ N)
    (hdoor : isDoor (κ.color (mkPt (a + 1) b (by omega))) (κ.color (mkPt a (b + 1) (by omega)))
      = true) :
    CellDoor κ (Sum.inr ⟨(a, b), by rw [mem_downCarrier]; omega⟩)
      (Sum.inl ⟨(a, b), by rw [mem_upCarrier]; omega⟩) := by
  refine ⟨by simp, mkPt (a + 1) b (by omega), ?_, mkPt a (b + 1) (by omega), ?_, ?_, ?_, ?_, hdoor⟩
  · simp [triVerts, downVerts]
  · simp [triVerts, downVerts]
  · rw [Ne, mkPt_inj]; omega
  · simp [triVerts, upVerts]
  · simp [triVerts, upVerts]

end CRNT.Analysis.SpernerLattice

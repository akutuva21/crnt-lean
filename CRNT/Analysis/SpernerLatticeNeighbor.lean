import CRNT.Analysis.SpernerLatticeBipartite

/-!
# Locating the door-graph neighbors of a triangle

Building on the bipartiteness of `CRNT.Analysis.SpernerLatticeBipartite`, this module *locates* the
door-graph neighbors of each triangle, the step before counting them. Two facts combine:

* **Orientation** (`cellDoor_inl_isRight`, `cellDoor_inr_isLeft`): a door-neighbor of an up-triangle
  is a down-triangle, and vice versa — immediate from bipartiteness.
* **Index** (`up_down_share_two`): if an up-triangle `up(a, b)` and a down-triangle `down(c, e)` share
  two distinct vertices, then `down(c, e)` is one of the three partners across `up(a, b)`'s edges —
  the diagonal `down(a, b)`, the horizontal `down(a, b-1)`, or the vertical `down(a-1, b)`. Proved
  uniform in `N` by unfolding the vertex memberships to coordinates and `omega`.

Together these confine an up-triangle's neighbors to at most three explicit down-triangles (and dually
for a down-triangle), reducing the degree count to checking, edge by edge, which partner exists and
carries a door — discharged by the lattice-edge incidence lemmas.

## Main results

* `cellDoor_inl_isRight`, `cellDoor_inr_isLeft` — neighbors have the opposite orientation.
* `up_down_share_two` — a shared edge pins the partner index to one of three.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.SpernerLatticeBipartite`.
-/

namespace CRNT.Analysis.SpernerLattice

variable {N : ℕ}

/-- A door-neighbor of an up-triangle is a down-triangle. -/
theorem cellDoor_inl_isRight (κ : SpernerColoring N) {u : Up N} {t' : Cell N}
    (h : cellDoor κ (Sum.inl u) t') : ∃ d : Down N, t' = Sum.inr d := by
  cases t' with
  | inl u' => exact absurd h (not_cellDoor_inl_inl κ u u')
  | inr d => exact ⟨d, rfl⟩

/-- A door-neighbor of a down-triangle is an up-triangle. -/
theorem cellDoor_inr_isLeft (κ : SpernerColoring N) {d : Down N} {t' : Cell N}
    (h : cellDoor κ (Sum.inr d) t') : ∃ u : Up N, t' = Sum.inl u := by
  cases t' with
  | inl u => exact ⟨u, rfl⟩
  | inr d' => exact absurd h (not_cellDoor_inr_inr κ d d')

/-- **The partner index is one of three.** If an up-triangle `up(a, b)` and a down-triangle
`down(c, e)` share two distinct vertices, then `(c, e)` is the diagonal partner `(a, b)`, the
horizontal partner `(a, b-1)`, or the vertical partner `(a-1, b)`. -/
theorem up_down_share_two {u : Up N} {d : Down N} {p q : Pt N}
    (hpu : p ∈ upVerts u) (hpd : p ∈ downVerts d) (hqu : q ∈ upVerts u) (hqd : q ∈ downVerts d)
    (hpq : p ≠ q) :
    (d.1.1 = u.1.1 ∧ d.1.2 = u.1.2) ∨
      (d.1.1 = u.1.1 ∧ d.1.2 + 1 = u.1.2) ∨
      (d.1.1 + 1 = u.1.1 ∧ d.1.2 = u.1.2) := by
  rw [Ne, Subtype.ext_iff, Prod.ext_iff] at hpq
  simp only [upVerts, downVerts, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkPt,
    Prod.ext_iff] at hpu hpd hqu hqd
  omega

end CRNT.Analysis.SpernerLattice

import CRNT.Analysis.SpernerLatticeDoorGraph

/-!
# The door graph is bipartite between up- and down-triangles

This module proves the structural keystone of the door-degree bijection: in the `N`-subdivision two
triangles of the **same orientation** never share an edge, so the cell adjacency `cellDoor` relates
only an up-triangle to a down-triangle. This bipartiteness is what lets the neighbor-finset count
later reduce to "which down-triangle lies across each door edge of an up-triangle" (and conversely),
via the lattice-edge incidence lemmas.

The geometric core is that two distinct up-triangles (or two distinct down-triangles) share **at most
one vertex** (`up_up_share_le_one`, `down_down_share_le_one`): two common distinct vertices force the
indices to coincide. Each is a uniform-in-`N` computation — the three-element vertex memberships are
unfolded to their coordinate components and the index equality is discharged by `omega`. Since
`cellDoor` requires two common distinct vertices, it cannot hold between two up-triangles
(`not_cellDoor_inl_inl`) or two down-triangles (`not_cellDoor_inr_inr`).

## Main results

* `up_up_share_le_one`, `down_down_share_le_one` — same-orientation triangles share at most one vertex.
* `not_cellDoor_inl_inl`, `not_cellDoor_inr_inr` — `cellDoor` holds only between opposite orientations.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.SpernerLatticeDoorGraph`.
-/

namespace CRNT.Analysis.SpernerLattice

open CRNT.Analysis.Sperner2D

variable {N : ℕ}

/-- **Two distinct up-triangles share at most one vertex.** Two common distinct vertices force the
indices to coincide. -/
theorem up_up_share_le_one {u u' : Up N} {p q : Pt N}
    (hpu : p ∈ upVerts u) (hpu' : p ∈ upVerts u') (hqu : q ∈ upVerts u) (hqu' : q ∈ upVerts u')
    (hpq : p ≠ q) : u = u' := by
  rw [Ne, Subtype.ext_iff, Prod.ext_iff] at hpq
  rw [Subtype.ext_iff, Prod.ext_iff]
  simp only [upVerts, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkPt,
    Prod.ext_iff] at hpu hpu' hqu hqu' ⊢
  omega

/-- **Two distinct down-triangles share at most one vertex.** -/
theorem down_down_share_le_one {u u' : Down N} {p q : Pt N}
    (hpu : p ∈ downVerts u) (hpu' : p ∈ downVerts u') (hqu : q ∈ downVerts u)
    (hqu' : q ∈ downVerts u') (hpq : p ≠ q) : u = u' := by
  rw [Ne, Subtype.ext_iff, Prod.ext_iff] at hpq
  rw [Subtype.ext_iff, Prod.ext_iff]
  simp only [downVerts, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkPt,
    Prod.ext_iff] at hpu hpu' hqu hqu' ⊢
  omega

/-- **No two up-triangles are door-adjacent**: they cannot share the two distinct vertices a door
edge requires. -/
theorem not_cellDoor_inl_inl (κ : SpernerColoring N) (u u' : Up N) :
    ¬ cellDoor κ (Sum.inl u) (Sum.inl u') := by
  rintro ⟨hne, p, hpu, q, hqu, hpq, hpu', hqu', _⟩
  simp only [triVerts, Sum.elim_inl] at hpu hqu hpu' hqu'
  exact hne (congrArg Sum.inl (up_up_share_le_one hpu hpu' hqu hqu' hpq))

/-- **No two down-triangles are door-adjacent.** -/
theorem not_cellDoor_inr_inr (κ : SpernerColoring N) (d d' : Down N) :
    ¬ cellDoor κ (Sum.inr d) (Sum.inr d') := by
  rintro ⟨hne, p, hpu, q, hqu, hpq, hpu', hqu', _⟩
  simp only [triVerts, Sum.elim_inr] at hpu hqu hpu' hqu'
  exact hne (congrArg Sum.inr (down_down_share_le_one hpu hpu' hqu hqu' hpq))

end CRNT.Analysis.SpernerLattice

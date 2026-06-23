import CRNT.Analysis.SpernerLattice

/-!
# The lattice-edge incidence lemma (horizontal and vertical edges)

This module completes the lattice-edge incidence lemma of `CRNT.Analysis.SpernerLatticeIncidence` for
the remaining two edge orientations of the `N`-subdivision — **horizontal** and **vertical** edges —
uniform in `N`. Together with the diagonal case, every `{0,1}` sub-edge of the triangulation is now
known to border exactly two triangles when interior and exactly one when on the boundary.

* A **horizontal** edge `{(i, j), (i+1, j)}` is shared by `up(i, j)` and (when `j ≥ 1`) the down
  triangle `down(i, j-1)` below it; on the bottom side `j = 0` it bounds only `up(i, 0)`.
* A **vertical** edge `{(i, j), (i, j+1)}` is shared by `up(i, j)` and (when `i ≥ 1`) the down
  triangle `down(i-1, j)` to its left; on the left side `i = 0` it bounds only `up(0, j)`.

The proofs follow the diagonal pattern — case split on the cell, unfold the three-element vertex
membership by `simp`, and discharge the coordinate constraints by `omega` — with `and_false` added to
collapse the impossible boundary alignments (a coordinate forced to equal `0` against a successor)
that `omega` does not simplify on its own.

## Main results

* `horiz_incidence_interior`, `horiz_incidence_boundary` — horizontal-edge incidence.
* `vert_incidence_interior`, `vert_incidence_boundary` — vertical-edge incidence.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.SpernerLattice`.
-/

namespace CRNT.Analysis.SpernerLattice

/-- **Interior horizontal incidence.** A horizontal edge `{(i, j), (i+1, j)}` with `j ≥ 1` is
contained in exactly `up(i, j)` and the down triangle `down(i, j-1)` below it. -/
theorem horiz_incidence_interior (N i j : ℕ) (hj : 1 ≤ j) (hub : i + j + 1 ≤ N) (c : Cell N) :
    (mkPt i j (by omega) ∈ triVerts c ∧ mkPt (i + 1) j (by omega) ∈ triVerts c) ↔
      (c = Sum.inl ⟨(i, j), by rw [mem_upCarrier]; omega⟩ ∨
        c = Sum.inr ⟨(i, j - 1), by rw [mem_downCarrier]; omega⟩) := by
  cases c with
  | inl u =>
    obtain ⟨⟨a, b⟩, hu⟩ := u
    simp only [triVerts, Sum.elim_inl, upVerts, Finset.mem_insert, Finset.mem_singleton, mkPt_inj,
      Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq, reduceCtorEq, or_false]
    omega
  | inr d =>
    obtain ⟨⟨a, b⟩, hd'⟩ := d
    simp only [triVerts, Sum.elim_inr, downVerts, Finset.mem_insert, Finset.mem_singleton, mkPt_inj,
      Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq, reduceCtorEq, false_or]
    omega

/-- **Boundary horizontal incidence.** A horizontal edge `{(i, 0), (i+1, 0)}` on the bottom side
bounds exactly the one triangle `up(i, 0)`. -/
theorem horiz_incidence_boundary (N i : ℕ) (hi : i + 1 ≤ N) (c : Cell N) :
    (mkPt i 0 (by omega) ∈ triVerts c ∧ mkPt (i + 1) 0 (by omega) ∈ triVerts c) ↔
      c = Sum.inl ⟨(i, 0), by rw [mem_upCarrier]; omega⟩ := by
  cases c with
  | inl u =>
    obtain ⟨⟨a, b⟩, hu⟩ := u
    simp only [triVerts, Sum.elim_inl, upVerts, Finset.mem_insert, Finset.mem_singleton, mkPt_inj,
      Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq]
    omega
  | inr d =>
    obtain ⟨⟨a, b⟩, hd'⟩ := d
    simp only [triVerts, Sum.elim_inr, downVerts, Finset.mem_insert, Finset.mem_singleton, mkPt_inj,
      reduceCtorEq, iff_false, not_and, and_false, or_false]
    omega

/-- **Interior vertical incidence.** A vertical edge `{(i, j), (i, j+1)}` with `i ≥ 1` is contained in
exactly `up(i, j)` and the down triangle `down(i-1, j)` to its left. -/
theorem vert_incidence_interior (N i j : ℕ) (hi : 1 ≤ i) (hub : i + j + 1 ≤ N) (c : Cell N) :
    (mkPt i j (by omega) ∈ triVerts c ∧ mkPt i (j + 1) (by omega) ∈ triVerts c) ↔
      (c = Sum.inl ⟨(i, j), by rw [mem_upCarrier]; omega⟩ ∨
        c = Sum.inr ⟨(i - 1, j), by rw [mem_downCarrier]; omega⟩) := by
  cases c with
  | inl u =>
    obtain ⟨⟨a, b⟩, hu⟩ := u
    simp only [triVerts, Sum.elim_inl, upVerts, Finset.mem_insert, Finset.mem_singleton, mkPt_inj,
      Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq, reduceCtorEq, or_false]
    omega
  | inr d =>
    obtain ⟨⟨a, b⟩, hd'⟩ := d
    simp only [triVerts, Sum.elim_inr, downVerts, Finset.mem_insert, Finset.mem_singleton, mkPt_inj,
      Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq, reduceCtorEq, false_or]
    omega

/-- **Boundary vertical incidence.** A vertical edge `{(0, j), (0, j+1)}` on the left side bounds
exactly the one triangle `up(0, j)`. -/
theorem vert_incidence_boundary (N j : ℕ) (hj : j + 1 ≤ N) (c : Cell N) :
    (mkPt 0 j (by omega) ∈ triVerts c ∧ mkPt 0 (j + 1) (by omega) ∈ triVerts c) ↔
      c = Sum.inl ⟨(0, j), by rw [mem_upCarrier]; omega⟩ := by
  cases c with
  | inl u =>
    obtain ⟨⟨a, b⟩, hu⟩ := u
    simp only [triVerts, Sum.elim_inl, upVerts, Finset.mem_insert, Finset.mem_singleton, mkPt_inj,
      Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq]
    omega
  | inr d =>
    obtain ⟨⟨a, b⟩, hd'⟩ := d
    simp only [triVerts, Sum.elim_inr, downVerts, Finset.mem_insert, Finset.mem_singleton, mkPt_inj,
      reduceCtorEq, iff_false, not_and, false_and, false_or, or_false]
    omega

end CRNT.Analysis.SpernerLattice

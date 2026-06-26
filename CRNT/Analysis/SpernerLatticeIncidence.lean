import CRNT.Analysis.SpernerLattice

/-!
# The lattice-edge incidence lemma (diagonal edges)

This module proves the key geometric fact of the `N`-subdivision for its **diagonal** edges,
uniform in `N`: a diagonal edge `{(i+1, j), (i, j+1)}` borders **exactly two** triangles when it is
interior, and **exactly one** when it lies on the boundary. This is the diagonal case of the
incidence lemma the PLAN names — "every interior `{0,1}` sub-edge is shared by exactly two triangles;
every boundary `{0,1}` sub-edge bounds exactly one" — and it is exactly the interior-door incidence
that `CRNT.Analysis.SpernerGridGeometric` verified by `decide` at `N = 2`, now established for all `N`.

The diagonal `{(i+1, j), (i, j+1)}` is shared by the up triangle `up(i, j)` and the down triangle
`down(i, j)` (both indexed by the same `(i, j)`):

* `diag_incidence_interior` — when `down(i, j)` exists (`i + j + 2 ≤ N`), the only triangles
  containing both endpoints are `up(i, j)` and `down(i, j)`;
* `diag_incidence_boundary` — when the diagonal is the outer one (`i + j + 1 = N`, so `down(i, j)`
  does not exist), the only triangle containing both endpoints is `up(i, j)`.

Each proof is uniform in `N`: a case split on the cell (up vs down), the three-element membership of
its vertex set unfolded by `simp`, and the resulting coordinate constraints discharged by `omega`.
The same pattern handles the horizontal and vertical edge orientations (with the partner down
triangle at a shifted index), left to a follow-on step.

## Main results

* `diag_incidence_interior` — an interior diagonal borders exactly two triangles.
* `diag_incidence_boundary` — a boundary diagonal borders exactly one triangle.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.SpernerLattice`.
-/

namespace CRNT.Analysis.SpernerLattice

/-- **Interior diagonal incidence.** When the down triangle `down(i, j)` exists, the diagonal edge
`{(i+1, j), (i, j+1)}` is contained in exactly the two triangles `up(i, j)` and `down(i, j)`. -/
theorem diag_incidence_interior (N i j : ℕ) (hd : i + j + 2 ≤ N) (c : Cell N) :
    (mkPt (i + 1) j (by omega) ∈ triVerts c ∧ mkPt i (j + 1) (by omega) ∈ triVerts c) ↔
      (c = Sum.inl ⟨(i, j), by rw [mem_upCarrier]; omega⟩ ∨
        c = Sum.inr ⟨(i, j), by rw [mem_downCarrier]; omega⟩) := by
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

/-- **Boundary diagonal incidence.** When the diagonal `{(i+1, j), (i, j+1)}` is the outer one
(`i + j + 1 = N`, so `down(i, j)` does not exist), the only triangle containing both endpoints is
`up(i, j)`. -/
theorem diag_incidence_boundary (N i j : ℕ) (hb : i + j + 1 = N) (c : Cell N) :
    (mkPt (i + 1) j (by omega) ∈ triVerts c ∧ mkPt i (j + 1) (by omega) ∈ triVerts c) ↔
      c = Sum.inl ⟨(i, j), by rw [mem_upCarrier]; omega⟩ := by
  cases c with
  | inl u =>
    obtain ⟨⟨a, b⟩, hu⟩ := u
    simp only [triVerts, Sum.elim_inl, upVerts, Finset.mem_insert, Finset.mem_singleton, mkPt_inj,
      Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq]
    omega
  | inr d =>
    obtain ⟨⟨a, b⟩, hd'⟩ := d
    rw [mem_downCarrier] at hd'
    simp only [triVerts, Sum.elim_inr, downVerts, Finset.mem_insert, Finset.mem_singleton, mkPt_inj,
      reduceCtorEq, iff_false, not_and]
    omega

end CRNT.Analysis.SpernerLattice

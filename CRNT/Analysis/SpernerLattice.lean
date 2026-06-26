import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import CRNT.Analysis.Sperner2D

/-!
# The parametric N-subdivision of the 2-simplex: geometry layer

This module begins the *arbitrary-N* barycentric subdivision of the 2-simplex, generalizing the fixed
four-cell `N = 2` triangulation of `CRNT.Analysis.SpernerGridGeometric`. It supplies the geometric
data — lattice points, the up/down triangles, their vertex sets, and the Sperner coloring abstraction
— on which the later steps (the lattice-edge incidence lemma, the door-degree bijection, the
multi-outer assembly) will build toward a fully general two-dimensional Sperner lemma.

## Lattice points and cells

A **lattice point** of the `N`-subdivision is a pair `(i, j)` with `i + j ≤ N` (the third barycentric
coordinate `k = N − i − j` is implicit); these are the elements of `Pt N`, a `Fintype` carved out of
`ℕ × ℕ` by the carrier finset `ptCarrier`. The triangulation has two families of triangles:

* **up** triangles `Up N`, indexed by `(i, j)` with `i + j + 1 ≤ N`, with vertices
  `(i, j), (i+1, j), (i, j+1)`;
* **down** (inverted) triangles `Down N`, indexed by `(i, j)` with `i + j + 2 ≤ N`, with vertices
  `(i+1, j), (i, j+1), (i+1, j+1)`.

`Cell N := Up N ⊕ Down N` is the triangle type, and `triVerts : Cell N → Finset (Pt N)` reads off the
three vertices of each. `triVerts_card` proves every triangle has exactly three distinct vertices —
the basis for its three edges and its `doorCount`.

## Sperner coloring

`SpernerColoring N` is a color `Pt N → Fin 3` satisfying the proper boundary condition: a vertex
colored `0` has `i > 0`, colored `1` has `j > 0`, colored `2` has `k = N − i − j > 0` — equivalently,
each color names a strictly positive barycentric coordinate. This forces the corners to `0, 1, 2` and
each boundary side to avoid the opposite color, the hypothesis the two-dimensional Sperner lemma needs.

## Main definitions

* `Pt`, `mkPt`, `mkPt_inj` — lattice points and their equality.
* `Up`, `Down`, `Cell`, `triVerts` — triangles and their vertex sets.
* `SpernerColoring` — the proper Sperner coloring abstraction.

## Main results

* `triVerts_card` — every triangle has exactly three vertices.

This module is **stable** and `sorry`-free. Depends on: `Mathlib.Data.Finset.Prod`,
`Mathlib.Data.Finset.Card`, `CRNT.Analysis.Sperner2D`.
-/

namespace CRNT.Analysis.SpernerLattice

open CRNT.Analysis.Sperner2D

/-- The carrier finset of lattice points: pairs `(i, j)` with `i + j ≤ N`. -/
def ptCarrier (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun p => p.1 + p.2 ≤ N)

@[simp] theorem mem_ptCarrier {N : ℕ} {p : ℕ × ℕ} : p ∈ ptCarrier N ↔ p.1 + p.2 ≤ N := by
  simp only [ptCarrier, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega

/-- A lattice point of the `N`-subdivision of the 2-simplex: `(i, j)` with `i + j ≤ N`. -/
abbrev Pt (N : ℕ) : Type := {p : ℕ × ℕ // p ∈ ptCarrier N}

/-- Build a lattice point from coordinates `i, j` with `i + j ≤ N`. -/
def mkPt {N : ℕ} (i j : ℕ) (h : i + j ≤ N) : Pt N := ⟨(i, j), mem_ptCarrier.mpr h⟩

@[simp] theorem mkPt_inj {N : ℕ} {i j i' j' : ℕ} {h : i + j ≤ N} {h' : i' + j' ≤ N} :
    mkPt i j h = mkPt i' j' h' ↔ i = i' ∧ j = j' := by
  simp only [mkPt, Subtype.mk.injEq, Prod.mk.injEq]

/-- The carrier of up-triangle indices: `(i, j)` with `i + j + 1 ≤ N`. -/
def upCarrier (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun p => p.1 + p.2 + 1 ≤ N)

@[simp] theorem mem_upCarrier {N : ℕ} {p : ℕ × ℕ} : p ∈ upCarrier N ↔ p.1 + p.2 + 1 ≤ N := by
  simp only [upCarrier, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega

/-- The carrier of down-triangle indices: `(i, j)` with `i + j + 2 ≤ N`. -/
def downCarrier (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun p => p.1 + p.2 + 2 ≤ N)

@[simp] theorem mem_downCarrier {N : ℕ} {p : ℕ × ℕ} : p ∈ downCarrier N ↔ p.1 + p.2 + 2 ≤ N := by
  simp only [downCarrier, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega

/-- An **up** (upright) triangle of the subdivision, indexed by its lower-left corner. -/
abbrev Up (N : ℕ) : Type := {p : ℕ × ℕ // p ∈ upCarrier N}

/-- A **down** (inverted) triangle of the subdivision. -/
abbrev Down (N : ℕ) : Type := {p : ℕ × ℕ // p ∈ downCarrier N}

/-- The triangles of the subdivision: up triangles and down triangles. -/
abbrev Cell (N : ℕ) : Type := Up N ⊕ Down N

/-- The three vertices of an up triangle: `(i, j), (i+1, j), (i, j+1)`. -/
def upVerts {N : ℕ} (c : Up N) : Finset (Pt N) :=
  {mkPt c.1.1 c.1.2 (by have := mem_upCarrier.mp c.2; omega),
    mkPt (c.1.1 + 1) c.1.2 (by have := mem_upCarrier.mp c.2; omega),
    mkPt c.1.1 (c.1.2 + 1) (by have := mem_upCarrier.mp c.2; omega)}

/-- The three vertices of a down triangle: `(i+1, j), (i, j+1), (i+1, j+1)`. -/
def downVerts {N : ℕ} (c : Down N) : Finset (Pt N) :=
  {mkPt (c.1.1 + 1) c.1.2 (by have := mem_downCarrier.mp c.2; omega),
    mkPt c.1.1 (c.1.2 + 1) (by have := mem_downCarrier.mp c.2; omega),
    mkPt (c.1.1 + 1) (c.1.2 + 1) (by have := mem_downCarrier.mp c.2; omega)}

/-- The three vertices of a triangle. -/
def triVerts {N : ℕ} (c : Cell N) : Finset (Pt N) := Sum.elim upVerts downVerts c

theorem upVerts_card {N : ℕ} (c : Up N) : (upVerts c).card = 3 := by
  rw [upVerts, Finset.card_eq_three]
  refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩
  · rw [Ne, mkPt_inj]; omega
  · rw [Ne, mkPt_inj]; omega
  · rw [Ne, mkPt_inj]; omega

theorem downVerts_card {N : ℕ} (c : Down N) : (downVerts c).card = 3 := by
  rw [downVerts, Finset.card_eq_three]
  refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩
  · rw [Ne, mkPt_inj]; omega
  · rw [Ne, mkPt_inj]; omega
  · rw [Ne, mkPt_inj]; omega

/-- **Every triangle has exactly three vertices.** -/
theorem triVerts_card {N : ℕ} (c : Cell N) : (triVerts c).card = 3 := by
  cases c with
  | inl u => exact upVerts_card u
  | inr d => exact downVerts_card d

/-- A **proper Sperner coloring** of the `N`-subdivision: each lattice point is colored by a strictly
positive barycentric coordinate. A vertex colored `0` has `i > 0`, colored `1` has `j > 0`, and
colored `2` has `k = N − i − j > 0` (i.e. `i + j < N`). This is the boundary hypothesis of the
two-dimensional Sperner lemma; it forces the corners to `0, 1, 2`. -/
structure SpernerColoring (N : ℕ) where
  /-- The color of each lattice point. -/
  color : Pt N → Color
  /-- A point colored `0` has a positive first coordinate. -/
  proper0 : ∀ p : Pt N, color p = 0 → 0 < p.1.1
  /-- A point colored `1` has a positive second coordinate. -/
  proper1 : ∀ p : Pt N, color p = 1 → 0 < p.1.2
  /-- A point colored `2` has a positive third (implicit) coordinate `k = N − i − j`. -/
  proper2 : ∀ p : Pt N, color p = 2 → p.1.1 + p.1.2 < N

end CRNT.Analysis.SpernerLattice

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Option
import CRNT.Analysis.Sperner2D
import CRNT.Analysis.Sperner
import CRNT.Analysis.SpernerTriangulation

/-!
# A concrete single-cell door-incidence datum

This module constructs a *concrete* `CRNT.Analysis.SpernerTriangulation.DoorIncidence` term over an
explicitly built finite triangle type and feeds it to
`CRNT.Analysis.SpernerTriangulation.DoorIncidence.exists_rainbow`, exercising the whole
door-incidence pipeline on a genuinely constructed (non-abstract) term.

The triangulated domain is the minimal one: a single triangle `Cell` carrying the rainbow color
triple `(0, 1, 2)`, with the outer region `none` and the cell `some Cell.tri` joined by exactly one
door. The colored boundary side is the one-edge segment `0, 1` with `bc 0 = false`, `bc 1 = true`,
the minimal one-dimensional Sperner coloring (one rainbow edge).

The two key geometric incidence fields are proved by direct degree computation on the
two-vertex door graph `Option Cell`:

* `cell_degree`: the cell's door degree is `1`, matching `doorCount 0 1 2 = 1`;
* `outer_degree`: the outer region's door degree is `1`, matching the single rainbow edge of the
  boundary segment.

Each degree is computed by exhibiting the neighbor finset explicitly (`Finset.ext` over the
two-element `Option Cell`, decided pointwise) and rewriting through
`SimpleGraph.card_neighborFinset_eq_degree`.

## Main definitions

* `CRNT.Analysis.SpernerGrid.Cell` — the single-triangle datatype with a manual `Fintype` instance.
* `CRNT.Analysis.SpernerGrid.doorGraph` — the two-vertex door graph via `SimpleGraph.fromRel`.
* `CRNT.Analysis.SpernerGrid.boundaryColoring` — the minimal Sperner boundary coloring of `0, 1`.
* `CRNT.Analysis.SpernerGrid.doorIncidence` — the packaged concrete `DoorIncidence Cell`.

## Main results

* `CRNT.Analysis.SpernerGrid.exists_rainbow_cell` — the concretely constructed door-incidence datum
  has a rainbow triangle.

## What is deferred

A *multi-triangle* grid (the up/down lattice split of `{(i, j) : i + j ≤ N}`) is not reachable
`sorry`-free in one module, and not only for size: `DoorIncidence.G` is a `SimpleGraph`, so the
outer vertex `none` collapses every one of a cell's boundary doors into a single adjacency. A
boundary cell with two `{0,1}` boundary edges then cannot satisfy
`cell_degree : G.degree (some t) = doorCount … = 2` (its only extra neighbor on the boundary is
`none`, one edge), and `outer_degree` requires each boundary rainbow edge to come from a distinct
cell. Resolving this needs per-cell `≤ 1`-boundary-door bookkeeping together with the interior
"every `{0,1}` sub-edge is shared by exactly two triangles" incidence lemma — the genuine geometric
crux, and multi-module work that cannot edit the committed `DoorIncidence` structure. The
single-cell datum here sidesteps the collapse (one cell, one door to `none`).

This module is **stable** and `sorry`-free. Depends on:
`Mathlib.Combinatorics.SimpleGraph.Finite`, `Mathlib.Data.Fintype.Option`,
`CRNT.Analysis.Sperner2D`, `CRNT.Analysis.Sperner`, `CRNT.Analysis.SpernerTriangulation`.
-/

namespace CRNT.Analysis.SpernerGrid

open SimpleGraph Finset CRNT.Analysis CRNT.Analysis.Sperner2D

/-- The single-triangle datatype of the minimal triangulated domain. -/
inductive Cell
  | tri
  deriving DecidableEq

/-- Manual `Fintype` instance for the single-triangle type. -/
instance : Fintype Cell := ⟨{Cell.tri}, by intro x; cases x; decide⟩

/-- The three vertex colors of each triangle: the rainbow triple `(0, 1, 2)`. -/
def cellColors : Cell → Color × Color × Color := fun _ => (0, 1, 2)

/-- The minimal one-dimensional Sperner boundary coloring of the segment `0, 1`:
`bc 0 = false`, `bc 1 = true`. -/
def boundaryColoring : ℕ → Bool := fun i => decide (1 ≤ i)

/-- The boundary coloring satisfies the one-dimensional Sperner boundary condition. -/
theorem boundaryColoring_sperner : Sperner.IsSpernerColoring 1 boundaryColoring := by
  constructor <;> decide

/-- The door relation on `Option Cell`: the outer region `none` and the cell `some Cell.tri` form a
single door. -/
def doorRel : Option Cell → Option Cell → Prop := fun a b =>
  (a = none ∧ b = some Cell.tri) ∨ (a = some Cell.tri ∧ b = none)

instance : DecidableRel doorRel := fun a b => by
  unfold doorRel; infer_instance

/-- The two-vertex door graph. -/
def doorGraph : SimpleGraph (Option Cell) := SimpleGraph.fromRel doorRel

instance : DecidableRel doorGraph.Adj := by
  unfold doorGraph; infer_instance

/-- The neighbor finset of the cell is exactly the outer region `{none}`. -/
theorem neighborFinset_some : doorGraph.neighborFinset (some Cell.tri) = {none} := by
  ext v
  simp only [mem_neighborFinset, Finset.mem_singleton]
  constructor
  · intro h
    rw [doorGraph, fromRel_adj] at h
    rcases v with _ | c
    · rfl
    · cases c
      simp only [doorRel] at h
      rcases h with ⟨_, h2 | h2⟩ <;> simp at h2
  · rintro rfl
    rw [doorGraph, fromRel_adj]
    refine ⟨by simp, Or.inl (Or.inr ⟨rfl, rfl⟩)⟩

/-- The neighbor finset of the outer region is exactly the cell `{some Cell.tri}`. -/
theorem neighborFinset_none : doorGraph.neighborFinset none = {some Cell.tri} := by
  ext v
  simp only [mem_neighborFinset, Finset.mem_singleton]
  constructor
  · intro h
    rw [doorGraph, fromRel_adj] at h
    rcases v with _ | c
    · exact absurd h.2 (by simp [doorRel])
    · cases c; rfl
  · rintro rfl
    rw [doorGraph, fromRel_adj]
    refine ⟨by simp, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩

/-- The cell's door degree is `1`. -/
theorem degree_some : doorGraph.degree (some Cell.tri) = 1 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_some, Finset.card_singleton]

/-- The outer region's door degree is `1`. -/
theorem degree_none : doorGraph.degree none = 1 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_none, Finset.card_singleton]

/-- The concrete single-cell door-incidence datum. -/
def doorIncidence : SpernerTriangulation.DoorIncidence Cell where
  G := doorGraph
  col := cellColors
  n := 1
  bc := boundaryColoring
  hboundary := boundaryColoring_sperner
  cell_degree := by
    intro t
    cases t
    rw [degree_some]
    decide
  outer_degree := by
    rw [degree_none]
    decide

/-- **Concrete two-dimensional Sperner.** The concretely constructed single-cell door-incidence
datum has a rainbow triangle. -/
theorem exists_rainbow_cell : ∃ t : Cell, doorIncidence.IsRainbowCell t :=
  doorIncidence.exists_rainbow

end CRNT.Analysis.SpernerGrid

import CRNT.Analysis.SpernerLatticeCellDegree
import CRNT.Analysis.SpernerLatticeBoundary
import CRNT.Analysis.SpernerMultiIncidence

/-!
# The two-dimensional Sperner lemma for the `N`-subdivision (parametric `N`)

The capstone of the lattice development: assembling the `MultiDoorIncidence` datum of the
`N`-subdivision from its two discharged obligations — `cell_degree` (each triangle's door-graph
degree equals its local `doorCount`) and `outer_odd_count` (an odd number of boundary outer vertices
have odd degree) — and applying `MultiDoorIncidence.exists_rainbow` yields a rainbow triangle. Thus
every proper Sperner coloring of the `N`-subdivision of the 2-simplex has a triangle whose three
vertices carry all three colors, for **arbitrary `N`** — the constructive content of the
two-dimensional Sperner lemma over a full triangular grid.

Depends on: `CRNT.Analysis.SpernerLatticeCellDegree`,
`CRNT.Analysis.SpernerLatticeBoundary`, `CRNT.Analysis.SpernerMultiIncidence`.
-/

namespace CRNT.Analysis.SpernerLattice

open CRNT.Analysis.Sperner2D CRNT.Analysis.SpernerTriangulation

variable {N : ℕ}

/-- The **multi-door-incidence datum** of the `N`-subdivision under a proper Sperner coloring: the
full door graph, the per-triangle colors, and the two discharged geometric obligations. -/
def multiDoorIncidence (κ : SpernerColoring N) : MultiDoorIncidence (Cell N) (Outer N) where
  G := fullDoorGraph κ
  col := col κ
  cell_degree := cell_degree κ
  outer_odd := outer_odd_count κ

/-- **Two-dimensional Sperner lemma (parametric `N`).** Every proper Sperner coloring of the
`N`-subdivision of the 2-simplex has a rainbow triangle — one whose three vertices carry the three
colors `0, 1, 2`. -/
theorem exists_rainbow_cell (κ : SpernerColoring N) :
    ∃ t : Cell N, isRainbow (col κ t).1 (col κ t).2.1 (col κ t).2.2 = true :=
  (multiDoorIncidence κ).exists_rainbow

end CRNT.Analysis.SpernerLattice

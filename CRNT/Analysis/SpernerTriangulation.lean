import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Option
import CRNT.Analysis.Sperner2D
import CRNT.Analysis.Sperner

/-!
# The door-incidence interface for the two-dimensional Sperner lemma

This module bundles the two purely *geometric* facts about a triangulated planar door graph into a
single structure `DoorIncidence` and, on top of those bundled facts, proves the **full
two-dimensional Sperner lemma**: a Sperner-colored triangulation has a rainbow triangle.

The structure `DoorIncidence Cell` packages, for an abstract finite triangle type `Cell`:

* the door graph `G : SimpleGraph (Option Cell)`, with `none` the outer region and `some t` a
  triangle, together with decidability of its adjacency;
* the vertex colors `col t` of each triangle, and the one-dimensional colored boundary side
  `bc : ℕ → Bool` on the segment `0, …, n` with its Sperner boundary condition `hboundary`;
* the two geometric incidence facts as fields: each triangle's door degree equals its local
  `doorCount` (`cell_degree`), and the outer region's door degree equals the number of rainbow
  edges along the colored boundary side (`outer_degree`).

From these the module discharges the two hypotheses that the abstract rung-2 handshaking conclusion
`Sperner2D.doorGraph_odd_rainbow` defers — `hcell` (via the local door-count parity
`Sperner2D.doorCount_odd_iff`) and `houter` (via the one-dimensional `Sperner.sperner_odd_rainbowEdges`
on the colored boundary side) — and assembles `odd_rainbow` (the rainbow-triangle count is odd) and
`exists_rainbow` (the full two-dimensional Sperner conclusion).

## What is deferred

`DoorIncidence` takes the two incidence facts (`cell_degree`, `outer_degree`) as hypothesis fields;
constructing them over a *concrete* triangulated grid is the named next dependency:

* a concrete triangle datatype `Cell` of up/down lattice triangles over the integer points
  `{(i, j, k) : i + j + k = N}` of the standard `N`-fold barycentric subdivision of the
  `2`-simplex, with its `Fintype` instance (the natural inductive does not support
  `deriving Fintype`, so a manual instance is required);
* the `{0,1}`-door sub-edge incidence relation building `G` via `SimpleGraph.fromRel`;
* the load-bearing geometric incidence lemma — every *interior* `{0,1}` sub-edge is shared by
  exactly two triangles and every *boundary* `{0,1}` sub-edge bounds exactly one triangle — which
  discharges `cell_degree` through a finset bijection between a triangle's three edges and its
  door-graph neighbors;
* the boundary-side reduction discharging `outer_degree` by identifying the outer region's incident
  doors with the rainbow edges of the one-dimensional colored boundary segment.

This module is **stable** and `sorry`-free. Depends on: `Mathlib.Combinatorics.SimpleGraph.DegreeSum`,
`Mathlib.Data.Fintype.Option`, `CRNT.Analysis.Sperner2D`, `CRNT.Analysis.Sperner`.
-/

namespace CRNT.Analysis.SpernerTriangulation

open SimpleGraph Finset CRNT.Analysis

/-- A **door-incidence datum** over an abstract finite triangle type `Cell`. It bundles a door graph
`G` (`none` is the outer region, `some t` a triangle), the vertex colors `col t` of each triangle,
the one-dimensional colored boundary side `bc` with its Sperner condition `hboundary`, and the two
geometric incidence facts (`cell_degree`, `outer_degree`) as fields. -/
structure DoorIncidence (Cell : Type*) [Fintype Cell] where
  /-- The door graph: `none` is the outer region, `some t` a triangle. -/
  G : SimpleGraph (Option Cell)
  /-- Adjacency of the door graph is decidable. -/
  [decAdj : DecidableRel G.Adj]
  /-- The three vertex colors of each triangle. -/
  col : Cell → Sperner2D.Color × Sperner2D.Color × Sperner2D.Color
  /-- Length of the one-dimensional colored boundary side. -/
  n : ℕ
  /-- The color indicator along the boundary side. -/
  bc : ℕ → Bool
  /-- The boundary side satisfies the one-dimensional Sperner boundary condition. -/
  hboundary : Sperner.IsSpernerColoring n bc
  /-- **Geometric incidence fact (cells).** Each triangle's door degree equals its local
  `{0,1}`-door count. -/
  cell_degree : ∀ t : Cell,
    G.degree (some t) = Sperner2D.doorCount (col t).1 (col t).2.1 (col t).2.2
  /-- **Geometric incidence fact (outer region).** The outer region's door degree equals the number
  of rainbow edges along the colored boundary side. -/
  outer_degree : G.degree none = (Sperner.rainbowEdges n bc).card

attribute [instance] DoorIncidence.decAdj

variable {Cell : Type*} [Fintype Cell]

/-- A triangle is *rainbow* when its three vertex colors are exactly `{0, 1, 2}`. -/
def DoorIncidence.IsRainbowCell (D : DoorIncidence Cell) (t : Cell) : Prop :=
  Sperner2D.isRainbow (D.col t).1 (D.col t).2.1 (D.col t).2.2

instance (D : DoorIncidence Cell) : DecidablePred D.IsRainbowCell := fun _ =>
  inferInstanceAs (Decidable (Sperner2D.isRainbow _ _ _ = true))

/-- **Cell parity bridge.** A triangle has odd door degree iff it is rainbow. Discharges the
`hcell` hypothesis of `Sperner2D.doorGraph_odd_rainbow` via the local door-count parity. -/
theorem DoorIncidence.hcell (D : DoorIncidence Cell) :
    ∀ t : Cell, Odd (D.G.degree (some t)) ↔ D.IsRainbowCell t := by
  intro t
  rw [D.cell_degree]
  exact Sperner2D.doorCount_odd_iff _ _ _

/-- **Outer parity bridge.** The outer region has odd door degree. Discharges the `houter`
hypothesis of `Sperner2D.doorGraph_odd_rainbow` via the one-dimensional Sperner lemma on the colored
boundary side. -/
theorem DoorIncidence.houter (D : DoorIncidence Cell) : Odd (D.G.degree none) := by
  rw [D.outer_degree]
  exact Sperner.sperner_odd_rainbowEdges D.hboundary

/-- **Two-dimensional Sperner parity.** The number of rainbow triangles is odd. -/
theorem DoorIncidence.odd_rainbow (D : DoorIncidence Cell) :
    Odd #{t : Cell | D.IsRainbowCell t} :=
  Sperner2D.doorGraph_odd_rainbow D.G D.IsRainbowCell D.hcell D.houter

/-- **The two-dimensional Sperner lemma.** A Sperner-colored triangulation has a rainbow triangle. -/
theorem DoorIncidence.exists_rainbow (D : DoorIncidence Cell) :
    ∃ t : Cell, D.IsRainbowCell t :=
  Sperner2D.doorGraph_exists_rainbow D.G D.IsRainbowCell D.hcell D.houter

end CRNT.Analysis.SpernerTriangulation

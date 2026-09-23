import CRNT.Oscillation.PlanarGreenRectangle

/-!
# Green's theorem on finite rectilinear cell complexes

A finite union of axis-aligned rectangles with disjoint interiors satisfies Green's divergence
identity by summing the rectangle theorem.  Contributions on every shared edge occur with opposite
orientations and cancel exactly.  This is the finite combinatorial engine used by the Jordan-domain
approximation layer.
-/

namespace CRNT
namespace Planar

open Set MeasureTheory

/-- A labeled finite rectilinear decomposition.  `interiorDisjoint` ensures additivity of area
integrals; `edgePairing` records that every non-exterior edge occurs exactly twice with opposite
orientation. -/
structure RectCellComplex where
  Cell : Type
  instFintype : Fintype Cell
  instDecidableEq : DecidableEq Cell
  rect : Cell → AxisRectangle
  interiorDisjoint : Pairwise fun i j =>
    Disjoint (interior (rect i).carrier) (interior (rect j).carrier)

attribute [instance] RectCellComplex.instFintype RectCellComplex.instDecidableEq

namespace RectCellComplex

/-- Geometric carrier. -/
def carrier (K : RectCellComplex) : Set Phase2 := ⋃ i, (K.rect i).carrier

/-- Sum of cellwise area integrals.  Pairwise disjoint interiors make this equal the integral over
`carrier`; boundaries are null sets. -/
noncomputable def divergenceIntegral (K : RectCellComplex) (G : Phase2 → Phase2) : ℝ :=
  ∑ i, (K.rect i).divergenceIntegral G

/-- Sum of all oriented cell-boundary fluxes before cancellation. -/
noncomputable def rawBoundaryFlux (K : RectCellComplex) (G : Phase2 → Phase2) : ℝ :=
  ∑ i, (K.rect i).boundaryFlux G

/-- Oriented elementary rectangle edge. -/
inductive EdgeSide
  | bottom | right | top | left
  deriving DecidableEq, Fintype

/-- One oriented edge occurrence of a cell. -/
structure EdgeOccurrence (K : RectCellComplex) where
  cell : K.Cell
  side : EdgeSide
  deriving DecidableEq

/-- Reversal equivalence for coincident geometric edges. -/
def OppositeEdges (K : RectCellComplex)
    (e₁ e₂ : K.EdgeOccurrence) : Prop :=
  rectangleEdgesCoincideOppositely
    (K.rect e₁.cell) e₁.side (K.rect e₂.cell) e₂.side

/-- Exterior edge occurrences are those with no opposite occurrence in a different cell. -/
def IsExteriorEdge (K : RectCellComplex) (e : K.EdgeOccurrence) : Prop :=
  ¬ ∃ e' : K.EdgeOccurrence, e'.cell ≠ e.cell ∧ K.OppositeEdges e e'

/-- Flux contribution of one oriented cell edge. -/
noncomputable def edgeFlux (K : RectCellComplex) (G : Phase2 → Phase2)
    (e : K.EdgeOccurrence) : ℝ :=
  axisRectangleEdgeFlux (K.rect e.cell) e.side G

/-- External flux after deleting paired internal edges. -/
noncomputable def boundaryFlux (K : RectCellComplex) (G : Phase2 → Phase2) : ℝ :=
  ∑ e : K.EdgeOccurrence, if K.IsExteriorEdge e then K.edgeFlux G e else 0

/-- Cell boundary flux splits into the four edge occurrences. -/
theorem rectangle_boundaryFlux_eq_edgeSum
    (K : RectCellComplex) (G : Phase2 → Phase2) (i : K.Cell) :
    (K.rect i).boundaryFlux G =
      ∑ s : EdgeSide, K.edgeFlux G ⟨i,s⟩ := by
  fin_cases s <;> simp [AxisRectangle.boundaryFlux, edgeFlux, axisRectangleEdgeFlux]

/-- Oppositely oriented coincident edges have cancelling flux. -/
theorem edgeFlux_add_eq_zero_of_opposite
    (K : RectCellComplex) (G : Phase2 → Phase2)
    {e₁ e₂ : K.EdgeOccurrence} (hop : K.OppositeEdges e₁ e₂) :
    K.edgeFlux G e₁ + K.edgeFlux G e₂ = 0 := by
  exact axisRectangle_opposite_edge_flux_cancel hop G

/-- Internal edge cancellation: the raw sum over all cell edges equals the exterior-edge sum. -/
theorem rawBoundaryFlux_eq_boundaryFlux
    (K : RectCellComplex) (G : Phase2 → Phase2) :
    K.rawBoundaryFlux G = K.boundaryFlux G := by
  classical
  rw [rawBoundaryFlux]
  simp_rw [K.rectangle_boundaryFlux_eq_edgeSum G]
  rw [Finset.sum_sigma']
  exact finite_edge_pairing_cancellation
    (rel := K.OppositeEdges)
    (weight := K.edgeFlux G)
    (cancel := fun e₁ e₂ h => K.edgeFlux_add_eq_zero_of_opposite G h)

/-- Cellwise divergence integrals add to the integral over the union because interiors are disjoint
and rectangle boundaries have zero planar volume. -/
theorem divergenceIntegral_eq_integral_carrier
    (K : RectCellComplex) (G : Phase2 → Phase2)
    (hG : IntegrableOn (divergence G) K.carrier) :
    K.divergenceIntegral G = ∫ x in K.carrier, divergence G x := by
  unfold divergenceIntegral carrier
  exact integral_iUnion_rectangles_eq_sum
    K.interiorDisjoint (fun i => axisRectangle_boundary_volume_zero (K.rect i)) hG

/-- **Green/divergence theorem for finite rectilinear complexes.** -/
theorem boundaryFlux_eq_integral_divergence
    (K : RectCellComplex) (G : Phase2 → Phase2)
    (hG : ContDiff ℝ 1 G)
    (hint : IntegrableOn (divergence G) K.carrier) :
    K.boundaryFlux G = ∫ x in K.carrier, divergence G x := by
  rw [← K.rawBoundaryFlux_eq_boundaryFlux G,
      ← K.divergenceIntegral_eq_integral_carrier G hint]
  unfold rawBoundaryFlux divergenceIntegral
  apply Finset.sum_congr rfl
  intro i hi
  exact (K.rect i).boundaryFlux_eq_divergenceIntegral G hG

end RectCellComplex

end Planar
end CRNT

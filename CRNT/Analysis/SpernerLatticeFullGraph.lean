import CRNT.Analysis.SpernerLatticeDoorGraph

/-!
# The full door graph of the `N`-subdivision

The door graph on cells *and boundary outer vertices*. The `{0,1}` doors of the subdivision live only
on the hypotenuse side `i + j = N` (the other two sides omit one of the two colors), and that side is
colored entirely with `{0, 1}` (no point there is colored `2`). Its sub-edges are the boundary
diagonals: hypotenuse sub-edge `k` (`k : Fin N`) is the diagonal of the up-triangle `(k, N-1-k)`,
joining `(k+1, N-1-k)` and `(k, N-k)`.

`fullDoorGraph` adds one **outer vertex** per hypotenuse sub-edge, joined to its up-triangle exactly
when the sub-edge is a door. Its degree counts — `cell_degree` (every cell's degree equals its local
`doorCount`) and `outer_odd` (an odd number of outer vertices have odd degree) — are the two
obligations of `MultiDoorIncidence`, whose `exists_rainbow` then yields a fully-colored triangle.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.SpernerLatticeDoorGraph`.
-/

namespace CRNT.Analysis.SpernerLattice

open CRNT.Analysis.Sperner2D

variable {N : ℕ}

/-- Boundary **outer vertices**: one per hypotenuse (`i+j=N`) sub-edge of the `N`-subdivision. -/
abbrev Outer (N : ℕ) : Type := Fin N

/-- The up-triangle whose boundary diagonal is hypotenuse sub-edge `k`: the triangle `(k, N-1-k)`. -/
def outerTri (k : Outer N) : Cell N :=
  Sum.inl ⟨(k.val, N - 1 - k.val), mem_upCarrier.mpr (by have := k.isLt; omega)⟩

/-- The lower endpoint `(k+1, N-1-k)` of hypotenuse sub-edge `k`. -/
def outerPtA (k : Outer N) : Pt N :=
  mkPt (k.val + 1) (N - 1 - k.val) (by have := k.isLt; omega)

/-- The upper endpoint `(k, N-k)` of hypotenuse sub-edge `k`. -/
def outerPtB (k : Outer N) : Pt N :=
  mkPt k.val (N - k.val) (by have := k.isLt; omega)

/-- Hypotenuse sub-edge `k` carries a `{0,1}` door under the coloring `κ`. -/
def BoundaryDoor (κ : SpernerColoring N) (k : Outer N) : Prop :=
  isDoor (κ.color (outerPtA k)) (κ.color (outerPtB k)) = true

instance (κ : SpernerColoring N) (k : Outer N) : Decidable (BoundaryDoor κ k) :=
  inferInstanceAs (Decidable (_ = true))

/-- The door-graph adjacency on cells-plus-outer-vertices: cell–cell doors (`CellDoor`), plus each
outer vertex joined to its up-triangle exactly when its sub-edge is a door. -/
def fullDoorRel (κ : SpernerColoring N) :
    (Cell N ⊕ Outer N) → (Cell N ⊕ Outer N) → Prop
  | Sum.inl t, Sum.inl t' => CellDoor κ t t'
  | Sum.inl t, Sum.inr k => t = outerTri k ∧ BoundaryDoor κ k
  | Sum.inr k, Sum.inl t => t = outerTri k ∧ BoundaryDoor κ k
  | Sum.inr _, Sum.inr _ => False

instance (κ : SpernerColoring N) : DecidableRel (fullDoorRel κ) := by
  intro x y
  cases x <;> cases y <;> (dsimp only [fullDoorRel]; infer_instance)

/-- The **full door graph** of the `N`-subdivision: cells and boundary outer vertices, with the door
adjacency symmetrized and made loopless. -/
def fullDoorGraph (κ : SpernerColoring N) : SimpleGraph (Cell N ⊕ Outer N) :=
  SimpleGraph.fromRel (fullDoorRel κ)

instance (κ : SpernerColoring N) : DecidableRel (fullDoorGraph κ).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (fullDoorRel κ)).Adj)

/-- Cell–cell adjacency in the full door graph is exactly `CellDoor`. -/
theorem fullDoorGraph_adj_inl_inl (κ : SpernerColoring N) (t t' : Cell N) :
    (fullDoorGraph κ).Adj (Sum.inl t) (Sum.inl t') ↔ CellDoor κ t t' := by
  rw [fullDoorGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact cellDoor_symm κ h
  · intro h
    exact ⟨fun he => h.1 (Sum.inl.inj he), Or.inl h⟩

/-- Cell–outer adjacency in the full door graph: outer vertex `k` is joined to a cell `t` exactly
when `t` is its up-triangle and the sub-edge is a door. -/
theorem fullDoorGraph_adj_inl_inr (κ : SpernerColoring N) (t : Cell N) (k : Outer N) :
    (fullDoorGraph κ).Adj (Sum.inl t) (Sum.inr k) ↔ t = outerTri k ∧ BoundaryDoor κ k := by
  rw [fullDoorGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact h
  · intro h
    exact ⟨Sum.inl_ne_inr, Or.inl h⟩

/-- Outer vertices are pairwise non-adjacent in the full door graph. -/
theorem fullDoorGraph_not_adj_inr_inr (κ : SpernerColoring N) (k k' : Outer N) :
    ¬ (fullDoorGraph κ).Adj (Sum.inr k) (Sum.inr k') := by
  rw [fullDoorGraph, SimpleGraph.fromRel_adj]
  rintro ⟨_, h | h⟩ <;> exact h

/-- The neighbours of an outer vertex: its up-triangle when the sub-edge is a door, else none. -/
theorem outerNeighborFinset (κ : SpernerColoring N) (k : Outer N) :
    (fullDoorGraph κ).neighborFinset (Sum.inr k)
      = if BoundaryDoor κ k then {Sum.inl (outerTri k)} else ∅ := by
  by_cases h : BoundaryDoor κ k
  · rw [if_pos h]
    ext w
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    cases w with
    | inl t =>
      rw [SimpleGraph.adj_comm, fullDoorGraph_adj_inl_inr]
      constructor
      · rintro ⟨ht, _⟩; rw [ht]
      · intro h'; exact ⟨Sum.inl.inj h', h⟩
    | inr k' =>
      constructor
      · intro hadj; exact absurd hadj (fullDoorGraph_not_adj_inr_inr κ k k')
      · intro hc; exact absurd hc Sum.inr_ne_inl
  · rw [if_neg h, Finset.eq_empty_iff_forall_notMem]
    intro w
    rw [SimpleGraph.mem_neighborFinset]
    cases w with
    | inl t =>
      rw [SimpleGraph.adj_comm, fullDoorGraph_adj_inl_inr]
      rintro ⟨_, h'⟩; exact h h'
    | inr k' => exact fullDoorGraph_not_adj_inr_inr κ k k'

/-- **Outer-vertex degree.** An outer vertex has degree `1` when its hypotenuse sub-edge is a door and
`0` otherwise — the input to the `outer_odd` count via one-dimensional Sperner. -/
theorem outer_degree (κ : SpernerColoring N) (k : Outer N) :
    (fullDoorGraph κ).degree (Sum.inr k) = if BoundaryDoor κ k then 1 else 0 := by
  unfold SimpleGraph.degree
  rw [outerNeighborFinset]
  by_cases h : BoundaryDoor κ k <;> simp [h]

end CRNT.Analysis.SpernerLattice

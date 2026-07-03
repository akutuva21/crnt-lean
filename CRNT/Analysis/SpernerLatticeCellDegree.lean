import CRNT.Analysis.SpernerLatticeFullGraph
import CRNT.Analysis.SpernerLatticeNeighbor
import CRNT.Analysis.SpernerLatticeIncidence
import CRNT.Analysis.SpernerLatticeIncidenceHV

/-!
# Cell-neighbour location, construction, and the down-triangle degree

Toward the `cell_degree` obligation of `MultiDoorIncidence` (that each cell's door-graph degree equals
its local `doorCount`):

* **Locators** — `up_cellDoor_partner` / `down_cellDoor_partner`: a door-neighbour of a triangle has
  index pinned to one of the three lattice partners (diagonal, horizontal-shifted, vertical-shifted),
  by `up_down_share_two`.
* **Constructions** — `down_diagonal_cellDoor`, `down_horizTop_cellDoor`, `down_vertRight_cellDoor`:
  a door on an edge of `down(a,b)` makes it adjacent to the up-triangle across that edge.
* **Degree decomposition** — `degree_inl_eq`: a cell's degree splits into cell-neighbours and
  boundary outer-neighbours; `down_not_adj_outer` removes the outer term for down-triangles.
* **Down-triangle degree** — `down_cellDoor_iff` characterizes a down-triangle's cell-neighbours and
  `down_cell_degree` evaluates its degree to `doorCount`.

Depends on: `CRNT.Analysis.SpernerLatticeFullGraph`,
`CRNT.Analysis.SpernerLatticeNeighbor`, `CRNT.Analysis.SpernerLatticeIncidence`,
`CRNT.Analysis.SpernerLatticeIncidenceHV`.
-/

namespace CRNT.Analysis.SpernerLattice

open CRNT.Analysis.Sperner2D

variable {N : ℕ}

/-- A door-neighbour `d` of an up-triangle `u` has its index at one of `u`'s three lattice partners. -/
theorem up_cellDoor_partner (κ : SpernerColoring N) {u : Up N} {d : Down N}
    (h : CellDoor κ (Sum.inl u) (Sum.inr d)) :
    (d.1.1 = u.1.1 ∧ d.1.2 = u.1.2) ∨ (d.1.1 = u.1.1 ∧ d.1.2 + 1 = u.1.2) ∨
      (d.1.1 + 1 = u.1.1 ∧ d.1.2 = u.1.2) := by
  obtain ⟨_, p, hpu, q, hqu, hpq, hpd, hqd, _⟩ := h
  exact up_down_share_two hpu hpd hqu hqd hpq

/-- A door-neighbour `u` of a down-triangle `d` has its index at one of `d`'s three lattice partners. -/
theorem down_cellDoor_partner (κ : SpernerColoring N) {d : Down N} {u : Up N}
    (h : CellDoor κ (Sum.inr d) (Sum.inl u)) :
    (d.1.1 = u.1.1 ∧ d.1.2 = u.1.2) ∨ (d.1.1 = u.1.1 ∧ d.1.2 + 1 = u.1.2) ∨
      (d.1.1 + 1 = u.1.1 ∧ d.1.2 = u.1.2) := by
  obtain ⟨_, p, hpd, q, hqd, hpq, hpu, hqu, _⟩ := h
  exact up_down_share_two hpu hpd hqu hqd hpq

/-- A down-triangle is never adjacent to an outer vertex: outer vertices attach only to up-triangles
(the hypotenuse diagonals). -/
theorem down_not_adj_outer (κ : SpernerColoring N) (d : Down N) (k : Outer N) :
    ¬ (fullDoorGraph κ).Adj (Sum.inl (Sum.inr d)) (Sum.inr k) := by
  rw [fullDoorGraph_adj_inl_inr]; rintro ⟨h, _⟩; exact absurd h (by simp [outerTri])

/-- The door predicate is symmetric. -/
theorem isDoor_comm (x y : Color) : isDoor x y = isDoor y x := by
  unfold isDoor; by_cases hx0 : x = 0 <;> by_cases hy1 : y = 1 <;>
    by_cases hx1 : x = 1 <;> by_cases hy0 : y = 0 <;> simp_all

/-- If a door holds on a pair of vertices each lying in `{P, Q}` and the two are distinct, the door
holds on `P, Q` (door extraction up to the symmetry of the shared edge). -/
theorem isDoor_of_pair (κ : SpernerColoring N) {x y P Q : Pt N}
    (hx : x = P ∨ x = Q) (hy : y = P ∨ y = Q) (hxy : x ≠ y)
    (hdoor : isDoor (κ.color x) (κ.color y) = true) :
    isDoor (κ.color P) (κ.color Q) = true := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact hdoor
  · rw [isDoor_comm]; exact hdoor
  · exact absurd rfl hxy

/-- **Construction template (diagonal).** When an interior diagonal carries a door, the down- and
up-triangle sharing it are door-adjacent. -/
theorem down_diagonal_cellDoor (κ : SpernerColoring N) (a b : ℕ) (hd : a + b + 2 ≤ N)
    (hdoor : isDoor (κ.color (mkPt (a + 1) b (by omega))) (κ.color (mkPt a (b + 1) (by omega)))
      = true) :
    CellDoor κ (Sum.inr ⟨(a, b), by rw [mem_downCarrier]; omega⟩)
      (Sum.inl ⟨(a, b), by rw [mem_upCarrier]; omega⟩) := by
  refine ⟨by simp, mkPt (a + 1) b (by omega), ?_, mkPt a (b + 1) (by omega), ?_, ?_, ?_, ?_, hdoor⟩
  · simp [triVerts, downVerts]
  · simp [triVerts, downVerts]
  · rw [Ne, mkPt_inj]; omega
  · simp [triVerts, upVerts]
  · simp [triVerts, upVerts]

/-- **Construction (down top-horizontal).** A door on the top edge `{(a,b+1),(a+1,b+1)}` of
`down(a,b)` makes it adjacent to `up(a,b+1)`. -/
theorem down_horizTop_cellDoor (κ : SpernerColoring N) (a b : ℕ) (hd : a + b + 2 ≤ N)
    (hdoor : isDoor (κ.color (mkPt a (b + 1) (by omega)))
      (κ.color (mkPt (a + 1) (b + 1) (by omega))) = true) :
    CellDoor κ (Sum.inr ⟨(a, b), by rw [mem_downCarrier]; omega⟩)
      (Sum.inl ⟨(a, b + 1), by rw [mem_upCarrier]; omega⟩) := by
  refine ⟨by simp, mkPt a (b + 1) (by omega), ?_, mkPt (a + 1) (b + 1) (by omega), ?_, ?_, ?_, ?_,
    hdoor⟩
  · simp [triVerts, downVerts]
  · simp [triVerts, downVerts]
  · rw [Ne, mkPt_inj]; omega
  · simp [triVerts, upVerts]
  · simp [triVerts, upVerts]

/-- **Construction (down right-vertical).** A door on the right edge `{(a+1,b),(a+1,b+1)}` of
`down(a,b)` makes it adjacent to `up(a+1,b)`. -/
theorem down_vertRight_cellDoor (κ : SpernerColoring N) (a b : ℕ) (hd : a + b + 2 ≤ N)
    (hdoor : isDoor (κ.color (mkPt (a + 1) b (by omega)))
      (κ.color (mkPt (a + 1) (b + 1) (by omega))) = true) :
    CellDoor κ (Sum.inr ⟨(a, b), by rw [mem_downCarrier]; omega⟩)
      (Sum.inl ⟨(a + 1, b), by rw [mem_upCarrier]; omega⟩) := by
  refine ⟨by simp, mkPt (a + 1) b (by omega), ?_, mkPt (a + 1) (b + 1) (by omega), ?_, ?_, ?_, ?_,
    hdoor⟩
  · simp [triVerts, downVerts]
  · simp [triVerts, downVerts]
  · rw [Ne, mkPt_inj]; omega
  · simp [triVerts, upVerts]
  · simp [triVerts, upVerts]

/-- **Characterization of a down-triangle's cell-neighbours.** `down(a,b)` is door-adjacent to an
up-triangle `u` exactly when `u` is one of its three edge-partners and that edge carries a door. -/
theorem down_cellDoor_iff (κ : SpernerColoring N) (a b : ℕ) (hd : a + b + 2 ≤ N) (u : Up N) :
    CellDoor κ (Sum.inr ⟨(a, b), by rw [mem_downCarrier]; omega⟩) (Sum.inl u) ↔
      (u = ⟨(a, b), by rw [mem_upCarrier]; omega⟩ ∧
        isDoor (κ.color (mkPt (a + 1) b (by omega))) (κ.color (mkPt a (b + 1) (by omega))) = true) ∨
      (u = ⟨(a, b + 1), by rw [mem_upCarrier]; omega⟩ ∧
        isDoor (κ.color (mkPt a (b + 1) (by omega)))
          (κ.color (mkPt (a + 1) (b + 1) (by omega))) = true) ∨
      (u = ⟨(a + 1, b), by rw [mem_upCarrier]; omega⟩ ∧
        isDoor (κ.color (mkPt (a + 1) b (by omega)))
          (κ.color (mkPt (a + 1) (b + 1) (by omega))) = true) := by
  constructor
  · intro h
    obtain ⟨_, x, hxd, y, hyd, hxy, hxu, hyu, hdoor⟩ := h
    obtain ⟨⟨p, q⟩, hu⟩ := u
    have hpart := up_down_share_two hxu hxd hyu hyd hxy
    simp only [triVerts, Sum.elim_inr, Sum.elim_inl, downVerts, upVerts, Finset.mem_insert,
      Finset.mem_singleton] at hxd hyd hxu hyu
    dsimp only at hpart hxd hyd hxu hyu
    rcases hpart with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine Or.inl ⟨rfl, isDoor_of_pair κ ?_ ?_ hxy hdoor⟩
      · rcases hxd with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · rw [h] at hxu; rcases hxu with h' | h' | h' <;> (rw [mkPt_inj] at h'; omega)
      · rcases hyd with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · rw [h] at hyu; rcases hyu with h' | h' | h' <;> (rw [mkPt_inj] at h'; omega)
    · refine Or.inr (Or.inl ⟨rfl, isDoor_of_pair κ ?_ ?_ hxy hdoor⟩)
      · rcases hxd with h | h | h
        · rw [h] at hxu; rcases hxu with h' | h' | h' <;> (rw [mkPt_inj] at h'; omega)
        · exact Or.inl h
        · exact Or.inr h
      · rcases hyd with h | h | h
        · rw [h] at hyu; rcases hyu with h' | h' | h' <;> (rw [mkPt_inj] at h'; omega)
        · exact Or.inl h
        · exact Or.inr h
    · refine Or.inr (Or.inr ⟨rfl, isDoor_of_pair κ ?_ ?_ hxy hdoor⟩)
      · rcases hxd with h | h | h
        · exact Or.inl h
        · rw [h] at hxu; rcases hxu with h' | h' | h' <;> (rw [mkPt_inj] at h'; omega)
        · exact Or.inr h
      · rcases hyd with h | h | h
        · exact Or.inl h
        · rw [h] at hyu; rcases hyu with h' | h' | h' <;> (rw [mkPt_inj] at h'; omega)
        · exact Or.inr h
  · rintro (⟨rfl, hdoor⟩ | ⟨rfl, hdoor⟩ | ⟨rfl, hdoor⟩)
    · exact down_diagonal_cellDoor κ a b hd hdoor
    · exact down_horizTop_cellDoor κ a b hd hdoor
    · exact down_vertRight_cellDoor κ a b hd hdoor

open Finset in
/-- **Degree decomposition.** A cell's door-graph degree splits into its cell-neighbours (`CellDoor`
partners) and its outer-neighbours (boundary diagonals). -/
theorem degree_inl_eq (κ : SpernerColoring N) (t : Cell N) :
    (fullDoorGraph κ).degree (Sum.inl t)
      = (univ.filter (fun c : Cell N => CellDoor κ t c)).card
        + (univ.filter (fun k : Outer N => t = outerTri k ∧ BoundaryDoor κ k)).card := by
  have hnb : (fullDoorGraph κ).neighborFinset (Sum.inl t)
      = univ.filter (fun w => (fullDoorGraph κ).Adj (Sum.inl t) w) := by
    ext w; rw [SimpleGraph.mem_neighborFinset, mem_filter]
    exact (and_iff_right (mem_univ w)).symm
  rw [SimpleGraph.degree, hnb, Finset.card_filter, Fintype.sum_sum_type]
  congr 1
  · rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun c _ => by simp only [fullDoorGraph_adj_inl_inl]
  · rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun k _ => by simp only [fullDoorGraph_adj_inl_inr]

open Finset in
set_option linter.unusedSimpArgs false in
/-- **Down-triangle degree.** A down-triangle (always interior) has no outer neighbour, and its three
cell-neighbours are the up-triangles across its door edges — so its degree is its `doorCount`. -/
theorem down_cell_degree (κ : SpernerColoring N) (a b : ℕ) (hd : a + b + 2 ≤ N) :
    (fullDoorGraph κ).degree
        (Sum.inl (Sum.inr ⟨(a, b), by rw [mem_downCarrier]; omega⟩ : Cell N))
      = doorCount (κ.color (mkPt (a + 1) b (by omega))) (κ.color (mkPt a (b + 1) (by omega)))
          (κ.color (mkPt (a + 1) (b + 1) (by omega))) := by
  rw [degree_inl_eq]
  have houter : (univ.filter (fun k : Outer N =>
      (Sum.inr ⟨(a, b), by rw [mem_downCarrier]; omega⟩ : Cell N) = outerTri k ∧
        BoundaryDoor κ k)) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    rw [Finset.mem_filter] at hk
    exact absurd hk.2.1 (by simp [outerTri])
  rw [houter, Finset.card_empty, add_zero]
  -- the cell-neighbour finset is the union of the three door-gated up-partners
  set U1 : Cell N := Sum.inl ⟨(a, b), by rw [mem_upCarrier]; omega⟩ with hU1
  set U2 : Cell N := Sum.inl ⟨(a, b + 1), by rw [mem_upCarrier]; omega⟩ with hU2
  set U3 : Cell N := Sum.inl ⟨(a + 1, b), by rw [mem_upCarrier]; omega⟩ with hU3
  set d1 := isDoor (κ.color (mkPt (a + 1) b (by omega))) (κ.color (mkPt a (b + 1) (by omega)))
    with hd1
  set d2 := isDoor (κ.color (mkPt a (b + 1) (by omega)))
    (κ.color (mkPt (a + 1) (b + 1) (by omega))) with hd2
  set d3 := isDoor (κ.color (mkPt (a + 1) b (by omega)))
    (κ.color (mkPt (a + 1) (b + 1) (by omega))) with hd3
  have hfilter : (univ.filter (fun c : Cell N =>
      CellDoor κ (Sum.inr ⟨(a, b), by rw [mem_downCarrier]; omega⟩) c))
      = (if d1 then {U1} else ∅) ∪ (if d2 then {U2} else ∅) ∪ (if d3 then {U3} else ∅) := by
    ext c
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_union]
    constructor
    · rintro ⟨-, hcd⟩
      cases c with
      | inl u =>
        rw [down_cellDoor_iff κ a b hd] at hcd
        rcases hcd with ⟨rfl, hdoor⟩ | ⟨rfl, hdoor⟩ | ⟨rfl, hdoor⟩
        · exact Or.inl (Or.inl (by rw [if_pos hdoor, hU1]; exact Finset.mem_singleton_self _))
        · exact Or.inl (Or.inr (by rw [if_pos hdoor, hU2]; exact Finset.mem_singleton_self _))
        · exact Or.inr (by rw [if_pos hdoor, hU3]; exact Finset.mem_singleton_self _)
      | inr d' => exact absurd hcd (not_cellDoor_inr_inr κ _ d')
    · intro hc
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hc with (hc | hc) | hc
      · by_cases h : d1
        · rw [if_pos h, Finset.mem_singleton] at hc
          rw [hc, hU1]; exact (down_cellDoor_iff κ a b hd _).mpr (Or.inl ⟨rfl, h⟩)
        · rw [if_neg h] at hc; exact absurd hc (Finset.notMem_empty _)
      · by_cases h : d2
        · rw [if_pos h, Finset.mem_singleton] at hc
          rw [hc, hU2]; exact (down_cellDoor_iff κ a b hd _).mpr (Or.inr (Or.inl ⟨rfl, h⟩))
        · rw [if_neg h] at hc; exact absurd hc (Finset.notMem_empty _)
      · by_cases h : d3
        · rw [if_pos h, Finset.mem_singleton] at hc
          rw [hc, hU3]; exact (down_cellDoor_iff κ a b hd _).mpr (Or.inr (Or.inr ⟨rfl, h⟩))
        · rw [if_neg h] at hc; exact absurd hc (Finset.notMem_empty _)
  rw [hfilter, doorCount]
  have h12 : U1 ≠ U2 := by rw [hU1, hU2]; simp [Sum.inl.injEq, Subtype.ext_iff]
  have h13 : U1 ≠ U3 := by rw [hU1, hU3]; simp [Sum.inl.injEq, Subtype.ext_iff]
  have h23 : U2 ≠ U3 := by rw [hU2, hU3]; simp [Sum.inl.injEq, Subtype.ext_iff]
  by_cases hb1 : d1 <;> by_cases hb2 : d2 <;> by_cases hb3 : d3 <;>
    simp [← hd1, ← hd2, ← hd3, hb1, hb2, hb3, h12, h13, h23, Finset.card_union_of_disjoint,
      Finset.disjoint_singleton]

/-- **Up construction (diagonal).** `up(a,b)` is door-adjacent to `down(a,b)` across their shared
diagonal (interior). -/
theorem up_diagonal_cellDoor (κ : SpernerColoring N) (a b : ℕ) (hd : a + b + 2 ≤ N)
    (hdoor : isDoor (κ.color (mkPt (a + 1) b (by omega))) (κ.color (mkPt a (b + 1) (by omega)))
      = true) :
    CellDoor κ (Sum.inl ⟨(a, b), by rw [mem_upCarrier]; omega⟩)
      (Sum.inr ⟨(a, b), by rw [mem_downCarrier]; omega⟩) :=
  cellDoor_symm κ (down_diagonal_cellDoor κ a b hd hdoor)

/-- **Up construction (horizontal).** `up(a,b+1)` is door-adjacent to `down(a,b)` across `up`'s bottom
edge `{(a,b+1),(a+1,b+1)}`. -/
theorem up_horiz_cellDoor (κ : SpernerColoring N) (a b : ℕ) (hd : a + b + 2 ≤ N)
    (hdoor : isDoor (κ.color (mkPt a (b + 1) (by omega)))
      (κ.color (mkPt (a + 1) (b + 1) (by omega))) = true) :
    CellDoor κ (Sum.inl ⟨(a, b + 1), by rw [mem_upCarrier]; omega⟩)
      (Sum.inr ⟨(a, b), by rw [mem_downCarrier]; omega⟩) :=
  cellDoor_symm κ (down_horizTop_cellDoor κ a b hd hdoor)

/-- **Up construction (vertical).** `up(a+1,b)` is door-adjacent to `down(a,b)` across `up`'s left
edge `{(a+1,b),(a+1,b+1)}`. -/
theorem up_vert_cellDoor (κ : SpernerColoring N) (a b : ℕ) (hd : a + b + 2 ≤ N)
    (hdoor : isDoor (κ.color (mkPt (a + 1) b (by omega)))
      (κ.color (mkPt (a + 1) (b + 1) (by omega))) = true) :
    CellDoor κ (Sum.inl ⟨(a + 1, b), by rw [mem_upCarrier]; omega⟩)
      (Sum.inr ⟨(a, b), by rw [mem_downCarrier]; omega⟩) :=
  cellDoor_symm κ (down_vertRight_cellDoor κ a b hd hdoor)

/-- **Characterization of an up-triangle's cell-neighbours.** For any `up(a,b)` (`a+b+1 ≤ N`), a
down-triangle `⟨(p,q),_⟩` is door-adjacent iff its index is one of the three edge-partners — `(a,b)`
(diagonal), `(a,b-1)` (horizontal, `q+1=b`), `(a-1,b)` (vertical, `p+1=a`) — and the corresponding
edge carries a door. (On the hypotenuse the diagonal partner `down(a,b)` does not exist, so that
disjunct is vacuous — the diagonal then reaches an outer vertex instead.) -/
theorem up_cellDoor_iff (κ : SpernerColoring N) (a b : ℕ) (hu : a + b + 1 ≤ N) (p q : ℕ)
    (hpq : (p, q) ∈ downCarrier N) :
    CellDoor κ (Sum.inl ⟨(a, b), by rw [mem_upCarrier]; omega⟩) (Sum.inr ⟨(p, q), hpq⟩) ↔
      (p = a ∧ q = b ∧
        isDoor (κ.color (mkPt (a + 1) b (by omega))) (κ.color (mkPt a (b + 1) (by omega))) = true) ∨
      (p = a ∧ q + 1 = b ∧
        isDoor (κ.color (mkPt a b (by omega))) (κ.color (mkPt (a + 1) b (by omega))) = true) ∨
      (p + 1 = a ∧ q = b ∧
        isDoor (κ.color (mkPt a b (by omega))) (κ.color (mkPt a (b + 1) (by omega))) = true) := by
  constructor
  · intro h
    obtain ⟨_, x, hxu, y, hyu, hxy, hxd, hyd, hdoor⟩ := h
    have hpart := up_down_share_two hxu hxd hyu hyd hxy
    simp only [triVerts, Sum.elim_inl, Sum.elim_inr, upVerts, downVerts, Finset.mem_insert,
      Finset.mem_singleton] at hxu hyu hxd hyd
    dsimp only at hpart hxu hyu hxd hyd
    rcases hpart with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine Or.inl ⟨rfl, rfl, isDoor_of_pair κ ?_ ?_ hxy hdoor⟩
      · rcases hxu with h | h | h
        · rw [h] at hxd; rcases hxd with h' | h' | h' <;> (rw [mkPt_inj] at h'; omega)
        · exact Or.inl h
        · exact Or.inr h
      · rcases hyu with h | h | h
        · rw [h] at hyd; rcases hyd with h' | h' | h' <;> (rw [mkPt_inj] at h'; omega)
        · exact Or.inl h
        · exact Or.inr h
    · refine Or.inr (Or.inl ⟨rfl, rfl, isDoor_of_pair κ ?_ ?_ hxy hdoor⟩)
      · rcases hxu with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · rw [h] at hxd; rcases hxd with h' | h' | h' <;> (rw [mkPt_inj] at h'; omega)
      · rcases hyu with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · rw [h] at hyd; rcases hyd with h' | h' | h' <;> (rw [mkPt_inj] at h'; omega)
    · refine Or.inr (Or.inr ⟨rfl, rfl, isDoor_of_pair κ ?_ ?_ hxy hdoor⟩)
      · rcases hxu with h | h | h
        · exact Or.inl h
        · rw [h] at hxd; rcases hxd with h' | h' | h' <;> (rw [mkPt_inj] at h'; omega)
        · exact Or.inr h
      · rcases hyu with h | h | h
        · exact Or.inl h
        · rw [h] at hyd; rcases hyd with h' | h' | h' <;> (rw [mkPt_inj] at h'; omega)
        · exact Or.inr h
  · rintro (⟨hp, hq, hdoor⟩ | ⟨hp, hq, hdoor⟩ | ⟨hp, hq, hdoor⟩)
    · subst a; subst b
      exact up_diagonal_cellDoor κ p q (by rw [mem_downCarrier] at hpq; omega) hdoor
    · subst a; subst b
      exact up_horiz_cellDoor κ p q (by rw [mem_downCarrier] at hpq; omega) hdoor
    · subst a; subst b
      exact up_vert_cellDoor κ p q (by rw [mem_downCarrier] at hpq; omega) hdoor

open Finset in
set_option linter.unusedSimpArgs false in
/-- **Up-triangle degree.** An up-triangle's door-graph degree equals its `doorCount`: each of its
three door edges reaches a unique neighbour — an interior cell-partner, or (for the diagonal on the
hypotenuse) a boundary outer vertex. -/
theorem up_cell_degree (κ : SpernerColoring N) (a b : ℕ) (hu : a + b + 1 ≤ N) :
    (fullDoorGraph κ).degree
        (Sum.inl (Sum.inl ⟨(a, b), by rw [mem_upCarrier]; omega⟩ : Cell N))
      = doorCount (κ.color (mkPt a b (by omega))) (κ.color (mkPt (a + 1) b (by omega)))
          (κ.color (mkPt a (b + 1) (by omega))) := by
  rw [degree_inl_eq]
  set HD := isDoor (κ.color (mkPt a b (by omega))) (κ.color (mkPt (a + 1) b (by omega))) with hHD
  set DD := isDoor (κ.color (mkPt (a + 1) b (by omega))) (κ.color (mkPt a (b + 1) (by omega)))
    with hDD
  set VD := isDoor (κ.color (mkPt a b (by omega))) (κ.color (mkPt a (b + 1) (by omega))) with hVD
  -- a horizontal/vertical door forces its partner triangle to exist
  have hHDb : HD = true → 1 ≤ b := by
    intro h; rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; rw [hHD, bottom_H_not_door κ a (by omega)] at h; exact absurd h (by simp)
    · exact hb
  have hVDa : VD = true → 1 ≤ a := by
    intro h; rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; rw [hVD, left_V_not_door κ b (by omega)] at h; exact absurd h (by simp)
    · exact ha
  -- the cell-neighbour finset as the union of the three door-gated partners
  set Ddiag : Finset (Cell N) :=
    if h : a + b + 2 ≤ N then (if DD then {Sum.inr (⟨(a, b), by rw [mem_downCarrier]; omega⟩ : Down N)}
      else ∅) else ∅ with hDdiag
  set Dhoriz : Finset (Cell N) :=
    if h : HD = true then {Sum.inr (⟨(a, b - 1), by have := hHDb h; rw [mem_downCarrier]; omega⟩
      : Down N)} else ∅ with hDhoriz
  set Dvert : Finset (Cell N) :=
    if h : VD = true then {Sum.inr (⟨(a - 1, b), by have := hVDa h; rw [mem_downCarrier]; omega⟩
      : Down N)} else ∅ with hDvert
  have hset : (univ.filter (fun c : Cell N =>
      CellDoor κ (Sum.inl ⟨(a, b), by rw [mem_upCarrier]; omega⟩) c))
      = Ddiag ∪ Dhoriz ∪ Dvert := by
    ext c
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_union]
    constructor
    · rintro ⟨-, hcd⟩
      cases c with
      | inl u' => exact absurd hcd (not_cellDoor_inl_inl κ _ u')
      | inr d =>
        obtain ⟨⟨p, q⟩, hpq⟩ := d
        have hpqN : p + q + 2 ≤ N := by rw [mem_downCarrier] at hpq; exact hpq
        rw [up_cellDoor_iff κ a b hu p q hpq] at hcd
        rcases hcd with ⟨hp, hq, hdoor⟩ | ⟨hp, hq, hdoor⟩ | ⟨hp, hq, hdoor⟩
        · refine Or.inl (Or.inl ?_)
          rw [hDdiag, dif_pos (show a + b + 2 ≤ N by omega), if_pos hdoor, Finset.mem_singleton,
            Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq]
          exact ⟨hp, hq⟩
        · refine Or.inl (Or.inr ?_)
          rw [hDhoriz, dif_pos hdoor, Finset.mem_singleton, Sum.inr.injEq, Subtype.mk.injEq,
            Prod.mk.injEq]
          exact ⟨hp, by omega⟩
        · refine Or.inr ?_
          rw [hDvert, dif_pos hdoor, Finset.mem_singleton, Sum.inr.injEq, Subtype.mk.injEq,
            Prod.mk.injEq]
          exact ⟨by omega, hq⟩
    · intro hc
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hc with (hc | hc) | hc
      · rw [hDdiag] at hc
        split at hc
        · rename_i hI
          split at hc
          · rename_i hdd
            rw [Finset.mem_singleton] at hc; subst hc
            exact (up_cellDoor_iff κ a b hu a b (by rw [mem_downCarrier]; omega)).mpr
              (Or.inl ⟨rfl, rfl, hdd⟩)
          · exact absurd hc (Finset.notMem_empty _)
        · exact absurd hc (Finset.notMem_empty _)
      · rw [hDhoriz] at hc
        split at hc
        · rename_i hdd
          rw [Finset.mem_singleton] at hc; subst hc
          refine (up_cellDoor_iff κ a b hu a (b - 1) _).mpr (Or.inr (Or.inl ⟨rfl, ?_, hdd⟩))
          have := hHDb hdd; omega
        · exact absurd hc (Finset.notMem_empty _)
      · rw [hDvert] at hc
        split at hc
        · rename_i hdd
          rw [Finset.mem_singleton] at hc; subst hc
          refine (up_cellDoor_iff κ a b hu (a - 1) b _).mpr (Or.inr (Or.inr ⟨?_, rfl, hdd⟩))
          have := hVDa hdd; omega
        · exact absurd hc (Finset.notMem_empty _)
  -- the outer-neighbour finset: the hypotenuse diagonal, only on the boundary
  have houter : (univ.filter (fun k : Outer N =>
      (Sum.inl ⟨(a, b), by rw [mem_upCarrier]; omega⟩ : Cell N) = outerTri k ∧ BoundaryDoor κ k)).card
      = if a + b + 2 ≤ N then 0 else (if DD then 1 else 0) := by
    by_cases hI : a + b + 2 ≤ N
    · rw [if_pos hI, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro k hk
      rw [Finset.mem_filter] at hk
      have he := hk.2.1
      rw [outerTri, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at he
      have := k.isLt; omega
    · rw [if_neg hI]
      have hbdy : a + b + 1 = N := by omega
      have haN : a < N := by omega
      have het : outerTri (⟨a, haN⟩ : Outer N) = Sum.inl ⟨(a, b), by rw [mem_upCarrier]; omega⟩ := by
        show Sum.inl (⟨(a, N - 1 - a), by rw [mem_upCarrier]; omega⟩ : Up N) = _
        rw [Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq]; omega
      have hpa : outerPtA (⟨a, haN⟩ : Outer N) = mkPt (a + 1) b (by omega) := by
        show mkPt (a + 1) (N - 1 - a) (by omega) = mkPt (a + 1) b (by omega)
        rw [mkPt_inj]; omega
      have hpb : outerPtB (⟨a, haN⟩ : Outer N) = mkPt a (b + 1) (by omega) := by
        show mkPt a (N - a) (by omega) = mkPt a (b + 1) (by omega)
        rw [mkPt_inj]; omega
      have hbd_iff : BoundaryDoor κ (⟨a, haN⟩ : Outer N) ↔ DD = true := by
        rw [BoundaryDoor, hpa, hpb, ← hDD]
      have hkey : (univ.filter (fun k : Outer N =>
          (Sum.inl ⟨(a, b), by rw [mem_upCarrier]; omega⟩ : Cell N) = outerTri k ∧ BoundaryDoor κ k))
          = if DD then {(⟨a, haN⟩ : Outer N)} else ∅ := by
        ext k
        rw [Finset.mem_filter]
        constructor
        · rintro ⟨-, he, hbd⟩
          rw [outerTri, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at he
          obtain ⟨hka, -⟩ := he
          have hk : k = ⟨a, haN⟩ := Fin.ext hka.symm
          subst hk
          rw [if_pos (hbd_iff.mp hbd), Finset.mem_singleton]
        · intro hk
          by_cases hdd : DD
          · rw [if_pos hdd, Finset.mem_singleton] at hk; subst hk
            exact ⟨Finset.mem_univ _, het.symm, hbd_iff.mpr hdd⟩
          · rw [if_neg hdd] at hk; exact absurd hk (Finset.notMem_empty _)
      rw [hkey]; by_cases hdd : DD <;> simp [hdd]
  rw [hset]
  -- cardinalities of the three door-gated singletons, with disjointness
  have hcd : (Ddiag ∪ Dhoriz ∪ Dvert).card
      = (if a + b + 2 ≤ N then (if DD then 1 else 0) else 0)
        + (if HD then 1 else 0) + (if VD then 1 else 0) := by
    have hcardD : Ddiag.card = if a + b + 2 ≤ N then (if DD then 1 else 0) else 0 := by
      rw [hDdiag]; by_cases hI : a + b + 2 ≤ N <;> by_cases hd : DD <;> simp [hI, hd]
    have hcardH : Dhoriz.card = if HD then 1 else 0 := by
      rw [hDhoriz]; by_cases hd : HD = true <;> simp [hd]
    have hcardV : Dvert.card = if VD then 1 else 0 := by
      rw [hDvert]; by_cases hd : VD = true <;> simp [hd]
    have hdisj1 : Disjoint Ddiag Dhoriz := by
      rw [Finset.disjoint_left]; intro x hx hy
      rw [hDdiag] at hx; rw [hDhoriz] at hy
      split at hx
      · split at hx
        · rw [Finset.mem_singleton] at hx
          split at hy
          · rename_i hh
            rw [Finset.mem_singleton] at hy
            have := hHDb hh; rw [hx] at hy
            simp only [Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq] at hy; omega
          · exact absurd hy (Finset.notMem_empty _)
        · exact absurd hx (Finset.notMem_empty _)
      · exact absurd hx (Finset.notMem_empty _)
    have hdisj2 : Disjoint (Ddiag ∪ Dhoriz) Dvert := by
      rw [Finset.disjoint_left]; intro x hx hy
      rw [hDvert] at hy
      split at hy
      · rename_i hv
        rw [Finset.mem_singleton] at hy; have := hVDa hv
        rw [Finset.mem_union] at hx
        rcases hx with hx | hx
        · rw [hDdiag] at hx; split at hx
          · split at hx
            · rw [Finset.mem_singleton, hy] at hx
              simp only [Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq] at hx; omega
            · exact absurd hx (Finset.notMem_empty _)
          · exact absurd hx (Finset.notMem_empty _)
        · rw [hDhoriz] at hx; split at hx
          · rename_i hh
            rw [Finset.mem_singleton, hy] at hx
            have := hHDb hh
            simp only [Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq] at hx; omega
          · exact absurd hx (Finset.notMem_empty _)
      · exact absurd hy (Finset.notMem_empty _)
    rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
      hcardD, hcardH, hcardV]
  rw [hcd, houter, doorCount, ← hHD, ← hDD, ← hVD]
  by_cases hI : a + b + 2 ≤ N <;> by_cases h1 : HD <;> by_cases h2 : DD <;> by_cases h3 : VD <;>
    simp [hI, h1, h2, h3]

/-- **The cell-degree obligation.** Every triangle's door-graph degree equals its `doorCount` — the
`cell_degree` field of `MultiDoorIncidence` for the `N`-subdivision. -/
theorem cell_degree (κ : SpernerColoring N) (t : Cell N) :
    (fullDoorGraph κ).degree (Sum.inl t)
      = doorCount (col κ t).1 (col κ t).2.1 (col κ t).2.2 := by
  cases t with
  | inl u =>
    obtain ⟨⟨a, b⟩, hu⟩ := u
    rw [mem_upCarrier] at hu
    exact up_cell_degree κ a b (by omega)
  | inr d =>
    obtain ⟨⟨a, b⟩, hd⟩ := d
    rw [mem_downCarrier] at hd
    exact down_cell_degree κ a b (by omega)

end CRNT.Analysis.SpernerLattice

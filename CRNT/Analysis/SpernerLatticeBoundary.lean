import CRNT.Analysis.SpernerLatticeFullGraph
import CRNT.Analysis.Sperner

/-!
# The boundary door count is odd (one-dimensional Sperner on the hypotenuse)

The `outer_odd` obligation of `MultiDoorIncidence` for the `N`-subdivision: the number of outer
vertices of `fullDoorGraph` with odd degree is odd. By `odd_degree_outer_iff` that count is the number
of hypotenuse (`i+j=N`) sub-edges carrying a `{0,1}` door, and the hypotenuse is a one-dimensional
Sperner path — colored entirely with `{0,1}` (no point with `i+j=N` is colored `2`), running from
color `0` at the corner `(N,0)` to color `1` at `(0,N)`. The one-dimensional Sperner lemma
(`Sperner.sperner_odd_rainbowEdges`) then gives an odd number of door sub-edges.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.SpernerLatticeFullGraph`,
`CRNT.Analysis.Sperner`.
-/

namespace CRNT.Analysis.SpernerLattice

open CRNT.Analysis.Sperner2D CRNT.Analysis.Sperner Finset

variable {N : ℕ}

/-- A color of `Fin 3` that is neither `1` nor `2` is `0`. -/
private theorem color_eq_zero_of_ne {x : Fin 3} (h1 : x ≠ 1) (h2 : x ≠ 2) : x = 0 := by
  fin_cases x <;> simp_all

/-- The door predicate on `{0,1}`-restricted colors is the color-change predicate. -/
private theorem isDoor_iff_decide_ne {x y : Fin 3} (hx : x ≠ 2) (hy : y ≠ 2) :
    (isDoor x y = true) ↔ (decide (x = 0) ≠ decide (y = 0)) := by
  fin_cases x <;> fin_cases y <;> revert hx hy <;> decide

/-- The `a`-th vertex of the hypotenuse path: `(a, N-a)` (clamped by `min` to stay in range, keeping
the coloring a total function `ℕ → Bool`). -/
def hypPt (a : ℕ) : Pt N := mkPt (min a N) (N - min a N) (by omega)

@[simp] theorem hypPt_fst {a : ℕ} (h : a ≤ N) : (hypPt a : Pt N).1.1 = a := by
  simp only [hypPt, mkPt, Nat.min_eq_left h]

@[simp] theorem hypPt_snd {a : ℕ} (h : a ≤ N) : (hypPt a : Pt N).1.2 = N - a := by
  simp only [hypPt, mkPt, Nat.min_eq_left h]

/-- A hypotenuse point is never colored `2` (its barycentric coordinate `k = N-i-j` is `0`). -/
theorem hyp_ne_two (κ : SpernerColoring N) {a : ℕ} (h : a ≤ N) : κ.color (hypPt a) ≠ 2 := by
  intro hc
  have hlt := κ.proper2 _ hc
  rw [hypPt_fst h, hypPt_snd h] at hlt
  omega

/-- The one-dimensional coloring of the hypotenuse path: `true` exactly when the point is colored
`0`. Endpoints: `(N,0)` is `0` (true), `(0,N)` is `1` (false). -/
def hypColor (κ : SpernerColoring N) (a : ℕ) : Bool := decide (κ.color (hypPt a) = 0)

theorem hypColor_zero (κ : SpernerColoring N) : hypColor κ 0 = false := by
  simp only [hypColor, decide_eq_false_iff_not]
  intro hc
  have := κ.proper0 _ hc
  rw [hypPt_fst (Nat.zero_le N)] at this
  omega

theorem hypColor_N (κ : SpernerColoring N) : hypColor κ N = true := by
  simp only [hypColor, decide_eq_true_eq]
  refine color_eq_zero_of_ne ?_ (hyp_ne_two κ le_rfl)
  intro hc
  have := κ.proper1 _ hc
  rw [hypPt_snd le_rfl] at this
  omega

/-- The hypotenuse coloring satisfies the one-dimensional Sperner boundary condition. -/
theorem hyp_isSpernerColoring (κ : SpernerColoring N) :
    IsSpernerColoring N (hypColor κ) :=
  ⟨hypColor_zero κ, hypColor_N κ⟩

/-- A hypotenuse sub-edge is a door exactly when it is a one-dimensional Sperner rainbow edge. -/
theorem boundaryDoor_iff (κ : SpernerColoring N) (k : Outer N) :
    BoundaryDoor κ k ↔ hypColor κ (k.val + 1) ≠ hypColor κ k.val := by
  have hk1 : k.val + 1 ≤ N := by have := k.isLt; omega
  have hk0 : k.val ≤ N := by have := k.isLt; omega
  have hA : outerPtA k = hypPt (k.val + 1) := by
    unfold outerPtA hypPt
    rw [mkPt_inj]; omega
  have hB : outerPtB k = hypPt k.val := by
    unfold outerPtB hypPt
    rw [mkPt_inj]; omega
  unfold BoundaryDoor
  rw [hA, hB, isDoor_iff_decide_ne (hyp_ne_two κ hk1) (hyp_ne_two κ hk0)]
  rfl

/-- The number of boundary doors equals the one-dimensional Sperner rainbow-edge count. -/
theorem boundaryDoors_card (κ : SpernerColoring N) :
    (univ.filter (fun k : Outer N => BoundaryDoor κ k)).card
      = (rainbowEdges N (hypColor κ)).card := by
  rw [Finset.card_filter, rainbowEdges, Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range (fun i => if hypColor κ (i + 1) ≠ hypColor κ i then 1 else 0) N]
  apply Finset.sum_congr rfl
  intro k _
  simp only [boundaryDoor_iff κ k]

/-- **The boundary door count is odd.** -/
theorem boundaryDoors_odd (κ : SpernerColoring N) :
    Odd (univ.filter (fun k : Outer N => BoundaryDoor κ k)).card := by
  rw [boundaryDoors_card]
  exact sperner_odd_rainbowEdges (hyp_isSpernerColoring κ)

/-- **The `outer_odd` obligation.** The number of odd-degree outer vertices of the full door graph is
odd — discharging the boundary field of `MultiDoorIncidence`. -/
theorem outer_odd_count (κ : SpernerColoring N) :
    Odd #{o : Outer N | Odd ((fullDoorGraph κ).degree (Sum.inr o))} := by
  have heq : (univ.filter (fun o : Outer N => Odd ((fullDoorGraph κ).degree (Sum.inr o))))
      = (univ.filter (fun k : Outer N => BoundaryDoor κ k)) := by
    apply Finset.filter_congr
    intro k _
    exact odd_degree_outer_iff κ k
  show Odd (univ.filter (fun o : Outer N => Odd ((fullDoorGraph κ).degree (Sum.inr o)))).card
  rw [heq]
  exact boundaryDoors_odd κ

end CRNT.Analysis.SpernerLattice

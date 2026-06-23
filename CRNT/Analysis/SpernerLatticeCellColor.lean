import CRNT.Analysis.SpernerLatticeColoring

/-!
# Cell color triples and the confinement of boundary doors

This module supplies the coloring-side data the door-degree bijection needs: the **color triple** of
each triangle of the `N`-subdivision (its three vertex colors), and the structural fact that
**boundary `{0,1}`-doors occur only on the `k = 0` side** of the simplex.

`col` reads off the three vertex colors of each triangle from a `SpernerColoring`: for an up triangle
`up(a, b)` the colors of `(a, b), (a+1, b), (a, b+1)`, and for a down triangle `down(a, b)` those of
`(a+1, b), (a, b+1), (a+1, b+1)`. The local door count `doorCount (col κ c)` is then the number of a
triangle's three edges whose endpoints are colored `{0, 1}` — the quantity the bijection equates to
the triangle's door-graph degree.

The confinement lemmas use the Sperner boundary conditions of `CRNT.Analysis.SpernerLatticeColoring`.
The bottom side `j = 0` is colored within `{0, 2}` and the left side `i = 0` within `{1, 2}`, so
neither can carry a `{0, 1}` door:

* `bottom_H_not_door` — a horizontal edge on the bottom side is never a `{0,1}` door;
* `left_V_not_door` — a vertical edge on the left side is never a `{0,1}` door.

Only the `k = 0` side (`i + j = N`), colored within `{0, 1}`, can carry boundary doors. This is what
collapses the boundary outer vertices of the eventual door graph to a single side — the side the
one-dimensional Sperner lemma will act on for `outer_odd` — and confirms that every horizontal or
vertical `{0,1}`-door edge is interior, so its incidence partner (from
`CRNT.Analysis.SpernerLatticeIncidenceHV`) always exists.

## Main definitions

* `upCol`, `downCol`, `col` — the vertex-color triple of each triangle.

## Main results

* `isDoor_eq_false_of_ne_one`, `isDoor_eq_false_of_ne_zero` — a color pair avoiding `1` (resp. `0`)
  is not a door.
* `bottom_H_not_door`, `left_V_not_door` — boundary doors avoid the bottom and left sides.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.SpernerLatticeColoring`.
-/

namespace CRNT.Analysis.SpernerLattice

open CRNT.Analysis.Sperner2D

variable {N : ℕ}

/-- A color pair with neither entry equal to `1` is not a `{0,1}` door. -/
theorem isDoor_eq_false_of_ne_one {x y : Color} (hx : x ≠ 1) (hy : y ≠ 1) :
    isDoor x y = false := by
  unfold isDoor
  simp only [decide_eq_false_iff_not]
  rintro (⟨_, rfl⟩ | ⟨rfl, _⟩)
  · exact hy rfl
  · exact hx rfl

/-- A color pair with neither entry equal to `0` is not a `{0,1}` door. -/
theorem isDoor_eq_false_of_ne_zero {x y : Color} (hx : x ≠ 0) (hy : y ≠ 0) :
    isDoor x y = false := by
  unfold isDoor
  simp only [decide_eq_false_iff_not]
  rintro (⟨rfl, _⟩ | ⟨_, rfl⟩)
  · exact hx rfl
  · exact hy rfl

/-- The vertex-color triple of an up triangle `up(a, b)`: the colors of `(a, b), (a+1, b), (a, b+1)`. -/
def upCol (κ : SpernerColoring N) (c : Up N) : Color × Color × Color :=
  (κ.color (mkPt c.1.1 c.1.2 (by have := mem_upCarrier.mp c.2; omega)),
    κ.color (mkPt (c.1.1 + 1) c.1.2 (by have := mem_upCarrier.mp c.2; omega)),
    κ.color (mkPt c.1.1 (c.1.2 + 1) (by have := mem_upCarrier.mp c.2; omega)))

/-- The vertex-color triple of a down triangle `down(a, b)`: the colors of `(a+1, b), (a, b+1),
(a+1, b+1)`. -/
def downCol (κ : SpernerColoring N) (c : Down N) : Color × Color × Color :=
  (κ.color (mkPt (c.1.1 + 1) c.1.2 (by have := mem_downCarrier.mp c.2; omega)),
    κ.color (mkPt c.1.1 (c.1.2 + 1) (by have := mem_downCarrier.mp c.2; omega)),
    κ.color (mkPt (c.1.1 + 1) (c.1.2 + 1) (by have := mem_downCarrier.mp c.2; omega)))

/-- The vertex-color triple of a triangle. -/
def col (κ : SpernerColoring N) : Cell N → Color × Color × Color := Sum.elim (upCol κ) (downCol κ)

/-- **No boundary doors on the bottom side.** A horizontal edge `{(a, 0), (a+1, 0)}` on the side
`j = 0` is never a `{0,1}` door: both endpoints are colored within `{0, 2}`. -/
theorem bottom_H_not_door (κ : SpernerColoring N) (a : ℕ) (ha : a + 1 ≤ N) :
    isDoor (κ.color (mkPt a 0 (by omega))) (κ.color (mkPt (a + 1) 0 (by omega))) = false :=
  isDoor_eq_false_of_ne_one (side_jk_ne_one κ a (by omega)) (side_jk_ne_one κ (a + 1) (by omega))

/-- **No boundary doors on the left side.** A vertical edge `{(0, b), (0, b+1)}` on the side `i = 0`
is never a `{0,1}` door: both endpoints are colored within `{1, 2}`. -/
theorem left_V_not_door (κ : SpernerColoring N) (b : ℕ) (hb : b + 1 ≤ N) :
    isDoor (κ.color (mkPt 0 b (by omega))) (κ.color (mkPt 0 (b + 1) (by omega))) = false :=
  isDoor_eq_false_of_ne_zero (side_ik_ne_zero κ b (by omega)) (side_ik_ne_zero κ (b + 1) (by omega))

end CRNT.Analysis.SpernerLattice

import CRNT.Analysis.SpernerLattice

/-!
# The Sperner boundary conditions of a proper coloring

This module derives the classical Sperner *boundary conditions* of the `N`-subdivision from the
`SpernerColoring` axioms of `CRNT.Analysis.SpernerLattice`: the three corners carry the colors
`0, 1, 2`, and each boundary side omits the color of the opposite corner. These are exactly the
hypotheses the two-dimensional Sperner lemma needs at the boundary, and they feed the
one-dimensional Sperner reduction that will discharge `outer_odd` in the eventual multi-outer
assembly.

The proofs are uniform in `N`: each corner color is pinned by eliminating the two colors whose
positivity clause its coordinates violate (a corner has two zero barycentric coordinates), and each
side restriction is a single clause of the proper-coloring condition.

## Main results

* `corner_color_i`, `corner_color_j`, `corner_color_k` — the corners `(N,0)`, `(0,N)`, `(0,0)` are
  colored `0`, `1`, `2`.
* `side_jk_ne_one`, `side_ik_ne_zero`, `side_ij_ne_two` — on the side `j = 0` the color is never `1`,
  on `i = 0` never `0`, and on `i + j = N` (the `k = 0` side) never `2`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.SpernerLattice`.
-/

namespace CRNT.Analysis.SpernerLattice

open CRNT.Analysis.Sperner2D

/-- Every color is `0`, `1`, or `2`. -/
theorem fin3_cases (c : Color) : c = 0 ∨ c = 1 ∨ c = 2 := by revert c; decide

variable {N : ℕ}

/-- **Boundary side `j = 0`.** A vertex on the side `j = 0` is never colored `1` (its second
barycentric coordinate vanishes). -/
theorem side_jk_ne_one (κ : SpernerColoring N) (i : ℕ) (h : i ≤ N) :
    κ.color (mkPt i 0 (by omega)) ≠ 1 := by
  intro hc; have := κ.proper1 _ hc; simp [mkPt] at this

/-- **Boundary side `i = 0`.** A vertex on the side `i = 0` is never colored `0`. -/
theorem side_ik_ne_zero (κ : SpernerColoring N) (j : ℕ) (h : j ≤ N) :
    κ.color (mkPt 0 j (by omega)) ≠ 0 := by
  intro hc; have := κ.proper0 _ hc; simp [mkPt] at this

/-- **Boundary side `i + j = N` (the `k = 0` side).** A vertex on this side is never colored `2`. -/
theorem side_ij_ne_two (κ : SpernerColoring N) (i j : ℕ) (h : i + j = N) :
    κ.color (mkPt i j (by omega)) ≠ 2 := by
  intro hc; have := κ.proper2 _ hc; simp [mkPt] at this; omega

/-- **Corner `(N, 0)` is colored `0`.** Its second and third barycentric coordinates vanish, ruling
out the colors `1` and `2`. -/
theorem corner_color_i (κ : SpernerColoring N) : κ.color (mkPt N 0 (by omega)) = 0 := by
  have h1 : κ.color (mkPt N 0 (by omega)) ≠ 1 := by
    intro h; have := κ.proper1 _ h; simp [mkPt] at this
  have h2 : κ.color (mkPt N 0 (by omega)) ≠ 2 := by
    intro h; have := κ.proper2 _ h; simp [mkPt] at this
  rcases fin3_cases (κ.color (mkPt N 0 (by omega))) with h | h | h
  · exact h
  · exact absurd h h1
  · exact absurd h h2

/-- **Corner `(0, N)` is colored `1`.** Its first and third barycentric coordinates vanish, ruling
out the colors `0` and `2`. -/
theorem corner_color_j (κ : SpernerColoring N) : κ.color (mkPt 0 N (by omega)) = 1 := by
  have h0 : κ.color (mkPt 0 N (by omega)) ≠ 0 := by
    intro h; have := κ.proper0 _ h; simp [mkPt] at this
  have h2 : κ.color (mkPt 0 N (by omega)) ≠ 2 := by
    intro h; have := κ.proper2 _ h; simp [mkPt] at this
  rcases fin3_cases (κ.color (mkPt 0 N (by omega))) with h | h | h
  · exact absurd h h0
  · exact h
  · exact absurd h h2

/-- **Corner `(0, 0)` is colored `2`.** Its first and second barycentric coordinates vanish, ruling
out the colors `0` and `1` (its third coordinate `k = N` is positive when `0 < N`). -/
theorem corner_color_k (κ : SpernerColoring N) (hN : 0 < N) :
    κ.color (mkPt 0 0 (by omega)) = 2 := by
  have h0 : κ.color (mkPt 0 0 (by omega)) ≠ 0 := by
    intro h; have := κ.proper0 _ h; simp [mkPt] at this
  have h1 : κ.color (mkPt 0 0 (by omega)) ≠ 1 := by
    intro h; have := κ.proper1 _ h; simp [mkPt] at this
  rcases fin3_cases (κ.color (mkPt 0 0 (by omega))) with h | h | h
  · exact absurd h h0
  · exact absurd h h1
  · exact h

end CRNT.Analysis.SpernerLattice

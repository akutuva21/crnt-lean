import CRNT.Geometry.ZeroSeparatingCurve2D

/-!
# A polygonal separating-region predicate for the genuine flow

The zero-separating surface of Craciun, _Toric differential inclusions and a proof of the global
attractor conjecture_, is piecewise-linear: its region is a finite intersection of closed
half-planes `ZeroSeparatingCurve2D.polyRegion`, whose boundary is Lipschitz rather than `C¹`. This
module packages that polygonal region as a surface-existence predicate parallel to the `C¹`
`DifferentialInclusion.ZeroSeparatingSurfaceExists`, and wires it to the persistence conclusion for
the genuine flow through the distance-based closed-set Nagumo result.

## Contents

* `PolyZeroSeparatingExists f x₀` — the **polygonal surface-existence predicate.** There is a closed
  polygonal region `polyRegion faces` containing the start `x₀`, with one face carrying a unit normal
  and offset at least a margin `r > 0` (so the region misses the open `r`-ball about the origin), to
  which the field `f` is subtangent (`IsSupportField`). This is the Lipschitz counterpart of
  `ZeroSeparatingSurfaceExists`, stated against the half-plane region instead of a `C¹` sublevel set.

* `PolyZeroSeparatingExists.away_from_origin` — the **wiring lemma.** Given the polygonal region for
  `f` at `x₀`, a genuine curve `γ` through `x₀`, and the subtangency-to-distance bridge — that
  subtangency of `f` to a polygonal region makes `t ↦ Metric.infDist (γ t) (polyRegion faces)`
  nonincreasing along `γ` — the genuine trajectory keeps a hard distance `r` from the origin for all
  forward times. The bridge is the set-valued viability content recorded in `ClosedSetNagumo.lean`
  and `Viability.lean`; it is supplied as a hypothesis, as in `stays_away_from_zero_of_support`.

* `polyZeroSeparatingExists_diag` — a **worked non-vacuity witness** in the plane: a constant field
  whose value points into the diagonal half-plane `x + y ≥ 1` admits the polygonal separating region
  `diagFaces` at any start inside it.

## Scope

This module establishes the polygonal predicate and its persistence wiring, reusing the half-plane
geometry and the closed-set Nagumo result. The subtangency-to-distance bridge (set-valued viability)
is taken as a hypothesis, matching the form consumed by `ZeroSeparatingCurve2D`; the construction of
the region itself from a toric differential inclusion is not performed here.

Depends on: `CRNT.Geometry.ZeroSeparatingCurve2D`.
-/

namespace CRNT

namespace ZeroSeparatingCurve2D

open Set Metric
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Polygonal zero-separating region existence.** For a genuine field `f : E → E` and a start
`x₀`, there is a finite face list `faces` whose closed region `polyRegion faces` contains `x₀`, has
one face `(n, a)` with unit normal `‖n‖ = 1` and offset `a ≥ r` for some margin `r > 0` (so the
region misses the open `r`-ball about the origin), and to which `f` is subtangent
(`IsSupportField f faces`). This is the piecewise-linear counterpart of
`DifferentialInclusion.ZeroSeparatingSurfaceExists`: the same separating role played by a polygonal
region with Lipschitz boundary rather than a `C¹` sublevel set. -/
structure PolyZeroSeparatingExists (f : E → E) (x₀ : E) : Prop where
  /-- The polygonal region, its separating face, the margin, the start membership, and subtangency. -/
  exists_region :
    ∃ (faces : List (E × ℝ)) (n : E) (a r : ℝ),
      (n, a) ∈ faces ∧ ‖n‖ = 1 ∧ r ≤ a ∧ 0 < r ∧
      x₀ ∈ polyRegion faces ∧ IsSupportField f faces

/-- **Wiring lemma.** Given the polygonal separating region for `f` at `x₀`, a genuine curve `γ`
continuous solution of `ẋ = f (γ t)` (the continuity/derivative facts enter through the supplied
bridge) starting at `γ 0 = x₀`, and the subtangency-to-distance bridge — that subtangency of `f` to
any polygonal region keeps `t ↦ Metric.infDist (γ t) (polyRegion faces)` nonincreasing on `[0, ∞)`
— the genuine trajectory keeps a hard distance `r > 0` from the origin for all forward times. The
origin is therefore not an `ω`-limit point of `γ`. The bridge is the set-valued viability content
(`ClosedSetNagumo`, `Viability`); it is carried as a hypothesis. -/
theorem PolyZeroSeparatingExists.away_from_origin {f : E → E} {x₀ : E}
    (h : PolyZeroSeparatingExists f x₀) {γ : ℝ → E} (hstart : γ 0 = x₀)
    (hbridge : ∀ faces : List (E × ℝ), IsSupportField f faces →
      AntitoneOn (fun t => Metric.infDist (γ t) (polyRegion faces)) (Set.Ici 0)) :
    ∃ r : ℝ, 0 < r ∧ ∀ t, 0 ≤ t → r ≤ dist (γ t) 0 := by
  obtain ⟨faces, n, a, r, hmem, hn, har, hr, h0region, hsupp⟩ := h.exists_region
  refine ⟨r, hr, fun t ht => ?_⟩
  have h0 : γ 0 ∈ polyRegion faces := by rw [hstart]; exact h0region
  exact stays_away_from_zero_of_support hmem hn har hr h0 (hbridge faces hsupp) ht

/-- **Worked non-vacuity witness.** In the plane, a constant field `fun _ => v` whose value points
into the diagonal half-plane (`0 ≤ ⟪diagNormal, v⟫_ℝ`, the region `x + y ≥ 1`) admits the polygonal
separating region `diagFaces` at any start `x₀` inside it. So `PolyZeroSeparatingExists` is
inhabited by a genuine planar instance. -/
theorem polyZeroSeparatingExists_diag {v x₀ : EuclideanSpace ℝ (Fin 2)}
    (hv : 0 ≤ ⟪diagNormal, v⟫_ℝ) (hx₀ : x₀ ∈ polyRegion diagFaces) :
    PolyZeroSeparatingExists (fun _ => v) x₀ where
  exists_region :=
    ⟨diagFaces, diagNormal, 1, 1, by simp [diagFaces], norm_diagNormal, le_rfl, one_pos, hx₀,
      diagField_isSupport hv⟩

end ZeroSeparatingCurve2D

end CRNT

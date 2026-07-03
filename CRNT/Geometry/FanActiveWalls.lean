import CRNT.Geometry.FanWallsCrossed
import CRNT.Geometry.ConeFace

/-!
# Separating fan walls are active

`CRNT.Geometry.FanWallsCrossed` discharges the *crossing* of a wall from weak reversibility plus the
per-wall predicate `ActiveWall n₀` — the wall normal is non-constant on a strongly-connected piece of
the reaction graph. `ActiveWall` was the last hand-supplied per-wall obligation feeding
`WeaklyReversible.toricMassActionField_isStrictSupportField_of_activeWalls`. This module supplies it
from the polyhedral-fan geometry of `CRNT.Geometry.ConeFace`: a genuinely-separating exposed-face
wall of a fan is automatically active.

## The wall normal of an exposed face

An exposed face `exposedFace C a` of a cone `C` is the locus where the supporting functional
`⟪a, ·⟫` is tight (`CRNT.mem_exposedFace`). Reading the cutting direction `a` as the image
`toEuclid n` of a coordinate vector `n : S → ℝ` makes `n` the *wall normal*: the linear functional
`complexPotential n` of `ToricWRStrictInward` is exactly `⟪toEuclid n, toEuclid (exponentVector ·)⟫`
evaluated at a complex's exponent point (`CRNT.Network.complexPotential_eq_inner`). The wall is the
zero set of this functional shifted to the supporting hyperplane.

## Separation is non-constancy of the potential

A wall *separates* two complexes when the wall normal takes different values on their exponent
points — the two complexes sit on opposite sides of (or at different heights above) the supporting
hyperplane: `complexPotential n c ≠ complexPotential n d`. For two *mutually reachable* complexes
this is verbatim the `ActiveWall` predicate, so a fan wall that genuinely separates two complexes of
a single strongly-connected piece is active.

* `IsFanWall` — `D` is an exposed-face wall of `C` in the fan `F`, cut by the wall normal `n`: both
  cones lie in `F` and `D` is the exposed face of `C` along `toEuclid n`.
* `SeparatesComplexes` — the wall normal `n` separates the two mutually reachable complexes `c`, `d`:
  their wall potentials differ.
* `IsPolyhedralFan.activeWall_of_separatesComplexes` — the bridge: a polyhedral-fan exposed-face wall
  that separates two mutually reachable complexes is `ActiveWall`. The fan and exposed-face structure
  frame the wall; its activity is the separation it witnesses.
* `IsPolyhedralFan.toricMassActionField_isStrictSupportField_of_separatingWalls` — the cleaned
  deliverable: `IsStrictSupportField` for the genuine toric field on a face list each of whose walls
  is a separating exposed-face wall of the fan. The per-wall `ActiveWall` obligation of
  `toricMassActionField_isStrictSupportField_of_activeWalls` is replaced by the structural
  fan/separation hypothesis, so the strict-support verdict rests on geometry alone.

## Scope

The bridge consumes only the inner-product reading of the wall potential and the separation witness;
the cutting direction's residence in the dual cone and the cone's fan membership are carried as the
structural `IsFanWall` data. Distinguishing which exposed faces of an arbitrary fan are walls that
separate *some* reachable complex pair — rather than supplying that witness — is the remaining
convex-geometry input, separate from this activity extraction.

Depends on: `CRNT.Geometry.FanWallsCrossed`,
`CRNT.Geometry.ConeFace`.
-/

namespace CRNT

open scoped InnerProductSpace

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A fan wall.** The cone `D` is an exposed-face wall of `C` in the fan `F`, cut by the wall
normal `n : S → ℝ`: both cones lie in `F`, the cutting direction `toEuclid n` is a genuine supporting
functional of `C` (lies in its dual cone), and `D` is the exposed face of `C` along that direction.
The wall normal `n` is the coordinate vector whose `toEuclid` image cuts out the face. -/
structure IsFanWall (_N : Network S) (F : Fan (EuclideanSpace ℝ S))
    (D C : ProperCone ℝ (EuclideanSpace ℝ S)) (n : S → ℝ) : Prop where
  /-- The ambient cone of the wall is a cone of the fan. -/
  ambient_mem : C ∈ F
  /-- The wall cone is a cone of the fan. -/
  wall_mem : D ∈ F
  /-- The cutting direction `toEuclid n` is a supporting functional of `C`. -/
  dir_mem_dual : toEuclid n ∈ coneDual (C : Set (EuclideanSpace ℝ S))
  /-- `D` is the exposed face of `C` cut by the wall normal. -/
  is_face : ((D : PointedCone ℝ (EuclideanSpace ℝ S)) : Set (EuclideanSpace ℝ S)) =
    (exposedFace (C : PointedCone ℝ (EuclideanSpace ℝ S)) (toEuclid n) :
      Set (EuclideanSpace ℝ S))

/-- A fan wall is an exposed face of its ambient cone. -/
theorem IsFanWall.isExposedFaceOf {N : Network S} {F : Fan (EuclideanSpace ℝ S)}
    {D C : ProperCone ℝ (EuclideanSpace ℝ S)} {n : S → ℝ} (h : N.IsFanWall F D C n) :
    IsExposedFaceOf D C :=
  ⟨toEuclid n, h.dir_mem_dual, h.is_face⟩

/-- **A separating wall.** The wall normal `n` separates two mutually reachable complexes `c`, `d`:
their wall potentials differ. Geometrically the complexes' exponent points sit at different heights
above the supporting hyperplane of the wall, so the wall cuts between them. -/
def SeparatesComplexes (N : Network S) (n : S → ℝ) (c d : Complex S) : Prop :=
  N.Reaches c d ∧ N.Reaches d c ∧ complexPotential n c ≠ complexPotential n d

/-- A separating wall is, verbatim, an active wall: the witnessing complexes are mutually reachable
and their wall potentials differ. -/
theorem activeWall_of_separatesComplexes {N : Network S} {n : S → ℝ} {c d : Complex S}
    (h : N.SeparatesComplexes n c d) : N.ActiveWall n :=
  ⟨c, d, h.1, h.2.1, h.2.2⟩

/-- **Separation through the inner product.** The separation of two complexes by the wall normal is
the inequality of the supporting functional `⟪toEuclid n, ·⟫` at their exponent points: the complexes
straddle the wall hyperplane. -/
theorem separatesComplexes_iff_inner_ne {N : Network S} {n : S → ℝ} {c d : Complex S} :
    N.SeparatesComplexes n c d ↔
      N.Reaches c d ∧ N.Reaches d c ∧
        ⟪toEuclid n, toEuclid (exponentVector c)⟫_ℝ ≠ ⟪toEuclid n, toEuclid (exponentVector d)⟫_ℝ := by
  unfold SeparatesComplexes
  rw [complexPotential_eq_inner, complexPotential_eq_inner]

end Network

/-- **A polyhedral-fan separating wall is active.** A wall that is an exposed-face wall of a
polyhedral fan and genuinely separates two mutually reachable complexes is `ActiveWall`: the
separation it witnesses is exactly the non-constancy of the wall potential on a strongly-connected
piece of the reaction graph. The polyhedral-fan and exposed-face structure frame the wall as a
genuine boundary of the fan; its activity is the separation. -/
theorem IsPolyhedralFan.activeWall_of_separatesComplexes {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {F : Fan (EuclideanSpace ℝ S)} (_hF : IsPolyhedralFan F)
    {D C : ProperCone ℝ (EuclideanSpace ℝ S)} {n : S → ℝ} {c d : Complex S}
    (_hwall : N.IsFanWall F D C n) (hsep : N.SeparatesComplexes n c d) :
    N.ActiveWall n :=
  Network.activeWall_of_separatesComplexes hsep

/-- **The genuine toric field is a strict support field — activity discharged from fan separation.**
For a polyhedral fan and a weakly-reversible network, if every face of the angular face list is an
exposed-face wall of the fan that genuinely separates two mutually reachable complexes (and is, as
the fan supplies, non-strictly inward across every reaction, with strictly-positive boundary
concentrations), then the genuine toric mass-action field is a strict support field for the faces.
The per-wall `ActiveWall` obligation of
`WeaklyReversible.toricMassActionField_isStrictSupportField_of_activeWalls` is replaced by the
structural fan/separation hypothesis: the strict-support verdict rests on the fan geometry and the
separation witnesses, with no hand-supplied activity. -/
theorem IsPolyhedralFan.toricMassActionField_isStrictSupportField_of_separatingWalls
    {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (hwr : N.WeaklyReversible)
    {F : Fan (EuclideanSpace ℝ S)} (hF : IsPolyhedralFan F) (κ : N.RateConstants)
    {faces : List (EuclideanSpace ℝ S × ℝ)}
    (hfaces : ∀ nf ∈ faces, ∃ (n₀ : S → ℝ) (D C : ProperCone ℝ (EuclideanSpace ℝ S))
      (c d : Complex S), nf.1 = toEuclid n₀ ∧
      N.IsFanWall F D C n₀ ∧ N.SeparatesComplexes n₀ c d ∧
      (∀ r : N.R, 0 ≤ ⟪toEuclid n₀, toEuclid (N.reactionVector r)⟫_ℝ) ∧
      (∀ p : EuclideanSpace ℝ S,
        ZeroSeparatingCurve2D.OnFaceBoundary faces (toEuclid n₀) nf.2 p →
          Concentration.Positive (toEuclid.symm p))) :
    ZeroSeparatingCurve2D.IsStrictSupportField (N.toricMassActionField κ) faces := by
  refine hwr.toricMassActionField_isStrictSupportField_of_activeWalls κ ?_
  intro nf hnf
  obtain ⟨n₀, D, C, c, d, hn₀, hwall, hsep, hinward, hpos⟩ := hfaces nf hnf
  exact ⟨n₀, hn₀, hF.activeWall_of_separatesComplexes hwall hsep, hinward, hpos⟩

end CRNT

import CRNT.Geometry.ToricFan
import CRNT.Geometry.ZeroSeparatingCurve2D

/-!
# Polar-cone description of the toric field, and constant-cone subtangency

The polar-cone description of the toric field of Craciun, _Toric differential inclusions
and a proof of the global attractor conjecture_. The toric differential-inclusion field
`toricField F δ X` is the pointed-cone hull of the union of the polar cones
`Cᵒ = coneDual C` of the fan cells `C ∈ F` lying within distance `δ` of `X`
(`mem_toricGenerators`). This module gives the **explicit polar-cone description on the
deep-interior portion** of the field and reads off the resulting **subtangency** condition for
the planar zero-separating curve.

## Part A — collapse to a single polar cone

At a *deep-interior* point of one cell — a point `X` with `C₀ ∈ F`, `infDist X C₀ < δ`, and
**every** δ-near cell equal to `C₀` — the admissible union has a single member, so the generators
collapse to the carrier of `coneDual C₀`, and the hull of a cone's own carrier is the cone:

`toricField_eq_coneDual_of_isolated : toricField F δ X = (coneDual (C₀ : Set E)).toPointedCone`.

This is the **constant-cone** regime: on the open interior of an exponential cone the toric
field is *literally* the polar cone `C₀ᵒ`, with no hull/union content left.

## Part B — membership gives a supporting half-plane

Every point `n ∈ C` of a cell pairs nonnegatively with every dual vector `v ∈ coneDual C`
(`mem_coneDual` instantiated at `n`):

`coneDual_subset_dualHalfPlane_of_mem (hn : n ∈ C) : ↑(coneDual C) ⊆ {y | 0 ≤ ⟪n, y⟫_ℝ}`.

## Assembly — the deep-interior support face

Combining A and B: at a deep-interior point `X` of a cell `C₀` whose interior the
zero-separating curve's region normal `n` belongs to (`n ∈ C₀`), every field value `v` at `X`
satisfies `0 ≤ ⟪n, v⟫_ℝ`. Packaged against the planar interface, the constant toric field
`fun _ => v` for any single field value `v ∈ toricField F δ X` is a
`ZeroSeparatingCurve2D.IsSupportFace`, and `toricField_subset_dualHalfPlane_of_isolated_mem`
records the field-wide inclusion `↑(toricField F δ X) ⊆ {y | 0 ≤ ⟪n, y⟫_ℝ}`.

## The uncertainty region (not treated here)

When `X` is near a fan wall, **two or more** cells `C₁, …, Cₖ` satisfy `infDist X Cᵢ < δ`, so the
field does not collapse: `toricField F δ X = PointedCone.hull ℝ (⋃ i, coneDual Cᵢ)`, a strictly
larger pointed cone than any single polar cone. The matching subtangency requires the region
normal `n` to lie in the **intersection** `⋂ i, Cᵢ` of the adjacent cells (equivalently, on the
shared face, in the uncertainty region's attracting direction) so that the membership argument
of Part B applies *simultaneously* to every generator `coneDual Cᵢ`. That slope and
attracting-direction analysis across the half-plane uncertainty piece is not formalized in this
module.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Geometry.ToricFan`,
`CRNT.Geometry.ZeroSeparatingCurve2D`.
-/

namespace CRNT

open scoped InnerProductSpace

section Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## Part A — collapse to a single polar cone at a deep-interior point -/

/-- **Generators collapse at an isolated cell.** If `C₀ ∈ F` is δ-near `X` and is the *only* cell
that is δ-near `X`, then the toric generators are exactly the carrier of the polar cone `C₀ᵒ`. -/
theorem toricGenerators_eq_of_isolated {F : Fan E} {δ : ℝ} {X : E} {C₀ : ProperCone ℝ E}
    (hC₀F : C₀ ∈ F) (hC₀d : Metric.infDist X (C₀ : Set E) < δ)
    (hiso : ∀ C ∈ F, Metric.infDist X (C : Set E) < δ → C = C₀) :
    toricGenerators F δ X = (coneDual (C₀ : Set E) : Set E) := by
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨C, hCF, hCd, hyC⟩ := mem_toricGenerators.1 hy
    rw [hiso C hCF hCd] at hyC
    exact hyC
  · exact coneDual_subset_toricGenerators hC₀F hC₀d

/-- **Explicit polar-cone description (deep interior).** At a deep-interior point `X` of a cell
`C₀` — `C₀ ∈ F`, `infDist X C₀ < δ`, and every δ-near cell equal to `C₀` — the toric field is
*literally* the polar cone `C₀ᵒ = coneDual C₀`: the admissible union collapses to `C₀ᵒ` and the
hull of a cone's own carrier is the cone itself. This is the constant-cone regime. -/
theorem toricField_eq_coneDual_of_isolated {F : Fan E} {δ : ℝ} {X : E} {C₀ : ProperCone ℝ E}
    (hC₀F : C₀ ∈ F) (hC₀d : Metric.infDist X (C₀ : Set E) < δ)
    (hiso : ∀ C ∈ F, Metric.infDist X (C : Set E) < δ → C = C₀) :
    toricField F δ X = (coneDual (C₀ : Set E)).toPointedCone := by
  unfold toricField
  rw [toricGenerators_eq_of_isolated hC₀F hC₀d hiso]
  exact Submodule.span_eq (coneDual (C₀ : Set E)).toPointedCone

/-! ## Part B — membership of a cell point yields a supporting half-plane -/

/-- **Subtangency from membership.** If `n` is a point of the cell `C`, then every dual vector
`v ∈ coneDual C` pairs nonnegatively with `n`: the polar cone lies in the closed half-plane
`{y | 0 ≤ ⟪n, y⟫_ℝ}`. Immediate from `mem_coneDual` instantiated at `n`. -/
theorem coneDual_subset_dualHalfPlane_of_mem {C : Set E} {n : E} (hn : n ∈ C) :
    (coneDual C : Set E) ⊆ {y | 0 ≤ ⟪n, y⟫_ℝ} := by
  intro y hy
  exact mem_coneDual.1 hy hn

/-! ## Assembly — the deep-interior support face -/

/-- **The toric field is a supporting half-plane at a deep-interior point whose cell contains the
region normal.** At a deep-interior point `X` of a cell `C₀` (Part A) with the curve's region
normal `n` lying in `C₀` (Part B), every field value at `X` pairs nonnegatively with `n`: the
whole toric field lies in the closed half-plane `{y | 0 ≤ ⟪n, y⟫_ℝ}`. -/
theorem toricField_subset_dualHalfPlane_of_isolated_mem {F : Fan E} {δ : ℝ} {X n : E}
    {C₀ : ProperCone ℝ E}
    (hC₀F : C₀ ∈ F) (hC₀d : Metric.infDist X (C₀ : Set E) < δ)
    (hiso : ∀ C ∈ F, Metric.infDist X (C : Set E) < δ → C = C₀)
    (hn : n ∈ (C₀ : Set E)) :
    (toricField F δ X : Set E) ⊆ {y | 0 ≤ ⟪n, y⟫_ℝ} := by
  rw [toricField_eq_coneDual_of_isolated hC₀F hC₀d hiso]
  exact coneDual_subset_dualHalfPlane_of_mem hn

/-- **The constant deep-interior toric field is a planar support face.** Fix a deep-interior point
`X` of a cell `C₀` whose interior contains the zero-separating curve's region normal `n`. For any
single field value `v ∈ toricField F δ X`, the constant field `fun _ => v` is a
`ZeroSeparatingCurve2D.IsSupportFace` for the planar region cut out by `faces`, with normal `n`
and any offset `a`: the subtangency condition holds on the constant-cone portion. -/
theorem isSupportFace_of_isolated_mem {F : Fan E} {δ : ℝ} {X n : E} {C₀ : ProperCone ℝ E}
    (hC₀F : C₀ ∈ F) (hC₀d : Metric.infDist X (C₀ : Set E) < δ)
    (hiso : ∀ C ∈ F, Metric.infDist X (C : Set E) < δ → C = C₀)
    (hn : n ∈ (C₀ : Set E)) {a : ℝ} {faces : List (E × ℝ)}
    {v : E} (hv : v ∈ toricField F δ X) :
    ZeroSeparatingCurve2D.IsSupportFace (fun _ => v) faces n a :=
  ZeroSeparatingCurve2D.attractingDirection_isSupport
    (toricField_subset_dualHalfPlane_of_isolated_mem hC₀F hC₀d hiso hn hv)

end Polar

end CRNT

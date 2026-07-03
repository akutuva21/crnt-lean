import CRNT.Geometry.ToricFan
import CRNT.Geometry.ToricFieldPolar
import CRNT.Geometry.ZeroSeparatingCurve2D

/-!
# Multi-cell polar-cone subtangency for the toric field

The multi-cell case of the toric-field subtangency condition of Craciun, _Toric differential
inclusions and a proof of the global attractor conjecture_. `ToricFieldPolar` reads off the
subtangency condition on the **constant-cone** regime, where a single cell `C₀` is δ-near the
point `X` and the toric field collapses to one polar cone `C₀ᵒ`. This module extends that
reading to the **uncertainty region** near a fan wall, where several cells `C₁, …, Cₖ` are
simultaneously δ-near `X` and the field is the genuine hull
`PointedCone.hull ℝ (⋃ i, coneDual Cᵢ)` of more than one polar cone.

## The half-plane cone

For a normal `n`, the closed half-plane `{y | 0 ≤ ⟪n, y⟫_ℝ}` is itself a `PointedCone ℝ E`:
it is closed under addition (`inner_add_right`) and under nonnegative scaling
(`inner_smul_right`). `dualHalfPlaneCone n` packages it, with membership simp lemma `mem_dualHalfPlaneCone`.

## Subtangency from membership in every δ-near cell

Suppose the region normal `n` lies in **every** δ-near cell: `n ∈ C` for each `C ∈ F` with
`infDist X C < δ`. Each generator `y ∈ toricGenerators F δ X` lies in some `coneDual Cᵢ` with
`Cᵢ` δ-near, so `n ∈ Cᵢ` gives `0 ≤ ⟪n, y⟫_ℝ` (`coneDual_subset_dualHalfPlane_of_mem`). Hence the
generators lie in `dualHalfPlaneCone n`, and since the toric field is the *least* pointed cone
containing them (`Submodule.span_le`), the whole field lies in `{y | 0 ≤ ⟪n, y⟫_ℝ}`:

`toricField_subset_dualHalfPlane_of_mem_forall`.

This is the membership argument of `ToricFieldPolar` Part B applied *simultaneously* to every
generator, with no collapse to a single cell required: `n` need only lie in the intersection of
the δ-near cells.

## The uncertainty-region support face

Packaging against the planar interface, the constant toric field `fun _ => v` for any single
field value `v ∈ toricField F δ X` is a `ZeroSeparatingCurve2D.IsSupportFace` whenever the region
normal lies in every δ-near cell (`isSupportFace_of_mem_forall`), mirroring
`ToricFieldPolar.isSupportFace_of_isolated_mem` for the multi-cell regime.

Depends on: `CRNT.Geometry.ToricFan`,
`CRNT.Geometry.ToricFieldPolar`, `CRNT.Geometry.ZeroSeparatingCurve2D`.
-/

namespace CRNT

open scoped InnerProductSpace

section PolarMulti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## The closed half-plane as a pointed cone -/

/-- **The dual half-plane cone.** For a normal `n`, the closed half-plane
`{y | 0 ≤ ⟪n, y⟫_ℝ}` is a `PointedCone ℝ E`: it contains `0`, is closed under addition, and is
closed under nonnegative scaling. -/
def dualHalfPlaneCone (n : E) : PointedCone ℝ E where
  carrier := {y | 0 ≤ ⟪n, y⟫_ℝ}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rw [inner_add_right]; positivity
  zero_mem' := by simp only [Set.mem_setOf_eq, inner_zero_right, le_refl]
  smul_mem' := by
    intro c y hy
    simp only [Set.mem_setOf_eq] at *
    rw [← Nonneg.coe_smul c y, inner_smul_right]
    have := c.2
    positivity

omit [CompleteSpace E] in
@[simp] theorem mem_dualHalfPlaneCone {n y : E} :
    y ∈ dualHalfPlaneCone n ↔ 0 ≤ ⟪n, y⟫_ℝ := Iff.rfl

/-! ## Subtangency from membership in every δ-near cell -/

/-- **Uncertainty-region subtangency.** If the region normal `n` lies in **every** δ-near cell of
the fan — `n ∈ C` for each `C ∈ F` with `infDist X C < δ` — then every value of the toric field
at `X` pairs nonnegatively with `n`: the whole field lies in the closed half-plane
`{y | 0 ≤ ⟪n, y⟫_ℝ}`. Each generator lies in some δ-near `coneDual Cᵢ`, and `n ∈ Cᵢ` forces
`0 ≤ ⟪n, y⟫_ℝ`; the toric field is the least pointed cone over the generators, so the half-plane
cone — which contains every generator — contains it. -/
theorem toricField_subset_dualHalfPlane_of_mem_forall {F : Fan E} {δ : ℝ} {X n : E}
    (h : ∀ C ∈ F, Metric.infDist X (C : Set E) < δ → n ∈ (C : Set E)) :
    (toricField F δ X : Set E) ⊆ {y | 0 ≤ ⟪n, y⟫_ℝ} := by
  have hgen : toricGenerators F δ X ⊆ (dualHalfPlaneCone n : Set E) := by
    intro y hy
    obtain ⟨C, hCF, hCd, hyC⟩ := mem_toricGenerators.1 hy
    exact coneDual_subset_dualHalfPlane_of_mem (h C hCF hCd) hyC
  have hle : toricField F δ X ≤ dualHalfPlaneCone n :=
    (Submodule.span_le).2 hgen
  intro y hy
  exact hle hy

/-! ## Assembly — the uncertainty-region support face -/

/-- **The toric field is a planar support face at an uncertainty-region point whose every δ-near
cell contains the region normal.** When the zero-separating curve's region normal `n` lies in
every cell `C ∈ F` with `infDist X C < δ`, any single field value `v ∈ toricField F δ X` makes the
constant field `fun _ => v` a `ZeroSeparatingCurve2D.IsSupportFace` for the planar region cut out
by `faces`, with normal `n` and any offset `a`. This is the subtangency condition on the
multi-cell uncertainty regime, mirroring the constant-cone `isSupportFace_of_isolated_mem`. -/
theorem isSupportFace_of_mem_forall {F : Fan E} {δ : ℝ} {X n : E}
    (h : ∀ C ∈ F, Metric.infDist X (C : Set E) < δ → n ∈ (C : Set E))
    {a : ℝ} {faces : List (E × ℝ)} {v : E} (hv : v ∈ toricField F δ X) :
    ZeroSeparatingCurve2D.IsSupportFace (fun _ => v) faces n a :=
  ZeroSeparatingCurve2D.attractingDirection_isSupport
    (toricField_subset_dualHalfPlane_of_mem_forall h hv)

end PolarMulti

end CRNT

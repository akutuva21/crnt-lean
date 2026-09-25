import CRNT.Geometry.ZeroSeparatingInduction
import CRNT.Geometry.FaithfulCurve
import CRNT.Geometry.ConeFace

/-!
# Fan refinement and faithful transfer to a coarser fan

A ruled patch aligned simultaneously to several attracting directions has no surface normal once
those directions span the ambient space, which first occurs in dimension four
(`ZeroSeparatingInduction.over_determined_in_dim_four`). This over-determination is avoided by
*refining the fan*: subdivide each cell into finer cells, build the zero-separating surface for the
finer inclusion, and observe that for each coarse cell the surface's normals (away from the coarse
uncertainty regions) land in the coarse cell's attracting cone — so the finer surface is **faithful
for the coarse inclusion**. Refinement breaks each over-constrained patch into a sequence of patches
each crossing a single uncertainty region, keeping the per-patch constraint count below `finrank`
(the planar angular chaining, lifted to `n` dimensions).

This module provides the two engines of that transfer:

* the **faithful-transfer engine** — admissibility for a finer cell transfers to the containing coarse
  cell, so the finer surface's normals are admissible for the coarse fan; and

* the **feasibility restoration** — a refined patch carrying fewer than `finrank ℝ E` active
  attracting directions always admits a valid surface normal.

## Contents

* `Refines F' F` — the refinement relation: every cell of `F'` is contained (as a set) in some cell
  of `F`.

* `attractsToward_coarse_of_fine` — a normal admissible for a finer cell `C' ⊆ C` is admissible for
  the coarse cell `C` (`Faithful.AttractsToward` is monotone under cell containment).

* `coneDual_coarse_subset_halfPlane_of_fine_mem` — consequently the coarse cell's toric-field polar
  `coneDual C` lies in the normal's region-side half-plane `{y | 0 ≤ ⟪n, y⟫_ℝ}`: a fine-admissible
  normal makes the coarse field inward.

* `exists_coarse_cell_of_refines` — packaged over `Refines`: a normal admissible for a cell of the
  refinement is admissible for some cell of the coarse fan.

* `refined_patch_normal_exists` — a refined patch with fewer than `finrank ℝ E` attracting-direction
  constraints admits a nonzero orthogonal surface normal: refinement keeps each patch below the
  over-determination threshold.

## Scope

This module proves the refinement relation, the faithful-transfer of admissibility (and of field
inwardness) from fine to coarse cells, and the feasibility restoration. Not constructed here: the
explicit decomposition that produces the refined fan with each patch crossing a single uncertainty
region, and the analysis matching the per-patch attracting directions — the constructions these
engines consume.

Depends on: `CRNT.Geometry.ZeroSeparatingInduction`,
`CRNT.Geometry.FaithfulCurve`.
-/

namespace CRNT

namespace FanRefinement

open scoped InnerProductSpace
open CRNT.Faithful ZeroSeparatingInduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The refinement relation.** `F'` refines `F` when every cell of `F'` is contained, as a set, in
some cell of `F`: each coarse cell is subdivided into finer cells, so the finer fan resolves the
coarse one. -/
def Refines [CompleteSpace E] (F' F : Fan E) : Prop :=
  ∀ C' ∈ F', ∃ C ∈ F, (C' : Set E) ⊆ (C : Set E)

/-- The finite family of pairwise intersections of two cone families. Each cell lies in a cell
of either input family. This is only the cell data for a common refinement: proving exposed-face
closure is still necessary before it can be called a polyhedral fan. -/
noncomputable def intersectionFamily [CompleteSpace E] (F G : Fan E) : Fan E := by
  classical
  exact (F.product G).image (fun p : ProperCone ℝ E × ProperCone ℝ E => p.1 ⊓ p.2)

/-- Every cell in the pairwise intersection family is contained in a cell of the left family. -/
theorem intersectionFamily_refines_left [CompleteSpace E] {F G : Fan E} :
    Refines (intersectionFamily F G) F := by
  classical
  intro C' hC'
  rcases Finset.mem_image.mp hC' with ⟨⟨C, D⟩, hp, hEq⟩
  rcases Finset.mem_product.mp hp with ⟨hC, hD⟩
  subst C'
  exact ⟨C, hC, inf_le_left⟩

/-- Every cell in the pairwise intersection family is contained in a cell of the right family. -/
theorem intersectionFamily_refines_right [CompleteSpace E] {F G : Fan E} :
    Refines (intersectionFamily F G) G := by
  classical
  intro C' hC'
  rcases Finset.mem_image.mp hC' with ⟨⟨C, D⟩, hp, hEq⟩
  rcases Finset.mem_product.mp hp with ⟨hC, hD⟩
  subst C'
  exact ⟨D, hD, inf_le_right⟩

/-- Pairwise intersections of two polyhedral fans cover the ambient space. -/
theorem intersectionFamily_covers [CompleteSpace E] {F G : Fan E}
    (hF : IsPolyhedralFan F) (hG : IsPolyhedralFan G) :
    (⋃ C ∈ intersectionFamily F G, (C : Set E)) = Set.univ := by
  classical
  ext x
  constructor
  · intro _
    simp
  · intro _
    have hxF : ∃ C ∈ F, x ∈ (C : Set E) := by
      have hx := congrArg (fun s : Set E => x ∈ s) hF.covers
      simpa using hx
    have hxG : ∃ D ∈ G, x ∈ (D : Set E) := by
      have hx := congrArg (fun s : Set E => x ∈ s) hG.covers
      simpa using hx
    rcases hxF with ⟨C, hC, hxC⟩
    rcases hxG with ⟨D, hD, hxD⟩
    refine Set.mem_iUnion.mpr ⟨C ⊓ D, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨(C, D), Finset.mem_product.mpr ⟨hC, hD⟩, rfl⟩
    · simpa using And.intro hxC hxD

/-- The pairwise intersection family satisfies the common-intersection axiom when both inputs
do. Exposed-face closure, the remaining polyhedral-fan axiom, is not provided by these data. -/
theorem intersectionFamily_inter_common [CompleteSpace E] {F G : Fan E}
    (hF : IsPolyhedralFan F) (hG : IsPolyhedralFan G) :
    ∀ C ∈ intersectionFamily F G, ∀ D ∈ intersectionFamily F G,
      ∃ H ∈ intersectionFamily F G, (H : Set E) = (C : Set E) ∩ (D : Set E) := by
  classical
  intro C hC D hD
  rcases Finset.mem_image.mp hC with ⟨⟨C₁, D₁⟩, hpair₁, rfl⟩
  rcases Finset.mem_product.mp hpair₁ with ⟨hC₁, hD₁⟩
  rcases Finset.mem_image.mp hD with ⟨⟨C₂, D₂⟩, hpair₂, rfl⟩
  rcases Finset.mem_product.mp hpair₂ with ⟨hC₂, hD₂⟩
  obtain ⟨C₃, hC₃, hmeetC⟩ := hF.inter_common C₁ hC₁ C₂ hC₂
  obtain ⟨D₃, hD₃, hmeetD⟩ := hG.inter_common D₁ hD₁ D₂ hD₂
  refine ⟨C₃ ⊓ D₃, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    exact ⟨(C₃, D₃), Finset.mem_product.mpr ⟨hC₃, hD₃⟩, rfl⟩
  · ext x
    simp [hmeetC, hmeetD]
    tauto

/-- **Admissibility transfers from fine to coarse.** If a finer cell `C'` is contained in a coarse
cell `C` and the normal `n` attracts toward `C'` (`n ∈ C'`), then `n` attracts toward `C`: the
attracting-direction condition is monotone under cell containment. This is why a surface faithful for
the refined fan is faithful for the coarse fan — its normals, admissible for the finer cells, are
admissible for the containing coarse cells. -/
theorem attractsToward_coarse_of_fine {n : E} {C C' : ProperCone ℝ E}
    (hsub : (C' : Set E) ⊆ (C : Set E)) (h : AttractsToward n C') : AttractsToward n C :=
  hsub h

/-- **The coarse field is inward for a fine-admissible normal.** If `n ∈ C'` with the finer cell
`C'` contained in the coarse cell `C`, then the coarse cell's toric-field polar `coneDual C` lies in
the region-side half-plane `{y | 0 ≤ ⟪n, y⟫_ℝ}`. The fine-fan surface's normal makes the coarse toric
field point into the region — the support side of faithfulness transferred from fine to coarse. -/
theorem coneDual_coarse_subset_halfPlane_of_fine_mem [CompleteSpace E] {n : E} {C C' : ProperCone ℝ E}
    (hsub : (C' : Set E) ⊆ (C : Set E)) (h : n ∈ (C' : Set E)) :
    (coneDual (C : Set E) : Set E) ⊆ {y : E | 0 ≤ ⟪n, y⟫_ℝ} :=
  coneDual_subset_dualHalfPlane_of_mem (hsub h)

/-- **Admissibility for a refinement cell gives a coarse cell.** Packaged over `Refines`: if `n`
attracts toward a cell `C'` of the refinement `F'`, then `n` attracts toward some cell `C` of the
coarse fan `F`. The faithful-transfer at the fan level. -/
theorem exists_coarse_cell_of_refines [CompleteSpace E] {F' F : Fan E} (href : Refines F' F)
    {C' : ProperCone ℝ E} (hC' : C' ∈ F') {n : E} (h : AttractsToward n C') :
    ∃ C ∈ F, AttractsToward n C := by
  obtain ⟨C, hCF, hsub⟩ := href C' hC'
  exact ⟨C, hCF, attractsToward_coarse_of_fine hsub h⟩

/-- **Feasibility restoration by refinement.** A refined patch crossing fewer than `finrank ℝ E`
uncertainty regions carries fewer than `finrank ℝ E` attracting-direction constraints, so a nonzero
surface normal orthogonal to all of them exists. Refinement keeps every patch below this threshold —
each patch crossing a single uncertainty region — which is how it avoids the over-determination of
`over_determined_in_dim_four`. -/
theorem refined_patch_normal_exists [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (v : ι → E)
    (hcard : Fintype.card ι < Module.finrank ℝ E) :
    ∃ n : E, n ≠ 0 ∧ ∀ i, ⟪v i, n⟫_ℝ = 0 :=
  exists_orthogonal_normal_of_card_lt_finrank v hcard

end FanRefinement

end CRNT

import CRNT.Geometry.ZeroSeparatingInduction
import CRNT.Geometry.FaithfulCurve
import CRNT.Geometry.ConeFace
import CRNT.Geometry.FiniteConeClosed
import Mathlib.Geometry.Convex.Cone.DualFinite

/-!
# Fan refinement and faithful transfer to a coarser fan

A ruled patch aligned simultaneously to several attracting directions has no surface normal once
those directions span the ambient space, which first occurs in dimension four
(`ZeroSeparatingInduction.over_determined_in_dim_four`). Craciun's faithful blueprint controls which
fan cones constrain a normal at each smooth point. This module proves that admissibility transfers
from a supplied fine cell to a containing coarse cell, and that an explicitly supplied constraint
family of cardinality below `finrank` admits a nonzero orthogonal normal. It does not construct the
blueprint subdivision or prove that its local patches satisfy that cardinality bound.

This module provides the transfer and finite-refinement engines:

* the **faithful-transfer engine** — admissibility for a finer cell transfers to the containing coarse
  cell, so the finer surface's normals are admissible for the coarse fan; and

* the **finite common-refinement engine** — a finite list of supplied fans can be intersected
  successively, preserving the fan axioms and dual finite generation of every cell; and

* the **projection coverage step** — images of a complete fan cover the target of a surjective
  linear map, and images of finitely generated cells are exact finitely generated cones;

* the **conditional feasibility lemma** — a supplied patch with fewer than `finrank ℝ E` active
  attracting directions admits a valid surface normal.

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

* `exists_patch_normal_of_card_lt_finrank` — an explicitly indexed patch with fewer than
  `finrank ℝ E` attracting-direction constraints admits a nonzero orthogonal surface normal.

## Scope

This module proves the refinement relation, the faithful-transfer of admissibility (and of field
inwardness) from fine to coarse cells, finite common-refinement closure for supplied polyhedral fans
with dual-finitely-generated cells, and coverage of the closed-cone image family under a surjective
linear map. It also proves that images of finitely generated cells are exact. It does not prove that
an arbitrary projected image family is itself a fan or construct its fan-compatible subdivision.
The faithful blueprint, its patch decomposition, and the analysis matching per-patch attracting
directions remain separate constructions.

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

/-- The finite family of closed-cone images of a fan under a continuous linear map. Since the
proper-cone image operation takes closure, this family need not itself satisfy the fan axioms. -/
noncomputable def linearImageFamily {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (f : E →L[ℝ] F) [CompleteSpace E]
    (G : Fan E) : Fan F := by
  classical
  exact G.image (fun C => ProperCone.map f C)

/-- A surjective linear map sends the complete family of a covering fan to a family that covers
the target. This is the coverage part of projection; face-to-face intersection structure still
requires a separate refinement argument. -/
theorem linearImageFamily_covers_of_surjective {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] [CompleteSpace E]
    {G : Fan E} (hG : IsPolyhedralFan G) (f : E →L[ℝ] F)
    (hf : Function.Surjective f) :
    (⋃ C ∈ linearImageFamily f G, (C : Set F)) = Set.univ := by
  classical
  ext y
  constructor
  · intro _
    simp
  · intro _
    obtain ⟨x, rfl⟩ := hf y
    have hxcover : x ∈ ⋃ C ∈ G, (C : Set E) := by
      rw [hG.covers]
      simp
    rcases Set.mem_iUnion.mp hxcover with ⟨C, hC⟩
    rcases Set.mem_iUnion.mp hC with ⟨hCG, hxC⟩
    have hfxC : f x ∈ ProperCone.map f C := by
      rw [ProperCone.mem_map]
      change f x ∈ closure (f '' (C : Set E))
      exact subset_closure ⟨x, hxC, rfl⟩
    refine Set.mem_iUnion.mpr ⟨ProperCone.map f C, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, hfxC⟩
    change ProperCone.map f C ∈ G.image (fun C => ProperCone.map f C)
    exact Finset.mem_image.mpr ⟨C, hCG, rfl⟩

/-- The family of all final-coordinate deletions of a complete Euclidean coordinate fan covers the
lower coordinate space. This supplies the coverage clause before refining the projected cone family
into a fan. -/
theorem linearImageFamily_forgetLastEuclidean_covers {n : ℕ}
    (G : Fan (EuclideanSpace ℝ (Fin (n + 1)))) (hG : IsPolyhedralFan G) :
    (⋃ C ∈ linearImageFamily (forgetLastEuclidean n) G,
      (C : Set (EuclideanSpace ℝ (Fin n)))) = Set.univ :=
  linearImageFamily_covers_of_surjective hG _
    (forgetLastEuclidean_surjective n)

/-- The closed-cone image of a finite-generated cone equals the cone generated by the images of
its finite generators. In particular, the closure in `ProperCone.map` adds no extra points here. -/
theorem properCone_map_eq_finiteConeImage {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] [DecidableEq F]
    (f : E →L[ℝ] F) [CompleteSpace E] (S : Finset E) :
    ProperCone.map f (properConeOfFinset S) =
      properConeOfFinset (S.image (f : E →ₗ[ℝ] F)) := by
  classical
  apply ProperCone.ext
  intro y
  rw [ProperCone.mem_map]
  change y ∈ closure ((f : E →ₗ[ℝ] F) ''
    (properConeOfFinset S : Set E)) ↔
      y ∈ (properConeOfFinset (S.image (f : E →ₗ[ℝ] F)) : Set F)
  rw [linearMap_image_properConeOfFinset (f : E →ₗ[ℝ] F) S,
    (properConeOfFinset (S.image (f : E →ₗ[ℝ] F))).isClosed.closure_eq]

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


/-- Closed-cone version of a supporting hyperplane. -/
noncomputable def properSupportingHyperplane (a : E) : ProperCone ℝ E where
  toSubmodule := Submodule.restrictScalars (Nonneg ℝ) (LinearMap.ker (innerₗ E a))
  isClosed' := by
    change IsClosed {x : E | ⟪a, x⟫_ℝ = 0}
    exact isClosed_singleton.preimage (continuous_const.inner continuous_id)

@[simp] theorem mem_properSupportingHyperplane {a x : E} :
    x ∈ properSupportingHyperplane a ↔ ⟪a, x⟫_ℝ = 0 := by
  change x ∈ (LinearMap.ker (innerₗ E a) : Submodule ℝ E) ↔ _
  simp [LinearMap.mem_ker, innerₗ_apply_apply]

/-- A supporting hyperplane is the intersection of the two half-spaces with opposite normals,
so it has a finite half-space representation. -/
theorem properSupportingHyperplane_hasDualFG [CompleteSpace E] (a : E) :
    (properSupportingHyperplane a : PointedCone ℝ E).DualFG (innerₗ E) := by
  classical
  let S : Finset E := {a, -a}
  have hS : (coneDual (S : Set E) : PointedCone ℝ E).DualFG (innerₗ E) := by
    change (PointedCone.dual (innerₗ E) (S : Set E)).DualFG (innerₗ E)
    exact PointedCone.DualFG.dual_of_finset (innerₗ E) S
  have hEq : properSupportingHyperplane a = coneDual (S : Set E) := by
    apply ProperCone.ext
    intro x
    simp [S, mem_properSupportingHyperplane]
    constructor
    · intro hx
      rw [hx]
      exact ⟨le_rfl, le_rfl⟩
    · rintro ⟨hpos, hneg⟩
      exact le_antisymm hneg hpos
  rw [hEq]
  exact hS

/-- Exposed face represented as a closed cone, for use in the closed-cone fan family. -/
noncomputable def properExposedFace (C : ProperCone ℝ E) (a : E) : ProperCone ℝ E :=
  C ⊓ properSupportingHyperplane a

@[simp] theorem mem_properExposedFace {C : ProperCone ℝ E} {a x : E} :
    x ∈ properExposedFace C a ↔ x ∈ C ∧ ⟪a, x⟫_ℝ = 0 := by
  simp [properExposedFace]

/-- Taking an exposed face preserves finite half-space representability: it adds the two
inequalities for the exposing hyperplane to the existing finite description. -/
theorem properExposedFace_hasDualFG [CompleteSpace E] {C : ProperCone ℝ E} {a : E}
    (hC : (C : PointedCone ℝ E).DualFG (innerₗ E)) :
    (properExposedFace C a : PointedCone ℝ E).DualFG (innerₗ E) := by
  change ((C : PointedCone ℝ E) ⊓
    (properSupportingHyperplane a : PointedCone ℝ E)).DualFG (innerₗ E)
  exact hC.inf (properSupportingHyperplane_hasDualFG a)

/-- A closed exposed face belongs to its input fan. -/
theorem properExposedFace_isExposedFaceOf [CompleteSpace E] {C : ProperCone ℝ E} {a : E}
    (ha : a ∈ coneDual (C : Set E)) : IsExposedFaceOf (properExposedFace C a) C := by
  refine ⟨a, ha, ?_⟩
  ext x
  simp [properExposedFace, properSupportingHyperplane, mem_exposedFace,
    LinearMap.mem_ker, innerₗ_apply_apply]

/-- Dual decomposition condition needed to prove exposed-face closure for pairwise intersections. -/
def HasIntersectionDualDecomposition [CompleteSpace E] (F G : Fan E) : Prop :=
  ∀ C ∈ F, ∀ D ∈ G, ∀ a : E,
    a ∈ coneDual ((C : Set E) ∩ (D : Set E)) →
      ∃ b c : E, a = b + c ∧ b ∈ coneDual (C : Set E) ∧ c ∈ coneDual (D : Set E)

/-- If dual vectors of each cell intersection split between input dual cones, then the
pairwise-intersection family is closed under exposed faces. -/
theorem intersectionFamily_faces_mem [CompleteSpace E] {F G : Fan E}
    (hF : IsPolyhedralFan F) (hG : IsPolyhedralFan G)
    (hdual : HasIntersectionDualDecomposition F G) :
    ∀ C' ∈ intersectionFamily F G, ∀ H : ProperCone ℝ E,
      IsExposedFaceOf H C' → H ∈ intersectionFamily F G := by
  classical
  intro K hK H hHK
  rcases Finset.mem_image.mp hK with ⟨⟨C, D⟩, hpair, rfl⟩
  rcases Finset.mem_product.mp hpair with ⟨hC, hD⟩
  rcases hHK with ⟨a, ha, hset⟩
  have ha' : a ∈ coneDual ((C : Set E) ∩ (D : Set E)) := by
    rw [mem_coneDual]
    rw [mem_coneDual] at ha
    intro x hx
    have hx' : x ∈ (C ⊓ D : ProperCone ℝ E) := by simpa using hx
    exact ha hx'
  obtain ⟨b, c, hab, hb, hc⟩ := hdual C hC D hD a ha'
  let C' := properExposedFace C b
  let D' := properExposedFace D c
  have hC' : C' ∈ F := hF.faces_mem C hC C' (properExposedFace_isExposedFaceOf hb)
  have hD' : D' ∈ G := hG.faces_mem D hD D' (properExposedFace_isExposedFaceOf hc)
  have hcell : C' ⊓ D' ∈ intersectionFamily F G := by
    apply Finset.mem_image.mpr
    exact ⟨(C', D'), Finset.mem_product.mpr ⟨hC', hD'⟩, rfl⟩
  have hset' : ((H : PointedCone ℝ E) : Set E) =
      ((C' ⊓ D' : ProperCone ℝ E) : PointedCone ℝ E) := by
    rw [hset]
    ext x
    change ((x ∈ C ∧ x ∈ D) ∧ ⟪a, x⟫_ℝ = 0) ↔
      ((x ∈ C ∧ ⟪b, x⟫_ℝ = 0) ∧ x ∈ D ∧ ⟪c, x⟫_ℝ = 0)
    have hinner : ⟪a, x⟫_ℝ = ⟪b, x⟫_ℝ + ⟪c, x⟫_ℝ := by
      calc
        ⟪a, x⟫_ℝ = ⟪b + c, x⟫_ℝ := by rw [hab]
        _ = ⟪x, b + c⟫_ℝ := real_inner_comm _ _
        _ = ⟪x, b⟫_ℝ + ⟪x, c⟫_ℝ := inner_add_right (𝕜 := ℝ) x b c
        _ = ⟪b, x⟫_ℝ + ⟪c, x⟫_ℝ := by rw [real_inner_comm x b, real_inner_comm x c]
    constructor
    · rintro ⟨⟨hxC, hxD⟩, hzero⟩
      have hbn := inner_nonneg_of_mem_coneDual hb hxC
      have hcn := inner_nonneg_of_mem_coneDual hc hxD
      have hsum : ⟪b, x⟫_ℝ + ⟪c, x⟫_ℝ = 0 := by rw [← hinner, hzero]
      have hbzero : ⟪b, x⟫_ℝ = 0 := by nlinarith
      have hczero : ⟪c, x⟫_ℝ = 0 := by nlinarith
      exact ⟨⟨hxC, hbzero⟩, hxD, hczero⟩
    · rintro ⟨⟨hxC, hbzero⟩, hxD, hczero⟩
      refine ⟨⟨hxC, hxD⟩, ?_⟩
      rw [hinner, hbzero, hczero]
      ring
  have hpc : (H : PointedCone ℝ E) =
      (C' ⊓ D' : ProperCone ℝ E) := SetLike.coe_injective hset'
  have hcone : H = C' ⊓ D' := ProperCone.toPointedCone_injective hpc
  rw [hcone]
  exact hcell

/-- Pairwise intersections form a polyhedral fan once the dual-decomposition condition holds. -/
theorem intersectionFamily_isPolyhedralFan [CompleteSpace E] {F G : Fan E}
    (hF : IsPolyhedralFan F) (hG : IsPolyhedralFan G)
    (hdual : HasIntersectionDualDecomposition F G) :
    IsPolyhedralFan (intersectionFamily F G) :=
  ⟨intersectionFamily_faces_mem hF hG hdual,
    intersectionFamily_inter_common hF hG,
    intersectionFamily_covers hF hG⟩


/-- The dual of a finitely generated cone is the dual of its generators. -/
theorem coneDual_hull_eq [CompleteSpace E] (T : Finset E) :
    (coneDual (PointedCone.hull ℝ (T : Set E) : Set E) : Set E) =
      (PointedCone.dual (innerₗ E) (T : Set E) : Set E) := by
  ext x
  change x ∈ coneDual (PointedCone.hull ℝ (T : Set E) : Set E) ↔
    x ∈ PointedCone.dual (innerₗ E) (T : Set E)
  rw [mem_coneDual]
  change (∀ ⦃y⦄, y ∈ PointedCone.hull ℝ (T : Set E) → 0 ≤ ⟪y, x⟫_ℝ) ↔
    x ∈ PointedCone.dual (innerₗ E) (T : Set E)
  rw [PointedCone.mem_dual]
  constructor
  · intro h y hy
    exact h (PointedCone.subset_hull hy)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h hy
    | zero => simp
    | add y z _ _ hy hz =>
        rw [inner_add_left (𝕜 := ℝ)]
        exact add_nonneg hy hz
    | smul c y _ hy =>
        rw [← Nonneg.coe_smul, real_inner_smul_left]
        exact mul_nonneg c.2 hy

/-- The dual of the finite half-space cone with normals `S` is exactly the conical hull of those
normals. This finite Farkas representation is the face-closure input for hyperplane arrangements. -/
theorem coneDual_finset_dual_eq [CompleteSpace E] (S : Finset E) :
    coneDual (coneDual (S : Set E) : Set E) = properConeOfFinset S := by
  have hHull : (properConeOfFinset S : Set E) =
      (PointedCone.hull ℝ (S : Set E) : Set E) := by
    simp [coe_properConeOfFinset]
  have hDualSet : (coneDual (properConeOfFinset S : Set E) : Set E) =
      (PointedCone.dual (innerₗ E) (S : Set E) : Set E) := by
    rw [hHull]
    exact coneDual_hull_eq S
  have hDual : coneDual (properConeOfFinset S : Set E) = coneDual (S : Set E) := by
    apply ProperCone.ext
    intro x
    change x ∈ (coneDual (properConeOfFinset S : Set E) : Set E) ↔
      x ∈ (coneDual (S : Set E) : Set E)
    rw [hDualSet]
    rfl
  rw [← hDual]
  exact cone_dual_dual (properConeOfFinset S)

/-- For dual-finitely-generated cones, every dual vector of an intersection splits as a sum
of dual vectors of the two cones. -/
theorem coneDual_intersection_decomp_of_dualFG [CompleteSpace E] {C D : ProperCone ℝ E}
    (hCfin : (C : PointedCone ℝ E).DualFG (innerₗ E))
    (hDfin : (D : PointedCone ℝ E).DualFG (innerₗ E))
    {a : E} (ha : a ∈ coneDual ((C : Set E) ∩ (D : Set E))) :
    ∃ b c : E, a = b + c ∧ b ∈ coneDual (C : Set E) ∧ c ∈ coneDual (D : Set E) := by
  classical
  obtain ⟨S, hCfin⟩ := hCfin
  obtain ⟨T, hDfin⟩ := hDfin
  let A : ProperCone ℝ E := properConeOfFinset S
  let B : ProperCone ℝ E := properConeOfFinset T
  let U : ProperCone ℝ E := properConeOfFinset (S ∪ T)
  have hAco : (A : Set E) = (PointedCone.hull ℝ (S : Set E) : Set E) := by
    simpa [A] using coe_properConeOfFinset S
  have hBco : (B : Set E) = (PointedCone.hull ℝ (T : Set E) : Set E) := by
    simpa [B] using coe_properConeOfFinset T
  have hUco : (U : Set E) = (PointedCone.hull ℝ (S ∪ T : Set E) : Set E) := by
    simpa [U] using coe_properConeOfFinset (S ∪ T)
  have hAdualSet : (coneDual (A : Set E) : Set E) =
      (PointedCone.dual (innerₗ E) (S : Set E) : Set E) := by
    rw [hAco]
    exact coneDual_hull_eq S
  have hBdualSet : (coneDual (B : Set E) : Set E) =
      (PointedCone.dual (innerₗ E) (T : Set E) : Set E) := by
    rw [hBco]
    exact coneDual_hull_eq T
  have hUdualSet : (coneDual (U : Set E) : Set E) =
      (PointedCone.dual (innerₗ E) ((S ∪ T : Finset E) : Set E) : Set E) := by
    rw [hUco]
    simpa only [Finset.coe_union] using coneDual_hull_eq (S ∪ T)
  have hAdual : (coneDual (A : Set E) : PointedCone ℝ E) =
      PointedCone.dual (innerₗ E) (S : Set E) := SetLike.coe_injective hAdualSet
  have hBdual : (coneDual (B : Set E) : PointedCone ℝ E) =
      PointedCone.dual (innerₗ E) (T : Set E) := SetLike.coe_injective hBdualSet
  have hUdual : (coneDual (U : Set E) : PointedCone ℝ E) =
      PointedCone.dual (innerₗ E) ((S ∪ T : Finset E) : Set E) := SetLike.coe_injective hUdualSet
  have hCset : (C : Set E) = (coneDual (A : Set E) : Set E) := by
    ext x
    change x ∈ (C : PointedCone ℝ E) ↔
      x ∈ (coneDual (A : Set E) : PointedCone ℝ E)
    rw [← hCfin, hAdual]
  have hDset : (D : Set E) = (coneDual (B : Set E) : Set E) := by
    ext x
    change x ∈ (D : PointedCone ℝ E) ↔
      x ∈ (coneDual (B : Set E) : PointedCone ℝ E)
    rw [← hDfin, hBdual]
  have hCdualSet : (coneDual (C : Set E) : Set E) = (A : Set E) := by
    calc
      (coneDual (C : Set E) : Set E) =
          (coneDual (coneDual (A : Set E) : Set E) : Set E) := by rw [hCset]
      _ = (A : Set E) := congrArg (fun K : ProperCone ℝ E => (K : Set E)) (cone_dual_dual A)
  have hDdualSet : (coneDual (D : Set E) : Set E) = (B : Set E) := by
    calc
      (coneDual (D : Set E) : Set E) =
          (coneDual (coneDual (B : Set E) : Set E) : Set E) := by rw [hDset]
      _ = (B : Set E) := congrArg (fun K : ProperCone ℝ E => (K : Set E)) (cone_dual_dual B)
  have hKset : (C : Set E) ∩ (D : Set E) = (coneDual (U : Set E) : Set E) := by
    ext x
    rw [hCset, hDset, hAdualSet, hBdualSet, hUdualSet]
    change (x ∈ PointedCone.dual (innerₗ E) (S : Set E) ∧
      x ∈ PointedCone.dual (innerₗ E) (T : Set E)) ↔
      x ∈ PointedCone.dual (innerₗ E) ((S ∪ T : Finset E) : Set E)
    rw [show ((S ∪ T : Finset E) : Set E) = (S : Set E) ∪ (T : Set E) by simp]
    rw [PointedCone.dual_union]
    simp
  have hKinf : (C ⊓ D : ProperCone ℝ E) = coneDual (U : Set E) := by
    apply ProperCone.ext
    intro x
    have hmem : x ∈ (C ⊓ D : ProperCone ℝ E) ↔ x ∈ coneDual (U : Set E) := by
      change (x ∈ (C : Set E) ∧ x ∈ (D : Set E)) ↔
        x ∈ (coneDual (U : Set E) : Set E)
      exact Iff.of_eq (congrArg (fun s : Set E => x ∈ s) hKset)
    exact hmem
  have hKdual : (coneDual ((C : Set E) ∩ (D : Set E)) : Set E) = (U : Set E) := by
    have hInfSet : (C ⊓ D : ProperCone ℝ E) = (C : Set E) ∩ (D : Set E) := by
      ext x
      simp
    rw [← hInfSet, hKinf]
    exact congrArg (fun K : ProperCone ℝ E => (K : Set E)) (cone_dual_dual U)
  have haU : a ∈ (U : Set E) := by
    rw [← hKdual]
    exact ha
  have hUsup : (U : PointedCone ℝ E) =
      (A : PointedCone ℝ E) ⊔ (B : PointedCone ℝ E) := by
    apply PointedCone.ext
    intro x
    change x ∈ Submodule.span (Nonneg ℝ) ((S ∪ T : Finset E) : Set E) ↔
      x ∈ Submodule.span (Nonneg ℝ) (S : Set E) ⊔
        Submodule.span (Nonneg ℝ) (T : Set E)
    rw [Finset.coe_union, Submodule.span_union]
  have haSup : a ∈ (A : PointedCone ℝ E) ⊔ (B : PointedCone ℝ E) := by
    change a ∈ (U : PointedCone ℝ E) at haU
    rw [hUsup] at haU
    exact haU
  rcases Submodule.mem_sup.mp haSup with ⟨b, hbA, c, hcB, hbc⟩
  have hb : b ∈ coneDual (C : Set E) := by
    exact (Iff.of_eq (congrArg (fun s : Set E => b ∈ s) hCdualSet)).mpr hbA
  have hc : c ∈ coneDual (D : Set E) := by
    exact (Iff.of_eq (congrArg (fun s : Set E => c ∈ s) hDdualSet)).mpr hcB
  exact ⟨b, c, hbc.symm, hb, hc⟩

/-- Every cell of a fan is dual-finitely-generated. -/
def HasDualFGCells [CompleteSpace E] (F : Fan E) : Prop :=
  ∀ C ∈ F, (C : PointedCone ℝ E).DualFG (innerₗ E)

/-- The signed half-space normals describing one cell of a central hyperplane arrangement.
Normals in `P` impose nonnegative inner products, normals in `N` impose nonpositive inner
products, and normals in neither set occur with both signs and impose equality. -/
noncomputable def signCellNormals [DecidableEq E] (T P N : Finset E) : Finset E := by
  classical
  exact (P ∪ N.image (fun a => -a)) ∪
    ((T \ (P ∪ N)) ∪ (T \ (P ∪ N)).image (fun a => -a))

/-- A closed cone cut out by the sign constraints for a finite family of central hyperplanes. -/
noncomputable def signCell [CompleteSpace E] [DecidableEq E]
    (T P N : Finset E) : ProperCone ℝ E := by
  classical
  exact coneDual (signCellNormals T P N : Set E)

/-- Membership in a signed arrangement cell is exactly its intended weak sign/equality pattern. -/
theorem mem_signCell [CompleteSpace E] [DecidableEq E] {T P N : Finset E} {x : E} :
    x ∈ signCell T P N ↔
      (∀ a ∈ P, 0 ≤ ⟪a, x⟫_ℝ) ∧
      (∀ a ∈ N, 0 ≤ ⟪-a, x⟫_ℝ) ∧
      (∀ a ∈ T \ (P ∪ N), ⟪a, x⟫_ℝ = 0) := by
  classical
  simp [signCell, signCellNormals, mem_coneDual]
  constructor
  · intro h
    have hfull : ∀ y : E,
        (y ∈ P ∨ -y ∈ N ∨
          (y ∈ T ∧ y ∉ P ∧ y ∉ N) ∨ (-y ∈ T ∧ -y ∉ P ∧ -y ∉ N)) →
        0 ≤ ⟪y, x⟫_ℝ := by
      intro y hy
      exact h hy
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      exact hfull a (Or.inl ha)
    · intro a ha
      simpa [inner_neg_left] using hfull (-a) (Or.inr (Or.inl (by simpa using ha)))
    · intro a ha hPa hNa
      have hp := hfull a (Or.inr (Or.inr (Or.inl ⟨ha, hPa, hNa⟩)))
      have hn := hfull (-a) (Or.inr (Or.inr (Or.inr (by simpa using ⟨ha, hPa, hNa⟩))))
      have hn' : ⟪a, x⟫_ℝ ≤ 0 := by simpa [inner_neg_left] using hn
      nlinarith
  · rintro ⟨hP, hN, hZ⟩
    intro y hy
    rcases hy with hyP | hyN | hyZ | hyZneg
    · exact hP y hyP
    · simpa [inner_neg_left] using hN (-y) (by simpa using hyN)
    · rcases hyZ with ⟨hyT, hyP, hyN⟩
      have hzero := hZ y hyT hyP hyN
      rw [hzero]
    · rcases hyZneg with ⟨hyT, hyP, hyN⟩
      have hzero := hZ (-y) hyT hyP hyN
      have : ⟪y, x⟫_ℝ = 0 := by simpa using hzero
      rw [this]

/-- The finite central hyperplane arrangement family consists of every disjoint choice of
nonnegative and nonpositive normals, with all remaining normals imposing equality. -/
noncomputable def hyperplaneArrangementFamily [CompleteSpace E] [DecidableEq E]
    (T : Finset E) : Fan E := by
  classical
  exact ((T.powerset.product T.powerset).filter (fun p => Disjoint p.1 p.2)).image
    (fun p => signCell T p.1 p.2)

/-- The sign cells of a finite central hyperplane arrangement cover the ambient space. -/
theorem hyperplaneArrangementFamily_covers [CompleteSpace E] [DecidableEq E]
    (T : Finset E) :
    (⋃ C ∈ hyperplaneArrangementFamily T, (C : Set E)) = Set.univ := by
  classical
  ext x
  constructor
  · intro _
    simp
  · intro _
    let P := T.filter (fun a => 0 ≤ ⟪a, x⟫_ℝ)
    let N := T.filter (fun a => ⟪a, x⟫_ℝ < 0)
    have hPsub : P ⊆ T := Finset.filter_subset _ _
    have hNsub : N ⊆ T := Finset.filter_subset _ _
    have hdis : Disjoint P N := by
      rw [Finset.disjoint_left]
      intro a haP haN
      simp only [P, N, Finset.mem_filter] at haP haN
      linarith
    have hpair : (P, N) ∈
        ((T.powerset.product T.powerset).filter (fun p => Disjoint p.1 p.2)) := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mk_mem_product
          (Finset.mem_powerset.mpr hPsub) (Finset.mem_powerset.mpr hNsub)
      · exact hdis
    have hP : ∀ a ∈ P, 0 ≤ ⟪a, x⟫_ℝ := by
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    have hN : ∀ a ∈ N, 0 ≤ ⟪-a, x⟫_ℝ := by
      intro a ha
      have hneg : ⟪a, x⟫_ℝ < 0 := (Finset.mem_filter.mp ha).2
      rw [inner_neg_left]
      linarith
    have hZ : ∀ a ∈ T \ (P ∪ N), ⟪a, x⟫_ℝ = 0 := by
      intro a ha
      have haT : a ∈ T := (Finset.mem_sdiff.mp ha).1
      have hNotUnion : a ∉ P ∪ N := (Finset.mem_sdiff.mp ha).2
      have haP : a ∉ P := by
        intro h
        exact hNotUnion (Finset.mem_union.mpr (Or.inl h))
      have haN : a ∉ N := by
        intro h
        exact hNotUnion (Finset.mem_union.mpr (Or.inr h))
      have hnotPos : ¬ 0 ≤ ⟪a, x⟫_ℝ := by
        intro h
        exact haP (Finset.mem_filter.mpr ⟨haT, h⟩)
      have hnotNeg : ¬ ⟪a, x⟫_ℝ < 0 := by
        intro h
        exact haN (Finset.mem_filter.mpr ⟨haT, h⟩)
      linarith
    have hcell : x ∈ signCell T P N := mem_signCell.mpr ⟨hP, hN, hZ⟩
    have hfamily : signCell T P N ∈ hyperplaneArrangementFamily T := by
      apply Finset.mem_image.mpr
      exact ⟨(P, N), hpair, rfl⟩
    refine Set.mem_iUnion.mpr ⟨signCell T P N, ?_⟩
    exact Set.mem_iUnion.mpr ⟨hfamily, hcell⟩

/-- Negating a cone preserves dual finite generation: negate the finite set of half-space normals. -/
theorem negatedProperCone_hasDualFG [CompleteSpace E] (C : ProperCone ℝ E)
    (hC : (C : PointedCone ℝ E).DualFG (innerₗ E)) :
    (CRNT.negatedProperCone C : PointedCone ℝ E).DualFG (innerₗ E) := by
  classical
  obtain ⟨s, hs⟩ := hC
  refine ⟨s.image (fun v : E => -v), ?_⟩
  have himage : (s.image (fun v : E => -v) : Set E) = -(s : Set E) := by
    ext x
    simp
  rw [himage, PointedCone.dual_neg, hs]
  apply PointedCone.ext
  intro x
  simp [CRNT.negatedProperCone]

/-- Negating every cell of a fan preserves dual finite generation cellwise. -/
theorem negatedFan_hasDualFGCells [CompleteSpace E] (F : Fan E)
    (hF : HasDualFGCells F) : HasDualFGCells (CRNT.negatedFan F) := by
  classical
  intro C hC
  rw [CRNT.negatedFan, Finset.mem_image] at hC
  rcases hC with ⟨D, hD, rfl⟩
  exact negatedProperCone_hasDualFG D (hF D hD)

/-- Dual-finitely-generated cells provide the decomposition used for exposed-face closure. -/
theorem intersectionFamily_dualDecomposition [CompleteSpace E] {F G : Fan E}
    (hF : HasDualFGCells F) (hG : HasDualFGCells G) :
    HasIntersectionDualDecomposition F G := by
  intro C hC D hD a ha
  exact coneDual_intersection_decomp_of_dualFG (hF C hC) (hG D hD) ha

/-- The pairwise-intersection family is a polyhedral fan when both input fans have
dual-finitely-generated cells. -/
theorem intersectionFamily_isPolyhedralFan_of_dualFG [CompleteSpace E] {F G : Fan E}
    (hF : IsPolyhedralFan F) (hG : IsPolyhedralFan G)
    (hFdual : HasDualFGCells F) (hGdual : HasDualFGCells G) :
    IsPolyhedralFan (intersectionFamily F G) :=
  intersectionFamily_isPolyhedralFan hF hG (intersectionFamily_dualDecomposition hFdual hGdual)

/-- Pairwise intersections preserve dual finite generation of fan cells. This lets an iterated
common refinement keep the finite-inequality representation needed for the next exposed-face step. -/
theorem intersectionFamily_hasDualFGCells [CompleteSpace E] {F G : Fan E}
    (hFdual : HasDualFGCells F) (hGdual : HasDualFGCells G) :
    HasDualFGCells (intersectionFamily F G) := by
  classical
  intro K hK
  rcases Finset.mem_image.mp hK with ⟨⟨C, D⟩, hpair, rfl⟩
  rcases Finset.mem_product.mp hpair with ⟨hC, hD⟩
  exact PointedCone.DualFG.inf (hFdual C hC) (hGdual D hD)

/-- Iteratively intersect a finite list of fans with a starting fan. -/
noncomputable def iteratedIntersectionFamily [CompleteSpace E] (F : Fan E) : List (Fan E) → Fan E
  | [] => F
  | G :: rest => iteratedIntersectionFamily (intersectionFamily F G) rest

theorem refines_refl [CompleteSpace E] (F : Fan E) : Refines F F := by
  intro C hC
  exact ⟨C, hC, Set.Subset.rfl⟩

/-- Refinement is transitive: a cell contained in a fine cell is contained in its coarse cell. -/
theorem refines_trans [CompleteSpace E] {F G H : Fan E}
    (hFG : Refines F G) (hGH : Refines G H) : Refines F H := by
  intro C hC
  obtain ⟨D, hD, hsub₁⟩ := hFG C hC
  obtain ⟨K, hK, hsub₂⟩ := hGH D hD
  exact ⟨K, hK, hsub₁.trans hsub₂⟩

/-- The iterated intersection family refines its starting fan. -/
theorem iteratedIntersectionFamily_refines_base [CompleteSpace E]
    (F : Fan E) (Gs : List (Fan E)) :
    Refines (iteratedIntersectionFamily F Gs) F := by
  induction Gs generalizing F with
  | nil => exact refines_refl F
  | cons G Gs ih =>
      exact refines_trans (ih (intersectionFamily F G)) intersectionFamily_refines_left

/-- Every fan added to an iterated intersection family is also refined by the result. -/
theorem iteratedIntersectionFamily_refines_member [CompleteSpace E]
    (F : Fan E) (Gs : List (Fan E)) {G : Fan E} (hG : G ∈ Gs) :
    Refines (iteratedIntersectionFamily F Gs) G := by
  induction Gs generalizing F with
  | nil => simp at hG
  | cons H Gs ih =>
      rcases List.mem_cons.mp hG with hEq | hTail
      · subst G
        exact refines_trans
          (iteratedIntersectionFamily_refines_base (intersectionFamily F H) Gs)
          intersectionFamily_refines_right
      · exact ih (intersectionFamily F H) hTail

/-- If every input fan is a polyhedral fan with dual-finitely-generated cells, iterated pairwise
intersections form a polyhedral common refinement and retain dual finite generation cellwise. -/
theorem iteratedIntersectionFamily_isPolyhedralFan [CompleteSpace E]
    (F : Fan E) (Gs : List (Fan E))
    (hF : IsPolyhedralFan F) (hFdual : HasDualFGCells F)
    (hG : ∀ G ∈ Gs, IsPolyhedralFan G)
    (hGdual : ∀ G ∈ Gs, HasDualFGCells G) :
    IsPolyhedralFan (iteratedIntersectionFamily F Gs) ∧
      HasDualFGCells (iteratedIntersectionFamily F Gs) := by
  have hAux : ∀ (xs : List (Fan E)) (F : Fan E),
      IsPolyhedralFan F → HasDualFGCells F →
      (∀ G ∈ xs, IsPolyhedralFan G) → (∀ G ∈ xs, HasDualFGCells G) →
      IsPolyhedralFan (iteratedIntersectionFamily F xs) ∧
        HasDualFGCells (iteratedIntersectionFamily F xs) := by
    intro xs
    induction xs with
    | nil =>
        intro F hF hFdual _ _
        exact ⟨hF, hFdual⟩
    | cons G Gs ih =>
        intro F hF hFdual hGs hGsdual
        have hHead : IsPolyhedralFan (intersectionFamily F G) :=
          intersectionFamily_isPolyhedralFan_of_dualFG hF (hGs G (by simp)) hFdual
            (hGsdual G (by simp))
        have hHeadDual : HasDualFGCells (intersectionFamily F G) :=
          intersectionFamily_hasDualFGCells hFdual (hGsdual G (by simp))
        exact ih (intersectionFamily F G) hHead hHeadDual
          (fun H hH => hGs H (by simp [hH]))
          (fun H hH => hGsdual H (by simp [hH]))
  exact hAux Gs F hF hFdual hG hGdual

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

/-- **Conditional normal feasibility.** Given an explicitly indexed family of fewer than
`finrank ℝ E` attracting-direction constraints for a patch, a nonzero surface normal orthogonal to
all of them exists. The general-dimensional construction must still prove that its local patches
have such a constraint family. -/
theorem exists_patch_normal_of_card_lt_finrank [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (v : ι → E)
    (hcard : Fintype.card ι < Module.finrank ℝ E) :
    ∃ n : E, n ≠ 0 ∧ ∀ i, ⟪v i, n⟫_ℝ = 0 :=
  exists_orthogonal_normal_of_card_lt_finrank v hcard

end FanRefinement

end CRNT

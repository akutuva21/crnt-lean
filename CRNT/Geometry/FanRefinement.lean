import CRNT.Geometry.ZeroSeparatingInduction
import CRNT.Geometry.FaithfulCurve
import CRNT.Geometry.ConeFace
import CRNT.Geometry.FiniteConeClosed
import Mathlib.Geometry.Convex.Cone.DualFinite
import Mathlib.Analysis.InnerProductSpace.Adjoint

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

* the **one-dimensional projection step** — a finite half-space description remains finite under
  projection when each fiber is a translate of a single kernel direction and a linear section is
  supplied;

* the **conditional feasibility lemma** — a supplied patch with fewer than `finrank ℝ E` active
  attracting directions admits a valid surface normal.

* the **central-arrangement fan engine** — the family of all weak sign/equality cells for a finite
  set of hyperplane normals is a complete polyhedral fan, with exposed-face closure from finite
  Farkas decomposition; and

* the **conditional arrangement-refinement engine** — for any supplied covering polyhedral fan
  whose cells have finite dual representations, the arrangement of the union of those normals
  refines the fan;

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
linear map. It also proves that split projections with a one-dimensional kernel preserve finite
dual representations, that a finite central hyperplane arrangement gives a polyhedral fan covering
the ambient space, and that its arrangement refines any supplied covering cone family with
dual-finitely-generated cells. In particular, the arrangement refines the projected image family of
a complete polyhedral fan under such a projection, yielding a complete polyhedral fan refinement
with dual-finitely-generated cells; this does not establish that the image family itself is a fan. The
faithful blueprint, its patch decomposition, and the analysis matching per-patch attracting
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

theorem exists_scalar_for_finite_linear_inequalities
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (a b : ι → ℝ)
    (hzero : ∀ i ∈ S, b i = 0 → 0 ≤ a i)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, 0 < b i → b j < 0 →
      0 ≤ b i * a j - b j * a i) :
    ∃ t : ℝ, ∀ i ∈ S, 0 ≤ a i + b i * t := by
  classical
  let Pos := S.filter (fun i => 0 < b i)
  let Neg := S.filter (fun i => b i < 0)
  let lower (i : ι) := -a i / b i
  let upper (i : ι) := a i / (-b i)
  by_cases hPos : Pos.Nonempty
  · let lowers := Pos.image lower
    have hLowers : lowers.Nonempty := Finset.image_nonempty.mpr hPos
    let t := lowers.max' hLowers
    refine ⟨t, ?_⟩
    intro i hi
    by_cases hbi : 0 < b i
    · have hiPos : i ∈ Pos := Finset.mem_filter.mpr ⟨hi, hbi⟩
      have hlow : lower i ≤ t := by
        exact Finset.le_max' lowers (lower i) (Finset.mem_image.mpr ⟨i, hiPos, rfl⟩)
      have hmul := (div_le_iff₀ hbi).mp hlow
      linarith
    · by_cases hneg : b i < 0
      · have hiNeg : i ∈ Neg := Finset.mem_filter.mpr ⟨hi, hneg⟩
        have hupper : t ≤ upper i := by
          apply (Finset.max'_le_iff lowers hLowers).2
          intro j hj
          rcases Finset.mem_image.mp hj with ⟨j, hjPos, rfl⟩
          have hjmem : j ∈ S := (Finset.mem_filter.mp hjPos).1
          have hjpos : 0 < b j := (Finset.mem_filter.mp hjPos).2
          have hpair' := hpair j hjmem i hi hjpos hneg
          have hbi' : 0 < -b i := neg_pos.mpr hneg
          have hratio : lower j ≤ upper i := by
            apply (div_le_div_iff₀ hjpos hbi').2
            nlinarith
          exact hratio
        have hmul := (le_div_iff₀ (neg_pos.mpr hneg)).mp hupper
        linarith
      · have hbi0 : b i = 0 := le_antisymm (le_of_not_gt hbi) (le_of_not_gt hneg)
        have ha := hzero i hi hbi0
        simpa [hbi0] using ha
  · by_cases hNeg : Neg.Nonempty
    · let uppers := Neg.image upper
      have hUppers : uppers.Nonempty := Finset.image_nonempty.mpr hNeg
      let t := uppers.min' hUppers
      refine ⟨t, ?_⟩
      intro i hi
      by_cases hbi : 0 < b i
      · exact (False.elim (hPos <| ⟨i, Finset.mem_filter.mpr ⟨hi, hbi⟩⟩))
      · by_cases hneg : b i < 0
        · have hiNeg : i ∈ Neg := Finset.mem_filter.mpr ⟨hi, hneg⟩
          have hupper : t ≤ upper i :=
            Finset.min'_le uppers (upper i) (Finset.mem_image.mpr ⟨i, hiNeg, rfl⟩)
          have hmul := (le_div_iff₀ (neg_pos.mpr hneg)).mp hupper
          linarith
        · have hbi0 : b i = 0 := le_antisymm (le_of_not_gt hbi) (le_of_not_gt hneg)
          have ha := hzero i hi hbi0
          simpa [hbi0] using ha
    · refine ⟨0, ?_⟩
      intro i hi
      have hnotPos : ¬ 0 < b i := fun h => hPos ⟨i, Finset.mem_filter.mpr ⟨hi, h⟩⟩
      have hnotNeg : ¬ b i < 0 := fun h => hNeg ⟨i, Finset.mem_filter.mpr ⟨hi, h⟩⟩
      have hbi0 : b i = 0 := le_antisymm (le_of_not_gt hnotPos) (le_of_not_gt hnotNeg)
      simpa [hbi0] using hzero i hi hbi0



/-- A projection of a finitely described closed cone still has a finite half-space description when
each fiber is a translate of the supplied kernel direction. The proof is Fourier--Motzkin
elimination along that direction. -/
theorem properCone_map_dualFG_of_dualFG_of_oneDimensionalFibers
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [DecidableEq E] [DecidableEq F]
    (f : E →L[ℝ] F) (g : F →L[ℝ] E) (v : E)
    (hfg : ∀ y, f (g y) = y)
    (hv0 : f v = 0)
    (hdecomp : ∀ x, ∃ t : ℝ, x = g (f x) + t • v)
    (C : ProperCone ℝ E)
    (hC : (C : PointedCone ℝ E).DualFG (innerₗ E)) :
    (C.map f : PointedCone ℝ F).DualFG (innerₗ F) := by
  classical
  obtain ⟨S, hS⟩ := hC
  change PointedCone.dual (innerₗ E) (S : Set E) = (C : PointedCone ℝ E) at hS
  have hCset : (C : Set E) = (coneDual (S : Set E) : Set E) := by
    apply congrArg (fun K : PointedCone ℝ E => (K : Set E)) hS.symm
  let normal (s : E) : F := g.adjoint s
  let beta (s : E) : ℝ := ⟪s, v⟫_ℝ
  let alpha (s : E) (y : F) : ℝ := ⟪normal s, y⟫_ℝ
  let Pos := S.filter (fun s => 0 < beta s)
  let Neg := S.filter (fun s => beta s < 0)
  let Zero := S.filter (fun s => beta s = 0)
  let pairNormal (p : E × E) : F :=
    (-beta p.2) • normal p.1 + beta p.1 • normal p.2
  let T : Finset F := Zero.image normal ∪ (Pos.product Neg).image pairNormal
  have hinner (x : E) (t : ℝ) (ht : x = g (f x) + t • v) (s : E) :
      ⟪s, x⟫_ℝ = alpha s (f x) + beta s * t := by
    calc
      ⟪s, x⟫_ℝ = ⟪s, g (f x) + t • v⟫_ℝ := by nth_rw 1 [ht]
      _ = ⟪s, g (f x)⟫_ℝ + t * ⟪s, v⟫_ℝ := by
        rw [inner_add_right, real_inner_smul_right]
      _ = ⟪normal s, f x⟫_ℝ + beta s * t := by
        rw [← g.adjoint_inner_left (f x) s]
        dsimp [normal, beta]
        ring
      _ = alpha s (f x) + beta s * t := rfl
  have hImageSub : f '' (C : Set E) ⊆ (coneDual (T : Set F) : Set F) := by
    rintro y ⟨x, hxC, rfl⟩
    have hxS : x ∈ coneDual (S : Set E) := by
      rw [hCset] at hxC
      exact hxC
    obtain ⟨t, ht⟩ := hdecomp x
    have hAlpha (s : E) : alpha s (f x) = ⟪s, x⟫_ℝ - beta s * t := by
      have hi := hinner x t ht s
      linarith
    apply mem_coneDual.mpr
    intro u hu
    rcases Finset.mem_union.mp hu with huZero | huPair
    · rcases Finset.mem_image.mp huZero with ⟨s, hsZero, rfl⟩
      have hsS : s ∈ S := (Finset.mem_filter.mp hsZero).1
      have hbeta : beta s = 0 := (Finset.mem_filter.mp hsZero).2
      have hxs := (mem_coneDual.mp hxS) hsS
      change 0 ≤ alpha s (f x)
      rw [hAlpha s]
      simpa [hbeta] using hxs
    · rcases Finset.mem_image.mp huPair with ⟨⟨s, j⟩, hp, rfl⟩
      have hsS : s ∈ S := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).1
      have hjS : j ∈ S := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).1
      have hsPos : 0 < beta s := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
      have hjNeg : beta j < 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2
      have hxs := (mem_coneDual.mp hxS) hsS
      have hxj := (mem_coneDual.mp hxS) hjS
      have hcombo : ⟪pairNormal (s, j), f x⟫_ℝ =
          (-beta j) * ⟪s, x⟫_ℝ + beta s * ⟪j, x⟫_ℝ := by
        calc
          ⟪pairNormal (s, j), f x⟫_ℝ =
              (-beta j) * alpha s (f x) + beta s * alpha j (f x) := by
                simp [pairNormal, normal, alpha, inner_add_left, real_inner_smul_left]
          _ = (-beta j) * (⟪s, x⟫_ℝ - beta s * t) +
              beta s * (⟪j, x⟫_ℝ - beta j * t) := by rw [hAlpha s, hAlpha j]
          _ = _ := by ring
      rw [hcombo]
      exact add_nonneg (mul_nonneg (le_of_lt (neg_pos.mpr hjNeg)) hxs)
        (mul_nonneg hsPos.le hxj)
  have hMapEq : (C.map f : Set F) = (coneDual (T : Set F) : Set F) := by
    ext y
    change y ∈ C.map f ↔ y ∈ coneDual (T : Set F)
    constructor
    · intro hy
      rw [ProperCone.mem_map] at hy
      exact closure_minimal hImageSub (coneDual (T : Set F)).isClosed hy
    · intro hy
      have hzero (s : E) (hs : s ∈ S) (hb : beta s = 0) : 0 ≤ alpha s y := by
        have hsZero : s ∈ Zero := Finset.mem_filter.mpr ⟨hs, hb⟩
        have hn : normal s ∈ T := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, hsZero, rfl⟩)
        simpa [alpha, normal] using (mem_coneDual.mp hy) hn
      have hpair (s : E) (hs : s ∈ S) (j : E) (hj : j ∈ S)
          (hbs : 0 < beta s) (hbj : beta j < 0) :
          0 ≤ beta s * alpha j y - beta j * alpha s y := by
        have hsPos : s ∈ Pos := Finset.mem_filter.mpr ⟨hs, hbs⟩
        have hjNeg : j ∈ Neg := Finset.mem_filter.mpr ⟨hj, hbj⟩
        have hp : (s, j) ∈ Pos.product Neg := Finset.mem_product.mpr ⟨hsPos, hjNeg⟩
        have hn : pairNormal (s, j) ∈ T :=
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(s, j), hp, rfl⟩)
        have hy' := (mem_coneDual.mp hy) hn
        have hEq : ⟪pairNormal (s, j), y⟫_ℝ =
            beta s * alpha j y - beta j * alpha s y := by
          simp [pairNormal, normal, alpha, inner_add_left, real_inner_smul_left]
          ring
        rw [hEq] at hy'
        exact hy'
      obtain ⟨t, ht⟩ := exists_scalar_for_finite_linear_inequalities S
        (fun s => alpha s y) beta hzero hpair
      let x : E := g y + t • v
      have hxS : x ∈ coneDual (S : Set E) := by
        apply mem_coneDual.mpr
        intro s hs
        have hsineq := ht s hs
        have hcalc : ⟪s, x⟫_ℝ = alpha s y + beta s * t := by
          dsimp [x, alpha, normal, beta]
          rw [inner_add_right, real_inner_smul_right, ← g.adjoint_inner_left y s]
          ring
        rw [hcalc]
        exact hsineq
      have hxC : x ∈ C := by
        change x ∈ (C : Set E)
        rw [hCset]
        exact hxS
      have hfx : f x = y := by
        dsimp [x]
        simp [hfg, hv0]
      have himage : y ∈ f '' (C : Set E) := ⟨x, hxC, hfx⟩
      change y ∈ C.map f
      rw [ProperCone.mem_map]
      exact subset_closure himage
  have hMapEqCone : C.map f = coneDual (T : Set F) :=
    ProperCone.ext (fun y => Iff.of_eq (congrArg (fun U : Set F => y ∈ U) hMapEq))
  rw [hMapEqCone]
  change (PointedCone.dual (innerₗ F) (T : Set F)).DualFG (innerₗ F)
  exact PointedCone.DualFG.dual_of_finset (innerₗ F) T


/-- A finite family of cones with fibers directed by one supplied kernel vector inherits finite dual
representations from its source cones. -/
theorem linearImageFamily_hasDualFGCells_of_oneDimensionalFibers
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [DecidableEq E] [DecidableEq F] [CompleteSpace E]
    (f : E →L[ℝ] F) (g : F →L[ℝ] E) (v : E)
    (hfg : ∀ y, f (g y) = y) (hv0 : f v = 0)
    (hdecomp : ∀ x, ∃ t : ℝ, x = g (f x) + t • v)
    (G : Fan E) (hG : HasDualFGCells G) :
    HasDualFGCells (linearImageFamily f G) := by
  classical
  intro C hC
  change C ∈ G.image (fun D => ProperCone.map f D) at hC
  rcases Finset.mem_image.mp hC with ⟨D, hD, rfl⟩
  exact properCone_map_dualFG_of_dualFG_of_oneDimensionalFibers
    f g v hfg hv0 hdecomp D (hG D hD)

/-- The linear map appending a zero coordinate. -/
def appendZeroCoordinate (n : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun x := Fin.snoc x 0
  map_add' x y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.snoc_last]
    · simp [Fin.snoc_castSucc]
  map_smul' c x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.snoc_last]
    · simp [Fin.snoc_castSucc]

/-- Append a zero as a continuous linear map in the Euclidean coordinate model. -/
noncomputable def appendZeroEuclidean (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) := by
  let sourceEquiv := WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)
  let targetEquiv := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  let g := sourceEquiv.symm.toLinearMap.comp
    ((appendZeroCoordinate n).comp targetEquiv.toLinearMap)
  exact ⟨g, g.continuous_of_finiteDimensional⟩

/-- The final coordinate unit vector in Euclidean coordinates. -/
noncomputable def lastBasisEuclidean (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) := by
  let sourceEquiv := WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)
  exact sourceEquiv.symm (Fin.lastCases 1 (fun _ : Fin n => 0))

theorem forgetLast_appendZeroEuclidean (n : ℕ) :
    (forgetLastEuclidean n).comp (appendZeroEuclidean n) = ContinuousLinearMap.id ℝ _ := by
  ext y i
  simp [forgetLastEuclidean, appendZeroEuclidean, appendZeroCoordinate, forgetLastCoordinate,
    LinearMap.comp_apply, Fin.snoc_castSucc]

theorem forgetLast_decomposeEuclidean (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ∃ t : ℝ, x = appendZeroEuclidean n (forgetLastEuclidean n x) + t • lastBasisEuclidean n := by
  let sourceEquiv := WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)
  refine ⟨sourceEquiv x (Fin.last n), ?_⟩
  apply sourceEquiv.injective
  rw [sourceEquiv.map_add, sourceEquiv.map_smul]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [appendZeroEuclidean, appendZeroCoordinate, forgetLastEuclidean,
      forgetLastCoordinate, lastBasisEuclidean, sourceEquiv, Fin.snoc_last]
  · simp [appendZeroEuclidean, appendZeroCoordinate, forgetLastEuclidean,
      forgetLastCoordinate, lastBasisEuclidean, sourceEquiv, Fin.snoc_castSucc]



theorem forgetLast_lastBasis_eq_zero (n : ℕ) :
    forgetLastEuclidean n (lastBasisEuclidean n) = 0 := by
  ext i
  simp [forgetLastEuclidean, lastBasisEuclidean, forgetLastCoordinate,
    WithLp.linearEquiv]


theorem linearImageFamily_forgetLast_hasDualFGCells {n : ℕ}
    (G : Fan (EuclideanSpace ℝ (Fin (n + 1)))) (hG : HasDualFGCells G) :
    HasDualFGCells (linearImageFamily (forgetLastEuclidean n) G) := by
  apply linearImageFamily_hasDualFGCells_of_oneDimensionalFibers
    (forgetLastEuclidean n) (appendZeroEuclidean n) (lastBasisEuclidean n)
  · intro y
    have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) => L y) (forgetLast_appendZeroEuclidean n)
    simpa using h
  · exact forgetLast_lastBasis_eq_zero n
  · exact forgetLast_decomposeEuclidean n
  · exact hG

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

theorem mem_hyperplaneArrangementFamily_iff [CompleteSpace E] [DecidableEq E]
    {T : Finset E} {C : ProperCone ℝ E} :
    C ∈ hyperplaneArrangementFamily T ↔
      ∃ P N, P ⊆ T ∧ N ⊆ T ∧ Disjoint P N ∧ C = signCell T P N := by
  classical
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨p, hp, rfl⟩
    rcases Finset.mem_filter.mp hp with ⟨hp, hdis⟩
    rcases Finset.mem_product.mp hp with ⟨hP, hN⟩
    exact ⟨p.1, p.2, Finset.mem_powerset.mp hP, Finset.mem_powerset.mp hN, hdis, rfl⟩
  · rintro ⟨P, N, hP, hN, hdis, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(P, N), Finset.mem_filter.mpr ?_, rfl⟩
    exact ⟨Finset.mk_mem_product (Finset.mem_powerset.mpr hP)
      (Finset.mem_powerset.mpr hN), hdis⟩

/-- Pairwise intersections of sign cells are sign cells: coordinates with opposite signs or a
zero assignment become equalities, while coordinates with the same strict sign retain it. -/
theorem hyperplaneArrangementFamily_inter_common [CompleteSpace E] [DecidableEq E]
    {T : Finset E} {C D : ProperCone ℝ E}
    (hC : C ∈ hyperplaneArrangementFamily T) (hD : D ∈ hyperplaneArrangementFamily T) :
    ∃ G ∈ hyperplaneArrangementFamily T,
      (G : Set E) = (C : Set E) ∩ (D : Set E) := by
  classical
  obtain ⟨P, N, hPT, hNT, hPN, rfl⟩ := mem_hyperplaneArrangementFamily_iff.mp hC
  obtain ⟨P', N', hP'T, hN'T, hP'N', rfl⟩ := mem_hyperplaneArrangementFamily_iff.mp hD
  let Q := P ∩ P'
  let R := N ∩ N'
  have hQT : Q ⊆ T := Finset.inter_subset_left.trans hPT
  have hRT : R ⊆ T := Finset.inter_subset_left.trans hNT
  have hQR : Disjoint Q R := by
    rw [Finset.disjoint_left]
    intro a haQ haR
    exact (Finset.disjoint_left.mp hPN) (Finset.mem_inter.mp haQ).1
      (Finset.mem_inter.mp haR).1
  have not_union {A B : Finset E} {a : E} (hA : a ∉ A) (hB : a ∉ B) :
      a ∉ A ∪ B := by
    intro hab
    rcases Finset.mem_union.mp hab with ha | hb
    · exact hA ha
    · exact hB hb
  have hpair : (Q, R) ∈
      ((T.powerset.product T.powerset).filter (fun p => Disjoint p.1 p.2)) := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mk_mem_product
        (Finset.mem_powerset.mpr hQT) (Finset.mem_powerset.mpr hRT)
    · exact hQR
  let G := signCell T Q R
  have hG : G ∈ hyperplaneArrangementFamily T := by
    change signCell T Q R ∈ hyperplaneArrangementFamily T
    apply Finset.mem_image.mpr
    exact ⟨(Q, R), hpair, rfl⟩
  have hset : (G : Set E) = (signCell T P N : Set E) ∩
      (signCell T P' N' : Set E) := by
    ext x
    change x ∈ signCell T Q R ↔
      x ∈ signCell T P N ∧ x ∈ signCell T P' N'
    rw [mem_signCell, mem_signCell, mem_signCell]
    constructor
    · rintro ⟨hQ, hR, hZ⟩
      have hC' : x ∈ signCell T P N := by
        apply mem_signCell.mpr
        refine ⟨?_, ?_, ?_⟩
        · intro a ha
          by_cases haP' : a ∈ P'
          · exact hQ a (Finset.mem_inter.mpr ⟨ha, haP'⟩)
          · have hnotQ : a ∉ Q := fun h => haP' (Finset.mem_inter.mp h).2
            have hnotR : a ∉ R := by
              intro h
              exact (Finset.disjoint_left.mp hPN) ha (Finset.mem_inter.mp h).1
            have hz := hZ a (Finset.mem_sdiff.mpr
              ⟨hPT ha, not_union hnotQ hnotR⟩)
            rw [hz]
        · intro a ha
          by_cases haN' : a ∈ N'
          · exact hR a (Finset.mem_inter.mpr ⟨ha, haN'⟩)
          · have hnotR : a ∉ R := fun h => haN' (Finset.mem_inter.mp h).2
            have hnotQ : a ∉ Q := by
              intro h
              exact (Finset.disjoint_left.mp hPN) (Finset.mem_inter.mp h).1 ha
            have hz := hZ a (Finset.mem_sdiff.mpr
              ⟨hNT ha, not_union hnotQ hnotR⟩)
            rw [inner_neg_left, hz]
            simp
        · intro a ha
          have haNot := (Finset.mem_sdiff.mp ha).2
          have haP : a ∉ P := fun h => haNot (Finset.mem_union.mpr (Or.inl h))
          have haN : a ∉ N := fun h => haNot (Finset.mem_union.mpr (Or.inr h))
          have haQ : a ∉ Q := fun h => haP (Finset.mem_inter.mp h).1
          have haR : a ∉ R := fun h => haN (Finset.mem_inter.mp h).1
          exact hZ a (Finset.mem_sdiff.mpr
            ⟨(Finset.mem_sdiff.mp ha).1, not_union haQ haR⟩)
      have hD' : x ∈ signCell T P' N' := by
        apply mem_signCell.mpr
        refine ⟨?_, ?_, ?_⟩
        · intro a ha
          by_cases haP : a ∈ P
          · exact hQ a (Finset.mem_inter.mpr ⟨haP, ha⟩)
          · have hnotQ : a ∉ Q := fun h => haP (Finset.mem_inter.mp h).1
            have hnotR : a ∉ R := by
              intro h
              exact (Finset.disjoint_left.mp hP'N') ha (Finset.mem_inter.mp h).2
            have hz := hZ a (Finset.mem_sdiff.mpr
              ⟨hP'T ha, not_union hnotQ hnotR⟩)
            rw [hz]
        · intro a ha
          by_cases haN : a ∈ N
          · exact hR a (Finset.mem_inter.mpr ⟨haN, ha⟩)
          · have hnotR : a ∉ R := fun h => haN (Finset.mem_inter.mp h).1
            have hnotQ : a ∉ Q := by
              intro h
              exact (Finset.disjoint_left.mp hP'N') (Finset.mem_inter.mp h).2 ha
            have hz := hZ a (Finset.mem_sdiff.mpr
              ⟨hN'T ha, not_union hnotQ hnotR⟩)
            rw [inner_neg_left, hz]
            simp
        · intro a ha
          have haNot := (Finset.mem_sdiff.mp ha).2
          have haP' : a ∉ P' := fun h => haNot (Finset.mem_union.mpr (Or.inl h))
          have haN' : a ∉ N' := fun h => haNot (Finset.mem_union.mpr (Or.inr h))
          have haQ : a ∉ Q := fun h => haP' (Finset.mem_inter.mp h).2
          have haR : a ∉ R := fun h => haN' (Finset.mem_inter.mp h).2
          exact hZ a (Finset.mem_sdiff.mpr
            ⟨(Finset.mem_sdiff.mp ha).1, not_union haQ haR⟩)
      exact ⟨mem_signCell.mp hC', mem_signCell.mp hD'⟩
    · rintro ⟨hC, hD⟩
      rcases hC with ⟨hP, hN, hZP⟩
      rcases hD with ⟨hP', hN', hZP'⟩
      refine ⟨?_, ?_, ?_⟩
      · intro a ha
        exact hP a (Finset.mem_inter.mp ha).1
      · intro a ha
        exact hN a (Finset.mem_inter.mp ha).1
      · intro a ha
        have haT : a ∈ T := (Finset.mem_sdiff.mp ha).1
        have hnotUnion := (Finset.mem_sdiff.mp ha).2
        have hnotQ : a ∉ Q := fun h => hnotUnion (Finset.mem_union.mpr (Or.inl h))
        have hnotR : a ∉ R := fun h => hnotUnion (Finset.mem_union.mpr (Or.inr h))
        by_cases haP : a ∈ P
        · by_cases haP' : a ∈ P'
          · exact (hnotQ (Finset.mem_inter.mpr ⟨haP, haP'⟩)).elim
          · by_cases haN' : a ∈ N'
            · have hp := hP a haP
              have hn : ⟪a, x⟫_ℝ ≤ 0 := by
                simpa [inner_neg_left] using hN' a haN'
              exact le_antisymm hn hp
            · exact hZP' a (Finset.mem_sdiff.mpr
                ⟨haT, not_union haP' haN'⟩)
        · by_cases haN : a ∈ N
          · by_cases haP' : a ∈ P'
            · have hp := hP' a haP'
              have hn : ⟪a, x⟫_ℝ ≤ 0 := by
                simpa [inner_neg_left] using hN a haN
              exact le_antisymm hn hp
            · by_cases haN' : a ∈ N'
              · exact (hnotR (Finset.mem_inter.mpr ⟨haN, haN'⟩)).elim
              · exact hZP' a (Finset.mem_sdiff.mpr
                  ⟨haT, not_union haP' haN'⟩)
          · exact hZP a (Finset.mem_sdiff.mpr
              ⟨haT, not_union haP haN⟩)
  exact ⟨G, hG, hset⟩

/-- A dual vector of a finite half-space sign cell is a finite nonnegative combination of its
normals. This finite Farkas representation identifies the active inequalities on an exposed face. -/
theorem signCell_dual_mem_hull [CompleteSpace E] [DecidableEq E]
    {T P N : Finset E} {a : E}
    (ha : a ∈ coneDual (signCell T P N : Set E)) :
    ∃ c : E →₀ ℝ, c.support ⊆ signCellNormals T P N ∧
      (∀ y, 0 ≤ c y) ∧ c.sum (fun i r => r • i) = a := by
  let S := signCellNormals T P N
  have ha' : a ∈ coneDual (coneDual (S : Set E) : Set E) := by
    simpa [signCell, S] using ha
  rw [coneDual_finset_dual_eq S] at ha'
  change a ∈ (properConeOfFinset S : Set E) at ha'
  rw [coe_properConeOfFinset] at ha'
  exact PointedCone.mem_hull_set.mp ha'

/-- Every exposed face of a sign cell is another sign cell: the finite Farkas representation of
the exposing normal shows that precisely its active signed inequalities become equalities. -/
theorem hyperplaneArrangementFamily_faces_mem [CompleteSpace E] [DecidableEq E]
    {T : Finset E} {C D : ProperCone ℝ E}
    (hC : C ∈ hyperplaneArrangementFamily T) (hD : IsExposedFaceOf D C) :
    D ∈ hyperplaneArrangementFamily T := by
  classical
  obtain ⟨P, N, hPT, hNT, hPN, rfl⟩ := mem_hyperplaneArrangementFamily_iff.mp hC
  obtain ⟨a, ha, hset⟩ := hD
  have hDmem (x : E) :
      x ∈ D ↔ x ∈ exposedFace (signCell T P N : PointedCone ℝ E) a :=
    Iff.of_eq (congrArg (fun S : Set E => x ∈ S) hset)
  obtain ⟨c, hcsupp, hc0, hcsum⟩ := signCell_dual_mem_hull ha
  let A := c.support ∪ c.support.image (fun i => -i)
  let P0 := P.filter (fun i => i ∉ A)
  let N0 := N.filter (fun i => i ∉ A)
  have not_union {X Y : Finset E} {b : E} (hX : b ∉ X) (hY : b ∉ Y) :
      b ∉ X ∪ Y := by
    intro h
    rcases Finset.mem_union.mp h with hX' | hY'
    · exact hX hX'
    · exact hY hY'
  have hP0T : P0 ⊆ T := (Finset.filter_subset _ _).trans hPT
  have hN0T : N0 ⊆ T := (Finset.filter_subset _ _).trans hNT
  have hP0N0 : Disjoint P0 N0 := by
    rw [Finset.disjoint_left]
    intro i hiP hiN
    exact (Finset.disjoint_left.mp hPN) (Finset.filter_subset _ _ hiP)
      (Finset.filter_subset _ _ hiN)
  have hDfamily : signCell T P0 N0 ∈ hyperplaneArrangementFamily T :=
    mem_hyperplaneArrangementFamily_iff.mpr ⟨P0, N0, hP0T, hN0T, hP0N0, rfl⟩
  have hInnerSum (x : E) :
      ⟪a, x⟫_ℝ = ∑ i ∈ c.support, c i * ⟪i, x⟫_ℝ := by
    rw [← hcsum]
    simp [Finsupp.sum, sum_inner, real_inner_smul_left]
  have hCoeffZero (x : E) (hxD : x ∈ D) (i : E) (hi : i ∈ c.support) :
      ⟪i, x⟫_ℝ = 0 := by
    have hxFace := (hDmem x).mp hxD
    have hxC : x ∈ signCell T P N := (mem_exposedFace.mp hxFace).1
    have haZero : ⟪a, x⟫_ℝ = 0 := (mem_exposedFace.mp hxFace).2
    change x ∈ coneDual (signCellNormals T P N : Set E) at hxC
    have htermNonneg : ∀ j ∈ c.support, 0 ≤ c j * ⟪j, x⟫_ℝ := by
      intro j hj
      exact mul_nonneg (hc0 j)
        ((mem_coneDual.mp hxC) (hcsupp hj))
    have hsumZero : (∑ j ∈ c.support, c j * ⟪j, x⟫_ℝ) = 0 := by
      calc
        _ = ⟪a, x⟫_ℝ := (hInnerSum x).symm
        _ = 0 := haZero
    have htermZero := (Finset.sum_eq_zero_iff_of_nonneg htermNonneg).mp hsumZero i hi
    have hci : c i ≠ 0 := by
      simpa only [Finsupp.mem_support_iff] using hi
    rcases mul_eq_zero.mp htermZero with hciZero | hiZero
    · exact (hci hciZero).elim
    · exact hiZero
  have hActiveZero (x : E) (hxD : x ∈ D) : ∀ b ∈ A, ⟪b, x⟫_ℝ = 0 := by
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact hCoeffZero x hxD b hb
    · rcases Finset.mem_image.mp hb with ⟨i, hi, rfl⟩
      rw [inner_neg_left, hCoeffZero x hxD i hi]
      simp
  have hDmemCell (x : E) : x ∈ D ↔ x ∈ signCell T P0 N0 := by
    constructor
    · intro hxD
      have hxFace := (hDmem x).mp hxD
      have hxC : x ∈ signCell T P N := (mem_exposedFace.mp hxFace).1
      rcases mem_signCell.mp hxC with ⟨hP, hN, hZ⟩
      have hAzero := hActiveZero x hxD
      apply mem_signCell.mpr
      refine ⟨?_, ?_, ?_⟩
      · intro b hb
        exact hP b (Finset.filter_subset _ _ hb)
      · intro b hb
        exact hN b (Finset.filter_subset _ _ hb)
      · intro b hb
        have hbT : b ∈ T := (Finset.mem_sdiff.mp hb).1
        have hbNot := (Finset.mem_sdiff.mp hb).2
        have hbP0 : b ∉ P0 := fun h => hbNot (Finset.mem_union.mpr (Or.inl h))
        have hbN0 : b ∉ N0 := fun h => hbNot (Finset.mem_union.mpr (Or.inr h))
        by_cases hbP : b ∈ P
        · have hbA : b ∈ A := by
            by_contra hnotA
            exact hbP0 (Finset.mem_filter.mpr ⟨hbP, hnotA⟩)
          exact hAzero b hbA
        · by_cases hbN : b ∈ N
          · have hbA : b ∈ A := by
              by_contra hnotA
              exact hbN0 (Finset.mem_filter.mpr ⟨hbN, hnotA⟩)
            exact hAzero b hbA
          · exact hZ b (Finset.mem_sdiff.mpr ⟨hbT, not_union hbP hbN⟩)
    · intro hxCell
      rcases mem_signCell.mp hxCell with ⟨hP0, hN0, hZ0⟩
      have hGenZero (i : E) (hi : i ∈ c.support) : ⟪i, x⟫_ℝ = 0 := by
        have hiS : i ∈ signCellNormals T P N := hcsupp hi
        simp [signCellNormals] at hiS
        rcases hiS with hp | hn | hz | hzneg
        · have hiA : i ∈ A := Finset.mem_union.mpr (Or.inl hi)
          have hiP0 : i ∉ P0 := by
            intro h
            exact (Finset.mem_filter.mp h).2 hiA
          have hiN0 : i ∉ N0 := by
            intro h
            exact (Finset.disjoint_left.mp hPN) hp
              (Finset.filter_subset _ _ h)
          exact hZ0 i (Finset.mem_sdiff.mpr
            ⟨hPT hp, not_union hiP0 hiN0⟩)
        · rcases hn with ⟨b, hb, rfl⟩
          have hbA : b ∈ A := by
            apply Finset.mem_union.mpr
            right
            apply Finset.mem_image.mpr
            exact ⟨-b, hi, by simp⟩
          have hbP0 : b ∉ P0 := by
            intro h
            exact (Finset.disjoint_left.mp hPN) (Finset.filter_subset _ _ h) hb
          have hbN0 : b ∉ N0 := by
            intro h
            exact (Finset.mem_filter.mp h).2 hbA
          have hz := hZ0 b (Finset.mem_sdiff.mpr
            ⟨hNT hb, not_union hbP0 hbN0⟩)
          simpa [inner_neg_left] using hz
        · have hiA : i ∈ A := Finset.mem_union.mpr (Or.inl hi)
          have hiP0 : i ∉ P0 := by
            intro h
            exact (Finset.mem_filter.mp h).2 hiA
          have hiN0 : i ∉ N0 := by
            intro h
            exact (Finset.mem_filter.mp h).2 hiA
          exact hZ0 i (Finset.mem_sdiff.mpr
            ⟨hz.1, not_union hiP0 hiN0⟩)
        · rcases hzneg with ⟨b, hb, rfl⟩
          have hbA : b ∈ A := by
            apply Finset.mem_union.mpr
            right
            apply Finset.mem_image.mpr
            exact ⟨-b, hi, by simp⟩
          have hbP0 : b ∉ P0 := by
            intro h
            exact (Finset.mem_filter.mp h).2 hbA
          have hbN0 : b ∉ N0 := by
            intro h
            exact (Finset.mem_filter.mp h).2 hbA
          have hz := hZ0 b (Finset.mem_sdiff.mpr
            ⟨hb.1, not_union hbP0 hbN0⟩)
          simpa [inner_neg_left] using hz
      have hA0 : ∀ b ∈ A, ⟪b, x⟫_ℝ = 0 := by
        intro b hb
        rcases Finset.mem_union.mp hb with hb | hb
        · exact hGenZero b hb
        · rcases Finset.mem_image.mp hb with ⟨i, hi, rfl⟩
          rw [inner_neg_left, hGenZero i hi]
          simp
      have hxC : x ∈ signCell T P N := by
        apply mem_signCell.mpr
        refine ⟨?_, ?_, ?_⟩
        · intro b hb
          by_cases hbA : b ∈ A
          · rw [hA0 b hbA]
          · exact hP0 b (Finset.mem_filter.mpr ⟨hb, hbA⟩)
        · intro b hb
          by_cases hbA : b ∈ A
          · rw [inner_neg_left, hA0 b hbA]
            simp
          · exact hN0 b (Finset.mem_filter.mpr ⟨hb, hbA⟩)
        · intro b hb
          have hbT : b ∈ T := (Finset.mem_sdiff.mp hb).1
          have hbNot := (Finset.mem_sdiff.mp hb).2
          have hbP0 : b ∉ P0 := by
            intro h
            exact hbNot (Finset.mem_union.mpr (Or.inl (Finset.filter_subset _ _ h)))
          have hbN0 : b ∉ N0 := by
            intro h
            exact hbNot (Finset.mem_union.mpr (Or.inr (Finset.filter_subset _ _ h)))
          exact hZ0 b (Finset.mem_sdiff.mpr
            ⟨hbT, not_union hbP0 hbN0⟩)
      have hsumZero : (∑ i ∈ c.support, c i * ⟪i, x⟫_ℝ) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hGenZero i hi]
        simp
      have haZero : ⟪a, x⟫_ℝ = 0 := by
        rw [hInnerSum x, hsumZero]
      have hxFace : x ∈ exposedFace (signCell T P N : PointedCone ℝ E) a :=
        mem_exposedFace.mpr ⟨hxC, haZero⟩
      exact (hDmem x).mpr hxFace
  have hEq : D = signCell T P0 N0 := by
    apply ProperCone.ext
    intro x
    exact hDmemCell x
  exact mem_hyperplaneArrangementFamily_iff.mpr
    ⟨P0, N0, hP0T, hN0T, hP0N0, hEq⟩


/-- Finite central hyperplane arrangements form a complete polyhedral fan. -/
theorem hyperplaneArrangementFamily_isPolyhedralFan [CompleteSpace E] [DecidableEq E]
    (T : Finset E) : IsPolyhedralFan (hyperplaneArrangementFamily T) where
  faces_mem := fun _ hC _ hD => hyperplaneArrangementFamily_faces_mem hC hD
  inter_common := fun _ hC _ hD => hyperplaneArrangementFamily_inter_common hC hD
  covers := hyperplaneArrangementFamily_covers T

/-- Every sign cell in a finite central hyperplane arrangement has a finite half-space
representation, using the signed arrangement normals themselves. -/
theorem hyperplaneArrangementFamily_hasDualFGCells [CompleteSpace E] [DecidableEq E]
    (T : Finset E) : HasDualFGCells (hyperplaneArrangementFamily T) := by
  classical
  intro C hC
  obtain ⟨P, N, _, _, _, rfl⟩ := mem_hyperplaneArrangementFamily_iff.mp hC
  change (PointedCone.dual (innerₗ E) (signCellNormals T P N : Set E)).DualFG (innerₗ E)
  exact PointedCone.DualFG.dual_of_finset (innerₗ E) (signCellNormals T P N)

/-- Choose a point in a finite-dual cone that is strict on every inequality that can be strict.
The witness is the sum of one point witnessing each such inequality. -/
theorem exists_strict_point_for_finite_dual [CompleteSpace E] [DecidableEq E]
    (S : Finset E) :
    ∃ x ∈ coneDual (S : Set E), ∀ v ∈ S,
      (∃ y, y ∈ coneDual (S : Set E) ∧ 0 < ⟪v, y⟫_ℝ) →
        0 < ⟪v, x⟫_ℝ := by
  classical
  let D := coneDual (S : Set E)
  let P := S.filter (fun v => ∃ y, y ∈ D ∧ 0 < ⟪v, y⟫_ℝ)
  have hWitness (v : E) (hv : v ∈ P) : ∃ y, y ∈ D ∧ 0 < ⟪v, y⟫_ℝ :=
    (Finset.mem_filter.mp hv).2
  let w : E → E := fun v =>
    if hv : v ∈ P then Classical.choose (hWitness v hv) else 0
  have hw (v : E) (hv : v ∈ P) : w v ∈ D ∧ 0 < ⟪v, w v⟫_ℝ := by
    dsimp [w]
    rw [dite_eq_left hv]
    exact Classical.choose_spec (hWitness v hv)
  let x := ∑ v ∈ P, w v
  have hx : x ∈ D := by
    change x ∈ coneDual (S : Set E)
    apply Submodule.sum_mem
    intro v hv
    exact (hw v hv).1
  refine ⟨x, hx, ?_⟩
  intro v hv hpositive
  have hvP : v ∈ P := Finset.mem_filter.mpr ⟨hv, hpositive⟩
  have hsum : ⟪v, x⟫_ℝ = ∑ u ∈ P, ⟪v, w u⟫_ℝ := by
    simp [x, inner_sum]
  have hterms : ∀ u ∈ P, 0 ≤ ⟪v, w u⟫_ℝ := by
    intro u hu
    exact (mem_coneDual.mp (hw u hu).1) hv
  have hle := Finset.single_le_sum hterms hvP
  rw [hsum]
  exact lt_of_lt_of_le (hw v hvP).2 hle

/-- Collect one finite half-space representation for every cell in a finite fan. -/
noncomputable def fanNormalSet [CompleteSpace E] [DecidableEq E]
    (F : Fan E) (hF : HasDualFGCells F) : Finset E := by
  classical
  exact F.attach.biUnion (fun C => Classical.choose (hF C.1 C.2))

theorem mem_fanNormalSet [CompleteSpace E] [DecidableEq E]
    {F : Fan E} {hF : HasDualFGCells F} {C : ProperCone ℝ E}
    (hC : C ∈ F) {s : E} (hs : s ∈ Classical.choose (hF C hC)) :
    s ∈ fanNormalSet F hF := by
  classical
  change s ∈ F.attach.biUnion (fun C => Classical.choose (hF C.1 C.2))
  apply Finset.mem_biUnion.mpr
  exact ⟨⟨C, hC⟩, Finset.mem_attach _ _, hs⟩

/-- The central arrangement of all finite half-space normals of a covering cone family refines that
family. The proof needs coverage, but not the fan intersection axioms: a cell chooses a point strict
on every inequality that can be strict, and a member cone containing that point contains the whole
cell. -/
theorem hyperplaneArrangementFamily_refines_of_covering_dualFG [CompleteSpace E] [DecidableEq E]
    {F : Fan E} (hCover : (⋃ C ∈ F, (C : Set E)) = Set.univ)
    (hFdual : HasDualFGCells F) :
    Refines (hyperplaneArrangementFamily (fanNormalSet F hFdual)) F := by
  classical
  let T := fanNormalSet F hFdual
  intro D hD
  obtain ⟨P, N, hPT, hNT, hPN, rfl⟩ := mem_hyperplaneArrangementFamily_iff.mp hD
  let S := signCellNormals T P N
  obtain ⟨x₀, hx₀, hstrict⟩ := exists_strict_point_for_finite_dual S
  have hx₀cell : x₀ ∈ signCell T P N := by
    change x₀ ∈ coneDual (S : Set E)
    exact hx₀
  have hsign₀ := mem_signCell.mp hx₀cell
  have hx₀cover : x₀ ∈ ⋃ C ∈ F, (C : Set E) := by
    rw [hCover]
    simp
  rcases Set.mem_iUnion.mp hx₀cover with ⟨C, hCmem⟩
  rcases Set.mem_iUnion.mp hCmem with ⟨hCF, hx₀C⟩
  let R := Classical.choose (hFdual C hCF)
  have hRrep : (coneDual (R : Set E) : Set E) = (C : Set E) := by
    have hpoint :
        (coneDual (R : Set E) : PointedCone ℝ E) = (C : PointedCone ℝ E) := by
      change PointedCone.dual (innerₗ E) (R : Set E) = (C : PointedCone ℝ E)
      exact Classical.choose_spec (hFdual C hCF)
    exact congrArg (fun K : PointedCone ℝ E => (K : Set E)) hpoint
  have hRsubT : ∀ s ∈ R, s ∈ T := by
    intro s hs
    exact mem_fanNormalSet hCF hs
  have hx₀R : ∀ s ∈ R, 0 ≤ ⟪s, x₀⟫_ℝ := by
    intro s hs
    have hx₀' : x₀ ∈ (coneDual (R : Set E) : Set E) := by
      rw [hRrep]
      exact hx₀C
    exact (mem_coneDual.mp hx₀') hs
  have hcell_subset : (signCell T P N : Set E) ⊆ (C : Set E) := by
    intro y hy
    have hyS : y ∈ coneDual (S : Set E) := by
      change y ∈ signCell T P N
      exact hy
    rcases mem_signCell.mp hy with ⟨hP, hN, hZ⟩
    have hyR : y ∈ coneDual (R : Set E) := by
      apply mem_coneDual.mpr
      intro s hs
      have hsT : s ∈ T := hRsubT s hs
      by_cases hsP : s ∈ P
      · exact hP s hsP
      · by_cases hsN : s ∈ N
        · have hnegS : -s ∈ S := by
            simp [S, signCellNormals, hsT, hsN]
          have hx₀Neg : ⟪-s, x₀⟫_ℝ = 0 := by
            have hnonneg := hx₀R s hs
            have hnonpos : ⟪s, x₀⟫_ℝ ≤ 0 := by
              have h := hsign₀.2.1 s hsN
              simpa [inner_neg_left] using h
            have hzero : ⟪s, x₀⟫_ℝ = 0 := le_antisymm hnonpos hnonneg
            simpa [inner_neg_left] using hzero
          have hnoPos : ¬ ∃ z, z ∈ signCell T P N ∧ 0 < ⟪-s, z⟫_ℝ := by
            intro hex
            have hpos := hstrict (-s) hnegS hex
            exact (ne_of_gt hpos) hx₀Neg
          have hyNeg : ⟪-s, y⟫_ℝ = 0 := by
            have hnonneg : 0 ≤ ⟪-s, y⟫_ℝ := (mem_coneDual.mp hyS) hnegS
            have hnotpos : ¬ 0 < ⟪-s, y⟫_ℝ := by
              intro hpos
              exact hnoPos ⟨y, hy, hpos⟩
            linarith
          have hyzero : ⟪s, y⟫_ℝ = 0 := by
            simpa [inner_neg_left] using hyNeg
          rw [hyzero]
        · have hz := hZ s (Finset.mem_sdiff.mpr
            ⟨hsT, by
              intro h
              rcases Finset.mem_union.mp h with hp | hn
              · exact hsP hp
              · exact hsN hn⟩)
          rw [hz]
    rw [← hRrep]
    exact hyR
  exact ⟨C, hCF, hcell_subset⟩

/-- The central arrangement of a covering polyhedral fan's finite dual normals refines the fan. -/
theorem hyperplaneArrangementFamily_refines_of_dualFG [CompleteSpace E] [DecidableEq E]
    {F : Fan E} (hF : IsPolyhedralFan F) (hFdual : HasDualFGCells F) :
    Refines (hyperplaneArrangementFamily (fanNormalSet F hFdual)) F :=
  hyperplaneArrangementFamily_refines_of_covering_dualFG hF.covers hFdual

/-- The arrangement from finite dual normals refines the family of one-coordinate projections of a
complete polyhedral fan. The image family need not satisfy the fan intersection axioms itself. -/
theorem hyperplaneArrangementFamily_refines_forgetLastImage {n : ℕ}
    (G : Fan (EuclideanSpace ℝ (Fin (n + 1)))) (hG : IsPolyhedralFan G)
    (hGdual : HasDualFGCells G) :
    Refines
      (hyperplaneArrangementFamily
        (fanNormalSet (linearImageFamily (forgetLastEuclidean n) G)
          (linearImageFamily_forgetLast_hasDualFGCells G hGdual)))
      (linearImageFamily (forgetLastEuclidean n) G) :=
  hyperplaneArrangementFamily_refines_of_covering_dualFG
    (linearImageFamily_forgetLastEuclidean_covers G hG)
    (linearImageFamily_forgetLast_hasDualFGCells G hGdual)

/-- Any surjective projection with fibers along one supplied kernel vector admits a complete
polyhedral fan refinement of its closed-cone image family. -/
theorem exists_polyhedral_fan_refinement_of_oneDimensional_projection
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E]
    [CompleteSpace F] [DecidableEq E] [DecidableEq F]
    (G : Fan E) (hG : IsPolyhedralFan G) (hGdual : HasDualFGCells G)
    (f : E →L[ℝ] F) (g : F →L[ℝ] E) (v : E)
    (hfg : ∀ y, f (g y) = y) (hv0 : f v = 0)
    (hdecomp : ∀ x, ∃ t : ℝ, x = g (f x) + t • v) :
    ∃ H : Fan F, IsPolyhedralFan H ∧ HasDualFGCells H ∧
      Refines H (linearImageFamily f G) := by
  have hf : Function.Surjective f := fun y => ⟨g y, hfg y⟩
  have hImageCover := linearImageFamily_covers_of_surjective hG f hf
  have hImageDual := linearImageFamily_hasDualFGCells_of_oneDimensionalFibers
    f g v hfg hv0 hdecomp G hGdual
  refine ⟨hyperplaneArrangementFamily (fanNormalSet (linearImageFamily f G) hImageDual),
    hyperplaneArrangementFamily_isPolyhedralFan _,
    hyperplaneArrangementFamily_hasDualFGCells _, ?_⟩
  exact hyperplaneArrangementFamily_refines_of_covering_dualFG hImageCover hImageDual

/-- A one-coordinate projected image family admits a complete polyhedral fan refinement whose
cells have finite dual representations. This supplies fan data for the projection step without
asserting that the raw image family is itself face-to-face. -/
theorem exists_polyhedral_fan_refinement_forgetLastImage {n : ℕ}
    (G : Fan (EuclideanSpace ℝ (Fin (n + 1)))) (hG : IsPolyhedralFan G)
    (hGdual : HasDualFGCells G) :
    ∃ H : Fan (EuclideanSpace ℝ (Fin n)), IsPolyhedralFan H ∧ HasDualFGCells H ∧
      Refines H (linearImageFamily (forgetLastEuclidean n) G) := by
  refine ⟨hyperplaneArrangementFamily
    (fanNormalSet (linearImageFamily (forgetLastEuclidean n) G)
      (linearImageFamily_forgetLast_hasDualFGCells G hGdual)), ?_, ?_, ?_⟩
  · exact hyperplaneArrangementFamily_isPolyhedralFan _
  · exact hyperplaneArrangementFamily_hasDualFGCells _
  · exact hyperplaneArrangementFamily_refines_forgetLastImage G hG hGdual


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

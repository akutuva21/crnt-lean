import CRNT.Multistationarity.RegularValueDegree
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The regular-value degree of an invertible linear map

The first oriented value of the regular-value topological degree `regularDegree`. An
invertible continuous linear map `T : E →L[ℝ] E` on a finite-dimensional real normed
space is a global bijection, so the preimage of any value `y` is a single point, and the
Fréchet derivative of `T` is `T` itself everywhere. Both summands of the degree formula
therefore collapse and

`regularDegree (⇑T) y = sign (det T)`.

This is `±1` according to the orientation of `T`, and in particular it is `-1` for an
orientation-reversing map. The orientation-reversing case is exercised on the negation
`-id` of `EuclideanSpace ℝ (Fin 1)`, whose determinant is `-1`.

* `preimage_singleton_of_det_ne_zero` / `finite_preimage_of_det_ne_zero` — the preimage
  of an invertible linear map is a finite singleton.
* `regularDegree_continuousLinearMap` — the degree of an invertible `T : E →L[ℝ] E` is
  `sign (det T)`.
* `regularDegree_continuousLinearEquiv` — the same for `T : E ≃L[ℝ] E`.
* `regularDegree_affine` — the degree of the affine map `x ↦ T x + b` is `sign (det T)`.
* `regularDegree_neg_id_eq_neg_one` — the orientation-reversing value `-1` on
  `EuclideanSpace ℝ (Fin 1)`.

-/

namespace CRNT

open scoped Finset

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The continuous linear equivalence attached to a continuous linear map of nonzero
determinant on a finite-dimensional real space. Its underlying function is `T`. -/
noncomputable def equivOfDetNeZero (T : E →L[ℝ] E)
    (hdet : LinearMap.det T.toLinearMap ≠ 0) : E ≃L[ℝ] E :=
  T.toContinuousLinearEquivOfDetNeZero hdet

@[simp]
theorem equivOfDetNeZero_apply (T : E →L[ℝ] E)
    (hdet : LinearMap.det T.toLinearMap ≠ 0) (x : E) :
    equivOfDetNeZero T hdet x = T x :=
  rfl

/-- The preimage of `y` under an invertible continuous linear map is the singleton of the
inverse image `T⁻¹ y`: `T` is a global bijection. -/
theorem preimage_singleton_of_det_ne_zero (T : E →L[ℝ] E)
    (hdet : LinearMap.det T.toLinearMap ≠ 0) (y : E) :
    (⇑T) ⁻¹' {y} = {(equivOfDetNeZero T hdet).symm y} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hx
    have : equivOfDetNeZero T hdet x = y := by
      rw [equivOfDetNeZero_apply]; exact hx
    rw [← this, ContinuousLinearEquiv.symm_apply_apply]
  · intro hx
    rw [hx, ← equivOfDetNeZero_apply T hdet, ContinuousLinearEquiv.apply_symm_apply]

/-- The preimage of `y` under an invertible continuous linear map is finite. -/
theorem finite_preimage_of_det_ne_zero (T : E →L[ℝ] E)
    (hdet : LinearMap.det T.toLinearMap ≠ 0) (y : E) :
    ((⇑T) ⁻¹' {y}).Finite := by
  rw [preimage_singleton_of_det_ne_zero T hdet y]
  exact Set.finite_singleton _

/-- **The degree of an invertible continuous linear map.** The regular degree of an
invertible `T : E →L[ℝ] E` at any value is the orientation sign `sign (det T)`: the
preimage is a single point and the derivative of `T` is `T` everywhere, so the single
summand is `sign (det T)`. This is `+1` or `-1` according to whether `T` preserves or
reverses orientation. -/
theorem regularDegree_continuousLinearMap (T : E →L[ℝ] E)
    (hdet : LinearMap.det T.toLinearMap ≠ 0) (y : E) :
    regularDegree (⇑T) y (finite_preimage_of_det_ne_zero T hdet y) =
      ((SignType.sign (LinearMap.det T.toLinearMap) : SignType) : ℤ) := by
  unfold regularDegree
  have htf : (finite_preimage_of_det_ne_zero T hdet y).toFinset =
      {(equivOfDetNeZero T hdet).symm y} := by
    ext z
    rw [Set.Finite.mem_toFinset, preimage_singleton_of_det_ne_zero T hdet y,
      Finset.mem_singleton, Set.mem_singleton_iff]
  rw [htf, Finset.sum_singleton]
  rw [show fderiv ℝ (⇑T) ((equivOfDetNeZero T hdet).symm y) = T from T.fderiv]

omit [FiniteDimensional ℝ E] in
/-- The degree of an invertible continuous linear equivalence at any value is the
orientation sign `sign (det T)`. -/
theorem regularDegree_continuousLinearEquiv (T : E ≃L[ℝ] E) (y : E)
    (hfin : ((⇑T) ⁻¹' {y}).Finite) :
    regularDegree (⇑T) y hfin =
      ((SignType.sign (LinearMap.det (T : E →L[ℝ] E).toLinearMap) : SignType) : ℤ) := by
  have hdet : LinearMap.det (T : E →L[ℝ] E).toLinearMap ≠ 0 :=
    (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero
  unfold regularDegree
  have htf : hfin.toFinset = {T.symm y} := by
    ext z
    have hpre : (⇑T) ⁻¹' {y} = {T.symm y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx; rw [← hx, ContinuousLinearEquiv.symm_apply_apply]
      · intro hx; rw [hx, ContinuousLinearEquiv.apply_symm_apply]
    rw [Set.Finite.mem_toFinset, hpre, Finset.mem_singleton, Set.mem_singleton_iff]
  rw [htf, Finset.sum_singleton,
    show fderiv ℝ (⇑T) (T.symm y) = (T : E →L[ℝ] E) from
      (T : E →L[ℝ] E).fderiv]

omit [FiniteDimensional ℝ E] in
/-- The identity continuous linear map has nonzero (indeed `1`) determinant. -/
theorem det_id_ne_zero :
    LinearMap.det (ContinuousLinearMap.id ℝ E).toLinearMap ≠ 0 := by
  rw [show (ContinuousLinearMap.id ℝ E).toLinearMap = LinearMap.id from rfl, LinearMap.det_id]
  norm_num

/-- The identity map has regular degree `1`, recovered from the invertible-linear-map
degree at `T = id` (determinant `1`, sign `+1`). -/
theorem regularDegree_id' (y : E) :
    regularDegree (⇑(ContinuousLinearMap.id ℝ E)) y
      (finite_preimage_of_det_ne_zero (ContinuousLinearMap.id ℝ E) det_id_ne_zero y) = 1 := by
  rw [regularDegree_continuousLinearMap _ det_id_ne_zero,
    show (ContinuousLinearMap.id ℝ E).toLinearMap = LinearMap.id from rfl, LinearMap.det_id]
  rw [sign_pos (by norm_num : (0 : ℝ) < 1)]
  rfl

/-- **The degree of an invertible affine map.** Translating an invertible linear map by a
constant `b` does not change its degree: the derivative is still `T` everywhere and the
preimage is still a single point, so `regularDegree (x ↦ T x + b) y = sign (det T)`. -/
theorem regularDegree_affine (T : E →L[ℝ] E)
    (hdet : LinearMap.det T.toLinearMap ≠ 0) (b y : E)
    (hfin : ((fun x => T x + b) ⁻¹' {y}).Finite) :
    regularDegree (fun x => T x + b) y hfin =
      ((SignType.sign (LinearMap.det T.toLinearMap) : SignType) : ℤ) := by
  -- `x ↦ T x + b = (T x) + b`, with derivative `T` everywhere and a single preimage point.
  have hderiv : ∀ x : E, fderiv ℝ (fun x => T x + b) x = T := by
    intro x
    rw [fderiv_add_const, T.fderiv]
  have hpre : (fun x => T x + b) ⁻¹' {y} = {(equivOfDetNeZero T hdet).symm (y - b)} := by
    have hpre' : (fun x => T x + b) ⁻¹' {y} = (⇑T) ⁻¹' {y - b} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx; rw [← hx]; abel
      · intro hx; rw [hx]; abel
    rw [hpre', preimage_singleton_of_det_ne_zero T hdet (y - b)]
  unfold regularDegree
  have htf : hfin.toFinset = {(equivOfDetNeZero T hdet).symm (y - b)} := by
    ext z
    rw [Set.Finite.mem_toFinset, hpre, Finset.mem_singleton, Set.mem_singleton_iff]
  rw [htf, Finset.sum_singleton, hderiv]

section OrientationReversing

/-- The negation `-id` of `EuclideanSpace ℝ (Fin 1)` has determinant `-1`: a single
coordinate is reflected, reversing orientation. -/
theorem det_neg_id_fin_one :
    LinearMap.det (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))).toLinearMap =
      (-1 : ℝ) := by
  have h : (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))).toLinearMap =
      (-1 : ℝ) • (LinearMap.id : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] _) := by
    ext x
    simp
  rw [h, LinearMap.det_smul, LinearMap.det_id, mul_one,
    finrank_euclideanSpace_fin]
  norm_num

/-- The negation `-id` of `EuclideanSpace ℝ (Fin 1)` is invertible (its determinant is
`-1 ≠ 0`). -/
theorem det_neg_id_fin_one_ne_zero :
    LinearMap.det (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))).toLinearMap ≠ 0 := by
  rw [det_neg_id_fin_one]; norm_num

/-- **The orientation-reversing degree `-1`.** The negation `-id` of
`EuclideanSpace ℝ (Fin 1)` reverses orientation (determinant `-1`), so its regular degree
at any value is `-1`. This is the first negative oriented degree value. -/
theorem regularDegree_neg_id_eq_neg_one (y : EuclideanSpace ℝ (Fin 1)) :
    regularDegree (⇑(-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))) y
      (finite_preimage_of_det_ne_zero _ det_neg_id_fin_one_ne_zero y) = -1 := by
  rw [regularDegree_continuousLinearMap _ det_neg_id_fin_one_ne_zero, det_neg_id_fin_one]
  rw [sign_neg (by norm_num : (-1 : ℝ) < 0)]
  rfl

end OrientationReversing

end CRNT

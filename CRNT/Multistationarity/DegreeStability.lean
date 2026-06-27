import CRNT.Multistationarity.DegreeAdditivity
import CRNT.Multistationarity.LinearDegree
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Local constancy of the regular-value degree in the value

The regular-value degree `regularDegree f y` and its localization `localDegree f y U` are
locally constant in the value `y` near a nondegenerate preimage point. This is the analytic
heart of well-definedness for the Brouwer degree: the signed count of solutions does not
change as the value moves through a neighbourhood of regular values.

The mechanism is the inverse function theorem. At a point `x₀` where `f` is `C¹` and the
derivative `Df x₀` is invertible (`det (Df x₀) ≠ 0`), `f` restricts to a homeomorphism `Φ`
of an open neighbourhood `U = Φ.source` of `x₀` onto an open neighbourhood of `f x₀`. For
`y` near `f x₀` the only solution of `f x = y` inside `U` is the local inverse `Φ.symm y`,
and the orientation sign `sign (det (Df (Φ.symm y)))` equals `sign (det (Df x₀))` because
`x ↦ det (Df x)` is continuous and `Φ.symm y → x₀`. Hence the local degree on `U` is the
constant `sign (det (Df x₀))` throughout a neighbourhood of `f x₀`.

* `eventually_sign_det_fderiv_eq` — the orientation sign `sign (det (Df x))` is locally
  constant near a nondegenerate point.
* `eventually_localInverse_sign_eq` — the orientation sign at the moving local solution
  `Φ.symm y` is eventually the sign at `x₀`.
* `eventually_preimage_inter_source_eq_singleton` — for `y` near `f x₀` the solutions of
  `f x = y` inside the neighbourhood `U` are exactly the single point `Φ.symm y`.
* `eventually_localDegree_eq` — **local constancy**: `localDegree f y U = sign (det (Df x₀))`
  for every `y` in a neighbourhood of `f x₀`, with `U` the inverse-function neighbourhood.
* `regularDegree_comp_continuousLinearMap` — **composition multiplicativity** in the linear
  case: `regularDegree (T ∘ U) = sign (det T) · sign (det U)`.

This module is `sorry`-free.
-/

namespace CRNT

open scoped Finset Topology Classical

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- The orientation sign `sign (det (Df x))` is locally constant near a point `x₀` where
`f` is `C¹` and `det (Df x₀) ≠ 0`: the determinant is continuous and nonzero at `x₀`, so
its sign is constant on a neighbourhood. -/
theorem eventually_sign_det_fderiv_eq (f : E → E) {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀)
    (hdet : LinearMap.det (fderiv ℝ f x₀).toLinearMap ≠ 0) :
    ∀ᶠ x in 𝓝 x₀,
      SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) =
        SignType.sign (LinearMap.det (fderiv ℝ f x₀).toLinearMap) := by
  have hcont : ContinuousAt (fun x => LinearMap.det (fderiv ℝ f x).toLinearMap) x₀ :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      (ContDiffAt.continuousAt_fderiv hf (by norm_num))
  rcases lt_trichotomy (LinearMap.det (fderiv ℝ f x₀).toLinearMap) 0 with h | h | h
  · filter_upwards [hcont.eventually_lt continuousAt_const (g := fun _ => (0 : ℝ)) h] with x hx
    rw [sign_neg hx, sign_neg h]
  · exact absurd h hdet
  · filter_upwards [continuousAt_const.eventually_lt hcont (f := fun _ => (0 : ℝ)) h] with x hx
    rw [sign_pos hx, sign_pos h]

/-- The continuous linear equivalence packaging the derivative `Df x₀` when it is
invertible, used to feed the inverse function theorem. Its underlying map is `Df x₀`. -/
noncomputable def fderivEquivOfDetNeZero (f : E → E) {x₀ : E}
    (hdet : LinearMap.det (fderiv ℝ f x₀).toLinearMap ≠ 0) : E ≃L[ℝ] E :=
  (fderiv ℝ f x₀).toContinuousLinearEquivOfDetNeZero hdet

omit [CompleteSpace E] in
theorem coe_fderivEquivOfDetNeZero (f : E → E) {x₀ : E}
    (hdet : LinearMap.det (fderiv ℝ f x₀).toLinearMap ≠ 0) :
    (fderivEquivOfDetNeZero f hdet : E →L[ℝ] E) = fderiv ℝ f x₀ :=
  (fderiv ℝ f x₀).coe_toContinuousLinearEquivOfDetNeZero hdet

omit [CompleteSpace E] in
/-- The strict Fréchet derivative of a `C¹` map at a nondegenerate point, expressed against
the invertible-equivalence packaging of `Df x₀`. This is the hypothesis the inverse function
theorem consumes. -/
theorem hasStrictFDerivAt_fderivEquiv (f : E → E) {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀)
    (hdet : LinearMap.det (fderiv ℝ f x₀).toLinearMap ≠ 0) :
    HasStrictFDerivAt f (fderivEquivOfDetNeZero f hdet : E →L[ℝ] E) x₀ :=
  (coe_fderivEquivOfDetNeZero f hdet) ▸ hf.hasStrictFDerivAt (by norm_num)

/-- The orientation sign at the moving local solution `Φ.symm y` of `f x = y` is eventually
the orientation sign at `x₀`: as `y → f x₀` the local inverse `Φ.symm y → x₀`, and the
orientation sign is continuous there. -/
theorem eventually_localInverse_sign_eq (f : E → E) {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀)
    (hdet : LinearMap.det (fderiv ℝ f x₀).toLinearMap ≠ 0) :
    ∀ᶠ y in 𝓝 (f x₀),
      SignType.sign (LinearMap.det
          (fderiv ℝ f
            ((hasStrictFDerivAt_fderivEquiv f hf hdet).localInverse f _ x₀ y)).toLinearMap) =
        SignType.sign (LinearMap.det (fderiv ℝ f x₀).toLinearMap) := by
  have hstrict := hasStrictFDerivAt_fderivEquiv f hf hdet
  have htend : Tendsto (hstrict.localInverse f _ x₀) (𝓝 (f x₀)) (𝓝 x₀) :=
    hstrict.localInverse_tendsto
  exact htend.eventually (eventually_sign_det_fderiv_eq f hf hdet)

/-- For `y` near `f x₀` the solutions of `f x = y` lying in the inverse-function
neighbourhood `U = Φ.source` are exactly the single point `Φ.symm y`. Existence is the
eventual right inverse `f (Φ.symm y) = y`; uniqueness is injectivity of `f` on the source. -/
theorem eventually_preimage_inter_source_eq_singleton (f : E → E) {x₀ : E}
    (hf : ContDiffAt ℝ 1 f x₀)
    (hdet : LinearMap.det (fderiv ℝ f x₀).toLinearMap ≠ 0) :
    ∀ᶠ y in 𝓝 (f x₀),
      f ⁻¹' {y} ∩ ((hasStrictFDerivAt_fderivEquiv f hf hdet).toOpenPartialHomeomorph f).source =
        ({(hasStrictFDerivAt_fderivEquiv f hf hdet).localInverse f _ x₀ y} : Set E) := by
  have hstrict := hasStrictFDerivAt_fderivEquiv f hf hdet
  set Φ := hstrict.toOpenPartialHomeomorph f with hΦ
  have hcoeΦ : (Φ : E → E) = f := hstrict.toOpenPartialHomeomorph_coe
  have hx₀U : x₀ ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hri : ∀ᶠ y in 𝓝 (f x₀), f (Φ.symm y) = y := by
    have := Φ.eventually_right_inverse' hx₀U
    simpa [hcoeΦ] using this
  have htgt : Φ.target ∈ 𝓝 (f x₀) := by
    refine Φ.open_target.mem_nhds ?_
    have := hstrict.image_mem_toOpenPartialHomeomorph_target
    simpa [hΦ] using this
  filter_upwards [hri, htgt] with y hry hyt
  have hsymmU : Φ.symm y ∈ Φ.source := Φ.map_target hyt
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨hry, hsymmU⟩, ?_⟩
  rintro x ⟨hxpre, hxU⟩
  have hfx : f x = y := hxpre
  -- `f x = y = f (Φ.symm y)` with both `x` and `Φ.symm y` in the source; `f` is injective there.
  have : Φ x = Φ (Φ.symm y) := by
    rw [hcoeΦ, hfx, hry]
  exact Φ.injOn hxU hsymmU this

/-- **Local constancy of the local degree in the value.** Near a point `x₀` where `f` is
`C¹` with `det (Df x₀) ≠ 0`, for every value `y` in a neighbourhood of `f x₀` whose preimage
is finite, the local degree of `f` at `y` on the inverse-function neighbourhood
`U = Φ.source` equals the orientation sign `sign (det (Df x₀))`. The local degree is the
single oriented count of the unique nearby solution `Φ.symm y`, whose orientation matches
that of `x₀`. -/
theorem eventually_localDegree_eq (f : E → E) {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀)
    (hdet : LinearMap.det (fderiv ℝ f x₀).toLinearMap ≠ 0) :
    ∀ᶠ y in 𝓝 (f x₀),
      ∀ (hfin : (f ⁻¹' {y}).Finite),
        localDegree f y hfin
            ((hasStrictFDerivAt_fderivEquiv f hf hdet).toOpenPartialHomeomorph f).source =
          ((SignType.sign (LinearMap.det (fderiv ℝ f x₀).toLinearMap) : SignType) : ℤ) := by
  have hstrict := hasStrictFDerivAt_fderivEquiv f hf hdet
  set Φ := hstrict.toOpenPartialHomeomorph f with hΦ
  set g := hstrict.localInverse f _ x₀ with hg
  filter_upwards [eventually_preimage_inter_source_eq_singleton f hf hdet,
    eventually_localInverse_sign_eq f hf hdet] with y hsing hsign
  intro hfin
  -- the filtered finset over the source is the singleton `{g y}`.
  unfold localDegree
  have hfilter : hfin.toFinset.filter (· ∈ Φ.source) = {g y} := by
    ext z
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hzpre, hzU⟩
      have : z ∈ ({g y} : Set E) := hsing ▸ ⟨hzpre, hzU⟩
      exact this
    · intro hz
      have : z ∈ f ⁻¹' {y} ∩ Φ.source := by rw [hsing]; exact hz
      exact ⟨this.1, this.2⟩
  rw [hfilter, Finset.sum_singleton, hsign]

section Composition

omit [CompleteSpace E] in
/-- **Composition multiplicativity, linear case.** The degree of a composite of invertible
continuous linear maps is the product of the degrees: `sign (det (T ∘ U)) = sign (det T) ·
sign (det U)`, by multiplicativity of the determinant. This is the linear shadow of the
chain rule `D(g ∘ f) = Dg ∘ Df`, which yields `det (D(g ∘ f)) = det (Dg) · det (Df)` and
hence multiplicativity of the oriented degree under composition. -/
theorem regularDegree_comp_continuousLinearMap (T U : E →L[ℝ] E)
    (hT : LinearMap.det T.toLinearMap ≠ 0) (hU : LinearMap.det U.toLinearMap ≠ 0) (y : E) :
    regularDegree (⇑(T.comp U)) y
        (finite_preimage_of_det_ne_zero (T.comp U)
          (by
            rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
            exact mul_ne_zero hT hU) y) =
      regularDegree (⇑T) y (finite_preimage_of_det_ne_zero T hT y) *
        regularDegree (⇑U) y (finite_preimage_of_det_ne_zero U hU y) := by
  have hcomp : LinearMap.det (T.comp U).toLinearMap ≠ 0 := by
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
    exact mul_ne_zero hT hU
  rw [regularDegree_continuousLinearMap (T.comp U) hcomp,
    regularDegree_continuousLinearMap T hT, regularDegree_continuousLinearMap U hU]
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, sign_mul]
  push_cast
  ring

end Composition

end CRNT

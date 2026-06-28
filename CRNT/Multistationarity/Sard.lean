import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Sard's theorem in equal dimension: critical values have measure zero

For a differentiable map `f : E → E` on a finite-dimensional real normed space carrying an additive
Haar measure, the set of **critical values** — the image of the critical set `{x | det (Df x) = 0}`
— has measure zero. In equal dimension this is the whole content of Sard's theorem for `C¹` maps: it
follows directly from the change-of-variables machinery, since where the derivative is singular the
local volume scaling degenerates, so the image of the singular set is null (Mathlib's
`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`). The high-codimension Sard theorem (smooth maps
between spaces of different dimension) is not needed here and is not developed.

This is the measure-theoretic input that lifts the regular-value topological degree to a degree for
arbitrary values: the critical values are negligible, so a regular value can be found near any value.

* `measure_image_critical_eq_zero` — the image of the critical set `{x | det (Df x) = 0}` is null.
* `measure_criticalValues_eq_zero` — the critical values `{y | ∃ x, f x = y ∧ det (Df x) = 0}` are
  null.

This module is `sorry`-free.
-/

namespace CRNT

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Sard's theorem in equal dimension (critical set).** The image under a differentiable map
`f : E → E` of its critical set `{x | det (Df x) = 0}` — the points where the derivative is
singular — has Haar measure zero. -/
theorem measure_image_critical_eq_zero (f : E → E) (hf : Differentiable ℝ f) :
    μ (f '' {x | (fderiv ℝ f x).det = 0}) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (f' := fun x => fderiv ℝ f x) μ
  · intro x _
    exact (hf x).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    exact hx

/-- **Sard's theorem in equal dimension (critical values).** The set of critical values of a
differentiable map `f : E → E` — the values attained at a point where `Df` is singular — has Haar
measure zero. Equivalently, almost every value is regular. -/
theorem measure_criticalValues_eq_zero (f : E → E) (hf : Differentiable ℝ f) :
    μ {y | ∃ x, f x = y ∧ (fderiv ℝ f x).det = 0} = 0 := by
  have hset : {y | ∃ x, f x = y ∧ (fderiv ℝ f x).det = 0}
      = f '' {x | (fderiv ℝ f x).det = 0} := by
    ext y
    simp only [mem_image, mem_setOf_eq]
    exact ⟨fun ⟨x, hfx, hdet⟩ => ⟨x, hdet, hfx⟩, fun ⟨x, hdet, hfx⟩ => ⟨x, hfx, hdet⟩⟩
  rw [hset]
  exact measure_image_critical_eq_zero μ f hf

end CRNT

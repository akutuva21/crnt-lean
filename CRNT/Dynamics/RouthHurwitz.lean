import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Roots

/-!
# The Routh–Hurwitz stability criterion in low degree

A real polynomial is **Hurwitz** when all of its complex roots lie in the open left
half-plane `{z : ℂ | z.re < 0}`. Such a polynomial is exactly the characteristic
polynomial of a linear system whose every mode decays, so the Hurwitz property is the
algebraic heart of linear asymptotic stability.

The Routh–Hurwitz criterion characterizes the Hurwitz property by sign conditions on
finitely many determinants formed from the coefficients. This module establishes the
criterion in the low-degree cases that are fully self-contained over `Mathlib`'s
polynomial and complex-analysis libraries:

* `CRNT.IsHurwitz` — the half-plane root predicate for a complex polynomial.
* `CRNT.hurwitz_quadratic_root_iff` — the **degree-2** criterion in root-predicate form:
  every solution of `z² + a₁z + a₀ = 0` lies in the open left half-plane iff `0 < a₁` and
  `0 < a₀`. Proved by exhibiting the two roots through a square root of the discriminant
  and reading off the real and imaginary parts.
* `CRNT.hurwitz_cubic_necessary` — the **degree-3** necessity direction: a Hurwitz monic
  real cubic `X³ + a₂X² + a₁X + a₀` satisfies the four Routh–Hurwitz conditions
  `0 < a₂`, `0 < a₁`, `0 < a₀`, and `a₀ < a₂ * a₁` (the determinant condition
  `Δ₂ = a₂a₁ − a₀ > 0`). Proved from the factorization over `ℂ` into one real root and a
  conjugate pair (or three real roots), with the symmetric-function identities finished by
  `nlinarith`.

The general-degree converse (positivity of all minors implies Hurwitz) and degree-3
sufficiency require Hurwitz-matrix / Hermite–Biehler machinery that `Mathlib` does not yet
provide, so they are out of scope here.

This module is **stable** and `sorry`-free. Depends on:
Mathlib.Algebra.QuadraticDiscriminant, Mathlib.Analysis.Complex.Polynomial.Basic,
Mathlib.Algebra.Polynomial.Splits, Mathlib.Algebra.Polynomial.Roots.
-/

namespace CRNT

open Polynomial Complex

/-- A complex polynomial is **Hurwitz** when every one of its roots lies in the open left
half-plane `{z | z.re < 0}`. For a real polynomial `q` one applies this to
`q.map (algebraMap ℝ ℂ)`. -/
def IsHurwitz (p : Polynomial ℂ) : Prop := ∀ z ∈ p.roots, z.re < 0

/-! ## Degree 2 -/

/-- **Routh–Hurwitz, degree 2.** Every root of the monic quadratic `z² + a₁z + a₀` with
real coefficients lies in the open left half-plane iff the two Routh–Hurwitz conditions
`0 < a₁` and `0 < a₀` hold. -/
theorem hurwitz_quadratic_root_iff (a₁ a₀ : ℝ) :
    (∀ z : ℂ, z * z + (a₁ : ℂ) * z + (a₀ : ℂ) = 0 → z.re < 0) ↔ 0 < a₁ ∧ 0 < a₀ := by
  constructor
  · intro h
    -- A complex square root `s` of the discriminant `a₁² − 4a₀`.
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = ((a₁ : ℂ) ^ 2 - 4 * (a₀ : ℂ)) :=
      Complex.isAlgClosed.exists_pow_nat_eq _ (by norm_num)
    -- The two roots given by the quadratic formula.
    set z₁ : ℂ := (-(a₁ : ℂ) + s) / 2 with hz₁
    set z₂ : ℂ := (-(a₁ : ℂ) - s) / 2 with hz₂
    have root₁ : z₁ * z₁ + (a₁ : ℂ) * z₁ + (a₀ : ℂ) = 0 := by
      rw [hz₁]; linear_combination (1 / 4 : ℂ) * hs
    have root₂ : z₂ * z₂ + (a₁ : ℂ) * z₂ + (a₀ : ℂ) = 0 := by
      rw [hz₂]; linear_combination (1 / 4 : ℂ) * hs
    have hr₁ : z₁.re < 0 := h z₁ root₁
    have hr₂ : z₂.re < 0 := h z₂ root₂
    -- Real and imaginary parts of the two roots.
    have re₁ : z₁.re = (-a₁ + s.re) / 2 := by simp [hz₁]
    have re₂ : z₂.re = (-a₁ - s.re) / 2 := by simp [hz₂]
    have im₁ : z₁.im = s.im / 2 := by simp [hz₁]
    have im₂ : z₂.im = -s.im / 2 := by simp [hz₂]
    rw [re₁] at hr₁; rw [re₂] at hr₂
    -- `a₁ > 0` from the sum of the real parts; `a₀ > 0` from the product of the roots.
    refine ⟨by linarith, ?_⟩
    -- `a₀ = Re(z₁ z₂) = Re z₁ · Re z₂ + (Im z₁)²` since `Im z₂ = −Im z₁`.
    have hprod : (a₀ : ℂ) = z₁ * z₂ := by
      rw [hz₁, hz₂]; linear_combination (1 / 4 : ℂ) * hs
    have hprodre : a₀ = z₁.re * z₂.re - z₁.im * z₂.im := by
      have := congrArg Complex.re hprod
      simpa [Complex.mul_re] using this
    rw [hprodre, re₁, re₂, im₁, im₂]
    have hRe : 0 < ((-a₁ + s.re) / 2) * ((-a₁ - s.re) / 2) :=
      mul_pos_of_neg_of_neg hr₁ hr₂
    nlinarith [sq_nonneg s.im, hRe]
  · rintro ⟨ha₁, ha₀⟩ z hz
    -- Split into real and imaginary parts of the equation `z² + a₁z + a₀ = 0`.
    have hre : z.re * z.re - z.im * z.im + a₁ * z.re + a₀ = 0 := by
      have := congrArg Complex.re hz
      simpa [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im] using this
    have him : 2 * (z.re * z.im) + a₁ * z.im = 0 := by
      have := congrArg Complex.im hz
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.zero_im] at this
      ring_nf at this ⊢
      linarith
    -- From the imaginary part, either `z.im = 0` or `2 z.re + a₁ = 0`.
    rcases mul_eq_zero.1 (by ring_nf; linarith [him] :
        z.im * (2 * z.re + a₁) = 0) with hzero | hzero
    · -- `z.im = 0`: `z` is a real root of a quadratic with positive coefficients.
      rw [hzero] at hre
      by_contra hge
      rw [not_lt] at hge
      nlinarith [hge, ha₁, ha₀, mul_nonneg hge hge]
    · -- `2 z.re + a₁ = 0`: `z.re = −a₁/2 < 0`.
      linarith [hzero, ha₁]

/-- **Routh–Hurwitz, degree 2 (polynomial form).** The monic complex quadratic
`X² + (a₁ : ℂ)X + (a₀ : ℂ)` built from real coefficients is Hurwitz iff `0 < a₁` and
`0 < a₀`. -/
theorem hurwitz_quadratic_iff (a₁ a₀ : ℝ) :
    IsHurwitz (X ^ 2 + C (a₁ : ℂ) * X + C (a₀ : ℂ)) ↔ 0 < a₁ ∧ 0 < a₀ := by
  have hne : (X ^ 2 + C (a₁ : ℂ) * X + C (a₀ : ℂ)) ≠ 0 := by
    intro hzero
    have hco : (X ^ 2 + C (a₁ : ℂ) * X + C (a₀ : ℂ)).coeff 2 = 1 := by
      simp [coeff_X_pow]
    rw [hzero] at hco; simp at hco
  rw [← hurwitz_quadratic_root_iff a₁ a₀]
  unfold IsHurwitz
  constructor
  · intro h z hz
    refine h z ?_
    rw [mem_roots hne, IsRoot.def]
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
    rw [← hz]; ring
  · intro h z hz
    rw [mem_roots hne, IsRoot.def] at hz
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X] at hz
    exact h z (by rw [← hz]; ring)

/-! ## Degree 3 -/

/-- The arithmetic core of degree-3 necessity. If a monic cubic factors over `ℂ` as
`(X − r₁)(X − r₂)(X − r₃)` with **real** Vieta coefficients
`a₂ = −(r₁ + r₂ + r₃)`, `a₁ = r₁r₂ + r₁r₃ + r₂r₃`, `a₀ = −r₁r₂r₃`, and the three roots
either are all real and negative, or consist of a negative real `r₁` and a conjugate pair
`r₂ = conj r₃` with negative real part, then the four Routh–Hurwitz conditions hold. The
two structural cases are isolated as `hurwitz_cubic_necessary_allReal` and
`hurwitz_cubic_necessary_conjPair`. -/
theorem hurwitz_cubic_necessary_allReal (r₁ r₂ r₃ a₂ a₁ a₀ : ℝ)
    (hr₁ : r₁ < 0) (hr₂ : r₂ < 0) (hr₃ : r₃ < 0)
    (e₂ : a₂ = -(r₁ + r₂ + r₃)) (e₁ : a₁ = r₁ * r₂ + r₁ * r₃ + r₂ * r₃)
    (e₀ : a₀ = -(r₁ * r₂ * r₃)) :
    0 < a₂ ∧ 0 < a₁ ∧ 0 < a₀ ∧ a₀ < a₂ * a₁ := by
  refine ⟨by rw [e₂]; linarith, ?_, ?_, ?_⟩
  · rw [e₁]; nlinarith [mul_pos_of_neg_of_neg hr₁ hr₂, mul_pos_of_neg_of_neg hr₁ hr₃,
      mul_pos_of_neg_of_neg hr₂ hr₃]
  · rw [e₀]
    nlinarith [mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hr₁ hr₂) hr₃]
  · rw [e₀, e₂, e₁]
    nlinarith [mul_pos_of_neg_of_neg hr₁ hr₂, mul_pos_of_neg_of_neg hr₁ hr₃,
      mul_pos_of_neg_of_neg hr₂ hr₃, mul_pos_of_neg_of_neg hr₁ hr₁,
      mul_pos_of_neg_of_neg hr₂ hr₂, mul_pos_of_neg_of_neg hr₃ hr₃,
      mul_pos (mul_pos_of_neg_of_neg hr₁ hr₁) (mul_pos_of_neg_of_neg hr₂ hr₃),
      mul_pos (mul_pos_of_neg_of_neg hr₂ hr₂) (mul_pos_of_neg_of_neg hr₁ hr₃),
      mul_pos (mul_pos_of_neg_of_neg hr₃ hr₃) (mul_pos_of_neg_of_neg hr₁ hr₂)]

/-- The conjugate-pair case of degree-3 necessity: a negative real root `r` together with a
conjugate pair `u, conj u` of negative real part. Writing `p = Re u` (`< 0`) and
`q = (Im u)²` (`≥ 0`), the Vieta coefficients of `(X − r)(X − u)(X − conj u)` are real and
the four Routh–Hurwitz conditions hold. -/
theorem hurwitz_cubic_necessary_conjPair (r p q a₂ a₁ a₀ : ℝ)
    (hr : r < 0) (hp : p < 0) (hq : 0 ≤ q)
    (e₂ : a₂ = -(r + 2 * p)) (e₁ : a₁ = 2 * r * p + (p ^ 2 + q))
    (e₀ : a₀ = -(r * (p ^ 2 + q))) :
    0 < a₂ ∧ 0 < a₁ ∧ 0 < a₀ ∧ a₀ < a₂ * a₁ := by
  have hpq : 0 < p ^ 2 + q := by nlinarith [sq_nonneg p, mul_pos_of_neg_of_neg hp hp, hq]
  refine ⟨by rw [e₂]; linarith, ?_, ?_, ?_⟩
  · rw [e₁]; nlinarith [mul_pos_of_neg_of_neg hr hp, hpq]
  · rw [e₀]; nlinarith [mul_neg_of_neg_of_pos hr hpq]
  · rw [e₀, e₂, e₁]
    nlinarith [mul_pos_of_neg_of_neg hr hp, hpq, mul_pos_of_neg_of_neg hr hr,
      mul_pos_of_neg_of_neg hp hp, sq_nonneg p, hq,
      mul_nonneg (le_of_lt (mul_pos_of_neg_of_neg hr hr)) hq,
      mul_nonneg (neg_nonneg.2 (le_of_lt hp)) hq,
      mul_pos (mul_pos_of_neg_of_neg hr hr) hpq]

/-- **Routh–Hurwitz, degree 3 (necessity).** Over `ℂ` a monic real cubic
`X³ + a₂X² + a₁X + a₀` splits into three roots `z₁, z₂, z₃` whose elementary symmetric
functions are the (real) coefficients: `a₂ = −(z₁ + z₂ + z₃)`, `a₁ = z₁z₂ + z₁z₃ + z₂z₃`,
`a₀ = −z₁z₂z₃`. Because the coefficients are real the multiset of roots is closed under
complex conjugation, so the roots are either all real or one real together with a
conjugate pair. In either configuration, if every root lies in the open left half-plane
then the four Routh–Hurwitz conditions hold:
`0 < a₂`, `0 < a₁`, `0 < a₀`, and the determinant condition `a₀ < a₂ * a₁`.

The structural dichotomy is supplied as `hstruct`; both of its cases reduce, after taking
real and imaginary parts of the Vieta identities, to the arithmetic cores
`hurwitz_cubic_necessary_allReal` and `hurwitz_cubic_necessary_conjPair`. -/
theorem hurwitz_cubic_necessary (z₁ z₂ z₃ : ℂ) (a₂ a₁ a₀ : ℝ)
    (hz₁ : z₁.re < 0) (hz₂ : z₂.re < 0) (hz₃ : z₃.re < 0)
    (e₂ : (a₂ : ℂ) = -(z₁ + z₂ + z₃))
    (e₁ : (a₁ : ℂ) = z₁ * z₂ + z₁ * z₃ + z₂ * z₃)
    (e₀ : (a₀ : ℂ) = -(z₁ * z₂ * z₃))
    (hstruct : (z₁.im = 0 ∧ z₂.im = 0 ∧ z₃.im = 0) ∨ (z₃ = (starRingEnd ℂ) z₂)) :
    0 < a₂ ∧ 0 < a₁ ∧ 0 < a₀ ∧ a₀ < a₂ * a₁ := by
  rcases hstruct with ⟨i₁, i₂, i₃⟩ | hconj
  · -- All three roots are real and negative.
    refine hurwitz_cubic_necessary_allReal z₁.re z₂.re z₃.re a₂ a₁ a₀ hz₁ hz₂ hz₃ ?_ ?_ ?_
    · have := congrArg Complex.re e₂
      simpa [Complex.add_re, Complex.neg_re, Complex.ofReal_re] using this
    · have := congrArg Complex.re e₁
      simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, i₁, i₂, i₃] at this
      linarith [this]
    · have := congrArg Complex.re e₀
      simp only [Complex.ofReal_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
        i₁, i₂, i₃] at this
      linarith [this]
  · -- `z₃ = conj z₂`: a negative real root `z₁` and a conjugate pair `z₂, conj z₂`.
    -- The real part of `z₂` is negative; set `p = z₂.re`, `q = (z₂.im)²`.
    subst hconj
    have hp : z₂.re < 0 := hz₂
    refine hurwitz_cubic_necessary_conjPair z₁.re z₂.re (z₂.im ^ 2) a₂ a₁ a₀ hz₁ hp
      (sq_nonneg _) ?_ ?_ ?_
    · -- `a₂ = -(z₁.re + 2 z₂.re)`.
      have := congrArg Complex.re e₂
      simp only [Complex.ofReal_re, Complex.add_re, Complex.neg_re, Complex.conj_re] at this
      linarith [this]
    · -- `a₁ = 2 z₁.re z₂.re + ((z₂.re)² + (z₂.im)²)`.
      have := congrArg Complex.re e₁
      simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re,
        Complex.conj_re, Complex.conj_im] at this
      ring_nf at this ⊢
      nlinarith [this]
    · -- `a₀ = -(z₁.re ((z₂.re)² + (z₂.im)²))`.
      have := congrArg Complex.re e₀
      simp only [Complex.ofReal_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im] at this
      ring_nf at this ⊢
      nlinarith [this]

end CRNT

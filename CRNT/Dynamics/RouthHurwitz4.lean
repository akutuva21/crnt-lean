import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Roots
import CRNT.Dynamics.Hurwitz

/-!
# Degree-4 Routh–Hurwitz necessity (Liénard–Chipart)

A real polynomial is **Hurwitz** when all of its complex roots lie in the open left
half-plane. For the monic real quartic `X⁴ + a₃X³ + a₂X² + a₁X + a₀` the Routh–Hurwitz
criterion is sharpened by the **Liénard–Chipart** theorem: instead of testing every Hurwitz
determinant, it suffices to test the coefficients `a₃, a₂, a₁, a₀` together with the single
third Hurwitz determinant `Δ₃`. This module establishes the *necessity* direction — the
quartic analogue of the cubic necessity in `CRNT.Dynamics.RouthHurwitz`.

* `CRNT.hurwitz_quartic_necessary_allReal` — necessity from four negative real roots.
* `CRNT.hurwitz_quartic_necessary_oneConjPair` — necessity from two negative real roots and
  one conjugate pair of negative real part.
* `CRNT.hurwitz_quartic_necessary_twoConjPair` — necessity from two conjugate pairs of
  negative real part.
* `CRNT.hurwitz_quartic_necessary` — the assembled necessity statement: a Hurwitz monic real
  quartic satisfies the five Liénard–Chipart conditions
  `0 < a₃`, `0 < a₂`, `0 < a₁`, `0 < a₀`, and `a₁² + a₃²a₀ < a₃a₂a₁` (the strict form of
  `Δ₃ > 0`). The real-coefficient conjugation dichotomy is supplied as `hstruct`.
* `CRNT.hurwitzDet_three_quartic` — the bridge identity
  `hurwitzDet a 4 3 _ = a 3 * a 2 * a 1 - a 1² - a 3² * a 0`, tying the third leading
  principal minor of the degree-4 Hurwitz matrix to the scalar Δ₃ condition.

The factored Liénard–Chipart identity for `Δ₃ = a₃a₂a₁ − a₁² − a₃²a₀` in the root
parameters is what makes the conjugate-pair cores tractable: for one conjugate pair (real
roots `r, s`, pair `p ± i√q`) it is `2p(r+s)((r+p)²+q)((s+p)²+q)`, and for two conjugate
pairs (`p ± i√q`, `u ± i√v`) it is `4pu(((p+u)²+q+v)² − 4qv)`, both manifestly nonnegative
under the left-half-plane sign hypotheses.

Depends on: CRNT.Dynamics.Hurwitz.
-/

namespace CRNT

open Polynomial Complex

/-! ## Degree-4 necessity cores -/

/-- Necessity core, all-real case. If the four real numbers `r₁, r₂, r₃, r₄` are negative
roots of the monic quartic `X⁴ + a₃X³ + a₂X² + a₁X + a₀` through the Vieta identities, then
the five Liénard–Chipart conditions hold. The determinant condition uses the factorization
`a₃a₂a₁ − a₁² − a₃²a₀ = ∏_{i<j}(rᵢ + rⱼ)`, a product of six negative sums. -/
theorem hurwitz_quartic_necessary_allReal (r₁ r₂ r₃ r₄ a₃ a₂ a₁ a₀ : ℝ)
    (hr₁ : r₁ < 0) (hr₂ : r₂ < 0) (hr₃ : r₃ < 0) (hr₄ : r₄ < 0)
    (e₃ : a₃ = -(r₁ + r₂ + r₃ + r₄))
    (e₂ : a₂ = r₁ * r₂ + r₁ * r₃ + r₁ * r₄ + r₂ * r₃ + r₂ * r₄ + r₃ * r₄)
    (e₁ : a₁ = -(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ + r₁ * r₃ * r₄ + r₂ * r₃ * r₄))
    (e₀ : a₀ = r₁ * r₂ * r₃ * r₄) :
    0 < a₃ ∧ 0 < a₂ ∧ 0 < a₁ ∧ 0 < a₀ ∧ a₁ ^ 2 + a₃ ^ 2 * a₀ < a₃ * a₂ * a₁ := by
  refine ⟨by rw [e₃]; linarith, ?_, ?_, ?_, ?_⟩
  · rw [e₂]; nlinarith [mul_pos_of_neg_of_neg hr₁ hr₂, mul_pos_of_neg_of_neg hr₁ hr₃,
      mul_pos_of_neg_of_neg hr₁ hr₄, mul_pos_of_neg_of_neg hr₂ hr₃,
      mul_pos_of_neg_of_neg hr₂ hr₄, mul_pos_of_neg_of_neg hr₃ hr₄]
  · rw [e₁]
    nlinarith [mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hr₁ hr₂) hr₃,
      mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hr₁ hr₂) hr₄,
      mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hr₁ hr₃) hr₄,
      mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hr₂ hr₃) hr₄]
  · rw [e₀]
    nlinarith [mul_pos (mul_pos_of_neg_of_neg hr₁ hr₂) (mul_pos_of_neg_of_neg hr₃ hr₄)]
  · -- `Δ₃ = ∏_{i<j}(rᵢ + rⱼ)`: six negative factors, product positive.
    have hfac : a₃ * a₂ * a₁ - (a₁ ^ 2 + a₃ ^ 2 * a₀)
        = (r₁ + r₂) * (r₁ + r₃) * (r₁ + r₄) * (r₂ + r₃) * (r₂ + r₄) * (r₃ + r₄) := by
      rw [e₃, e₂, e₁, e₀]; ring
    have h12 : r₁ + r₂ < 0 := by linarith
    have h13 : r₁ + r₃ < 0 := by linarith
    have h14 : r₁ + r₄ < 0 := by linarith
    have h23 : r₂ + r₃ < 0 := by linarith
    have h24 : r₂ + r₄ < 0 := by linarith
    have h34 : r₃ + r₄ < 0 := by linarith
    have hpos : 0 < (r₁ + r₂) * (r₁ + r₃) * (r₁ + r₄) * (r₂ + r₃) * (r₂ + r₄) * (r₃ + r₄) := by
      have p1 : 0 < (r₁ + r₂) * (r₁ + r₃) := mul_pos_of_neg_of_neg h12 h13
      have p2 : 0 < (r₁ + r₄) * (r₂ + r₃) := mul_pos_of_neg_of_neg h14 h23
      have p3 : 0 < (r₂ + r₄) * (r₃ + r₄) := mul_pos_of_neg_of_neg h24 h34
      have := mul_pos (mul_pos p1 p2) p3
      nlinarith [this]
    linarith [hfac, hpos]

/-- Necessity core, one-conjugate-pair case. Two negative real roots `r, s` together with a
conjugate pair of real part `p` (`< 0`) and `q = (Im)² ≥ 0` parametrize the monic quartic
`X⁴ + a₃X³ + a₂X² + a₁X + a₀` through the Vieta identities. Then the five Liénard–Chipart
conditions hold; the determinant condition uses the factorization
`a₃a₂a₁ − a₁² − a₃²a₀ = 2p(r + s)((r + p)² + q)((s + p)² + q)`. -/
theorem hurwitz_quartic_necessary_oneConjPair (r s p q a₃ a₂ a₁ a₀ : ℝ)
    (hr : r < 0) (hs : s < 0) (hp : p < 0) (hq : 0 ≤ q)
    (e₃ : a₃ = -(r + s + 2 * p))
    (e₂ : a₂ = r * s + 2 * p * (r + s) + (p ^ 2 + q))
    (e₁ : a₁ = -(2 * p * r * s + (r + s) * (p ^ 2 + q)))
    (e₀ : a₀ = r * s * (p ^ 2 + q)) :
    0 < a₃ ∧ 0 < a₂ ∧ 0 < a₁ ∧ 0 < a₀ ∧ a₁ ^ 2 + a₃ ^ 2 * a₀ < a₃ * a₂ * a₁ := by
  have hpq : 0 < p ^ 2 + q := by nlinarith [mul_pos_of_neg_of_neg hp hp, hq]
  have hrs : 0 < r * s := mul_pos_of_neg_of_neg hr hs
  refine ⟨by rw [e₃]; linarith, ?_, ?_, ?_, ?_⟩
  · rw [e₂]
    nlinarith [hrs, mul_pos_of_neg_of_neg hp hr, mul_pos_of_neg_of_neg hp hs, hpq]
  · rw [e₁]
    nlinarith [mul_neg_of_neg_of_pos hp hrs, mul_neg_of_neg_of_pos (by linarith : r + s < 0) hpq]
  · rw [e₀]; exact mul_pos hrs hpq
  · -- `Δ₃ = 2p(r + s)((r + p)² + q)((s + p)² + q)`.
    have hfac : a₃ * a₂ * a₁ - (a₁ ^ 2 + a₃ ^ 2 * a₀)
        = 2 * p * (r + s) * ((r + p) ^ 2 + q) * ((s + p) ^ 2 + q) := by
      rw [e₃, e₂, e₁, e₀]; ring
    have hsum : r + s < 0 := by linarith
    have h2p : 2 * p < 0 := by linarith
    have hrp : 0 ≤ (r + p) ^ 2 + q := by positivity
    have hsp : 0 ≤ (s + p) ^ 2 + q := by positivity
    have hpos : 0 ≤ 2 * p * (r + s) * ((r + p) ^ 2 + q) * ((s + p) ^ 2 + q) := by
      have h1 : 0 < 2 * p * (r + s) := mul_pos_of_neg_of_neg h2p hsum
      have h2 : 0 ≤ ((r + p) ^ 2 + q) * ((s + p) ^ 2 + q) := mul_nonneg hrp hsp
      nlinarith [mul_nonneg (le_of_lt h1) h2]
    -- The product is in fact positive: the two real roots being distinct from `-p` is not
    -- needed; `2p(r+s) > 0` and the square-plus-`q` factors are `> 0` because `r+p < 0`
    -- (so `(r+p)² > 0`) — but `q` may be `0`. We only need `<`, so derive strict positivity
    -- of each `((·+p)²+q)` factor from the negativity of `·+p`.
    have hrp' : 0 < (r + p) ^ 2 + q := by nlinarith [sq_nonneg (r + p), mul_pos_of_neg_of_neg hr hr]
    have hsp' : 0 < (s + p) ^ 2 + q := by nlinarith [sq_nonneg (s + p), mul_pos_of_neg_of_neg hs hs]
    have hposlt : 0 < 2 * p * (r + s) * ((r + p) ^ 2 + q) * ((s + p) ^ 2 + q) := by
      have h1 : 0 < 2 * p * (r + s) := mul_pos_of_neg_of_neg h2p hsum
      have := mul_pos (mul_pos h1 hrp') hsp'
      nlinarith [this]
    linarith [hfac, hposlt]

/-- Necessity core, two-conjugate-pair case. Two conjugate pairs of real parts `p, u`
(both `< 0`) with `q = (Im)² ≥ 0`, `v = (Im)² ≥ 0` parametrize the monic quartic
`X⁴ + a₃X³ + a₂X² + a₁X + a₀` through the Vieta identities. Then the five Liénard–Chipart
conditions hold; the determinant condition uses the factorization
`a₃a₂a₁ − a₁² − a₃²a₀ = 4pu(((p + u)² + q + v)² − 4qv)`, nonnegative because `4pu > 0` and
`((p + u)² + q + v)² ≥ (q + v)² ≥ 4qv`. -/
theorem hurwitz_quartic_necessary_twoConjPair (p q u v a₃ a₂ a₁ a₀ : ℝ)
    (hp : p < 0) (hq : 0 ≤ q) (hu : u < 0) (hv : 0 ≤ v)
    (e₃ : a₃ = -(2 * p + 2 * u))
    (e₂ : a₂ = (p ^ 2 + q) + (u ^ 2 + v) + 4 * p * u)
    (e₁ : a₁ = -(2 * p * (u ^ 2 + v) + 2 * u * (p ^ 2 + q)))
    (e₀ : a₀ = (p ^ 2 + q) * (u ^ 2 + v)) :
    0 < a₃ ∧ 0 < a₂ ∧ 0 < a₁ ∧ 0 < a₀ ∧ a₁ ^ 2 + a₃ ^ 2 * a₀ < a₃ * a₂ * a₁ := by
  have hpq : 0 < p ^ 2 + q := by nlinarith [mul_pos_of_neg_of_neg hp hp, hq]
  have huv : 0 < u ^ 2 + v := by nlinarith [mul_pos_of_neg_of_neg hu hu, hv]
  have hpu : 0 < p * u := mul_pos_of_neg_of_neg hp hu
  refine ⟨by rw [e₃]; linarith, ?_, ?_, ?_, ?_⟩
  · rw [e₂]; nlinarith [hpq, huv, hpu]
  · rw [e₁]
    nlinarith [mul_neg_of_neg_of_pos hp huv, mul_neg_of_neg_of_pos hu hpq]
  · rw [e₀]; exact mul_pos hpq huv
  · -- `Δ₃ = 4pu(((p + u)² + q + v)² − 4qv)`.
    have hfac : a₃ * a₂ * a₁ - (a₁ ^ 2 + a₃ ^ 2 * a₀)
        = 4 * p * u * (((p + u) ^ 2 + q + v) ^ 2 - 4 * q * v) := by
      rw [e₃, e₂, e₁, e₀]; ring
    have h4pu : 0 < 4 * p * u := by nlinarith [hpu]
    -- `((p+u)²+q+v)² ≥ (q+v)² ≥ 4qv`, with strict from `(p+u)² > 0`.
    have hpu2 : 0 < (p + u) ^ 2 := by
      have h : p + u < 0 := by linarith
      have := mul_pos_of_neg_of_neg h h
      nlinarith [this]
    have hMpos : 0 < ((p + u) ^ 2 + q + v) ^ 2 - 4 * q * v := by
      nlinarith [hpu2, sq_nonneg (q - v), mul_nonneg hq hv, add_nonneg hq hv,
        mul_pos hpu2 (add_pos_of_pos_of_nonneg hpu2 (add_nonneg hq hv))]
    have hposlt : 0 < 4 * p * u * (((p + u) ^ 2 + q + v) ^ 2 - 4 * q * v) := mul_pos h4pu hMpos
    linarith [hfac, hposlt]

/-! ## Assembled degree-4 necessity -/

/-- **Routh–Hurwitz, degree 4 (Liénard–Chipart necessity).** Over `ℂ` a monic real quartic
`X⁴ + a₃X³ + a₂X² + a₁X + a₀` splits into four roots `z₁, z₂, z₃, z₄` whose elementary
symmetric functions are the (real) coefficients:
`a₃ = −(z₁ + z₂ + z₃ + z₄)`, `a₂ = ∑_{i<j} zᵢzⱼ`,
`a₁ = −∑_{i<j<k} zᵢzⱼz_k`, `a₀ = z₁z₂z₃z₄`. Because the coefficients are real the multiset of
roots is closed under conjugation, so the roots are all real, or two real with one conjugate
pair, or two conjugate pairs; this dichotomy is supplied as `hstruct`. If every root lies in
the open left half-plane then the five Liénard–Chipart conditions hold:
`0 < a₃`, `0 < a₂`, `0 < a₁`, `0 < a₀`, and the determinant condition
`a₁² + a₃²a₀ < a₃a₂a₁` (`Δ₃ > 0`).

The three structural cases reduce, after taking real parts of the Vieta identities, to the
arithmetic cores `hurwitz_quartic_necessary_{allReal,oneConjPair,twoConjPair}`. -/
theorem hurwitz_quartic_necessary (z₁ z₂ z₃ z₄ : ℂ) (a₃ a₂ a₁ a₀ : ℝ)
    (hz₁ : z₁.re < 0) (hz₂ : z₂.re < 0) (hz₃ : z₃.re < 0) (hz₄ : z₄.re < 0)
    (e₃ : (a₃ : ℂ) = -(z₁ + z₂ + z₃ + z₄))
    (e₂ : (a₂ : ℂ) = z₁ * z₂ + z₁ * z₃ + z₁ * z₄ + z₂ * z₃ + z₂ * z₄ + z₃ * z₄)
    (e₁ : (a₁ : ℂ) = -(z₁ * z₂ * z₃ + z₁ * z₂ * z₄ + z₁ * z₃ * z₄ + z₂ * z₃ * z₄))
    (e₀ : (a₀ : ℂ) = z₁ * z₂ * z₃ * z₄)
    (hstruct : (z₁.im = 0 ∧ z₂.im = 0 ∧ z₃.im = 0 ∧ z₄.im = 0)
      ∨ (z₂ = (starRingEnd ℂ) z₁ ∧ z₃.im = 0 ∧ z₄.im = 0)
      ∨ (z₂ = (starRingEnd ℂ) z₁ ∧ z₄ = (starRingEnd ℂ) z₃)) :
    0 < a₃ ∧ 0 < a₂ ∧ 0 < a₁ ∧ 0 < a₀ ∧ a₁ ^ 2 + a₃ ^ 2 * a₀ < a₃ * a₂ * a₁ := by
  rcases hstruct with ⟨i₁, i₂, i₃, i₄⟩ | ⟨hc, i₃, i₄⟩ | ⟨hc12, hc34⟩
  · -- All four roots are real and negative.
    refine hurwitz_quartic_necessary_allReal z₁.re z₂.re z₃.re z₄.re a₃ a₂ a₁ a₀
      hz₁ hz₂ hz₃ hz₄ ?_ ?_ ?_ ?_
    · have := congrArg Complex.re e₃
      simpa [Complex.add_re, Complex.neg_re, Complex.ofReal_re] using this
    · have := congrArg Complex.re e₂
      simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, i₁, i₂, i₃, i₄] at this
      linarith [this]
    · have := congrArg Complex.re e₁
      simp only [Complex.ofReal_re, Complex.neg_re, Complex.add_re, Complex.mul_re,
        Complex.mul_im, i₁, i₂, i₃, i₄] at this
      linarith [this]
    · have := congrArg Complex.re e₀
      simp only [Complex.ofReal_re, Complex.mul_re, Complex.mul_im, i₁, i₂, i₃, i₄] at this
      linarith [this]
  · -- `z₂ = conj z₁`, `z₃, z₄` real: real roots `z₃, z₄`, conjugate pair `z₁, conj z₁`.
    subst hc
    refine hurwitz_quartic_necessary_oneConjPair z₃.re z₄.re z₁.re (z₁.im ^ 2) a₃ a₂ a₁ a₀
      hz₃ hz₄ hz₁ (sq_nonneg _) ?_ ?_ ?_ ?_
    · have := congrArg Complex.re e₃
      simp only [Complex.ofReal_re, Complex.add_re, Complex.neg_re, Complex.conj_re] at this
      linarith [this]
    · have := congrArg Complex.re e₂
      simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re,
        Complex.conj_re, Complex.conj_im, i₃, i₄] at this
      ring_nf at this ⊢
      nlinarith [this]
    · have := congrArg Complex.re e₁
      simp only [Complex.ofReal_re, Complex.neg_re, Complex.add_re, Complex.mul_re,
        Complex.mul_im, Complex.conj_re, Complex.conj_im, i₃, i₄] at this
      ring_nf at this ⊢
      nlinarith [this]
    · have := congrArg Complex.re e₀
      simp only [Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, i₃, i₄] at this
      ring_nf at this ⊢
      nlinarith [this]
  · -- `z₂ = conj z₁`, `z₄ = conj z₃`: two conjugate pairs.
    subst hc12; subst hc34
    refine hurwitz_quartic_necessary_twoConjPair z₁.re (z₁.im ^ 2) z₃.re (z₃.im ^ 2) a₃ a₂ a₁ a₀
      hz₁ (sq_nonneg _) hz₃ (sq_nonneg _) ?_ ?_ ?_ ?_
    · have := congrArg Complex.re e₃
      simp only [Complex.ofReal_re, Complex.add_re, Complex.neg_re, Complex.conj_re] at this
      linarith [this]
    · have := congrArg Complex.re e₂
      simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re,
        Complex.conj_re, Complex.conj_im] at this
      ring_nf at this ⊢
      nlinarith [this]
    · have := congrArg Complex.re e₁
      simp only [Complex.ofReal_re, Complex.neg_re, Complex.add_re, Complex.mul_re,
        Complex.mul_im, Complex.conj_re, Complex.conj_im] at this
      ring_nf at this ⊢
      nlinarith [this]
    · have := congrArg Complex.re e₀
      simp only [Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im] at this
      ring_nf at this ⊢
      nlinarith [this]

/-! ## Hurwitz-determinant bridge -/

/-- Bridge identity. The third leading principal minor `Δ₃` of the degree-4 Hurwitz matrix of
the monic quartic `X⁴ + a₃X³ + a₂X² + a₁X + a₀` equals the scalar Liénard–Chipart
determinant `a 3 * a 2 * a 1 − a 1² − a 3² * a 0` used in `hurwitz_quartic_necessary`. -/
theorem hurwitzDet_three_quartic (a : ℕ → ℝ) :
    hurwitzDet a 4 3 (by norm_num) = a 3 * a 2 * a 1 - a 1 ^ 2 - a 3 ^ 2 * a 0 := by
  rw [hurwitzDet, Matrix.det_fin_three]
  simp only [Matrix.submatrix_apply, hurwitzMatrix, Matrix.of_apply, Fin.castLE,
    Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num [coeffDesc]
  ring

end CRNT

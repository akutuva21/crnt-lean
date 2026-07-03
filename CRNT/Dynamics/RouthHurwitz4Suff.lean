import CRNT.Dynamics.RouthHurwitz4

/-!
# Degree-4 Routh–Hurwitz sufficiency (Liénard–Chipart)

A real polynomial is **Hurwitz** when all of its complex roots lie in the open left
half-plane. For the monic real quartic `X⁴ + a₃X³ + a₂X² + a₁X + a₀` the Liénard–Chipart
form of the Routh–Hurwitz criterion tests the coefficients `a₃, a₂, a₁, a₀` together with the
single third Hurwitz determinant `Δ₃`. This module establishes the *sufficiency* direction —
the converse of the necessity in `CRNT.Dynamics.RouthHurwitz4` — and assembles the full
degree-4 criterion in root-predicate form.

* `CRNT.hurwitz_quartic_sufficient_allReal` — sufficiency from the five Liénard–Chipart sign
  conditions when all four roots are real.
* `CRNT.hurwitz_quartic_sufficient_oneConjPair` — sufficiency for two real roots and one
  conjugate pair.
* `CRNT.hurwitz_quartic_sufficient_twoConjPair` — sufficiency for two conjugate pairs.
* `CRNT.hurwitz_quartic_root_iff` — the **full degree-4 criterion** in root-predicate form:
  the five Liénard–Chipart conditions hold **iff** every root lies in the open left
  half-plane.

The all-real core is the value-positivity observation: a monic quartic with all five
descending coefficients positive is strictly positive at every `t ≥ 0`, hence has no
nonnegative real root. The conjugate-pair cores recover the negativity of the real roots the
same way, then read the sign of the real parts off the factored determinant condition
`Δ₃ = a₃a₂a₁ − a₁² − a₃²a₀`: `2p(r + s)((r + p)² + q)((s + p)² + q)` for one pair and
`4pu(((p + u)² + q + v)² − 4qv)` for two pairs.

Depends on: CRNT.Dynamics.RouthHurwitz4.
-/

namespace CRNT

open Polynomial Complex

/-! ## Degree-4 sufficiency cores -/

/-- Sufficiency core, all-real case. If the four real numbers `r₁, r₂, r₃, r₄` are the roots
of the monic quartic `X⁴ + a₃X³ + a₂X² + a₁X + a₀` through the Vieta identities, and the four
coefficient sign conditions `0 < a₃`, `0 < a₂`, `0 < a₁`, `0 < a₀` hold, then every root is
negative. The argument is value positivity: a monic quartic with all five descending
coefficients positive is strictly positive at every `t ≥ 0`, hence has no nonnegative
real root. -/
theorem hurwitz_quartic_sufficient_allReal (r₁ r₂ r₃ r₄ a₃ a₂ a₁ a₀ : ℝ)
    (e₃ : a₃ = -(r₁ + r₂ + r₃ + r₄))
    (e₂ : a₂ = r₁ * r₂ + r₁ * r₃ + r₁ * r₄ + r₂ * r₃ + r₂ * r₄ + r₃ * r₄)
    (e₁ : a₁ = -(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ + r₁ * r₃ * r₄ + r₂ * r₃ * r₄))
    (e₀ : a₀ = r₁ * r₂ * r₃ * r₄)
    (_H₃ : 0 < a₃) (_H₂ : 0 < a₂) (H₁ : 0 < a₁) (H₀ : 0 < a₀) :
    r₁ < 0 ∧ r₂ < 0 ∧ r₃ < 0 ∧ r₄ < 0 := by
  -- For a root `r` we have `r⁴ + a₃r³ + a₂r² + a₁r + a₀ = 0`. With all coefficients positive
  -- the left side is `> 0` whenever `r ≥ 0`, so each real root is negative.
  have ev : ∀ r : ℝ, (r = r₁ ∨ r = r₂ ∨ r = r₃ ∨ r = r₄) →
      r ^ 4 + a₃ * r ^ 3 + a₂ * r ^ 2 + a₁ * r + a₀ = 0 := by
    intro r hr
    rcases hr with h | h | h | h <;> subst h <;> rw [e₃, e₂, e₁, e₀] <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    have hge : 0 ≤ r₁ := le_of_not_gt h
    have := ev r₁ (Or.inl rfl)
    nlinarith [pow_nonneg hge 4, pow_nonneg hge 3, pow_nonneg hge 2, mul_nonneg H₁.le hge]
  · by_contra h
    have hge : 0 ≤ r₂ := le_of_not_gt h
    have := ev r₂ (Or.inr (Or.inl rfl))
    nlinarith [pow_nonneg hge 4, pow_nonneg hge 3, pow_nonneg hge 2, mul_nonneg H₁.le hge]
  · by_contra h
    have hge : 0 ≤ r₃ := le_of_not_gt h
    have := ev r₃ (Or.inr (Or.inr (Or.inl rfl)))
    nlinarith [pow_nonneg hge 4, pow_nonneg hge 3, pow_nonneg hge 2, mul_nonneg H₁.le hge]
  · by_contra h
    have hge : 0 ≤ r₄ := le_of_not_gt h
    have := ev r₄ (Or.inr (Or.inr (Or.inr rfl)))
    nlinarith [pow_nonneg hge 4, pow_nonneg hge 3, pow_nonneg hge 2, mul_nonneg H₁.le hge]

/-- Sufficiency core, one-conjugate-pair case. Two real roots `r, s` together with a
conjugate pair of real part `p` and `q = (Im)² ≥ 0` parametrize the monic quartic
`X⁴ + a₃X³ + a₂X² + a₁X + a₀` through the Vieta identities. Under the four coefficient sign
conditions and the determinant condition `a₁² + a₃²a₀ < a₃a₂a₁` every structural parameter is
negative: `r < 0`, `s < 0`, and `p < 0`. The real roots are forced negative by value
positivity; the real part `p` is forced negative by the factored determinant
`a₃a₂a₁ − a₁² − a₃²a₀ = 2p(r + s)((r + p)² + q)((s + p)² + q)`. -/
theorem hurwitz_quartic_sufficient_oneConjPair (r s p q a₃ a₂ a₁ a₀ : ℝ) (hq : 0 ≤ q)
    (e₃ : a₃ = -(r + s + 2 * p))
    (e₂ : a₂ = r * s + 2 * p * (r + s) + (p ^ 2 + q))
    (e₁ : a₁ = -(2 * p * r * s + (r + s) * (p ^ 2 + q)))
    (e₀ : a₀ = r * s * (p ^ 2 + q))
    (H₃ : 0 < a₃) (H₂ : 0 < a₂) (H₁ : 0 < a₁) (H₀ : 0 < a₀)
    (HΔ : a₁ ^ 2 + a₃ ^ 2 * a₀ < a₃ * a₂ * a₁) :
    r < 0 ∧ s < 0 ∧ p < 0 := by
  -- Value positivity forces the two real roots negative.
  have ev : ∀ t : ℝ, (t = r ∨ t = s) →
      t ^ 4 + a₃ * t ^ 3 + a₂ * t ^ 2 + a₁ * t + a₀ = 0 := by
    intro t ht
    rcases ht with h | h <;> subst h <;> rw [e₃, e₂, e₁, e₀] <;> ring
  have hr : r < 0 := by
    by_contra h
    have hge : 0 ≤ r := le_of_not_gt h
    have := ev r (Or.inl rfl)
    nlinarith [pow_nonneg hge 4, pow_nonneg hge 3, pow_nonneg hge 2, mul_nonneg H₁.le hge]
  have hs : s < 0 := by
    by_contra h
    have hge : 0 ≤ s := le_of_not_gt h
    have := ev s (Or.inr rfl)
    nlinarith [pow_nonneg hge 4, pow_nonneg hge 3, pow_nonneg hge 2, mul_nonneg H₁.le hge]
  refine ⟨hr, hs, ?_⟩
  -- `p < 0`: the determinant gap factors as `2p(r+s)((r+p)²+q)((s+p)²+q)`. With `p ≥ 0`,
  -- `2p ≥ 0` while `r+s < 0` and the square-plus-`q` factors are `≥ 0`, so the gap is `≤ 0`,
  -- contradicting the strict determinant condition.
  by_contra hp
  have hp0 : 0 ≤ p := le_of_not_gt hp
  have hsum : r + s < 0 := by linarith
  have key : a₃ * a₂ * a₁ - (a₁ ^ 2 + a₃ ^ 2 * a₀) ≤ 0 := by
    have hfac : a₃ * a₂ * a₁ - (a₁ ^ 2 + a₃ ^ 2 * a₀)
        = 2 * p * (r + s) * ((r + p) ^ 2 + q) * ((s + p) ^ 2 + q) := by
      rw [e₃, e₂, e₁, e₀]; ring
    rw [hfac]
    have hrp : 0 ≤ (r + p) ^ 2 + q := by positivity
    have hsp : 0 ≤ (s + p) ^ 2 + q := by positivity
    have h1 : 2 * p * (r + s) ≤ 0 := by nlinarith [mul_nonneg hp0 (neg_nonneg.mpr hsum.le)]
    nlinarith [mul_nonneg hrp hsp, mul_nonpos_of_nonpos_of_nonneg h1 (mul_nonneg hrp hsp)]
  linarith [HΔ, key]

/-- Sufficiency core, two-conjugate-pair case. Two conjugate pairs of real parts `p, u` with
`q = (Im)² ≥ 0`, `v = (Im)² ≥ 0` parametrize the monic quartic `X⁴ + a₃X³ + a₂X² + a₁X + a₀`
through the Vieta identities. Under the four coefficient sign conditions and the determinant
condition `a₁² + a₃²a₀ < a₃a₂a₁` both real parts are negative: `p < 0` and `u < 0`. From
`0 < a₃` the sum `p + u` is negative; the factor `((p + u)² + q + v)² − 4qv` is strictly
positive, so the factored determinant `4pu(((p + u)² + q + v)² − 4qv)` being positive forces
`pu > 0`, which together with `p + u < 0` gives `p < 0` and `u < 0`. -/
theorem hurwitz_quartic_sufficient_twoConjPair (p q u v a₃ a₂ a₁ a₀ : ℝ) (hq : 0 ≤ q)
    (hv : 0 ≤ v)
    (e₃ : a₃ = -(2 * p + 2 * u))
    (e₂ : a₂ = (p ^ 2 + q) + (u ^ 2 + v) + 4 * p * u)
    (e₁ : a₁ = -(2 * p * (u ^ 2 + v) + 2 * u * (p ^ 2 + q)))
    (e₀ : a₀ = (p ^ 2 + q) * (u ^ 2 + v))
    (H₃ : 0 < a₃) (_H₂ : 0 < a₂) (_H₁ : 0 < a₁) (_H₀ : 0 < a₀)
    (HΔ : a₁ ^ 2 + a₃ ^ 2 * a₀ < a₃ * a₂ * a₁) :
    p < 0 ∧ u < 0 := by
  -- From `0 < a₃ = -(2p + 2u)` the sum of real parts is negative.
  have hsum : p + u < 0 := by rw [e₃] at H₃; linarith
  -- The factor `((p+u)²+q+v)² − 4qv` is strictly positive: `((p+u)²+q+v)² ≥ (q+v)² ≥ 4qv`
  -- with strictness from `(p+u)² > 0`.
  have hpu2 : 0 < (p + u) ^ 2 := by
    have := mul_pos_of_neg_of_neg hsum hsum
    nlinarith [this]
  have hMpos : 0 < ((p + u) ^ 2 + q + v) ^ 2 - 4 * q * v := by
    nlinarith [hpu2, sq_nonneg (q - v), mul_nonneg hq hv, add_nonneg hq hv,
      mul_pos hpu2 (add_pos_of_pos_of_nonneg hpu2 (add_nonneg hq hv))]
  -- The determinant gap factors as `4pu · M`; with `M > 0` the strict condition forces `pu > 0`.
  have hfac : a₃ * a₂ * a₁ - (a₁ ^ 2 + a₃ ^ 2 * a₀)
      = 4 * p * u * (((p + u) ^ 2 + q + v) ^ 2 - 4 * q * v) := by
    rw [e₃, e₂, e₁, e₀]; ring
  have hgap : 0 < a₃ * a₂ * a₁ - (a₁ ^ 2 + a₃ ^ 2 * a₀) := by linarith [HΔ]
  rw [hfac] at hgap
  have hpu : 0 < p * u := by nlinarith [hgap, hMpos]
  -- `pu > 0 ∧ p + u < 0 ⟹ p < 0 ∧ u < 0`.
  constructor
  · by_contra h
    have hp0 : 0 ≤ p := le_of_not_gt h
    nlinarith [hpu, hsum, mul_nonneg hp0 (neg_nonneg.mpr (by linarith : u ≤ 0))]
  · by_contra h
    have hu0 : 0 ≤ u := le_of_not_gt h
    nlinarith [hpu, hsum, mul_nonneg hu0 (neg_nonneg.mpr (by linarith : p ≤ 0))]

/-! ## The full degree-4 root-predicate criterion -/

/-- **Routh–Hurwitz, degree 4 (Liénard–Chipart full criterion).** Over `ℂ` the monic real
quartic `X⁴ + a₃X³ + a₂X² + a₁X + a₀` splits as `z₁, z₂, z₃, z₄` with the (real) elementary
symmetric identities `a₃ = −(z₁ + z₂ + z₃ + z₄)`, `a₂ = ∑_{i<j} zᵢzⱼ`,
`a₁ = −∑_{i<j<k} zᵢzⱼz_k`, `a₀ = z₁z₂z₃z₄`. Because the coefficients are real the roots are
all real, two real with one conjugate pair, or two conjugate pairs; this dichotomy is the
hypothesis `hstruct`. Then the five Liénard–Chipart conditions `0 < a₃`, `0 < a₂`, `0 < a₁`,
`0 < a₀`, `a₁² + a₃²a₀ < a₃a₂a₁` hold **iff** every root lies in the open left half-plane.

The backward direction is `hurwitz_quartic_necessary`; the forward direction extracts the
real Vieta parameters and invokes the sufficiency cores. -/
theorem hurwitz_quartic_root_iff (z₁ z₂ z₃ z₄ : ℂ) (a₃ a₂ a₁ a₀ : ℝ)
    (e₃ : (a₃ : ℂ) = -(z₁ + z₂ + z₃ + z₄))
    (e₂ : (a₂ : ℂ) = z₁ * z₂ + z₁ * z₃ + z₁ * z₄ + z₂ * z₃ + z₂ * z₄ + z₃ * z₄)
    (e₁ : (a₁ : ℂ) = -(z₁ * z₂ * z₃ + z₁ * z₂ * z₄ + z₁ * z₃ * z₄ + z₂ * z₃ * z₄))
    (e₀ : (a₀ : ℂ) = z₁ * z₂ * z₃ * z₄)
    (hstruct : (z₁.im = 0 ∧ z₂.im = 0 ∧ z₃.im = 0 ∧ z₄.im = 0)
      ∨ (z₂ = (starRingEnd ℂ) z₁ ∧ z₃.im = 0 ∧ z₄.im = 0)
      ∨ (z₂ = (starRingEnd ℂ) z₁ ∧ z₄ = (starRingEnd ℂ) z₃)) :
    (0 < a₃ ∧ 0 < a₂ ∧ 0 < a₁ ∧ 0 < a₀ ∧ a₁ ^ 2 + a₃ ^ 2 * a₀ < a₃ * a₂ * a₁) ↔
      (z₁.re < 0 ∧ z₂.re < 0 ∧ z₃.re < 0 ∧ z₄.re < 0) := by
  constructor
  · rintro ⟨H₃, H₂, H₁, H₀, HΔ⟩
    rcases hstruct with ⟨i₁, i₂, i₃, i₄⟩ | ⟨hc, i₃, i₄⟩ | ⟨hc12, hc34⟩
    · -- All four roots are real; the real parts ARE the roots.
      have re₃ : a₃ = -(z₁.re + z₂.re + z₃.re + z₄.re) := by
        have := congrArg Complex.re e₃
        simpa [Complex.add_re, Complex.neg_re, Complex.ofReal_re] using this
      have re₂ : a₂ = z₁.re * z₂.re + z₁.re * z₃.re + z₁.re * z₄.re
          + z₂.re * z₃.re + z₂.re * z₄.re + z₃.re * z₄.re := by
        have := congrArg Complex.re e₂
        simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, i₁, i₂, i₃, i₄] at this
        linarith [this]
      have re₁ : a₁ = -(z₁.re * z₂.re * z₃.re + z₁.re * z₂.re * z₄.re
          + z₁.re * z₃.re * z₄.re + z₂.re * z₃.re * z₄.re) := by
        have := congrArg Complex.re e₁
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.add_re, Complex.mul_re,
          Complex.mul_im, i₁, i₂, i₃, i₄] at this
        linarith [this]
      have re₀ : a₀ = z₁.re * z₂.re * z₃.re * z₄.re := by
        have := congrArg Complex.re e₀
        simp only [Complex.ofReal_re, Complex.mul_re, Complex.mul_im, i₁, i₂, i₃, i₄] at this
        linarith [this]
      exact hurwitz_quartic_sufficient_allReal z₁.re z₂.re z₃.re z₄.re a₃ a₂ a₁ a₀
        re₃ re₂ re₁ re₀ H₃ H₂ H₁ H₀
    · -- `z₂ = conj z₁`, `z₃, z₄` real: real roots `z₃, z₄`, conjugate pair `z₁, conj z₁`.
      subst hc
      have re₃ : a₃ = -(z₃.re + z₄.re + 2 * z₁.re) := by
        have := congrArg Complex.re e₃
        simp only [Complex.ofReal_re, Complex.add_re, Complex.neg_re, Complex.conj_re] at this
        linarith [this]
      have re₂ : a₂ = z₃.re * z₄.re + 2 * z₁.re * (z₃.re + z₄.re)
          + (z₁.re ^ 2 + z₁.im ^ 2) := by
        have := congrArg Complex.re e₂
        simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re,
          Complex.conj_re, Complex.conj_im, i₃, i₄] at this
        ring_nf at this ⊢
        nlinarith [this]
      have re₁ : a₁ = -(2 * z₁.re * z₃.re * z₄.re
          + (z₃.re + z₄.re) * (z₁.re ^ 2 + z₁.im ^ 2)) := by
        have := congrArg Complex.re e₁
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.add_re, Complex.mul_re,
          Complex.mul_im, Complex.conj_re, Complex.conj_im, i₃, i₄] at this
        ring_nf at this ⊢
        nlinarith [this]
      have re₀ : a₀ = z₃.re * z₄.re * (z₁.re ^ 2 + z₁.im ^ 2) := by
        have := congrArg Complex.re e₀
        simp only [Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
          Complex.conj_re, Complex.conj_im, i₃, i₄] at this
        ring_nf at this ⊢
        nlinarith [this]
      obtain ⟨hz₃, hz₄, hp⟩ := hurwitz_quartic_sufficient_oneConjPair
        z₃.re z₄.re z₁.re (z₁.im ^ 2) a₃ a₂ a₁ a₀ (sq_nonneg _)
        re₃ re₂ re₁ re₀ H₃ H₂ H₁ H₀ HΔ
      refine ⟨hp, ?_, hz₃, hz₄⟩
      simpa [Complex.conj_re] using hp
    · -- `z₂ = conj z₁`, `z₄ = conj z₃`: two conjugate pairs.
      subst hc12; subst hc34
      have re₃ : a₃ = -(2 * z₁.re + 2 * z₃.re) := by
        have := congrArg Complex.re e₃
        simp only [Complex.ofReal_re, Complex.add_re, Complex.neg_re, Complex.conj_re] at this
        linarith [this]
      have re₂ : a₂ = (z₁.re ^ 2 + z₁.im ^ 2) + (z₃.re ^ 2 + z₃.im ^ 2)
          + 4 * z₁.re * z₃.re := by
        have := congrArg Complex.re e₂
        simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re,
          Complex.conj_re, Complex.conj_im] at this
        ring_nf at this ⊢
        nlinarith [this]
      have re₁ : a₁ = -(2 * z₁.re * (z₃.re ^ 2 + z₃.im ^ 2)
          + 2 * z₃.re * (z₁.re ^ 2 + z₁.im ^ 2)) := by
        have := congrArg Complex.re e₁
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.add_re, Complex.mul_re,
          Complex.mul_im, Complex.conj_re, Complex.conj_im] at this
        ring_nf at this ⊢
        nlinarith [this]
      have re₀ : a₀ = (z₁.re ^ 2 + z₁.im ^ 2) * (z₃.re ^ 2 + z₃.im ^ 2) := by
        have := congrArg Complex.re e₀
        simp only [Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
          Complex.conj_re, Complex.conj_im] at this
        ring_nf at this ⊢
        nlinarith [this]
      obtain ⟨hp, hu⟩ := hurwitz_quartic_sufficient_twoConjPair
        z₁.re (z₁.im ^ 2) z₃.re (z₃.im ^ 2) a₃ a₂ a₁ a₀ (sq_nonneg _) (sq_nonneg _)
        re₃ re₂ re₁ re₀ H₃ H₂ H₁ H₀ HΔ
      refine ⟨hp, ?_, hu, ?_⟩
      · simpa [Complex.conj_re] using hp
      · simpa [Complex.conj_re] using hu
  · rintro ⟨hz₁, hz₂, hz₃, hz₄⟩
    exact hurwitz_quartic_necessary z₁ z₂ z₃ z₄ a₃ a₂ a₁ a₀ hz₁ hz₂ hz₃ hz₄ e₃ e₂ e₁ e₀ hstruct

end CRNT

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith
import CRNT.Dynamics.RouthHurwitz

/-!
# Hurwitz matrices and the full degree-3 Routh–Hurwitz criterion

`CRNT.Dynamics.RouthHurwitz` establishes the *necessity* direction of the degree-3
Routh–Hurwitz criterion: a Hurwitz monic real cubic satisfies the four sign conditions
`0 < a₂`, `0 < a₁`, `0 < a₀`, `a₀ < a₂ * a₁`. This module supplies the missing *sufficiency*
direction at the arithmetic-core level and packages the two halves into a genuine
root-predicate `iff`. It also introduces the general Hurwitz-matrix and
Hurwitz-determinant objects and evaluates the low-degree leading principal minors.

The encoding fixes a real coefficient sequence `a : ℕ → ℝ` whose entries `a (n-1), …, a 0`
are the subleading coefficients of the monic degree-`n` polynomial
`Xⁿ + a (n-1) X^{n-1} + ⋯ + a 1 X + a 0` (the leading coefficient is `1`).

* `CRNT.hurwitz_cubic_sufficient_allReal` and `CRNT.hurwitz_cubic_sufficient_conjPair` —
  the converses of `hurwitz_cubic_necessary_{allReal,conjPair}`: the four sign conditions,
  together with the real Vieta parametrization, force every root into the open left
  half-plane (all-real case) or force the structural parameters `r, p` negative
  (conjugate-pair case).
* `CRNT.hurwitz_cubic_root_iff` — the **full degree-3 criterion** in root-predicate form:
  given the complex splitting Vieta identities and the real-coefficient conjugation
  dichotomy `hstruct`, the four Routh–Hurwitz conditions hold **iff** all three roots lie
  in the open left half-plane.
* `CRNT.hurwitzMatrix` / `CRNT.hurwitzDet` — the `n × n` Hurwitz matrix of a real
  coefficient sequence and its `k`-th leading principal minor determinant.
* `CRNT.hurwitzDet_two_cubic` — the bridge identity
  `hurwitzDet a 3 2 _ = a 2 * a 1 - a 0`, tying the `2 × 2` leading principal minor of the
  degree-3 Hurwitz matrix to the scalar determinant condition `a₀ < a₂ * a₁` used in
  `hurwitz_cubic_necessary`.

The general-degree converse (positivity of all `n` Hurwitz determinants implies Hurwitz)
needs Hermite–Biehler / Routh-array continued-fraction machinery absent from `Mathlib`, so
degree-4+ sufficiency and the `n`-dimensional criterion remain out of scope.

This module is **stable** and `sorry`-free. Depends on:
Mathlib.LinearAlgebra.Matrix.Determinant.Basic, Mathlib.Data.Matrix.Basic,
Mathlib.Tactic.FinCases, Mathlib.Tactic.Linarith, Mathlib.Tactic.Polyrith,
CRNT.Dynamics.RouthHurwitz.
-/

namespace CRNT

open Polynomial Complex

/-! ## Degree-3 sufficiency cores -/

/-- Sufficiency core, all-real case. If the three real numbers `r₁, r₂, r₃` are the roots
of the monic cubic `X³ + a₂X² + a₁X + a₀` through the Vieta identities, and the four
Routh–Hurwitz conditions `0 < a₂`, `0 < a₁`, `0 < a₀`, `a₀ < a₂ * a₁` hold, then every root
is negative. The argument is the value-positivity observation: a monic cubic with all four
descending coefficients positive is strictly positive at every `t ≥ 0`, hence has no
nonnegative real root. -/
theorem hurwitz_cubic_sufficient_allReal (r₁ r₂ r₃ a₂ a₁ a₀ : ℝ)
    (e₂ : a₂ = -(r₁ + r₂ + r₃)) (e₁ : a₁ = r₁ * r₂ + r₁ * r₃ + r₂ * r₃)
    (e₀ : a₀ = -(r₁ * r₂ * r₃))
    (H₂ : 0 < a₂) (H₁ : 0 < a₁) (H₀ : 0 < a₀) :
    r₁ < 0 ∧ r₂ < 0 ∧ r₃ < 0 := by
  -- For a root `r` we have `r³ + a₂r² + a₁r + a₀ = 0`. With all coefficients positive the
  -- left side is `> 0` whenever `r ≥ 0`, so each real root is negative.
  have ev : ∀ r : ℝ, (r = r₁ ∨ r = r₂ ∨ r = r₃) →
      r ^ 3 + a₂ * r ^ 2 + a₁ * r + a₀ = 0 := by
    intro r hr
    rcases hr with h | h | h <;> subst h <;> rw [e₂, e₁, e₀] <;> ring
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    have hge : 0 ≤ r₁ := le_of_not_gt h
    have := ev r₁ (Or.inl rfl)
    nlinarith [pow_nonneg hge 3, pow_nonneg hge 2, mul_nonneg (le_of_lt H₁) hge]
  · by_contra h
    have hge : 0 ≤ r₂ := le_of_not_gt h
    have := ev r₂ (Or.inr (Or.inl rfl))
    nlinarith [pow_nonneg hge 3, pow_nonneg hge 2, mul_nonneg (le_of_lt H₁) hge]
  · by_contra h
    have hge : 0 ≤ r₃ := le_of_not_gt h
    have := ev r₃ (Or.inr (Or.inr rfl))
    nlinarith [pow_nonneg hge 3, pow_nonneg hge 2, mul_nonneg (le_of_lt H₁) hge]

/-- Sufficiency core, conjugate-pair case. With a real root `r` and a conjugate pair of real
part `p` and `q = (Im)² ≥ 0` parametrizing the monic cubic `X³ + a₂X² + a₁X + a₀` through
the Vieta identities, the four Routh–Hurwitz conditions force both structural parameters
negative: `r < 0` and `p < 0`. -/
theorem hurwitz_cubic_sufficient_conjPair (r p q a₂ a₁ a₀ : ℝ) (hq : 0 ≤ q)
    (e₂ : a₂ = -(r + 2 * p)) (e₁ : a₁ = 2 * r * p + (p ^ 2 + q))
    (e₀ : a₀ = -(r * (p ^ 2 + q)))
    (_H₂ : 0 < a₂) (_H₁ : 0 < a₁) (H₀ : 0 < a₀) (HΔ : a₀ < a₂ * a₁) :
    r < 0 ∧ p < 0 := by
  have hpq : 0 < p ^ 2 + q := by
    rcases lt_or_eq_of_le hq with hqpos | hqzero
    · nlinarith [sq_nonneg p]
    · -- if `q = 0` and `p² + q = 0` then `a₀ = 0`, contradicting `H₀`.
      rcases lt_or_eq_of_le (by positivity : (0 : ℝ) ≤ p ^ 2 + q) with h | h
      · exact h
      · exfalso; rw [e₀, ← h] at H₀; simp at H₀
  -- `r < 0`: from `a₀ = -(r (p²+q)) > 0` and `p²+q > 0`.
  have hr : r < 0 := by
    rw [e₀] at H₀
    nlinarith [hpq, H₀]
  refine ⟨hr, ?_⟩
  -- `p < 0`: the determinant gap `a₂a₁ - a₀ > 0` equals `-2p (p²+q) - 2r² p - ...`
  -- arranged so that with `r < 0` and `p²+q > 0` positivity forces `p < 0`.
  by_contra hp
  have hp0 : 0 ≤ p := le_of_not_gt hp
  -- `a₂ * a₁ - a₀` with the substitutions; show it is `≤ 0` when `p ≥ 0`, contradicting `HΔ`.
  -- `a₂a₁ - a₀ = -2p · ((r+p)² + q)`, nonpositive when `p ≥ 0`.
  have key : a₂ * a₁ - a₀ ≤ 0 := by
    have hfac : a₂ * a₁ - a₀ = -2 * p * ((r + p) ^ 2 + q) := by rw [e₂, e₁, e₀]; ring
    rw [hfac]
    have hnn : 0 ≤ (r + p) ^ 2 + q := by positivity
    nlinarith [mul_nonneg hp0 hnn]
  linarith [HΔ, key]

/-! ## The full degree-3 root-predicate criterion -/

/-- **Routh–Hurwitz, degree 3 (full criterion).** Over `ℂ` the monic real cubic
`X³ + a₂X² + a₁X + a₀` splits as `z₁, z₂, z₃` with the (real) elementary symmetric
identities `a₂ = -(z₁ + z₂ + z₃)`, `a₁ = z₁z₂ + z₁z₃ + z₂z₃`, `a₀ = -z₁z₂z₃`. Because the
coefficients are real the roots are either all real or one real with a conjugate pair, which
is supplied as the dichotomy `hstruct`. Then the four Routh–Hurwitz conditions hold **iff**
every root lies in the open left half-plane.

The backward direction is `hurwitz_cubic_necessary`; the forward direction extracts the real
Vieta parameters and invokes the sufficiency cores. -/
theorem hurwitz_cubic_root_iff (z₁ z₂ z₃ : ℂ) (a₂ a₁ a₀ : ℝ)
    (e₂ : (a₂ : ℂ) = -(z₁ + z₂ + z₃))
    (e₁ : (a₁ : ℂ) = z₁ * z₂ + z₁ * z₃ + z₂ * z₃)
    (e₀ : (a₀ : ℂ) = -(z₁ * z₂ * z₃))
    (hstruct : (z₁.im = 0 ∧ z₂.im = 0 ∧ z₃.im = 0) ∨ (z₃ = (starRingEnd ℂ) z₂)) :
    (0 < a₂ ∧ 0 < a₁ ∧ 0 < a₀ ∧ a₀ < a₂ * a₁) ↔
      (z₁.re < 0 ∧ z₂.re < 0 ∧ z₃.re < 0) := by
  constructor
  · rintro ⟨H₂, H₁, H₀, HΔ⟩
    rcases hstruct with ⟨i₁, i₂, i₃⟩ | hconj
    · -- All three roots are real; the real parts ARE the roots.
      have re₂ : a₂ = -(z₁.re + z₂.re + z₃.re) := by
        have := congrArg Complex.re e₂
        simpa [Complex.add_re, Complex.neg_re, Complex.ofReal_re] using this
      have re₁ : a₁ = z₁.re * z₂.re + z₁.re * z₃.re + z₂.re * z₃.re := by
        have := congrArg Complex.re e₁
        simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, i₁, i₂, i₃] at this
        linarith [this]
      have re₀ : a₀ = -(z₁.re * z₂.re * z₃.re) := by
        have := congrArg Complex.re e₀
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
          i₁, i₂, i₃] at this
        linarith [this]
      exact hurwitz_cubic_sufficient_allReal z₁.re z₂.re z₃.re a₂ a₁ a₀ re₂ re₁ re₀ H₂ H₁ H₀
    · -- `z₃ = conj z₂`: real root `z₁`, conjugate pair `z₂, conj z₂`.
      subst hconj
      have re₂ : a₂ = -(z₁.re + 2 * z₂.re) := by
        have := congrArg Complex.re e₂
        simp only [Complex.ofReal_re, Complex.add_re, Complex.neg_re, Complex.conj_re] at this
        linarith [this]
      have re₁ : a₁ = 2 * z₁.re * z₂.re + (z₂.re ^ 2 + z₂.im ^ 2) := by
        have := congrArg Complex.re e₁
        simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re,
          Complex.conj_re, Complex.conj_im] at this
        ring_nf at this ⊢
        nlinarith [this]
      have re₀ : a₀ = -(z₁.re * (z₂.re ^ 2 + z₂.im ^ 2)) := by
        have := congrArg Complex.re e₀
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
          Complex.conj_re, Complex.conj_im] at this
        ring_nf at this ⊢
        nlinarith [this]
      obtain ⟨hz₁, hp⟩ := hurwitz_cubic_sufficient_conjPair z₁.re z₂.re (z₂.im ^ 2)
        a₂ a₁ a₀ (sq_nonneg _) re₂ re₁ re₀ H₂ H₁ H₀ HΔ
      -- `z₃.re = (conj z₂).re = z₂.re < 0`.
      refine ⟨hz₁, hp, ?_⟩
      simpa [Complex.conj_re] using hp
  · rintro ⟨hz₁, hz₂, hz₃⟩
    exact hurwitz_cubic_necessary z₁ z₂ z₃ a₂ a₁ a₀ hz₁ hz₂ hz₃ e₂ e₁ e₀ hstruct

/-! ## Hurwitz matrices and determinants -/

/-- The descending coefficient of the monic degree-`n` polynomial encoded by `a` at
descending index `k`: `k = 0` is the leading coefficient `1`, and `k = n - j` is the
subleading coefficient `a j`. Indices outside `0 ≤ k ≤ n` give `0`. -/
def coeffDesc (a : ℕ → ℝ) (n k : ℕ) : ℝ :=
  if k = 0 then 1 else if k ≤ n then a (n - k) else 0

/-- The `n × n` **Hurwitz matrix** of a real coefficient sequence `a`, encoding the monic
degree-`n` polynomial `Xⁿ + a (n-1) X^{n-1} + ⋯ + a 0`. The entry in row `i`, column `j`
(both `0`-indexed) is the descending coefficient at index `2 * i - j + 1`, with the standard
out-of-range `= 0` and leading-coefficient `= 1` conventions. -/
def hurwitzMatrix (a : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => coeffDesc a n (2 * i.val + 1 - j.val)

/-- The `k`-th **Hurwitz determinant** of the monic degree-`n` polynomial encoded by `a`:
the determinant of the leading `k × k` principal submatrix of the `n × n` Hurwitz matrix
(requires `k ≤ n`). The successive leading principal minors `hurwitzDet a n 1, …,
hurwitzDet a n n` are the quantities tested in the Routh–Hurwitz criterion. -/
def hurwitzDet (a : ℕ → ℝ) (n k : ℕ) (h : k ≤ n) : ℝ :=
  ((hurwitzMatrix a n).submatrix (Fin.castLE h) (Fin.castLE h)).det

@[simp] theorem coeffDesc_zero (a : ℕ → ℝ) (n : ℕ) : coeffDesc a n 0 = 1 := by
  simp [coeffDesc]

/-- The first leading principal minor of the degree-3 Hurwitz matrix is the subleading
coefficient `a 2` of the monic cubic `X³ + a₂X² + a₁X + a₀`. -/
theorem hurwitzDet_one_cubic (a : ℕ → ℝ) :
    hurwitzDet a 3 1 (by norm_num) = a 2 := by
  rw [hurwitzDet, Matrix.det_unique]
  simp [hurwitzMatrix, coeffDesc, Fin.castLE]

/-- Bridge identity. The second leading principal minor `Δ₂` of the degree-3 Hurwitz matrix
of the monic cubic `X³ + a₂X² + a₁X + a₀` equals the scalar determinant condition
`a 2 * a 1 - a 0` used in `hurwitz_cubic_necessary`. -/
theorem hurwitzDet_two_cubic (a : ℕ → ℝ) :
    hurwitzDet a 3 2 (by norm_num) = a 2 * a 1 - a 0 := by
  rw [hurwitzDet, Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, hurwitzMatrix, Matrix.of_apply, Fin.castLE,
    Fin.val_zero, Fin.val_one]
  norm_num [coeffDesc]

end CRNT

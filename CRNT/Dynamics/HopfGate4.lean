import Mathlib.Tactic.Linarith
import CRNT.Dynamics.RouthHurwitz4

/-!
# The degree-4 Hopf eigenvalue-crossing gate

For the monic real quartic `X⁴ + a₃X³ + a₂X² + a₁X + a₀` the Liénard–Chipart form of the
Routh–Hurwitz criterion (`CRNT.Dynamics.RouthHurwitz4`) tests the coefficients together with
the third Hurwitz determinant `Δ₃ = a₃a₂a₁ − a₁² − a₃²a₀`. The **boundary** of that Hurwitz
region where `Δ₃ = 0` (with the lower data positive) is the locus on which an eigenvalue pair
reaches the imaginary axis. This module characterizes that crossing.

* `CRNT.hopf_crossing_core_quartic` — the arithmetic core. With two conjugate pairs of real
  parts `p, u` and squared imaginary parts `q, v ≥ 0` parametrizing the quartic through the
  Vieta identities, the vanishing of `Δ₃` together with `0 < a₃`, `0 < a₀` forces exactly one
  pair onto the imaginary axis: either `p = 0` with `0 < q` (purely imaginary) and `u < 0`, or
  symmetrically `u = 0` with `0 < v` and `p < 0`. The argument rests on the factorization
  `a₃a₂a₁ − a₁² − a₃²a₀ = 4pu(((p + u)² + q + v)² − 4qv)`: the second factor is strictly
  positive, so `Δ₃ = 0` forces `pu = 0`.
* `CRNT.hopf_crossing_gate_quartic` — the eigenvalue-crossing gate over `ℂ`. For two conjugate
  pairs `z₁, conj z₁` and `z₃, conj z₃` whose elementary symmetric (Vieta) data are the real
  coefficients, vanishing of `Δ₃` with `0 < a₃`, `0 < a₀` puts one pair on the imaginary axis
  (`re = 0`, `im ≠ 0`) while the other stays in the open left half-plane.

This is the **algebraic** crossing condition only — the boundary of the Hurwitz region. The
dynamical Hopf bifurcation / limit-cycle existence statement requires center-manifold theory
that `Mathlib` does not provide and is out of scope.

Depends on: CRNT.Dynamics.RouthHurwitz4.
-/

namespace CRNT

open Complex

/-- Arithmetic core of the degree-4 Hopf crossing gate. Two conjugate pairs of real parts
`p, u` and squared imaginary parts `q = (Im)² ≥ 0`, `v = (Im)² ≥ 0` parametrize the monic
quartic `X⁴ + a₃X³ + a₂X² + a₁X + a₀` through the Vieta identities. The vanishing of the third
Hurwitz determinant, `a₁² + a₃²a₀ = a₃a₂a₁` (i.e. `Δ₃ = 0`), together with `0 < a₃` and
`0 < a₀`, puts exactly one conjugate pair on the imaginary axis: either `p = 0` with `0 < q`
and `u < 0`, or `u = 0` with `0 < v` and `p < 0`. The factorization
`a₃a₂a₁ − a₁² − a₃²a₀ = 4pu(((p + u)² + q + v)² − 4qv)` has a strictly positive second factor,
so `Δ₃ = 0` forces `pu = 0`. -/
theorem hopf_crossing_core_quartic (p q u v a₃ a₂ a₁ a₀ : ℝ) (hq : 0 ≤ q) (hv : 0 ≤ v)
    (e₃ : a₃ = -(2 * p + 2 * u)) (e₂ : a₂ = (p ^ 2 + q) + (u ^ 2 + v) + 4 * p * u)
    (e₁ : a₁ = -(2 * p * (u ^ 2 + v) + 2 * u * (p ^ 2 + q))) (e₀ : a₀ = (p ^ 2 + q) * (u ^ 2 + v))
    (H₃ : 0 < a₃) (H₀ : 0 < a₀) (HΔ : a₁ ^ 2 + a₃ ^ 2 * a₀ = a₃ * a₂ * a₁) :
    (p = 0 ∧ 0 < q ∧ u < 0) ∨ (u = 0 ∧ 0 < v ∧ p < 0) := by
  -- `p + u < 0` from `a₃ = -(2p + 2u) > 0`.
  have hsum : p + u < 0 := by rw [e₃] at H₃; linarith
  -- `(p + u)² > 0`.
  have hpu2 : 0 < (p + u) ^ 2 := by
    have := mul_pos_of_neg_of_neg hsum hsum
    nlinarith [this]
  -- The Liénard–Chipart second factor is strictly positive (necessity hint list, verbatim).
  have hMpos : 0 < ((p + u) ^ 2 + q + v) ^ 2 - 4 * q * v := by
    nlinarith [hpu2, sq_nonneg (q - v), mul_nonneg hq hv, add_nonneg hq hv,
      mul_pos hpu2 (add_pos_of_pos_of_nonneg hpu2 (add_nonneg hq hv))]
  -- `Δ₃ = 4pu·M`.
  have hfac : a₃ * a₂ * a₁ - (a₁ ^ 2 + a₃ ^ 2 * a₀)
      = 4 * p * u * (((p + u) ^ 2 + q + v) ^ 2 - 4 * q * v) := by
    rw [e₃, e₂, e₁, e₀]; ring
  -- `Δ₃ = 0` gives `4pu·M = 0`, and with `M > 0` we get `pu = 0`.
  have hzero : 4 * p * u * (((p + u) ^ 2 + q + v) ^ 2 - 4 * q * v) = 0 := by
    rw [← hfac]; linarith [HΔ]
  have hpu0 : p * u = 0 := by
    rcases mul_eq_zero.1 hzero with h | h
    · rcases mul_eq_zero.1 h with h2 | h2
      · norm_num at h2; nlinarith [h2]
      · nlinarith [h2]
    · exact absurd h (ne_of_gt hMpos)
  -- Case split on which real part vanishes.
  rcases mul_eq_zero.1 hpu0 with hp0 | hu0
  · -- `p = 0`: then `u < 0` (from `hsum`) and `0 < q` (from `0 < a₀ = (p² + q)(u² + v)`).
    left
    refine ⟨hp0, ?_, by rw [hp0] at hsum; linarith⟩
    -- `u² + v > 0` since `u < 0`.
    have hu : u < 0 := by rw [hp0] at hsum; linarith
    have huv : 0 < u ^ 2 + v := by nlinarith [mul_pos_of_neg_of_neg hu hu, hv]
    rw [e₀, hp0] at H₀
    nlinarith [H₀, huv]
  · -- `u = 0`: symmetric — `p < 0` and `0 < v`.
    right
    refine ⟨hu0, ?_, by rw [hu0] at hsum; linarith⟩
    have hp : p < 0 := by rw [hu0] at hsum; linarith
    have hpq : 0 < p ^ 2 + q := by nlinarith [mul_pos_of_neg_of_neg hp hp, hq]
    rw [e₀, hu0] at H₀
    nlinarith [H₀, hpq]

/-- **Degree-4 Hopf eigenvalue-crossing gate.** Consider the monic real quartic
`X⁴ + a₃X³ + a₂X² + a₁X + a₀` whose roots over `ℂ` are two conjugate pairs `z₁, conj z₁` and
`z₃, conj z₃` (the configuration of two eigenvalue pairs, one approaching the imaginary axis),
with the real elementary symmetric (Vieta) identities. If the third Hurwitz determinant
vanishes, `a₁² + a₃²a₀ = a₃a₂a₁` (`Δ₃ = 0`, the boundary of the Liénard–Chipart Hurwitz
region), while the lower data stay positive, `0 < a₃` and `0 < a₀`, then exactly one conjugate
pair is **purely imaginary** while the other stays in the open left half-plane: either
`z₁.re = 0` with `z₁.im ≠ 0` and `z₃.re < 0`, or `z₃.re = 0` with `z₃.im ≠ 0` and `z₁.re < 0`.

This is the algebraic crossing condition underlying a Hopf bifurcation. The accompanying
limit-cycle existence statement requires center-manifold theory that `Mathlib` does not provide
and is out of scope. -/
theorem hopf_crossing_gate_quartic (z₁ z₃ : ℂ) (a₃ a₂ a₁ a₀ : ℝ)
    (e₃ : (a₃ : ℂ) = -(z₁ + (starRingEnd ℂ) z₁ + z₃ + (starRingEnd ℂ) z₃))
    (e₂ : (a₂ : ℂ) = z₁ * (starRingEnd ℂ) z₁ + z₁ * z₃ + z₁ * (starRingEnd ℂ) z₃
      + (starRingEnd ℂ) z₁ * z₃ + (starRingEnd ℂ) z₁ * (starRingEnd ℂ) z₃ + z₃ * (starRingEnd ℂ) z₃)
    (e₁ : (a₁ : ℂ) = -(z₁ * (starRingEnd ℂ) z₁ * z₃ + z₁ * (starRingEnd ℂ) z₁ * (starRingEnd ℂ) z₃
      + z₁ * z₃ * (starRingEnd ℂ) z₃ + (starRingEnd ℂ) z₁ * z₃ * (starRingEnd ℂ) z₃))
    (e₀ : (a₀ : ℂ) = z₁ * (starRingEnd ℂ) z₁ * z₃ * (starRingEnd ℂ) z₃)
    (H₃ : 0 < a₃) (H₀ : 0 < a₀) (HΔ : a₁ ^ 2 + a₃ ^ 2 * a₀ = a₃ * a₂ * a₁) :
    (z₁.re = 0 ∧ z₁.im ≠ 0 ∧ z₃.re < 0) ∨ (z₃.re = 0 ∧ z₃.im ≠ 0 ∧ z₁.re < 0) := by
  -- Real-part extraction of the Vieta identities, in `(p, q, u, v) = (z₁.re, z₁.im², z₃.re, z₃.im²)`.
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
  -- Apply the arithmetic core and translate the disjuncts.
  rcases hopf_crossing_core_quartic z₁.re (z₁.im ^ 2) z₃.re (z₃.im ^ 2) a₃ a₂ a₁ a₀
    (sq_nonneg _) (sq_nonneg _) re₃ re₂ re₁ re₀ H₃ H₀ HΔ with
    ⟨hp, hq, hu⟩ | ⟨hu, hv, hp⟩
  · -- `z₁` purely imaginary, `z₃` in the open left half-plane.
    refine Or.inl ⟨hp, ?_, hu⟩
    intro him; rw [him] at hq; simp at hq
  · -- `z₃` purely imaginary, `z₁` in the open left half-plane.
    refine Or.inr ⟨hu, ?_, hp⟩
    intro him; rw [him] at hv; simp at hv

end CRNT

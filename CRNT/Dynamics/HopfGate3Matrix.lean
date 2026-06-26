import CRNT.Dynamics.Hurwitz3Matrix

/-!
# The spatial (3×3) Hopf eigenvalue-crossing gate from the characteristic polynomial

A real `3 × 3` matrix `M` is the linearization of a three-dimensional dynamical system, with
characteristic polynomial `X³ − (trace M) X² + (c₂Fin3 M) X − (det M)` over `ℂ`, where `c₂Fin3 M`
is the sum of the three principal `2 × 2` minors (`CRNT.Dynamics.Hurwitz3Matrix`). The boundary of
the cubic Routh–Hurwitz region, where the penultimate Hurwitz determinant vanishes
(`−det M = (−trace M)(c₂Fin3 M)`), is the locus on which an eigenvalue pair reaches the imaginary
axis. This module characterizes that crossing at the matrix level.

* `CRNT.hurwitz_matrix_fin_three_hopf_crossing` — the matrix Hopf eigenvalue-crossing gate. On the
  boundary `(−det M) = (−trace M)(c₂Fin3 M)` with the lower data positive — `0 < −trace M`,
  `0 < c₂Fin3 M`, `0 < −det M` — write the three eigenvalues over `ℂ` as a real eigenvalue `z₁`
  together with a conjugate pair `z₂, conj z₂`, supplied as roots of the complexified
  characteristic polynomial through the real elementary symmetric (Vieta) identities. Then the
  conjugate pair is purely imaginary — `z₂.re = 0`, `z₂.im ≠ 0`, with `z₂.im² = c₂Fin3 M` — and
  the real eigenvalue is strictly negative.
* `CRNT.massActionJacobian_fin_three_hopf_crossing` — the three-species mass-action specialization:
  a network whose Jacobian `N.massActionJacobian κ x` sits on this boundary admits the
  purely-imaginary conjugate eigenvalue pair, the algebraic precondition for a Hopf bifurcation.

The matrix-level gate feeds `Matrix.charpoly_fin_three` and the bridge
`CRNT.hurwitz_matrix_fin_three_charpoly` into the cubic crossing core `CRNT.hopf_crossing_gate`.
This is the algebraic crossing condition only — the boundary of the Hurwitz region. The dynamical
Hopf bifurcation / limit-cycle existence statement requires center-manifold theory that `Mathlib`
does not provide and is out of scope; see Guckenheimer & Holmes, "Nonlinear Oscillations,
Dynamical Systems, and Bifurcations of Vector Fields" for the analytic theorem, and the
Liénard–Chipart form of the Routh–Hurwitz criterion for the algebraic boundary.

This module is **stable** and `sorry`-free. Depends on: CRNT.Dynamics.Hurwitz3Matrix.
-/

namespace CRNT

open Matrix Polynomial Complex

/-- **Matrix Hopf eigenvalue-crossing gate (degree 3).** For a real `3 × 3` matrix `M` on the
boundary of the cubic Hurwitz region, `(−det M) = (−trace M)(c₂Fin3 M)` (the vanishing of the
penultimate Hurwitz determinant) with the lower data positive — `0 < −trace M`, `0 < c₂Fin3 M`,
`0 < −det M` — write the three eigenvalues over `ℂ` as a real eigenvalue `z₁` together with a
conjugate pair `z₂, conj z₂`, supplied as roots of the complexified characteristic polynomial with
the real elementary symmetric (Vieta) identities. Then the conjugate pair is **purely imaginary** —
`z₂.re = 0`, `z₂.im ≠ 0`, with `z₂.im² = c₂Fin3 M` — and the real eigenvalue is strictly negative,
`z₁.re < 0`.

This is the algebraic crossing condition (boundary of the Hurwitz region) underlying a Hopf
bifurcation; the limit-cycle existence statement needs center-manifold theory absent from `Mathlib`
and is out of scope. -/
theorem hurwitz_matrix_fin_three_hopf_crossing (M : Matrix (Fin 3) (Fin 3) ℝ) (z₁ z₂ : ℂ)
    (hz₁im : z₁.im = 0)
    (e₂ : (-M.trace : ℂ) = -(z₁ + z₂ + (starRingEnd ℂ) z₂))
    (e₁ : (M.c₂Fin3 : ℂ) = z₁ * z₂ + z₁ * ((starRingEnd ℂ) z₂) + z₂ * ((starRingEnd ℂ) z₂))
    (e₀ : (-M.det : ℂ) = -(z₁ * z₂ * ((starRingEnd ℂ) z₂)))
    (H₂ : 0 < -M.trace) (H₀ : 0 < -M.det) (HΔ : (-M.det) = (-M.trace) * M.c₂Fin3) :
    z₁.re < 0 ∧ z₂.re = 0 ∧ z₂.im ≠ 0 ∧ z₂.im ^ 2 = M.c₂Fin3 := by
  -- The Hopf cubic crossing core, on coefficients `(a₂, a₁, a₀) = (-trace, c₂Fin3, -det)`. The
  -- core's Vieta hypotheses carry the negation outside the coercion, `↑(-trace)` and `↑(-det)`.
  obtain ⟨hre1, hre2, him2⟩ :=
    hopf_crossing_gate z₁ z₂ (-M.trace) M.c₂Fin3 (-M.det) hz₁im
      (by push_cast; linear_combination e₂)
      e₁
      (by push_cast; linear_combination e₀)
      H₂ H₀ HΔ.symm
  refine ⟨hre1, hre2, him2, ?_⟩
  -- `z₂.im² = c₂Fin3`: take the real part of the `X¹` Vieta identity at `z₂.re = 0`, `z₁.im = 0`.
  have hreal := congrArg Complex.re e₁
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, hz₁im, hre2] at hreal
  ring_nf at hreal ⊢
  nlinarith [hreal]

/-- **Matrix Hopf eigenvalue-crossing gate for a three-species mass-action Jacobian.** With the
Jacobian `J = N.massActionJacobian κ x` of a three-species mass-action network on the boundary of
the cubic Hurwitz region, `(−det J) = (−trace J)(c₂Fin3 J)` with `0 < −trace J`, `0 < c₂Fin3 J`,
`0 < −det J`, and the eigenvalues over `ℂ` written as a real eigenvalue `z₁` together with a
conjugate pair `z₂, conj z₂` carrying the real Vieta identities, the conjugate pair is purely
imaginary (`z₂.re = 0`, `z₂.im ≠ 0`, `z₂.im² = c₂Fin3 J`) and the real eigenvalue is strictly
negative. This is the algebraic precondition for a Hopf bifurcation of the network at `x`. -/
theorem massActionJacobian_fin_three_hopf_crossing (N : Network (Fin 3)) (κ : N.RateConstants)
    (x : Concentration (Fin 3)) (z₁ z₂ : ℂ)
    (hz₁im : z₁.im = 0)
    (e₂ : (-(N.massActionJacobian κ x).trace : ℂ) = -(z₁ + z₂ + (starRingEnd ℂ) z₂))
    (e₁ : ((N.massActionJacobian κ x).c₂Fin3 : ℂ)
      = z₁ * z₂ + z₁ * ((starRingEnd ℂ) z₂) + z₂ * ((starRingEnd ℂ) z₂))
    (e₀ : (-(N.massActionJacobian κ x).det : ℂ) = -(z₁ * z₂ * ((starRingEnd ℂ) z₂)))
    (H₂ : 0 < -(N.massActionJacobian κ x).trace)
    (H₀ : 0 < -(N.massActionJacobian κ x).det)
    (HΔ : (-(N.massActionJacobian κ x).det)
      = (-(N.massActionJacobian κ x).trace) * (N.massActionJacobian κ x).c₂Fin3) :
    z₁.re < 0 ∧ z₂.re = 0 ∧ z₂.im ≠ 0
      ∧ z₂.im ^ 2 = (N.massActionJacobian κ x).c₂Fin3 :=
  hurwitz_matrix_fin_three_hopf_crossing (N.massActionJacobian κ x) z₁ z₂ hz₁im e₂ e₁ e₀ H₂ H₀ HΔ

end CRNT

import CRNT.Dynamics.HopfGate
import CRNT.Kinetics.MassActionJacobian
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The spatial (Routh–Hurwitz, degree 3) stability test from the characteristic polynomial

A real `3 × 3` matrix `M` is the linearization of a three-dimensional dynamical system, and its
characteristic polynomial over `ℂ` is `X³ − (trace M) X² + (c₂ M) X − (det M)`, where `c₂ M` is
the sum of the three principal `2 × 2` minors. The matrix is a stable linearization — every
eigenvalue lies in the open left half-plane — exactly when the degree-3 Routh–Hurwitz conditions
hold. For the monic cubic `X³ + a₂ X² + a₁ X + a₀` with `a₂ = −trace M`, `a₁ = c₂ M`,
`a₀ = −det M`, those conditions read `0 < a₂`, `0 < a₁`, `0 < a₀`, and `a₀ < a₂ a₁`. This is the
classical Routh–Hurwitz stability test in dimension three (Liénard–Chipart form).

This module ties four statements together:

* `Matrix.charpoly_fin_three` — the degree-3 characteristic-polynomial coefficient identity that
  `Mathlib` lacks: over any commutative ring, the characteristic polynomial of a `3 × 3` matrix is
  `X³ − C (trace M) X² + C (c₂ M) X − C (det M)`. Proved by expanding `det (charmatrix M)` with
  `Matrix.det_fin_three`.
* `CRNT.hurwitz_matrix_fin_three_charpoly` — the **characteristic-polynomial bridge**: a complex
  number `z` is a root of `(M.map (algebraMap ℝ ℂ)).charpoly` iff
  `z³ + (−trace M) z² + (c₂ M) z + (−det M) = 0`. This is what makes the criterion a genuine
  statement about eigenvalues rather than a restatement of the matrix invariants.
* `CRNT.hurwitz_matrix_fin_three_iff` — the Routh–Hurwitz criterion: the eigenvalue predicate
  (every root of the complexified characteristic polynomial is in the open left half-plane) holds
  iff `0 < −trace M`, `0 < c₂ M`, `0 < −det M`, and `−det M < (−trace M)(c₂ M)`. Obtained by
  binding the bridge to `CRNT.hurwitz_cubic_root_iff_coeff`.
* `CRNT.massActionJacobian_fin_three_hurwitz_iff` — a no-oscillation gate for a three-species
  mass-action Jacobian: the eigenvalue predicate for `N.massActionJacobian κ x` reduces to the four
  Routh–Hurwitz coefficient conditions on its trace, second invariant, and determinant.

The dynamical Hopf-bifurcation theorem (that loss of stability through a purely imaginary
eigenvalue pair produces an oscillation) is a separate analytic statement and stays out of scope
here.

This module is **stable** and `sorry`-free. Depends on: CRNT.Dynamics.HopfGate,
CRNT.Kinetics.MassActionJacobian.
-/

namespace Matrix

open Polynomial

/-- The second characteristic coefficient of a `3 × 3` matrix: the sum of its three principal
`2 × 2` minors. It is the coefficient of `X` in the characteristic polynomial. -/
def c₂Fin3 {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) : R :=
  (M 0 0 * M 1 1 - M 0 1 * M 1 0) + (M 0 0 * M 2 2 - M 0 2 * M 2 0) +
    (M 1 1 * M 2 2 - M 1 2 * M 2 1)

/-- **The degree-3 characteristic-polynomial coefficient identity.** Over any commutative ring the
characteristic polynomial of a `3 × 3` matrix `M` is
`X³ − C (trace M) X² + C (c₂Fin3 M) X − C (det M)`, where `c₂Fin3 M` is the sum of the three
principal `2 × 2` minors. The analogue of `Matrix.charpoly_fin_two` one dimension up. -/
theorem charpoly_fin_three {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    M.charpoly = X ^ 3 - C M.trace * X ^ 2 + C M.c₂Fin3 * X - C M.det := by
  rw [charpoly, det_fin_three]
  rw [charmatrix_apply_eq, charmatrix_apply_eq, charmatrix_apply_eq,
    charmatrix_apply_ne _ _ _ (by decide), charmatrix_apply_ne _ _ _ (by decide),
    charmatrix_apply_ne _ _ _ (by decide), charmatrix_apply_ne _ _ _ (by decide),
    charmatrix_apply_ne _ _ _ (by decide), charmatrix_apply_ne _ _ _ (by decide)]
  rw [trace_fin_three, det_fin_three, c₂Fin3]
  simp only [map_add, map_sub, map_mul]
  ring

end Matrix

namespace CRNT

open Matrix Polynomial Complex

/-- **The characteristic-polynomial bridge (degree 3).** A complex number `z` is a root of
`(M.map (algebraMap ℝ ℂ)).charpoly` iff `z³ + (−trace M) z² + (c₂Fin3 M) z + (−det M) = 0`. The
complexified characteristic polynomial is `X³ − C (trace M) X² + C (c₂Fin3 M) X − C (det M)`. -/
theorem hurwitz_matrix_fin_three_charpoly (M : Matrix (Fin 3) (Fin 3) ℝ) (z : ℂ) :
    (M.map (algebraMap ℝ ℂ)).charpoly.IsRoot z ↔
      z ^ 3 + (-M.trace : ℂ) * z ^ 2 + (M.c₂Fin3 : ℂ) * z + (-M.det : ℂ) = 0 := by
  have htr : (M.map (algebraMap ℝ ℂ)).trace = (M.trace : ℂ) :=
    (AddMonoidHom.map_trace (algebraMap ℝ ℂ) M).symm
  have hdet : (M.map (algebraMap ℝ ℂ)).det = (M.det : ℂ) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  have hc₂ : (M.map (algebraMap ℝ ℂ)).c₂Fin3 = (M.c₂Fin3 : ℂ) := by
    simp only [c₂Fin3, Matrix.map_apply, show ∀ r : ℝ, algebraMap ℝ ℂ r = (r : ℂ) from
      fun _ => rfl]
    push_cast
    ring
  rw [Matrix.charpoly_fin_three, htr, hdet, hc₂, IsRoot.def]
  simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X]
  constructor <;> intro h <;> linear_combination h

/-- **Routh–Hurwitz, degree 3 (matrix form).** A real `3 × 3` matrix has all three roots of its
characteristic polynomial (over `ℂ`) in the open left half-plane iff the four Routh–Hurwitz
coefficient conditions hold: `0 < −trace M`, `0 < c₂Fin3 M`, `0 < −det M`, and
`−det M < (−trace M)(c₂Fin3 M)`. -/
theorem hurwitz_matrix_fin_three_iff (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ z : ℂ, z ^ 3 + (-M.trace : ℂ) * z ^ 2 + (M.c₂Fin3 : ℂ) * z + (-M.det : ℂ) = 0 →
        z.re < 0) ↔
      (0 < -M.trace ∧ 0 < M.c₂Fin3 ∧ 0 < -M.det ∧ -M.det < (-M.trace) * M.c₂Fin3) := by
  set p := (M.map (algebraMap ℝ ℂ)).charpoly with hp
  -- The complexified characteristic polynomial is monic of degree 3; over `ℂ` it splits.
  have hmonic : p.Monic := charpoly_monic _
  have hdeg : p.natDegree = 3 := by rw [hp, charpoly_natDegree_eq_dim]; simp
  obtain ⟨z₁, z₂, z₃, hsplit⟩ :
      ∃ z₁ z₂ z₃ : ℂ, p = (X - C z₁) * (X - C z₂) * (X - C z₃) := by
    have hsplits : p.Splits := IsAlgClosed.splits p
    obtain ⟨l, hl⟩ := splits_iff_exists_multiset.1 hsplits
    rw [hmonic.leadingCoeff, map_one, one_mul] at hl
    have hcard : l.card = 3 := by
      have := congrArg Polynomial.natDegree hl
      rw [hdeg, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at this
      exact this.symm
    obtain ⟨z₁, z₂, z₃, rfl⟩ := Multiset.card_eq_three.1 hcard
    refine ⟨z₁, z₂, z₃, ?_⟩
    rw [hl]
    simp [Multiset.insert_eq_cons]
    ring
  -- Vieta: comparing the coefficient form with the split form yields the symmetric identities.
  have hcharpoly : p = X ^ 3 - C (M.trace : ℂ) * X ^ 2 + C (M.c₂Fin3 : ℂ) * X - C (M.det : ℂ) := by
    have htr : (M.map (algebraMap ℝ ℂ)).trace = (M.trace : ℂ) :=
      (AddMonoidHom.map_trace (algebraMap ℝ ℂ) M).symm
    have hdet : (M.map (algebraMap ℝ ℂ)).det = (M.det : ℂ) := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    have hc₂ : (M.map (algebraMap ℝ ℂ)).c₂Fin3 = (M.c₂Fin3 : ℂ) := by
      simp only [c₂Fin3, Matrix.map_apply, show ∀ r : ℝ, algebraMap ℝ ℂ r = (r : ℂ) from
        fun _ => rfl]
      push_cast; ring
    rw [hp, Matrix.charpoly_fin_three, htr, hdet, hc₂]
  have hexpand :
      X ^ 3 - C (M.trace : ℂ) * X ^ 2 + C (M.c₂Fin3 : ℂ) * X - C (M.det : ℂ) =
        X ^ 3 + C (-(z₁ + z₂ + z₃)) * X ^ 2 + C (z₁ * z₂ + z₁ * z₃ + z₂ * z₃) * X
          + C (-(z₁ * z₂ * z₃)) := by
    rw [← hcharpoly, hsplit]
    simp only [C_neg, C_add, C_mul]
    ring
  have ecoeff : (M.trace : ℂ) = z₁ + z₂ + z₃ ∧
      (M.c₂Fin3 : ℂ) = z₁ * z₂ + z₁ * z₃ + z₂ * z₃ ∧ (M.det : ℂ) = z₁ * z₂ * z₃ := by
    have h2 := congrArg (fun q => Polynomial.coeff q 2) hexpand
    have h1 := congrArg (fun q => Polynomial.coeff q 1) hexpand
    have h0 := congrArg (fun q => Polynomial.coeff q 0) hexpand
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X] at h2 h1 h0
    norm_num at h2 h1 h0
    refine ⟨by linear_combination -h2, by linear_combination h1, by linear_combination h0⟩
  obtain ⟨et, ec, ed⟩ := ecoeff
  -- Bind to the proven degree-3 coefficient criterion.
  have hcubic := hurwitz_cubic_root_iff_coeff z₁ z₂ z₃ (-M.trace) M.c₂Fin3 (-M.det)
    (by push_cast; linear_combination -et) (by linear_combination ec)
    (by push_cast; linear_combination -ed)
  -- The root predicate over `ℂ` is exactly the LHP conjunction on `z₁, z₂, z₃`.
  have hroots : (∀ z : ℂ, z ^ 3 + (-M.trace : ℂ) * z ^ 2 + (M.c₂Fin3 : ℂ) * z +
      (-M.det : ℂ) = 0 → z.re < 0) ↔ (z₁.re < 0 ∧ z₂.re < 0 ∧ z₃.re < 0) := by
    have hr : ∀ z : ℂ, (z ^ 3 + (-M.trace : ℂ) * z ^ 2 + (M.c₂Fin3 : ℂ) * z +
        (-M.det : ℂ) = 0) ↔ (z = z₁ ∨ z = z₂ ∨ z = z₃) := by
      intro z
      rw [← hurwitz_matrix_fin_three_charpoly M z]
      rw [show (M.map (algebraMap ℝ ℂ)).charpoly = p from rfl, hsplit, IsRoot.def]
      simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero]
      tauto
    constructor
    · intro h
      exact ⟨h z₁ ((hr z₁).2 (Or.inl rfl)), h z₂ ((hr z₂).2 (Or.inr (Or.inl rfl))),
        h z₃ ((hr z₃).2 (Or.inr (Or.inr rfl)))⟩
    · rintro ⟨h₁, h₂, h₃⟩ z hz
      rcases (hr z).1 hz with rfl | rfl | rfl <;> assumption
  rw [hroots, ← hcubic]

/-- **No-oscillation gate for a three-species mass-action Jacobian.** The eigenvalue predicate for
the mass-action Jacobian `N.massActionJacobian κ x` holds iff the four Routh–Hurwitz coefficient
conditions hold for its trace, second invariant, and determinant. -/
theorem massActionJacobian_fin_three_hurwitz_iff (N : Network (Fin 3)) (κ : N.RateConstants)
    (x : Concentration (Fin 3)) :
    (∀ z : ℂ, z ^ 3 + (-(N.massActionJacobian κ x).trace : ℂ) * z ^ 2 +
        ((N.massActionJacobian κ x).c₂Fin3 : ℂ) * z + (-(N.massActionJacobian κ x).det : ℂ) = 0 →
        z.re < 0) ↔
      (0 < -(N.massActionJacobian κ x).trace ∧ 0 < (N.massActionJacobian κ x).c₂Fin3 ∧
        0 < -(N.massActionJacobian κ x).det ∧
        -(N.massActionJacobian κ x).det <
          (-(N.massActionJacobian κ x).trace) * (N.massActionJacobian κ x).c₂Fin3) :=
  hurwitz_matrix_fin_three_iff _

end CRNT

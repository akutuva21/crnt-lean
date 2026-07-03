import CRNT.Dynamics.RouthHurwitz
import CRNT.Kinetics.MassActionJacobian
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The planar (trace–determinant) stability test from the characteristic polynomial

A real `2 × 2` matrix `M` is the linearization of a planar dynamical system, and its
characteristic polynomial over `ℂ` is `X² − (trace M) X + (det M)`. The matrix is a
stable linearization — every eigenvalue lies in the open left half-plane — exactly when the
degree-2 Routh–Hurwitz conditions hold. For the monic quadratic with first coefficient
`−trace M` and constant coefficient `det M`, those conditions read `trace M < 0` and
`0 < det M`. This is the classical planar **trace–determinant** stability test.

This module ties three statements together:

* `CRNT.hurwitz_matrix_fin_two_iff` — the trace–determinant criterion: the eigenvalue
  predicate (every root of the complexified characteristic polynomial is in the open left
  half-plane) holds iff `trace M < 0` and `0 < det M`. Obtained from
  `CRNT.hurwitz_quadratic_root_iff` at `a₁ = −trace M`, `a₀ = det M`.
* `CRNT.hurwitz_matrix_fin_two_charpoly` — the **characteristic-polynomial bridge**:
  a complex number is a root of `(M.map (algebraMap ℝ ℂ)).charpoly` iff it satisfies
  `z² − (trace M) z + (det M) = 0`. This is what makes the criterion a genuine statement
  about eigenvalues rather than a restatement of the trace and determinant. Proved from
  `Matrix.charpoly_fin_two` together with the compatibility of trace and determinant with
  the scalar map `algebraMap ℝ ℂ`.
* `CRNT.massActionJacobian_fin_two_hurwitz_iff` — a no-oscillation gate for a two-species
  mass-action Jacobian: the eigenvalue predicate for `N.massActionJacobian κ x` reduces to
  `trace < 0` and `0 < det`.

The dynamical Hopf-bifurcation theorem (that loss of stability through a purely imaginary
eigenvalue pair produces an oscillation) is a separate analytic statement and stays out of
scope here. Degree `≥ 3` is likewise out of scope: `Mathlib` has no `charpoly_fin_three`,
and the higher Routh–Hurwitz sufficiency directions require Hurwitz-matrix machinery not
available.

Depends on: CRNT.Dynamics.RouthHurwitz,
CRNT.Kinetics.MassActionJacobian.
-/

namespace CRNT

open Matrix Polynomial Complex

/-- **Routh–Hurwitz, degree 2 (matrix form).** A real `2 × 2` matrix has both roots of its
characteristic polynomial (over `ℂ`) in the open left half-plane iff `trace < 0` and
`0 < det`. This is the planar trace–determinant stability test. -/
theorem hurwitz_matrix_fin_two_iff (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ z : ℂ, z * z + (-M.trace : ℂ) * z + (M.det : ℂ) = 0 → z.re < 0) ↔
      (M.trace < 0 ∧ 0 < M.det) := by
  rw [← Complex.ofReal_neg, hurwitz_quadratic_root_iff (-M.trace) M.det]
  constructor
  · rintro ⟨h, hd⟩; exact ⟨by linarith, hd⟩
  · rintro ⟨ht, hd⟩; exact ⟨by linarith, hd⟩

/-- **The characteristic-polynomial bridge.** The eigenvalue predicate is exactly "every root
of the complexified characteristic polynomial lies in the open left half-plane": a complex
number `z` is a root of `(M.map (algebraMap ℝ ℂ)).charpoly` iff
`z² − (trace M) z + (det M) = 0`. The complexified characteristic polynomial is
`X² − C (trace M) · X + C (det M)`. -/
theorem hurwitz_matrix_fin_two_charpoly (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    (M.map (algebraMap ℝ ℂ)).charpoly.IsRoot z ↔
      z * z + (-M.trace : ℂ) * z + (M.det : ℂ) = 0 := by
  have htr : (M.map (algebraMap ℝ ℂ)).trace = (M.trace : ℂ) :=
    (AddMonoidHom.map_trace (algebraMap ℝ ℂ) M).symm
  have hdet : (M.map (algebraMap ℝ ℂ)).det = (M.det : ℂ) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  rw [Matrix.charpoly_fin_two, htr, hdet, IsRoot.def]
  simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X]
  constructor <;> intro h <;> [linear_combination h; linear_combination h]

/-- **No-oscillation gate for a two-species mass-action Jacobian.** The eigenvalue predicate
for the planar mass-action Jacobian `N.massActionJacobian κ x` holds iff its trace is negative
and its determinant is positive — the trace–determinant stability test at the point `x`. -/
theorem massActionJacobian_fin_two_hurwitz_iff (N : Network (Fin 2)) (κ : N.RateConstants)
    (x : Concentration (Fin 2)) :
    (∀ z : ℂ, z * z + (-(N.massActionJacobian κ x).trace : ℂ) * z +
        ((N.massActionJacobian κ x).det : ℂ) = 0 → z.re < 0) ↔
      ((N.massActionJacobian κ x).trace < 0 ∧ 0 < (N.massActionJacobian κ x).det) :=
  hurwitz_matrix_fin_two_iff _

end CRNT

/-
Depends on: CRNT.Dynamics.RouthHurwitz, CRNT.Kinetics.MassActionJacobian.
-/

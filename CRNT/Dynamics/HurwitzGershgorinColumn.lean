import CRNT.Dynamics.HurwitzGershgorin
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The column form of the Gershgorin diagonal-dominance Hurwitz test

Gershgorin's circle theorem applies equally to the columns of a matrix, because a matrix and its
transpose have the same eigenvalues. The transpose `Aᵀ` is strictly row diagonally dominant exactly
when `A` is strictly column diagonally dominant, so the row test of `CRNT.Dynamics.HurwitzGershgorin`
transfers to a column criterion: if for every column `k` the diagonal real part plus the
off-diagonal column norm-sum is negative, `(A k k).re + ∑ i ≠ k, ‖A i k‖ < 0`, then every eigenvalue
of `Matrix.toLin' A` lies in the open left half-plane.

The bridge is `hasEigenvalue_transpose_iff`: `Aᵀ` and `A` share their characteristic polynomial, so
they have the same eigenvalues. Each statement here applies the corresponding row test of
`CRNT.Dynamics.HurwitzGershgorin` to `Aᵀ` and pulls the conclusion back to `A`.

* `CRNT.hurwitz_of_strict_col_diag_dominance` — the complex core.
* `CRNT.hurwitz_of_strict_col_diag_dominance_real` — the real-matrix version, on the
  complexification `A.map (algebraMap ℝ ℂ)`.
* `CRNT.massActionJacobian_hurwitz_of_strict_col_diag_dominance` — the all-dimension no-oscillation
  gate for a strictly column diagonally dominant mass-action Jacobian.

This is Gershgorin's circle theorem in its column form, read as a stability criterion. It is a
one-directional **sufficient** condition for the Hurwitz property: it can fail for matrices that are
nonetheless stable, so it is not a full Routh–Hurwitz equivalence. The dynamical Hopf-bifurcation
theorem is a separate analytic statement and stays out of scope here.

Depends on: `CRNT.Dynamics.HurwitzGershgorin`.
-/

namespace CRNT

open Matrix

/-- `Aᵀ` and `A` share their eigenvalues, because they have equal characteristic polynomials
(`(Aᵀ).charpoly = A.charpoly`). -/
theorem hasEigenvalue_transpose_iff {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (μ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' Aᵀ) μ ↔ Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    Matrix.charpoly_toLin', Matrix.charpoly_toLin', Matrix.charpoly_transpose]

/-- **Column-form Gershgorin diagonal-dominance Hurwitz test.** If every diagonal entry has negative
real part strictly exceeding (in magnitude) the column's off-diagonal norm-sum, i.e.
`(A k k).re + ∑ i ≠ k, ‖A i k‖ < 0` for all `k`, then every eigenvalue of `Matrix.toLin' A` lies in
the open left half-plane. This applies the row test to `Aᵀ`, whose rows are the columns of `A`, and
transfers the conclusion through `hasEigenvalue_transpose_iff`. -/
theorem hurwitz_of_strict_col_diag_dominance {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ)
    (h : ∀ k, (A k k).re + ∑ i ∈ Finset.univ.erase k, ‖A i k‖ < 0) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ.re < 0 := by
  intro μ hμ
  refine hurwitz_of_strict_diag_dominance Aᵀ ?_ μ ((hasEigenvalue_transpose_iff A μ).mpr hμ)
  intro k
  simpa only [Matrix.transpose_apply] using h k

/-- **Real-matrix column-form Gershgorin Hurwitz test.** If a real matrix is strictly column
diagonally dominant with negative diagonal, `A k k + ∑ i ≠ k, |A i k| < 0` for all `k`, then every
eigenvalue of its complexification `A.map (algebraMap ℝ ℂ)` lies in the open left half-plane. This
applies the real row test to `Aᵀ` and transfers the conclusion through the transpose spectrum
equality. -/
theorem hurwitz_of_strict_col_diag_dominance_real {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ)
    (h : ∀ k, A k k + ∑ i ∈ Finset.univ.erase k, |A i k| < 0) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0 := by
  intro μ hμ
  have hμT : Module.End.HasEigenvalue (Matrix.toLin' ((Aᵀ).map (algebraMap ℝ ℂ))) μ := by
    rw [Matrix.transpose_map]
    exact (hasEigenvalue_transpose_iff (A.map (algebraMap ℝ ℂ)) μ).mpr hμ
  refine hurwitz_of_strict_diag_dominance_real Aᵀ ?_ μ hμT
  intro k
  simpa only [Matrix.transpose_apply] using h k

/-- **All-dimension no-oscillation gate for a strictly column diagonally dominant mass-action
Jacobian.** If the mass-action Jacobian `N.massActionJacobian κ x` is strictly column diagonally
dominant with negative diagonal at the point `x`, then every eigenvalue of its complexification lies
in the open left half-plane: the linearization at `x` is Hurwitz. This is a one-directional
sufficient stability test valid in any number of species. -/
theorem massActionJacobian_hurwitz_of_strict_col_diag_dominance {S : Type} [DecidableEq S]
    [Fintype S] (N : Network S) (κ : N.RateConstants) (x : Concentration S)
    (h : ∀ k, (N.massActionJacobian κ x) k k +
        ∑ i ∈ Finset.univ.erase k, |(N.massActionJacobian κ x) i k| < 0) :
    ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toLin' ((N.massActionJacobian κ x).map (algebraMap ℝ ℂ))) μ → μ.re < 0 :=
  hurwitz_of_strict_col_diag_dominance_real _ h

end CRNT

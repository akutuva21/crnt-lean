import CRNT.Multistationarity.PMatrix
import CRNT.Multistationarity.PMatrixSchur
import CRNT.Multistationarity.PMatrixSignature

/-!
# Gale–Nikaido global univalence for P-matrix maps

The degree-free Gale–Nikaido theorem (Math. Ann. 159 (1965), 81–93): a `C¹` map whose Jacobian is a
P-matrix at every point of a rectangle is globally injective on that rectangle. The development
follows the original proof — Theorem 1 (a P-matrix reverses no nonnegative vector to nonpositive) →
Corollaries 1–2 (theorem-of-the-alternative consequences) → Theorem 3 (order-interval monotonicity,
by dimension induction) → Theorem 4 (univalence, by signature normalization) — and uses no topological
degree.

This module starts with the linear-algebra foundation. The reductions consume the committed P-matrix
API: principal-submatrix closure (`IsPMatrix.submatrix_isPMatrix`), signature-conjugation invariance
(`IsPMatrix.signatureConj`), and positivity of determinants/diagonals (`IsPMatrix.det_pos`,
`IsPMatrix.diag_pos`).

This module is **stable** and `sorry`-free. Depends on: `CRNT.Multistationarity.PMatrix`,
`CRNT.Multistationarity.PMatrixSchur`, `CRNT.Multistationarity.PMatrixSignature`.
-/

set_option linter.unusedSectionVars false

namespace Matrix

variable {n R : Type*}
variable [Fintype n] [DecidableEq n]
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **The transpose of a P-matrix is a P-matrix.** Each principal minor of `Mᵀ` is the transpose of
the corresponding principal minor of `M`, hence has the same (positive) determinant. -/
theorem IsPMatrix.transpose {M : Matrix n n R} (h : M.IsPMatrix) : Mᵀ.IsPMatrix := by
  intro s
  have hsub : Mᵀ.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))
      = (M.submatrix (fun i : s => (i : n)) (fun i : s => (i : n)))ᵀ := by
    rw [Matrix.transpose_submatrix]
  rw [hsub, Matrix.det_transpose]
  exact h s

end Matrix

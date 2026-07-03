import CRNT.Multistationarity.PMatrix

/-!
# P-matrices are invariant under signature conjugation

Conjugating a P-matrix `M` by a diagonal sign matrix `D = diagonal ε`, where every entry
`ε i ∈ {+1, -1}`, again yields a P-matrix. Since `D = D⁻¹` (`D² = 1`), the conjugate
`D * M * D = of (fun i j => ε i * M i j * ε j)` has the *same* principal minors as `M`: a
principal minor on an index set `s` picks up the factor `(∏_{i ∈ s} ε i)² = 1`, so it equals the
corresponding principal minor of `M`, which is positive.

This is the linear-algebraic step behind the coordinatewise `a < b` reduction in the inductive
Gale–Nikaido argument: replacing the map `F` by `D ∘ F ∘ D` flips chosen coordinate directions
while preserving the everywhere-P-matrix Jacobian hypothesis.

Depends on: `CRNT.Multistationarity.PMatrix`.
-/

set_option linter.unusedSectionVars false

namespace Matrix

variable {n R : Type*}
variable [Fintype n] [DecidableEq n]
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]

open scoped BigOperators

/-- **P-matrices are invariant under ±1 diagonal (signature) conjugation.** If `M` is a P-matrix and
`ε i ∈ {+1, -1}` for every index `i`, then the conjugate `of (fun i j => ε i * M i j * ε j)`
(i.e. `diagonal ε * M * diagonal ε`) is again a P-matrix. -/
theorem IsPMatrix.signatureConj {M : Matrix n n R} (h : M.IsPMatrix)
    {ε : n → R} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    (Matrix.of (fun i j => ε i * M i j * ε j)).IsPMatrix := by
  intro s
  -- The product of the signs over `s` squares to one.
  have hPP : (∏ i : s, ε (i : n)) * (∏ i : s, ε (i : n)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one ?_
    intro i _
    rcases hε (i : n) with h1 | h1 <;> rw [h1] <;> ring
  -- The conjugated principal submatrix is the signature conjugate of `M`'s principal submatrix.
  have hkey :
      (Matrix.of (fun i j => ε i * M i j * ε j)).submatrix
          (fun i : s => (i : n)) (fun i : s => (i : n))
        = Matrix.diagonal (fun a : s => ε (a : n))
            * M.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))
            * Matrix.diagonal (fun a : s => ε (a : n)) := by
    ext a b
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply, Matrix.of_apply]
  rw [hkey, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  -- The two sign-product factors cancel, leaving the (positive) principal minor of `M`.
  have key : ∀ d : R, 0 < d → 0 < (∏ i : s, ε (i : n)) * d * (∏ i : s, ε (i : n)) := by
    intro d hd
    have heq : (∏ i : s, ε (i : n)) * d * (∏ i : s, ε (i : n)) = d := by
      have e : (∏ i : s, ε (i : n)) * d * (∏ i : s, ε (i : n))
          = ((∏ i : s, ε (i : n)) * (∏ i : s, ε (i : n))) * d := by ring
      rw [e, hPP, one_mul]
    rw [heq]; exact hd
  exact key _ (h s)

end Matrix

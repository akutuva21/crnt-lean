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

/-- **The diagonal of `A⁻¹` is positive for a P-matrix.** `(A⁻¹) j j = (det A)⁻¹ · adjugate A j j`,
and `adjugate A j j` is the `(j,j)` principal minor (the cofactor sign is `+1`), itself a positive
P-matrix principal minor; `det A > 0`. -/
theorem IsPMatrix.inv_diag_pos {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsPMatrix) (j : Fin (n + 1)) : 0 < A⁻¹ j j := by
  have hdet : 0 < A.det := hA.det_pos
  have hadj : 0 < adjugate A j j := by
    rw [adjugate_fin_succ_eq_det_submatrix]
    have hsign : ((-1 : ℝ)) ^ ((j : ℕ) + (j : ℕ)) = 1 :=
      Even.neg_one_pow ⟨(j : ℕ), rfl⟩
    rw [hsign, one_mul]
    exact hA.submatrix_det_pos (Fin.succAbove_right_injective)
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact mul_pos (inv_pos.mpr hdet) hadj

/-- **Gale–Nikaido Theorem 1.** A P-matrix sends no nonnegative vector to a nonpositive one except
`0`: if `A` is a P-matrix, `x ≥ 0`, and `A *ᵥ x ≤ 0`, then `x = 0`. Proof by induction on dimension:
the column `b = A⁻¹ e₀` satisfies `A *ᵥ b = e₀` with positive diagonal entry `b 0`; the minimal ratio
`θ = minᵢ xᵢ/bᵢ` zeroes a coordinate `k` of `y = x − θ b` while keeping `y ≥ 0`, `A *ᵥ y ≤ 0`; deleting
`k` (a principal submatrix, again a P-matrix) and applying the inductive hypothesis forces `y = 0`,
whence `x = θ b`, `A *ᵥ x = θ e₀ ≤ 0` gives `θ = 0`, so `x = 0`. -/
theorem IsPMatrix.eq_zero_of_mulVec_nonpos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsPMatrix) {x : Fin n → ℝ} (hx : 0 ≤ x) (hAx : A *ᵥ x ≤ 0) : x = 0 := by
  induction n with
  | zero => funext i; exact i.elim0
  | succ m ih =>
    classical
    have hunit : IsUnit A.det := hA.det_ne_zero.isUnit
    set b : Fin (m + 1) → ℝ := fun i => A⁻¹ i 0 with hbdef
    have hAb : A *ᵥ b = Pi.single (0 : Fin (m + 1)) 1 := by
      funext i
      have h1 : (A *ᵥ b) i = (A * A⁻¹) i 0 := by
        simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, hbdef]
      rw [h1, mul_nonsing_inv A hunit]
      simp [Matrix.one_apply, Pi.single_apply]
    have hb0 : 0 < b 0 := hA.inv_diag_pos 0
    set S : Finset (Fin (m + 1)) := Finset.univ.filter (fun i => 0 < b i) with hSdef
    have hSne : S.Nonempty := ⟨0, by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ 0, hb0⟩⟩
    set θ : ℝ := S.inf' hSne (fun i => x i / b i) with hθdef
    have hθnn : 0 ≤ θ := by
      rw [hθdef, Finset.le_inf'_iff]
      intro i hi
      rw [hSdef, Finset.mem_filter] at hi
      exact div_nonneg (hx i) (le_of_lt hi.2)
    obtain ⟨k, hkS, hθk⟩ := S.exists_mem_eq_inf' hSne (fun i => x i / b i)
    rw [hSdef, Finset.mem_filter] at hkS
    have hbk : 0 < b k := hkS.2
    set y : Fin (m + 1) → ℝ := x - θ • b with hydef
    have hyk : y k = 0 := by
      have hbk' : b k ≠ 0 := ne_of_gt hbk
      rw [hydef]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [show θ = x k / b k from hθk, div_mul_cancel₀ (x k) hbk', sub_self]
    have hynn : 0 ≤ y := by
      intro i
      rw [Pi.zero_apply, hydef]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hxi : (0 : ℝ) ≤ x i := hx i
      by_cases hbi : 0 < b i
      · have hle : θ ≤ x i / b i := by
          rw [hθdef]
          exact Finset.inf'_le _ (by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hbi⟩)
        have hmul := (le_div_iff₀ hbi).mp hle
        linarith
      · rw [not_lt] at hbi
        have hmul : θ * b i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθnn hbi
        linarith
    have hAy : A *ᵥ y ≤ 0 := by
      intro i
      rw [Pi.zero_apply]
      have hexp : (A *ᵥ y) i = (A *ᵥ x) i - θ * (A *ᵥ b) i := by
        rw [hydef, Matrix.mulVec_sub, Matrix.mulVec_smul]
        simp [Pi.sub_apply, Pi.smul_apply]
      rw [hexp, hAb]
      have hAxi : (A *ᵥ x) i ≤ 0 := hAx i
      by_cases hi0 : i = 0
      · subst hi0; rw [Pi.single_eq_same, mul_one]; linarith [hθnn]
      · rw [Pi.single_eq_of_ne hi0, mul_zero, sub_zero]; exact hAxi
    have hÂP : (A.submatrix k.succAbove k.succAbove).IsPMatrix :=
      hA.submatrix_isPMatrix Fin.succAbove_right_injective
    set ŷ : Fin m → ℝ := fun i => y (k.succAbove i) with hŷdef
    have hŷnn : 0 ≤ ŷ := fun i => hynn (k.succAbove i)
    have hÂŷ : (A.submatrix k.succAbove k.succAbove) *ᵥ ŷ ≤ 0 := by
      intro i
      have heq : ((A.submatrix k.succAbove k.succAbove) *ᵥ ŷ) i = (A *ᵥ y) (k.succAbove i) := by
        simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, hŷdef]
        rw [Fin.sum_univ_succAbove (fun j => A (k.succAbove i) j * y j) k, hyk, mul_zero, zero_add]
      rw [heq]; exact hAy (k.succAbove i)
    have hŷ0 : ŷ = 0 := ih hÂP hŷnn hÂŷ
    have hy0 : y = 0 := by
      funext i
      rcases eq_or_ne i k with rfl | hik
      · exact hyk
      · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hik
        have hl := congrFun hŷ0 l
        rw [hŷdef] at hl
        exact hl
    have hxθb : x = θ • b := sub_eq_zero.mp (by rw [← hydef]; exact hy0)
    have hθ0 : θ = 0 := by
      have hAx0 : (A *ᵥ x) 0 ≤ 0 := hAx 0
      rw [hxθb, Matrix.mulVec_smul, hAb, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
        mul_one] at hAx0
      linarith [hθnn]
    rw [hxθb, hθ0, zero_smul]

end Matrix

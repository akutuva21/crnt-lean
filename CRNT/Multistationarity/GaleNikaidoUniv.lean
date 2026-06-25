import CRNT.Multistationarity.PMatrixUnivalence
import CRNT.Multistationarity.GaleNikaidoBox

/-!
# Gale–Nikaido global univalence: the analytic theorems

Building on the linear-algebra layer (`PMatrixUnivalence`: Theorem 1 and Corollaries 1–2) and the
`jacobianMatrix` bridge (`GaleNikaidoBox`), this module proves the two analytic Gale–Nikaido theorems:

* **Theorem 3** (order-interval monotonicity): a `C¹` map with a P-matrix Jacobian on a box has, for
  `a ≤ x` in the box with `F x ≤ F a`, only the solution `x = a`. By induction on dimension, via the
  isolation of `a` (`o(‖·‖)` differentiability + Corollary 1), a minimal counterexample, the
  strict-descent case (Corollary 2), and the boundary-coordinate face reduction (principal submatrix).
* **Theorem 4** (univalence): the unconditional box-Gale–Nikaido theorem `Set.InjOn F`, by signature
  normalization (`IsPMatrix.signatureConj`) reducing every collision to the ordered case of Theorem 3.

Depends on: `CRNT.Multistationarity.PMatrixUnivalence`, `CRNT.Multistationarity.GaleNikaidoBox`.
-/

namespace CRNT

open scoped BigOperators Matrix
open Asymptotics Filter Topology

/-- **Isolation step (Gale–Nikaido Theorem 3).** Near a point `a`, a `C¹` map whose Jacobian at `a`
is a P-matrix has no other point `z ≥ a` with `F z ≤ F a`: by Corollary 1 the linear part
`L (z − a)` has a component `≥ λ‖z−a‖`, which the `o(‖z−a‖)` remainder cannot cancel for small
`z − a`, forcing that component of `F z` strictly above `F a`. -/
theorem pmatrix_isolated {n : ℕ} {F : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    {L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)} {a : Fin (n + 1) → ℝ}
    (hF : HasFDerivAt F L a) (hL : (jacobianMatrix L).IsPMatrix) :
    ∃ δ > 0, ∀ z, a ≤ z → z ≠ a → ‖z - a‖ < δ → ¬ (F z ≤ F a) := by
  obtain ⟨lam, hlam, hbound⟩ := hL.exists_pos_le_mulVec
  have hlo : (fun z => F z - F a - L (z - a)) =o[𝓝 a] (fun z => z - a) := hF.isLittleO
  have hev := hlo.def (c := lam / 2) (by positivity)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  refine ⟨δ, hδ, fun z haz hzne hzδ hle => ?_⟩
  have hva : (0 : Fin (n + 1) → ℝ) ≤ z - a := sub_nonneg.mpr haz
  have hpos : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
  obtain ⟨i, hi⟩ := hbound (z - a) hva
  rw [jacobianMatrix_mulVec] at hi
  have hbnd : ‖F z - F a - L (z - a)‖ ≤ (lam / 2) * ‖z - a‖ := by
    have h := hball (y := z) (by rw [dist_eq_norm]; exact hzδ)
    simpa using h
  have hri : |(F z - F a - L (z - a)) i| ≤ (lam / 2) * ‖z - a‖ :=
    le_trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (F z - F a - L (z - a)) i) hbnd
  have hcomp : (F z) i - (F a) i = (L (z - a)) i + (F z - F a - L (z - a)) i := by
    simp only [Pi.sub_apply]; ring
  have hlb : (lam / 2) * ‖z - a‖ ≤ (F z) i - (F a) i := by
    rw [hcomp]
    have h2 : -((lam / 2) * ‖z - a‖) ≤ (F z - F a - L (z - a)) i := by
      have := abs_le.mp hri; linarith [this.1]
    linarith [hi]
  have : (F z) i ≤ (F a) i := hle i
  nlinarith [hlb, hpos, hlam]

/-- **The derivative of the `Fin.insertNth` embedding.** Holding coordinate `i` fixed at `c`,
`y ↦ Fin.insertNth i c y` has derivative `Δ ↦ Fin.insertNth i 0 Δ`. -/
theorem hasFDerivAt_insertNth {n : ℕ} (i : Fin (n + 1)) (c : ℝ) (y : Fin n → ℝ) :
    HasFDerivAt (fun w => (Fin.insertNth i c w : Fin (n + 1) → ℝ))
      (ContinuousLinearMap.pi
        (Fin.insertNth i (0 : (Fin n → ℝ) →L[ℝ] ℝ) (fun l => ContinuousLinearMap.proj l))) y := by
  rw [hasFDerivAt_pi']
  intro k
  refine Fin.succAboveCases i ?_ (fun l => ?_) k
  · simp only [ContinuousLinearMap.proj_pi, Fin.insertNth_apply_same]
    exact hasFDerivAt_const c y
  · simp only [ContinuousLinearMap.proj_pi, Fin.insertNth_apply_succAbove]
    exact hasFDerivAt_apply l y

/-- **Face Jacobian is a principal submatrix.** The reduced map obtained by holding coordinate `i`
fixed and dropping equation `i` has Jacobian equal to the principal submatrix of `jacobianMatrix L`
deleting row and column `i`. -/
theorem jacobianMatrix_face_eq_submatrix {n : ℕ}
    (L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) (i : Fin (n + 1)) :
    jacobianMatrix ((ContinuousLinearMap.pi (fun k : Fin n =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (i.succAbove k))).comp
      (L.comp (ContinuousLinearMap.pi
        (Fin.insertNth i (0 : (Fin n → ℝ) →L[ℝ] ℝ) (fun l => ContinuousLinearMap.proj l)))))
      = (jacobianMatrix L).submatrix i.succAbove i.succAbove := by
  set M := jacobianMatrix L with hMdef
  set DG := (ContinuousLinearMap.pi (fun k : Fin n =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (i.succAbove k))).comp
    (L.comp (ContinuousLinearMap.pi
      (Fin.insertNth i (0 : (Fin n → ℝ) →L[ℝ] ℝ) (fun l => ContinuousLinearMap.proj l)))) with hDGdef
  have hins : ∀ Δ : Fin n → ℝ,
      (ContinuousLinearMap.pi (Fin.insertNth i (0 : (Fin n → ℝ) →L[ℝ] ℝ)
        (fun l => ContinuousLinearMap.proj l))) Δ = (Fin.insertNth i (0 : ℝ) Δ : Fin (n + 1) → ℝ) := by
    intro Δ; funext k
    refine Fin.succAboveCases i ?_ (fun l => ?_) k
    · simp [ContinuousLinearMap.pi_apply, Fin.insertNth_apply_same]
    · simp [ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
        Fin.insertNth_apply_succAbove]
  apply Matrix.ext
  intro k l
  have hact : DG (Pi.single l 1) k = M (i.succAbove k) (i.succAbove l) := by
    simp only [hDGdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.proj_apply, hins]
    rw [← jacobianMatrix_mulVec, ← hMdef]
    have hsingle : (Fin.insertNth i (0 : ℝ) (Pi.single l 1) : Fin (n + 1) → ℝ)
        = Pi.single (i.succAbove l) 1 := by
      funext j
      refine Fin.succAboveCases i ?_ (fun m => ?_) j
      · rw [Fin.insertNth_apply_same, Pi.single_eq_of_ne (Fin.succAbove_ne i l).symm]
      · rw [Fin.insertNth_apply_succAbove]
        simp only [Pi.single_apply, (Fin.succAbove_right_injective (p := i)).eq_iff]
    rw [hsingle, Matrix.mulVec_single]
    simp
  rw [Matrix.submatrix_apply, ← hact, ← jacobianMatrix_mulVec]
  simp [Matrix.mulVec_single]

end CRNT


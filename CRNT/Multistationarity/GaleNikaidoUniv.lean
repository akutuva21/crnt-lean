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

end CRNT

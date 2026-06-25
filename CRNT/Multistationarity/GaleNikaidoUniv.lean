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

/-- **Descent step (Gale–Nikaido Theorem 3).** At a point `c` whose Jacobian is a P-matrix, Corollary
2 provides a direction `w ≥ 0`, `w ≠ 0` with `L w > 0` componentwise; moving against it
(`c − t w`) strictly decreases every component of `F` for small `t > 0`, so `F (c − t w) ≤ F c`. -/
theorem pmatrix_descent {n : ℕ} {F : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    {L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)} {c : Fin (n + 1) → ℝ}
    (hF : HasFDerivAt F L c) (hL : (jacobianMatrix L).IsPMatrix) :
    ∃ w : Fin (n + 1) → ℝ, 0 ≤ w ∧ w ≠ 0 ∧
      ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → F (c - t • w) ≤ F c := by
  obtain ⟨w, hwnn, hwpos⟩ := hL.exists_nonneg_mulVec_pos
  have hLw : ∀ i, 0 < (L w) i := by
    intro i; have := hwpos i; rwa [jacobianMatrix_mulVec] at this
  have hwne : w ≠ 0 := by
    intro h; have := hLw 0; rw [h, map_zero] at this; simp at this
  have hwpos' : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  set cmin : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i => (L w) i) with hcmin
  have hcminpos : 0 < cmin := by
    rw [hcmin, Finset.lt_inf'_iff]; intro i _; exact hLw i
  have hcminle : ∀ i, cmin ≤ (L w) i := fun i =>
    Finset.inf'_le _ (Finset.mem_univ i)
  have hlo : (fun z => F z - F c - L (z - c)) =o[𝓝 c] (fun z => z - c) := hF.isLittleO
  have hev := hlo.def (c := cmin / (2 * ‖w‖)) (by positivity)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ', hδ', hball⟩ := hev
  refine ⟨w, hwnn, hwne, δ' / ‖w‖, by positivity, fun t ht htδ => ?_⟩
  intro i
  have hzdist : dist (c - t • w) c < δ' := by
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    rw [lt_div_iff₀ hwpos'] at htδ; linarith [htδ]
  have hbnd : ‖F (c - t • w) - F c - L ((c - t • w) - c)‖ ≤ (cmin / (2 * ‖w‖)) * ‖(c - t • w) - c‖ :=
    hball hzdist
  rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hbnd
  have hri : |(F (c - t • w) - F c - L ((c - t • w) - c)) i| ≤ (cmin / (2 * ‖w‖)) * (t * ‖w‖) :=
    le_trans (by simpa [Real.norm_eq_abs] using
      norm_le_pi_norm (F (c - t • w) - F c - L ((c - t • w) - c)) i) hbnd
  have hLval : (L ((c - t • w) - c)) i = - (t * (L w) i) := by
    rw [sub_sub_cancel_left, map_neg, map_smul]; simp
  have hcomp : (F (c - t • w)) i - (F c) i
      = (L ((c - t • w) - c)) i + (F (c - t • w) - F c - L ((c - t • w) - c)) i := by
    simp only [Pi.sub_apply]; ring
  rw [show (F (c - t • w)) i = (F c) i + ((F (c - t • w)) i - (F c) i) by ring, hcomp, hLval]
  have hupper : (F (c - t • w) - F c - L ((c - t • w) - c)) i ≤ (cmin / (2 * ‖w‖)) * (t * ‖w‖) :=
    le_trans (le_abs_self _) hri
  have hsimp : (cmin / (2 * ‖w‖)) * (t * ‖w‖) = t * cmin / 2 := by
    field_simp
  have hkey : -(t * (L w) i) + (F (c - t • w) - F c - L ((c - t • w) - c)) i ≤ 0 := by
    have h1 : t * cmin ≤ t * (L w) i :=
      mul_le_mul_of_nonneg_left (hcminle i) (le_of_lt ht)
    have htc : 0 < t * cmin := mul_pos ht hcminpos
    rw [hsimp] at hupper
    linarith
  linarith [hkey]

/-- **Gale–Nikaido Theorem 3 (order-interval monotonicity).** On a box, a `C¹` map with a P-matrix
Jacobian everywhere has, for `a ≤ x` in the box with `F x ≤ F a`, only the solution `x = a`. By
induction on dimension: `a` is isolated among such points (`pmatrix_isolated`), so a minimal
counterexample `xm` exists by compactness; if `xm` is strictly above `a`, `pmatrix_descent` produces a
smaller one (contradiction), and otherwise a coordinate `xm i = a i` lets the inductive hypothesis on
the principal-submatrix face force `xm = a`. -/
theorem pmatrix_order_eq : ∀ {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {F' : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))} {lo hi : Fin n → ℝ},
    (∀ z ∈ Set.Icc lo hi, HasFDerivAt F (F' z) z) →
    (∀ z ∈ Set.Icc lo hi, (jacobianMatrix (F' z)).IsPMatrix) →
    ∀ {a x : Fin n → ℝ}, a ∈ Set.Icc lo hi → x ∈ Set.Icc lo hi → a ≤ x → F x ≤ F a → x = a := by
  intro n
  induction n with
  | zero => intro F F' lo hi _ _ a x _ _ _ _; exact Subsingleton.elim x a
  | succ n ih =>
    intro F F' lo hi hF hP a x ha hx hax hFle
    by_contra hxne
    classical
    obtain ⟨δ, hδ, hiso⟩ := pmatrix_isolated (hF a ha) (hP a ha)
    set K : Set (Fin (n + 1) → ℝ) :=
      {z | z ∈ Set.Icc lo hi ∧ a ≤ z ∧ F z ≤ F a ∧ δ ≤ ‖z - a‖} with hKdef
    have hFcont : ContinuousOn F (Set.Icc lo hi) :=
      fun z hz => (hF z hz).continuousAt.continuousWithinAt
    have hKcl : IsClosed K := by
      have h1 : IsClosed (Set.Icc lo hi ∩ F ⁻¹' Set.Iic (F a)) :=
        hFcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have heq : K = (Set.Icc lo hi ∩ F ⁻¹' Set.Iic (F a)) ∩ {z | a ≤ z} ∩
          {z | δ ≤ ‖z - a‖} := by
        ext z
        simp only [hKdef, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
        tauto
      rw [heq]
      exact (h1.inter (isClosed_le continuous_const continuous_id)).inter
        (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
    have hKsub : K ⊆ Set.Icc lo hi := fun z hz => hz.1
    have hKcompact : IsCompact K := isCompact_Icc.of_isClosed_subset hKcl hKsub
    have hxK : x ∈ K := by
      refine ⟨hx, hax, hFle, ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      exact hiso x hax hxne hlt hFle
    -- minimal counterexample: minimize ∑ over K
    have hsumcont : Continuous (fun z : Fin (n + 1) → ℝ => ∑ i, z i) :=
      continuous_finsetSum _ (fun i _ => continuous_apply i)
    obtain ⟨xm, hxmK, hxmmin⟩ :=
      hKcompact.exists_isMinOn ⟨x, hxK⟩ hsumcont.continuousOn
    obtain ⟨hxmbox, haxm, hFxm, hxmδ⟩ := hxmK
    have hxmne : xm ≠ a := fun h => by
      rw [h, sub_self, norm_zero] at hxmδ; linarith
    by_cases hstrict : ∀ i, a i < xm i
    · -- Case 1: strict descent
      obtain ⟨w, hwnn, hwne, δ', hδ', hdesc⟩ :=
        pmatrix_descent (hF xm hxmbox) (hP xm hxmbox)
      -- choose small t so that xm - t•w is a strictly smaller counterexample
      set m : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i => xm i - a i) with hm
      have hmpos : 0 < m := by rw [hm, Finset.lt_inf'_iff]; intro i _; linarith [hstrict i]
      set wsup : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => w i) with hwsup
      have hwsuppos : 0 < wsup := by
        rcases (Function.ne_iff).mp hwne with ⟨i, hi⟩
        have : 0 < w i := lt_of_le_of_ne (hwnn i) (Ne.symm (by simpa using hi))
        exact lt_of_lt_of_le this (Finset.le_sup' _ (Finset.mem_univ i))
      set t : ℝ := min (δ' / 2) (m / (2 * wsup)) with ht
      have htpos : 0 < t := lt_min (by positivity) (by positivity)
      have htδ' : t < δ' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      set z : Fin (n + 1) → ℝ := xm - t • w with hz
      have hzle : z ≤ xm := by
        intro i; rw [hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have : 0 ≤ t * w i := mul_nonneg (le_of_lt htpos) (hwnn i)
        linarith
      have hzne : z ≠ xm := by
        intro h; apply hwne; funext i
        have := congrFun h i
        rw [hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
        have htwi : t * w i = 0 := by linarith
        rcases mul_eq_zero.mp htwi with h0 | h0
        · exact absurd h0 (ne_of_gt htpos)
        · simp [h0]
      have hsumlt : ∑ i, z i < ∑ i, xm i := by
        have hle : ∀ i ∈ Finset.univ, z i ≤ xm i := fun i _ => hzle i
        rcases (Function.ne_iff).mp hzne with ⟨j, hj⟩
        exact Finset.sum_lt_sum hle ⟨j, Finset.mem_univ j, lt_of_le_of_ne (hzle j) hj⟩
      have hzgt : ∀ i, a i < z i := by
        intro i; rw [hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have hwle : w i ≤ wsup := Finset.le_sup' _ (Finset.mem_univ i)
        have htm : t * w i ≤ m / 2 := by
          calc t * w i ≤ (m / (2 * wsup)) * wsup :=
                mul_le_mul (min_le_right _ _) hwle (hwnn i) (by positivity)
            _ = m / 2 := by field_simp
        have hmi : m ≤ xm i - a i := Finset.inf'_le _ (Finset.mem_univ i)
        linarith [hstrict i]
      have hza : a ≤ z := fun i => le_of_lt (hzgt i)
      have hzne_a : z ≠ a := by
        intro h; have h0 := hzgt ⟨0, by omega⟩; rw [h] at h0; exact lt_irrefl _ h0
      have hzbox : z ∈ Set.Icc lo hi :=
        ⟨le_trans ha.1 hza, le_trans hzle hxmbox.2⟩
      have hzF : F z ≤ F a := le_trans (hdesc t htpos htδ') hFxm
      have hzK : z ∈ K := by
        refine ⟨hzbox, hza, hzF, ?_⟩
        by_contra hlt
        rw [not_le] at hlt
        exact hiso z hza hzne_a hlt hzF
      simp only [isMinOn_iff] at hxmmin
      linarith [hxmmin z hzK, hsumlt]
    · -- Case 2: face reduction
      simp only [not_forall, not_lt] at hstrict
      obtain ⟨i, hile⟩ := hstrict
      have hia : xm i = a i := le_antisymm hile (haxm i)
      -- the face map
      set G : (Fin n → ℝ) → (Fin n → ℝ) :=
        fun yh => fun k => F (Fin.insertNth i (a i) yh) (i.succAbove k) with hGdef
      set G' : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
        fun yh => (ContinuousLinearMap.pi (fun k : Fin n =>
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (i.succAbove k))).comp
          ((F' (Fin.insertNth i (a i) yh)).comp (ContinuousLinearMap.pi
            (Fin.insertNth i (0 : (Fin n → ℝ) →L[ℝ] ℝ) (fun l => ContinuousLinearMap.proj l))))
        with hG'def
      have hinsbox : ∀ yh : Fin n → ℝ, (Fin.removeNth i lo : Fin n → ℝ) ≤ yh →
          yh ≤ (Fin.removeNth i hi : Fin n → ℝ) →
          (Fin.insertNth i (a i) yh : Fin (n + 1) → ℝ) ∈ Set.Icc lo hi := by
        intro yh hyhlo hyhhi
        refine ⟨fun j => ?_, fun j => ?_⟩
        · refine Fin.succAboveCases i ?_ (fun k => ?_) j
          · rw [Fin.insertNth_apply_same]; exact ha.1 i
          · rw [Fin.insertNth_apply_succAbove]; exact hyhlo k
        · refine Fin.succAboveCases i ?_ (fun k => ?_) j
          · rw [Fin.insertNth_apply_same]; exact ha.2 i
          · rw [Fin.insertNth_apply_succAbove]; exact hyhhi k
      have hGF : ∀ yh ∈ Set.Icc (Fin.removeNth i lo) (Fin.removeNth i hi),
          HasFDerivAt G (G' yh) yh := by
        intro yh hyh
        have hmem := hinsbox yh hyh.1 hyh.2
        have hc1 := hasFDerivAt_insertNth i (a i) yh
        have hc2 := (hF _ hmem).comp yh hc1
        exact (ContinuousLinearMap.pi (fun k : Fin n =>
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ)
            (i.succAbove k))).hasFDerivAt.comp yh hc2
      have hGP : ∀ yh ∈ Set.Icc (Fin.removeNth i lo) (Fin.removeNth i hi),
          (jacobianMatrix (G' yh)).IsPMatrix := by
        intro yh hyh
        rw [hG'def, jacobianMatrix_face_eq_submatrix]
        exact (hP _ (hinsbox yh hyh.1 hyh.2)).submatrix_isPMatrix Fin.succAbove_right_injective
      have hahbox : Fin.removeNth i a ∈ Set.Icc (Fin.removeNth i lo) (Fin.removeNth i hi) :=
        ⟨fun k => ha.1 (i.succAbove k), fun k => ha.2 (i.succAbove k)⟩
      have hxhbox : Fin.removeNth i xm ∈ Set.Icc (Fin.removeNth i lo) (Fin.removeNth i hi) :=
        ⟨fun k => hxmbox.1 (i.succAbove k), fun k => hxmbox.2 (i.succAbove k)⟩
      have hahxh : Fin.removeNth i a ≤ Fin.removeNth i xm := fun k => haxm (i.succAbove k)
      have hinsa : (Fin.insertNth i (a i) (Fin.removeNth i a) : Fin (n + 1) → ℝ) = a := by
        rw [Fin.insertNth_removeNth]; exact Function.update_eq_self i a
      have hinsxm : (Fin.insertNth i (a i) (Fin.removeNth i xm) : Fin (n + 1) → ℝ) = xm := by
        rw [← hia, Fin.insertNth_removeNth]; exact Function.update_eq_self i xm
      have hGfa : G (Fin.removeNth i a) = fun k => F a (i.succAbove k) := by
        funext k; rw [hGdef]; simp only; rw [hinsa]
      have hGfxm : G (Fin.removeNth i xm) = fun k => F xm (i.succAbove k) := by
        funext k; rw [hGdef]; simp only; rw [hinsxm]
      have hGle : G (Fin.removeNth i xm) ≤ G (Fin.removeNth i a) := by
        rw [hGfa, hGfxm]; intro k; exact hFxm (i.succAbove k)
      have hrm : Fin.removeNth i xm = Fin.removeNth i a :=
        ih hGF hGP hahbox hxhbox hahxh hGle
      apply hxmne
      funext j
      refine Fin.succAboveCases i ?_ (fun k => ?_) j
      · exact hia
      · exact congrFun hrm k

end CRNT



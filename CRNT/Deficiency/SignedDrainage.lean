import CRNT.LinearAlgebra.Substochastic
import CRNT.Deficiency.Drainage

/-!
# Signed drainage: kernel vectors of `A_k` vanish on transient complexes

A nonnegative kernel vector of the kinetic map is supported on terminal strong linkage
classes (`isTerminalSLC_of_pos_kernel`). For a **signed** kernel vector the mass-balance
argument fails — cancellation breaks the forward-closedness of the support — but the
substochastic Perron–Frobenius criterion recovers the result. Masking the rescaled
column-stochastic matrix `smat` to its transient rows gives a column-substochastic matrix
whose leaks are exactly the complexes draining to a terminal class; every transient complex
reaches such a leak, so the masked matrix has trivial fixed space. Hence any kernel vector of
`A_k` vanishes at every non-terminal complex.

* `kineticMap_eq_zero_of_not_terminal` — a kernel vector of `A_k` is zero at every
  non-terminal complex (signed drainage).

Depends on: `CRNT.LinearAlgebra.Substochastic`,
`CRNT.Deficiency.Drainage`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Signed drainage.** A kernel vector of the kinetic map `A_k` vanishes at every complex
whose strong linkage class is not terminal. Equivalently, the kernel of `A_k` is supported on
the terminal strong linkage classes — for signed vectors, not just nonnegative ones. -/
theorem kineticMap_eq_zero_of_not_terminal (N : Network S) (κ : RateConstants N)
    {v : N.ComplexIdx → ℝ} (hv : N.kineticMap κ v = 0)
    {c : N.ComplexIdx} (hc : ¬ N.IsTerminalSLC c.val) : v c = 0 := by
  have hfix : (PositiveKernel.smat N κ).mulVec v = v := (PositiveKernel.smat_fix_iff v).mpr hv
  -- No `smat` flow from a terminal class into a transient complex.
  have habsorb : ∀ {x y : N.ComplexIdx}, N.IsTerminalSLC y.val → ¬ N.IsTerminalSLC x.val →
      PositiveKernel.smat N κ x y = 0 := by
    intro x y hy hx
    have hxy : x ≠ y := fun h => hx (h ▸ hy)
    rw [PositiveKernel.smat_apply, if_neg hxy, zero_add]
    suffices hk : PositiveKernel.kmat N κ x y = 0 by rw [hk, mul_zero]
    simp only [PositiveKernel.kmat]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hsrc : N.sourceIdx r = y
    · rw [if_pos hsrc]
      by_cases htgt : N.targetIdx r = x
      · exfalso
        apply hx
        have hs : (N.reaction r).source = y.val := congrArg Subtype.val hsrc
        have ht : (N.reaction r).target = x.val := congrArg Subtype.val htgt
        have hsl : N.StronglyLinked y.val x.val := by
          have h2 := hy r; rw [hs, ht] at h2; exact h2 (StronglyLinked.refl N y.val)
        exact (N.isTerminalSLC_congr hsl).mp hy
      · rw [if_neg htgt, if_neg (Ne.symm hxy), sub_zero, mul_zero]
    · rw [if_neg hsrc]
  -- The `smat` masked to its transient rows: column-substochastic, leaks at drainage sites.
  set M : Matrix N.ComplexIdx N.ComplexIdx ℝ :=
    fun a c => if ¬ N.IsTerminalSLC a.val then PositiveKernel.smat N κ a c else 0 with hMdef
  set w : N.ComplexIdx → ℝ :=
    fun i => if ¬ N.IsTerminalSLC i.val then v i else 0 with hwdef
  have hMnn : ∀ a c, 0 ≤ M a c := by
    intro a c; simp only [hMdef]; by_cases h : N.IsTerminalSLC a.val
    · simp [h]
    · simp only [h, not_false_iff, if_true]; exact PositiveKernel.smat_nonneg a c
  have hMle : ∀ a c, M a c ≤ PositiveKernel.smat N κ a c := by
    intro a c; simp only [hMdef]; by_cases h : N.IsTerminalSLC a.val
    · simp only [h, not_true, if_false]; exact PositiveKernel.smat_nonneg a c
    · simp [h]
  have hMcol : ∀ c, ∑ a, M a c ≤ 1 := fun c =>
    (Finset.sum_le_sum fun a _ => hMle a c).trans_eq (PositiveKernel.smat_colsum c)
  -- `w` (the masked `v`) is fixed by `M`.
  have hMfix : M.mulVec w = w := by
    funext i
    show ∑ c, M i c * w c = w i
    by_cases hi : N.IsTerminalSLC i.val
    · rw [show w i = 0 by simp [hwdef, hi]]
      exact Finset.sum_eq_zero fun c _ => by simp [hMdef, hi]
    · rw [show w i = v i by simp [hwdef, hi]]
      have hterm : ∑ c, M i c * w c = ∑ c, PositiveKernel.smat N κ i c * v c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [hMdef, hi, not_false_iff, if_true]
        by_cases hct : N.IsTerminalSLC c.val
        · rw [show w c = 0 by simp [hwdef, hct], habsorb hct hi]; ring
        · rw [show w c = v c by simp [hwdef, hct]]
      rw [hterm]
      have := congrFun hfix i
      simpa [Matrix.mulVec, dotProduct] using this
  -- Every nonempty set closed under reverse support edges contains a leak.
  have hclosed : ∀ T : N.ComplexIdx → Prop, (∃ i, T i) →
      (∀ a c, M a c ≠ 0 → T c → T a) → ∃ ℓ, T ℓ ∧ ∑ i, M i ℓ < 1 := by
    intro T hTne hTc
    by_cases hexterm : ∃ t, T t ∧ N.IsTerminalSLC t.val
    · obtain ⟨t, hTt, htt⟩ := hexterm
      refine ⟨t, hTt, ?_⟩
      have h0 : ∑ a, M a t = 0 := Finset.sum_eq_zero fun a _ => by
        by_cases ha : N.IsTerminalSLC a.val
        · simp [hMdef, ha]
        · simp only [hMdef, ha, not_false_iff, if_true]; exact habsorb htt ha
      rw [h0]; norm_num
    · simp only [not_exists, not_and] at hexterm
      by_contra hno
      simp only [not_exists, not_and, not_lt] at hno
      obtain ⟨c0, hc0⟩ := hTne
      -- With no leak in `T`, `T` is reaction-closed: every reaction from `T` lands in `T`.
      have hclosedD : ∀ r : N.R, T (N.sourceIdx r) → T (N.targetIdx r) := by
        intro r hsrc
        have hcol1 : ∑ i, M i (N.sourceIdx r) = 1 := le_antisymm (hMcol _) (hno _ hsrc)
        -- The source's column avoids terminals: terminal rows carry no `smat` mass.
        have hzero : ∀ i, N.IsTerminalSLC i.val →
            PositiveKernel.smat N κ i (N.sourceIdx r) = 0 := by
          have hdiff : ∀ i ∈ Finset.univ,
              0 ≤ PositiveKernel.smat N κ i (N.sourceIdx r) - M i (N.sourceIdx r) :=
            fun i _ => by linarith [hMle i (N.sourceIdx r)]
          have hsum0 : ∑ i, (PositiveKernel.smat N κ i (N.sourceIdx r) - M i (N.sourceIdx r)) = 0 := by
            rw [Finset.sum_sub_distrib, PositiveKernel.smat_colsum, hcol1, sub_self]
          intro i hit
          have he := (Finset.sum_eq_zero_iff_of_nonneg hdiff).mp hsum0 i (Finset.mem_univ i)
          have hMi0 : M i (N.sourceIdx r) = 0 := by simp [hMdef, hit]
          linarith [he, hMi0]
        have htgtnt : ¬ N.IsTerminalSLC (N.targetIdx r).val := fun htt =>
          PositiveKernel.smat_ne_zero_of_reaction r rfl rfl (hzero _ htt)
        have hMne : M (N.targetIdx r) (N.sourceIdx r) ≠ 0 := by
          simp only [hMdef]; rw [if_pos htgtnt]
          exact PositiveKernel.smat_ne_zero_of_reaction r rfl rfl
        exact hTc _ _ hMne hsrc
      obtain ⟨d, hTd, hdterm⟩ := N.exists_terminal_mem_of_closed hclosedD hc0
      exact hexterm d hTd hdterm
  have hw0 : w = 0 :=
    mulVec_fixed_eq_zero_of_substochastic_of_closed M hMnn hMcol hclosed hMfix
  simpa [hwdef, hc] using congrFun hw0 c

end Network

end CRNT

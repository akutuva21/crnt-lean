import CRNT.Deficiency.ClosedSetKernel

/-!
# Strict positivity of the terminal-strong-linkage-class kernel mode

A terminal strong linkage class is reaction-closed (it supports a nonnegative kernel vector of
`A_k`) and strongly connected (its complexes mutually reach one another). Positivity therefore
spreads from the one coordinate the kernel vector must have to the whole class
(`exists_pos_kernelVector_on_terminalSLC`): the kernel mode is strictly positive on the
terminal strong linkage class and zero off it.

This module is **stable**. Depends on: `CRNT.Deficiency.ClosedSetKernel`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A terminal strong linkage class carries a kernel vector of `A_k` strictly positive on the
class and zero off it.** -/
theorem exists_pos_kernelVector_on_terminalSLC (N : Network S) (κ : RateConstants N)
    {c : N.ComplexIdx} (hc : N.IsTerminalSLC c.val) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c', N.StronglyLinked c.val c'.val → 0 < b c') ∧
      (∀ c', ¬ N.StronglyLinked c.val c'.val → b c' = 0) ∧ N.kineticMap κ b = 0 := by
  obtain ⟨b, hbnn, hb0, hbsupp, hbker⟩ := N.exists_nonneg_kernelVector_on_terminalSLC κ hc
  have hbfix : (PositiveKernel.smat N κ).mulVec b = b := (PositiveKernel.smat_fix_iff b).mpr hbker
  obtain ⟨c₀, hc₀ne⟩ := Function.ne_iff.mp hb0
  have hc₀sl : N.StronglyLinked c.val c₀.val := by by_contra h; exact hc₀ne (hbsupp c₀ h)
  have hc₀pos : 0 < b c₀ := (hbnn c₀).lt_of_ne (Ne.symm hc₀ne)
  refine ⟨b, fun c' hsl => ?_, hbsupp, hbker⟩
  have hreach : N.Reaches c₀.val c'.val := (hc₀sl.symm.trans hsl).1
  have hsupp : supportReaches (PositiveKernel.smat N κ) c' c₀ :=
    PositiveKernel.reaches_supportReaches c₀.val c₀.property hreach c'.property
  exact pos_of_supportReaches_pos (PositiveKernel.smat N κ)
    PositiveKernel.smat_nonneg b hbnn hbfix hsupp hc₀pos

/-- **Uniqueness of the terminal-SLC kernel mode.** A kernel vector `v` supported on a terminal
strong linkage class is a scalar multiple of a strictly-positive-on-class kernel vector `a`. -/
theorem terminalSLC_kernel_unique (N : Network S) (κ : RateConstants N)
    {c : N.ComplexIdx} {a v : N.ComplexIdx → ℝ}
    (hapos : ∀ c', N.StronglyLinked c.val c'.val → 0 < a c')
    (haoff : ∀ c', ¬ N.StronglyLinked c.val c'.val → a c' = 0) (haker : N.kineticMap κ a = 0)
    (hvoff : ∀ c', ¬ N.StronglyLinked c.val c'.val → v c' = 0) (hvker : N.kineticMap κ v = 0) :
    ∃ t : ℝ, v = t • a := by
  classical
  set T : Finset N.ComplexIdx := Finset.univ.filter (fun c' => N.StronglyLinked c.val c'.val)
    with hTdef
  have hmemT : ∀ c', c' ∈ T ↔ N.StronglyLinked c.val c'.val := by
    intro c'; rw [hTdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ c', h⟩⟩
  have hcT : c ∈ T := (hmemT c).mpr (StronglyLinked.refl N c.val)
  obtain ⟨cm, hcmT, hmin⟩ := Finset.exists_min_image T (fun c' => v c' / a c') ⟨c, hcT⟩
  have hcmsl : N.StronglyLinked c.val cm.val := (hmemT cm).mp hcmT
  set t := v cm / a cm with ht
  refine ⟨t, ?_⟩
  set w := v - t • a with hw
  have hafix : (PositiveKernel.smat N κ).mulVec a = a := (PositiveKernel.smat_fix_iff a).mpr haker
  have hvfix : (PositiveKernel.smat N κ).mulVec v = v := (PositiveKernel.smat_fix_iff v).mpr hvker
  have hwfix : (PositiveKernel.smat N κ).mulVec w = w := by
    rw [hw, Matrix.mulVec_sub, Matrix.mulVec_smul, hvfix, hafix]
  have hwnn : ∀ c', 0 ≤ w c' := by
    intro c'
    by_cases hc' : N.StronglyLinked c.val c'.val
    · have hle : t ≤ v c' / a c' := hmin c' ((hmemT c').mpr hc')
      rw [le_div_iff₀ (hapos c' hc')] at hle
      simp only [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; linarith
    · rw [hw]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hvoff c' hc', haoff c' hc', mul_zero,
        sub_zero, le_refl]
  have hwcm : w cm = 0 := by
    have hcancel : v cm / a cm * a cm = v cm := div_mul_cancel₀ (v cm) (hapos cm hcmsl).ne'
    simp only [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ht]
    rw [hcancel, sub_self]
  have hw0 : w = 0 := by
    funext c'
    by_cases hc' : N.StronglyLinked c.val c'.val
    · by_contra hne
      have hcpos : 0 < w c' := (hwnn c').lt_of_ne (Ne.symm hne)
      have hreach : N.Reaches c'.val cm.val := (hc'.symm.trans hcmsl).1
      have hsupp : supportReaches (PositiveKernel.smat N κ) cm c' :=
        PositiveKernel.reaches_supportReaches c'.val c'.property hreach cm.property
      have hpos := pos_of_supportReaches_pos (PositiveKernel.smat N κ)
        PositiveKernel.smat_nonneg w hwnn hwfix hsupp hcpos
      rw [hwcm] at hpos; exact lt_irrefl 0 hpos
    · rw [hw]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hvoff c' hc', haoff c' hc', mul_zero,
        sub_zero, Pi.zero_apply]
  rw [← sub_eq_zero, ← hw]; exact hw0

end Network

end CRNT

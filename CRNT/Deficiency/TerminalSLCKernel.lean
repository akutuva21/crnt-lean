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

end Network

end CRNT

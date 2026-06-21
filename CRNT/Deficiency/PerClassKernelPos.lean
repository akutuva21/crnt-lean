import CRNT.Deficiency.PerClassKernel

/-!
# Strict positivity of the per-class kernel vector

A linkage class that is strongly connected — every complex reaches every other along directed
reactions — carries a kernel vector of `A_k` that is strictly positive throughout the class
(`exists_pos_kernelVector_on_class`). The nonnegative per-class kernel vector is a fixed vector
of the rescaled matrix `smat`; strong connectivity lets Perron–Frobenius positivity spread the
single positive coordinate it must have to the whole class.

In particular, every linkage class of a weakly reversible network supports such a strictly
positive kernel vector (`exists_pos_kernelVector_on_class_of_weaklyReversible`).

This module is **stable**. Depends on: `CRNT.Deficiency.PerClassKernel`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A strongly connected linkage class carries a strictly positive kernel vector of `A_k`.**
The vector is positive on the class and zero off it. -/
theorem exists_pos_kernelVector_on_class (N : Network S) (κ : RateConstants N)
    (θ : Quotient N.linkedSetoid)
    (hθ : ∀ c c' : N.ComplexIdx, N.classOf c = θ → N.classOf c' = θ → N.Reaches c.val c'.val) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c, N.classOf c = θ → 0 < b c) ∧
      (∀ c, N.classOf c ≠ θ → b c = 0) ∧ N.kineticMap κ b = 0 := by
  obtain ⟨b, hbnn, hb0, hbsupp, hbker⟩ := N.exists_nonneg_kernelVector_on_class κ θ
  have hbfix : (PositiveKernel.smat N κ).mulVec b = b := (PositiveKernel.smat_fix_iff b).mpr hbker
  obtain ⟨c₀, hc₀ne⟩ := Function.ne_iff.mp hb0
  have hc₀cls : N.classOf c₀ = θ := by by_contra h; exact hc₀ne (hbsupp c₀ h)
  have hc₀pos : 0 < b c₀ := (hbnn c₀).lt_of_ne (Ne.symm hc₀ne)
  refine ⟨b, fun c hccls => ?_, hbsupp, hbker⟩
  have hreach : N.Reaches c₀.val c.val := hθ c₀ c hc₀cls hccls
  have hsupp : supportReaches (PositiveKernel.smat N κ) c c₀ :=
    PositiveKernel.reaches_supportReaches c₀.val c₀.property hreach c.property
  exact pos_of_supportReaches_pos (PositiveKernel.smat N κ)
    PositiveKernel.smat_nonneg b hbnn hbfix hsupp hc₀pos

/-- **Every linkage class of a weakly reversible network carries a strictly positive kernel
vector of `A_k`.** -/
theorem exists_pos_kernelVector_on_class_of_weaklyReversible (N : Network S)
    (hwr : N.WeaklyReversible) (κ : RateConstants N) (θ : Quotient N.linkedSetoid) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c, N.classOf c = θ → 0 < b c) ∧
      (∀ c, N.classOf c ≠ θ → b c = 0) ∧ N.kineticMap κ b = 0 :=
  N.exists_pos_kernelVector_on_class κ θ fun _ _ hc hc' =>
    hwr.reaches_of_linked (Quotient.exact (hc.trans hc'.symm))

end Network

end CRNT

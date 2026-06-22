import CRNT.Deficiency.DeficiencyOneLine
import CRNT.Deficiency.TerminalSLCKernel

/-!
# The deficient-class kernel relation

On the single deficiency-one linkage class the two positive steady states satisfy a sharp
linear relation. Each steady state pins its kinetic image to the common deficiency line:
`A_k(Ψ x) = c_x · g` and `A_k(Ψ y) = c_y · g`. Hence the combination
`w := c_y · Ψ x − c_x · Ψ y` lies in `ker A_k`, and so does its restriction to the class.

When the deficient class is **strongly connected** (which holds for weakly reversible
networks), the kernel of `A_k` on the class is one-dimensional — spanned by the strictly
positive Perron–Frobenius mode `b` — so `w` restricted to the class is `λ · b`. Pointwise on
the class this reads `c_y · Ψ(x)_c − c_x · Ψ(y)_c = λ · b_c`. Reducing the deficiency-one
sign argument to forcing `λ = 0` (whence `Ψ(y)/Ψ(x)` is constant) is the remaining step.

* `deficientClass_kernel_relation` — the pointwise relation `c_y·Ψ(x) − c_x·Ψ(y) = λ·b` on a
  strongly connected deficient class, with `b` strictly positive there.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Deficiency.DeficiencyOneLine`, `CRNT.Deficiency.TerminalSLCKernel`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The deficient-class kernel relation.** For a deficiency-one network whose deficient
linkage class `θ` is strongly connected, two mass-action steady states `x`, `y` admit scalars
`c_x`, `c_y`, `λ` and a class-positive kernel mode `b` of `A_k` with
`c_y · Ψ(x)_c − c_x · Ψ(y)_c = λ · b_c` at every complex `c` of `θ`. The combination
`c_y · Ψ x − c_x · Ψ y` kills the deficiency line, lands in the one-dimensional class kernel,
and is therefore proportional to `b`. -/
theorem deficientClass_kernel_relation (N : Network S) (hδ : N.DeficiencyOne)
    (κ : RateConstants N) {θ : Quotient N.linkedSetoid}
    (hsc : ∀ c c' : N.ComplexIdx, N.classOf c = θ → N.classOf c' = θ →
      N.StronglyLinked c.val c'.val)
    {x y : Concentration S} (hxss : N.IsMassActionSteadyState κ x)
    (hyss : N.IsMassActionSteadyState κ y) :
    ∃ (b : N.ComplexIdx → ℝ) (cx cy lam : ℝ),
      (∀ c, N.classOf c = θ → 0 < b c) ∧
      ∀ c, N.classOf c = θ →
        cy * N.complexMonomialVector x c - cx * N.complexMonomialVector y c = lam * b c := by
  obtain ⟨c0, hc0⟩ := Quotient.exists_rep θ
  have hc0cls : N.classOf c0 = θ := hc0
  -- The strongly connected class is its own terminal strong linkage class.
  have hterm : N.IsTerminalSLC c0.val := by
    intro r hr
    have hsrc : N.classOf (N.sourceIdx r) = θ := (Quotient.sound hr.linked).symm.trans hc0cls
    have htgt : N.classOf (N.targetIdx r) = θ := by
      rw [← N.classOf_sourceIdx_eq_targetIdx r]; exact hsrc
    exact hsc c0 (N.targetIdx r) hc0cls htgt
  obtain ⟨b, hbpos, hboff, hbker⟩ := N.exists_pos_kernelVector_on_terminalSLC κ hterm
  obtain ⟨g, _, hsmul⟩ := N.exists_kineticImage_smul_of_deficiencyOne κ hδ
  obtain ⟨cx, hcx⟩ := hsmul hxss
  obtain ⟨cy, hcy⟩ := hsmul hyss
  set w : N.ComplexIdx → ℝ := cy • N.complexMonomialVector x - cx • N.complexMonomialVector y
    with hw
  have hwker : N.kineticMap κ w = 0 := by
    rw [hw, map_sub, map_smul, map_smul, hcx, hcy, smul_smul, smul_smul, mul_comm cy cx, sub_self]
  have hwθker : N.kineticMap κ (N.restrictToClass θ w) = 0 := by
    rw [kineticMap_restrictToClass, hwker]
    funext c; by_cases h : N.classOf c = θ <;>
      simp [restrictToClass_apply_of_eq, restrictToClass_apply_of_ne, h]
  have hvoff : ∀ c', ¬ N.StronglyLinked c0.val c'.val → N.restrictToClass θ w c' = 0 := by
    intro c' hc'
    exact restrictToClass_apply_of_ne _ _ fun hcls => hc' (hsc c0 c' hc0cls hcls)
  obtain ⟨lam, hlam⟩ := N.terminalSLC_kernel_unique κ hbpos hboff hbker hvoff hwθker
  refine ⟨b, cx, cy, lam, fun c hc => hbpos c (hsc c0 c hc0cls hc), fun c hc => ?_⟩
  have hval := congrFun hlam c
  rw [restrictToClass_apply_of_eq _ _ hc] at hval
  simpa [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hval

end Network

end CRNT

import CRNT.Deficiency.DeficiencyOneLine
import CRNT.Deficiency.TerminalSLCKernel
import CRNT.Deficiency.SignedDrainage

/-!
# The deficient-class kernel relation

On the single deficiency-one linkage class the two positive steady states satisfy a sharp
linear relation. Each steady state pins its kinetic image to the common deficiency line:
`A_k(Ψ x) = c_x · g` and `A_k(Ψ y) = c_y · g`. Hence the combination
`w := c_y · Ψ x − c_x · Ψ y` lies in `ker A_k`, and so does its restriction to the class.

Signed drainage (`kineticMap_eq_zero_of_not_terminal`) makes any kernel vector of `A_k`
vanish off the terminal strong linkage classes, and the deficiency-one hypotheses pin a unique
terminal class per linkage class. So the restricted combination is supported on that terminal
class, where the kernel of `A_k` is one-dimensional — spanned by the strictly positive
Perron–Frobenius mode `b` — making it `λ · b`. Pointwise on the class this reads
`c_y · Ψ(x)_c − c_x · Ψ(y)_c = λ · b_c`. Forcing `λ = 0` (whence `Ψ(y)/Ψ(x)` is constant on
the terminal class) is the remaining step of the deficiency-one sign argument.

* `deficientClass_kernel_relation` — the pointwise relation `c_y·Ψ(x) − c_x·Ψ(y) = λ·b` on the
  deficient class, with `b` strictly positive on its terminal strong linkage class.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Deficiency.DeficiencyOneLine`, `CRNT.Deficiency.TerminalSLCKernel`,
`CRNT.Deficiency.SignedDrainage`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The deficient-class kernel relation.** For a deficiency-one network meeting the
deficiency-one hypotheses, two mass-action steady states `x`, `y` admit scalars `c_x`, `c_y`,
`λ` and a kernel mode `b` of `A_k` — strictly positive on the deficient class's terminal
strong linkage class — with `c_y · Ψ(x)_c − c_x · Ψ(y)_c = λ · b_c` at every complex `c` of
the class. The combination `c_y · Ψ x − c_x · Ψ y` kills the deficiency line; signed drainage
plus the one-terminal-class condition place its class restriction in the one-dimensional
terminal-class kernel, so it is proportional to `b`. -/
theorem deficientClass_kernel_relation (N : Network S) (hδ : N.DeficiencyOne)
    (h : N.DeficiencyOneHypotheses) (κ : RateConstants N) {θ : Quotient N.linkedSetoid}
    {x y : Concentration S} (hxss : N.IsMassActionSteadyState κ x)
    (hyss : N.IsMassActionSteadyState κ y) :
    ∃ (b : N.ComplexIdx → ℝ) (cx cy lam : ℝ),
      (∀ c, N.classOf c = θ → N.IsTerminalSLC c.val → 0 < b c) ∧
      ∀ c, N.classOf c = θ →
        cy * N.complexMonomialVector x c - cx * N.complexMonomialVector y c = lam * b c := by
  obtain ⟨σ, ⟨hσθ, hσterm⟩, hσuniq⟩ := h.oneTerminal θ
  obtain ⟨c0, hc0σ⟩ := Quotient.exists_rep σ
  have hc0term : N.IsTerminalSLC c0.val := by rw [← isTerminalSLClass_mk, hc0σ]; exact hσterm
  -- The terminal complexes of `θ` are exactly those strongly linked to `c0` (unique terminal class).
  have hSL : ∀ c, N.classOf c = θ → N.IsTerminalSLC c.val → N.StronglyLinked c0.val c.val := by
    intro c hcθ hcterm
    have e1 : Quotient.mk N.stronglyLinkedSetoid c = σ :=
      hσuniq _ ⟨by rw [strongToLinkage_mk]; exact hcθ, by rw [isTerminalSLClass_mk]; exact hcterm⟩
    exact Quotient.exact (hc0σ.trans e1.symm)
  obtain ⟨b, hbpos, hboff, hbker⟩ := N.exists_pos_kernelVector_on_terminalSLC κ hc0term
  obtain ⟨g, _, hsmul⟩ := N.exists_kineticImage_smul_of_deficiencyOne κ hδ
  obtain ⟨cx, hcx⟩ := hsmul hxss
  obtain ⟨cy, hcy⟩ := hsmul hyss
  set w : N.ComplexIdx → ℝ := cy • N.complexMonomialVector x - cx • N.complexMonomialVector y
    with hw
  have hwker : N.kineticMap κ w = 0 := by
    rw [hw, map_sub, map_smul, map_smul, hcx, hcy, smul_smul, smul_smul, mul_comm cy cx, sub_self]
  have hwθker : N.kineticMap κ (N.restrictToClass θ w) = 0 := by
    rw [kineticMap_restrictToClass, hwker]
    funext c; by_cases hcq : N.classOf c = θ <;>
      simp [restrictToClass_apply_of_eq, restrictToClass_apply_of_ne, hcq]
  -- The class restriction vanishes off `c0`'s terminal class: outside `θ` trivially, on the
  -- transient part by signed drainage, and on other terminal complexes of `θ` not at all.
  have hvoff : ∀ c', ¬ N.StronglyLinked c0.val c'.val → N.restrictToClass θ w c' = 0 := by
    intro c' hc'
    by_cases hc'θ : N.classOf c' = θ
    · by_cases hc'term : N.IsTerminalSLC c'.val
      · exact absurd (hSL c' hc'θ hc'term) hc'
      · exact N.kineticMap_eq_zero_of_not_terminal κ hwθker hc'term
    · exact restrictToClass_apply_of_ne _ _ hc'θ
  obtain ⟨lam, hlam⟩ := N.terminalSLC_kernel_unique κ hbpos hboff hbker hvoff hwθker
  refine ⟨b, cx, cy, lam, fun c hcθ hcterm => hbpos c (hSL c hcθ hcterm), fun c hcθ => ?_⟩
  have hval := congrFun hlam c
  rw [restrictToClass_apply_of_eq _ _ hcθ] at hval
  simpa [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hval

end Network

end CRNT

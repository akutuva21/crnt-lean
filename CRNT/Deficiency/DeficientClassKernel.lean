import CRNT.Deficiency.DeficiencyOneLine
import CRNT.Deficiency.TerminalSLCKernel
import CRNT.Deficiency.SignedDrainage

/-!
# The per-class kernel mode and the deficient-class kernel relation

On a linkage class meeting the deficiency-one hypotheses (one terminal strong linkage class)
the kernel of the kinetic map `A_k`, restricted to vectors supported on the class, is
one-dimensional: there is a mode `b` strictly positive on the class's terminal strong linkage
class, and every kernel vector supported on the class is a scalar multiple of it
(`exists_kernel_mode_of_deficiencyOne`). This is Feinberg's Lemma II.6 (`ℓ = t = 1` kernel
structure), obtained here from signed drainage (kernel vectors vanish off terminal classes)
together with Perron–Frobenius uniqueness on the terminal class.

Its consequence is the **deficient-class kernel relation**: for two mass-action steady states
`x`, `y`, the combination `c_y · Ψ x − c_x · Ψ y` kills the deficiency line, so its class
restriction is a kernel vector supported on the class, hence `λ · b`. Pointwise this reads
`c_y · Ψ(x)_c − c_x · Ψ(y)_c = λ · b_c`; forcing `λ = 0` is the remaining sign step.

* `exists_kernel_mode_of_deficiencyOne` — the per-class kernel mode (Lemma II.6).
* `deficientClass_kernel_relation` — the pointwise relation.

Depends on:
`CRNT.Deficiency.DeficiencyOneLine`, `CRNT.Deficiency.TerminalSLCKernel`,
`CRNT.Deficiency.SignedDrainage`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The per-class kernel mode (Feinberg's Lemma II.6).** Under the deficiency-one
hypotheses, a linkage class `θ` carries a kernel mode `b` of `A_k`, strictly positive on its
terminal strong linkage class, such that every kernel vector of `A_k` supported on `θ` is a
scalar multiple of `b`. The kernel of `A_k` restricted to `θ` is thus one-dimensional. -/
theorem exists_kernel_mode_of_deficiencyOne (N : Network S)
    (h : N.DeficiencyOneHypotheses) (κ : RateConstants N) (θ : Quotient N.linkedSetoid) :
    ∃ b : N.ComplexIdx → ℝ,
      (∀ c, N.classOf c = θ → N.IsTerminalSLC c.val → 0 < b c) ∧
      N.kineticMap κ b = 0 ∧
      ∀ v : N.ComplexIdx → ℝ, N.kineticMap κ v = 0 →
        (∀ c, N.classOf c ≠ θ → v c = 0) → ∃ t : ℝ, v = t • b := by
  obtain ⟨σ, ⟨hσθ, hσterm⟩, hσuniq⟩ := h.oneTerminal θ
  obtain ⟨c0, hc0σ⟩ := Quotient.exists_rep σ
  have hc0term : N.IsTerminalSLC c0.val := by rw [← isTerminalSLClass_mk, hc0σ]; exact hσterm
  -- The terminal complexes of `θ` are exactly those strongly linked to `c0`.
  have hSL : ∀ c, N.classOf c = θ → N.IsTerminalSLC c.val → N.StronglyLinked c0.val c.val := by
    intro c hcθ hcterm
    have e1 : Quotient.mk N.stronglyLinkedSetoid c = σ :=
      hσuniq _ ⟨by rw [strongToLinkage_mk]; exact hcθ, by rw [isTerminalSLClass_mk]; exact hcterm⟩
    exact Quotient.exact (hc0σ.trans e1.symm)
  obtain ⟨b, hbpos, hboff, hbker⟩ := N.exists_pos_kernelVector_on_terminalSLC κ hc0term
  refine ⟨b, fun c hcθ hcterm => hbpos c (hSL c hcθ hcterm), hbker, ?_⟩
  intro v hvker hvsupp
  refine N.terminalSLC_kernel_unique κ hbpos hboff hbker ?_ hvker
  intro c' hc'
  by_cases hc'θ : N.classOf c' = θ
  · by_cases hc'term : N.IsTerminalSLC c'.val
    · exact absurd (hSL c' hc'θ hc'term) hc'
    · exact N.kineticMap_eq_zero_of_not_terminal κ hvker hc'term
  · exact hvsupp c' hc'θ

/-- **The deficient-class kernel relation.** For a deficiency-one network meeting the
hypotheses, two mass-action steady states `x`, `y` admit scalars `c_x`, `c_y`, `λ` and the
per-class kernel mode `b` (strictly positive on the terminal strong linkage class) with
`c_y · Ψ(x)_c − c_x · Ψ(y)_c = λ · b_c` at every complex `c` of the class. -/
theorem deficientClass_kernel_relation (N : Network S) (hδ : N.DeficiencyOne)
    (h : N.DeficiencyOneHypotheses) (κ : RateConstants N) {θ : Quotient N.linkedSetoid}
    {x y : Concentration S} (hxss : N.IsMassActionSteadyState κ x)
    (hyss : N.IsMassActionSteadyState κ y) :
    ∃ (b : N.ComplexIdx → ℝ) (cx cy lam : ℝ),
      (∀ c, N.classOf c = θ → N.IsTerminalSLC c.val → 0 < b c) ∧
      ∀ c, N.classOf c = θ →
        cy * N.complexMonomialVector x c - cx * N.complexMonomialVector y c = lam * b c := by
  obtain ⟨b, hbpos, hbker, huniq⟩ := N.exists_kernel_mode_of_deficiencyOne h κ θ
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
  obtain ⟨lam, hlam⟩ := huniq (N.restrictToClass θ w) hwθker
    fun c hc => restrictToClass_apply_of_ne _ _ hc
  refine ⟨b, cx, cy, lam, hbpos, fun c hcθ => ?_⟩
  have hval := congrFun hlam c
  rw [restrictToClass_apply_of_eq _ _ hcθ] at hval
  simpa [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hval

end Network

end CRNT

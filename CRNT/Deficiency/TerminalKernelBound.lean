import CRNT.Deficiency.TerminalSLCKernel
import CRNT.Deficiency.TerminalSLC
import CRNT.Deficiency.KernelDimensionBound

/-!
# The kinetic-map kernel has dimension at least the terminal-strong-linkage-class count

Each terminal strong linkage class carries a kernel vector of `A_k` strictly positive on it and
zero elsewhere (`exists_pos_kernelVector_on_terminalSLC`). Distinct terminal strong linkage
classes are disjoint, so these modes are linearly independent, giving

```text
t ≤ dim ker A_k
```

(`numTerminalSLC_le_finrank_ker_kineticMap`), where `t` is the number of terminal strong
linkage classes. This sharpens the linkage-class bound `ℓ ≤ dim ker A_k` (since `ℓ ≤ t`) and is
the tight lower half of Feinberg's identity `dim ker A_k = t`.

This module is **stable**. Depends on: `CRNT.Deficiency.TerminalSLCKernel`,
`CRNT.Deficiency.TerminalSLC`, `CRNT.Deficiency.KernelDimensionBound`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **`t ≤ dim ker A_k`.** The number of terminal strong linkage classes bounds the kernel
dimension from below. -/
theorem numTerminalSLC_le_finrank_ker_kineticMap (N : Network S) (κ : RateConstants N) :
    N.numTerminalSLC ≤ Module.finrank ℝ (LinearMap.ker (N.kineticMap κ)) := by
  classical
  -- terminality of each terminal strong linkage class, read off a representative complex.
  have hterm : ∀ σ : N.TerminalSLC, N.IsTerminalSLC (σ.val.out).val := by
    intro σ
    have h := σ.property
    rw [← Quotient.out_eq σ.val, isTerminalSLClass_mk] at h
    exact h
  choose b hbpos hboff hbker using
    fun σ : N.TerminalSLC => N.exists_pos_kernelVector_on_terminalSLC κ (hterm σ)
  have hli : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg σ₀
    have hgc := congrFun hg σ₀.val.out
    rw [Finset.sum_apply] at hgc
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hgc
    rw [Finset.sum_eq_single σ₀] at hgc
    · have hpos : 0 < b σ₀ σ₀.val.out := hbpos σ₀ σ₀.val.out (StronglyLinked.refl N _)
      exact (mul_eq_zero.mp hgc).resolve_right hpos.ne'
    · intro σ _ hσ
      rw [hboff σ σ₀.val.out ?_, mul_zero]
      intro hsl
      apply hσ
      apply Subtype.ext
      rw [← Quotient.out_eq σ.val, ← Quotient.out_eq σ₀.val]
      exact Quotient.sound hsl
    · intro h; exact absurd (Finset.mem_univ σ₀) h
  have hspan_le : Submodule.span ℝ (Set.range b) ≤ LinearMap.ker (N.kineticMap κ) := by
    rw [Submodule.span_le]
    rintro _ ⟨σ, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hbker σ
  calc N.numTerminalSLC
      = Fintype.card N.TerminalSLC := rfl
    _ = Module.finrank ℝ (Submodule.span ℝ (Set.range b)) := (finrank_span_eq_card hli).symm
    _ ≤ Module.finrank ℝ (LinearMap.ker (N.kineticMap κ)) := Submodule.finrank_mono hspan_le

end Network

end CRNT

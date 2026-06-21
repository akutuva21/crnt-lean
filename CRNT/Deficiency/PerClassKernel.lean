import CRNT.Theorems.DeficiencyZero.PositiveKernel
import CRNT.Deficiency.KineticBlock

/-!
# Each linkage class supports a nonnegative kernel vector of the kinetic map

The kinetic matrix `A_k` is block diagonal across linkage classes, and the rescaled matrix
`P = 1 + d⁻¹ A_k` is column-stochastic. Restricting `P` to the complexes of a single linkage
class `θ` keeps it column-stochastic (the class is closed under reactions), so Perron–Frobenius
provides a nonnegative nonzero fixed vector on the class. Extending it by zero gives a
nonnegative nonzero kernel vector of `A_k` supported on `θ`
(`exists_nonneg_kernelVector_on_class`).

This is the existence half of the per-class kernel structure underlying the deficiency-one
theorem: each linkage class carries its own equilibrium mode of `A_k`.

This module is **stable**. Depends on: `CRNT.Theorems.DeficiencyZero.PositiveKernel`,
`CRNT.Deficiency.KineticBlock`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Each linkage class supports a nonnegative nonzero kernel vector of `A_k`.** The vector
is supported on the class: it vanishes at every complex outside it. -/
theorem exists_nonneg_kernelVector_on_class (N : Network S) (κ : RateConstants N)
    (θ : Quotient N.linkedSetoid) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c, 0 ≤ b c) ∧ b ≠ 0 ∧
      (∀ c, N.classOf c ≠ θ → b c = 0) ∧ N.kineticMap κ b = 0 := by
  classical
  obtain ⟨c0, hc0⟩ := Quotient.exists_rep θ
  haveI : Nonempty {c : N.ComplexIdx // N.classOf c = θ} := ⟨⟨c0, hc0⟩⟩
  have hfilter : ∀ x : N.ComplexIdx,
      x ∈ Finset.univ.filter (fun c => N.classOf c = θ) ↔ N.classOf x = θ := by
    intro x; rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩
  -- block-diagonal vanishing: `smat c c' = 0` whenever `c` is outside the class of `c'`.
  have hblock : ∀ {c c' : N.ComplexIdx}, N.classOf c ≠ N.classOf c' →
      PositiveKernel.smat N κ c c' = 0 := fun h => PositiveKernel.smat_blockdiag h
  -- the class sub-block of the column-stochastic matrix stays column-stochastic.
  have hPcol : ∀ j : {c : N.ComplexIdx // N.classOf c = θ},
      ∑ i : {c : N.ComplexIdx // N.classOf c = θ}, PositiveKernel.smat N κ i.val j.val = 1 := by
    intro j
    rw [Finset.sum_subtype (Finset.univ.filter (fun c => N.classOf c = θ)) hfilter
        (fun c => PositiveKernel.smat N κ c j.val) |>.symm,
      Finset.sum_subset (Finset.filter_subset _ _), PositiveKernel.smat_colsum]
    intro c _ hcf
    refine hblock ?_
    rw [j.property]
    exact fun h => hcf ((hfilter c).mpr h)
  obtain ⟨bθ, hbθnn, hbθ0, hbθfix⟩ :=
    exists_nonneg_mulVec_fixed_of_colStochastic
      (fun i j : {c : N.ComplexIdx // N.classOf c = θ} => PositiveKernel.smat N κ i.val j.val)
      (fun i j => PositiveKernel.smat_nonneg i.val j.val) hPcol
  refine ⟨fun c => if h : N.classOf c = θ then bθ ⟨c, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro c
    dsimp only
    by_cases h : N.classOf c = θ
    · rw [dif_pos h]; exact hbθnn _
    · rw [dif_neg h]
  · intro hb
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hbθ0
    apply hi
    have := congrFun hb i.val
    rwa [dif_pos i.property, Pi.zero_apply] at this
  · intro c hc; dsimp only; rw [dif_neg hc]
  · rw [← PositiveKernel.smat_fix_iff]
    funext c
    show ∑ c', PositiveKernel.smat N κ c c' *
      (if h : N.classOf c' = θ then bθ ⟨c', h⟩ else 0) = _
    by_cases hc : N.classOf c = θ
    · rw [dif_pos hc]
      have hzero : ∀ c' ∈ Finset.univ,
          c' ∉ Finset.univ.filter (fun c => N.classOf c = θ) →
            PositiveKernel.smat N κ c c' *
              (if h : N.classOf c' = θ then bθ ⟨c', h⟩ else 0) = 0 := by
        intro c' _ hc'
        rw [dif_neg (fun h => hc' ((hfilter c').mpr h)), mul_zero]
      rw [← Finset.sum_subset (Finset.filter_subset _ _) hzero,
        Finset.sum_subtype (Finset.univ.filter (fun c => N.classOf c = θ)) hfilter
          (fun c' => PositiveKernel.smat N κ c c' *
            (if h : N.classOf c' = θ then bθ ⟨c', h⟩ else 0))]
      calc ∑ i : {c : N.ComplexIdx // N.classOf c = θ},
              PositiveKernel.smat N κ c i.val *
                (if h : N.classOf i.val = θ then bθ ⟨i.val, h⟩ else 0)
          = ∑ i : {c : N.ComplexIdx // N.classOf c = θ},
              PositiveKernel.smat N κ c i.val * bθ i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [dif_pos i.property]
        _ = bθ ⟨c, hc⟩ := congrFun hbθfix ⟨c, hc⟩
    · rw [dif_neg hc]
      refine Finset.sum_eq_zero fun c' _ => ?_
      by_cases hc' : N.classOf c' = θ
      · rw [hblock (by rw [hc']; exact hc), zero_mul]
      · rw [dif_neg hc', mul_zero]

end Network

end CRNT

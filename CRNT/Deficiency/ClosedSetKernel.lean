import CRNT.Theorems.DeficiencyZero.PositiveKernel
import CRNT.Deficiency.KineticBlock
import CRNT.Decision.StrongLinkage

/-!
# Kernel vectors supported on reaction-closed sets of complexes

A set `D` of complexes is **reaction-closed** when no reaction leaves it: every reaction whose
source lies in `D` has its target in `D`. The rescaled kinetic matrix `smat = 1 + d⁻¹ A_k` then
keeps its mass inside `D`, so its restriction to `D` is column-stochastic and Perron–Frobenius
supplies a nonnegative nonzero fixed vector there. Extended by zero this is a nonnegative
nonzero kernel vector of `A_k` supported on `D` (`exists_nonneg_kernelVector_on_closed`).

Both linkage classes and terminal strong linkage classes are reaction-closed (the latter by
terminality), so this is the common engine behind the per-class and per-terminal-class kernel
modes. The terminal strong linkage class of a complex `c` whose class is terminal is recorded
as `exists_nonneg_kernelVector_on_terminalSLC`.

Depends on: `CRNT.Theorems.DeficiencyZero.PositiveKernel`,
`CRNT.Deficiency.KineticBlock`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A reaction-closed set supports a nonnegative nonzero kernel vector of `A_k`.** The vector
vanishes at every complex outside the set. -/
theorem exists_nonneg_kernelVector_on_closed (N : Network S) (κ : RateConstants N)
    (D : N.ComplexIdx → Prop) (hclosed : ∀ r : N.R, D (N.sourceIdx r) → D (N.targetIdx r))
    {c0 : N.ComplexIdx} (hc0 : D c0) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c, 0 ≤ b c) ∧ b ≠ 0 ∧
      (∀ c, ¬ D c → b c = 0) ∧ N.kineticMap κ b = 0 := by
  classical
  haveI : Nonempty {c : N.ComplexIdx // D c} := ⟨⟨c0, hc0⟩⟩
  have hfilter : ∀ x : N.ComplexIdx, x ∈ Finset.univ.filter (fun c => D c) ↔ D x := by
    intro x; rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩
  -- mass cannot leave `D`: `smat i j = 0` when `j ∈ D` but `i ∉ D`.
  have hzero_block : ∀ {i j : N.ComplexIdx}, ¬ D i → D j → PositiveKernel.smat N κ i j = 0 := by
    intro i j hi hj
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [PositiveKernel.smat_apply, if_neg hij, zero_add]
    have hk : PositiveKernel.kmat N κ i j = 0 := by
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hsrc : N.sourceIdx r = j
      · have htgt : N.targetIdx r ≠ i := fun h => hi (h ▸ hclosed r (hsrc ▸ hj))
        rw [if_pos hsrc, if_neg htgt, if_neg hij.symm, sub_zero, mul_zero]
      · rw [if_neg hsrc]
    rw [hk, mul_zero]
  have hPcol : ∀ j : {c : N.ComplexIdx // D c},
      ∑ i : {c : N.ComplexIdx // D c}, PositiveKernel.smat N κ i.val j.val = 1 := by
    intro j
    rw [Finset.sum_subtype (Finset.univ.filter (fun c => D c)) hfilter
        (fun c => PositiveKernel.smat N κ c j.val) |>.symm,
      Finset.sum_subset (Finset.filter_subset _ _), PositiveKernel.smat_colsum]
    intro c _ hcf
    exact hzero_block (fun h => hcf ((hfilter c).mpr h)) j.property
  obtain ⟨bθ, hbθnn, hbθ0, hbθfix⟩ :=
    exists_nonneg_mulVec_fixed_of_colStochastic
      (fun i j : {c : N.ComplexIdx // D c} => PositiveKernel.smat N κ i.val j.val)
      (fun i j => PositiveKernel.smat_nonneg i.val j.val) hPcol
  refine ⟨fun c => if h : D c then bθ ⟨c, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro c
    dsimp only
    by_cases h : D c
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
      (if h : D c' then bθ ⟨c', h⟩ else 0) = _
    by_cases hc : D c
    · rw [dif_pos hc]
      have hzero : ∀ c' ∈ Finset.univ,
          c' ∉ Finset.univ.filter (fun c => D c) →
            PositiveKernel.smat N κ c c' * (if h : D c' then bθ ⟨c', h⟩ else 0) = 0 := by
        intro c' _ hc'
        rw [dif_neg (fun h => hc' ((hfilter c').mpr h)), mul_zero]
      rw [← Finset.sum_subset (Finset.filter_subset _ _) hzero,
        Finset.sum_subtype (Finset.univ.filter (fun c => D c)) hfilter
          (fun c' => PositiveKernel.smat N κ c c' * (if h : D c' then bθ ⟨c', h⟩ else 0))]
      calc ∑ i : {c : N.ComplexIdx // D c},
              PositiveKernel.smat N κ c i.val * (if h : D i.val then bθ ⟨i.val, h⟩ else 0)
          = ∑ i : {c : N.ComplexIdx // D c}, PositiveKernel.smat N κ c i.val * bθ i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [dif_pos i.property]
        _ = bθ ⟨c, hc⟩ := congrFun hbθfix ⟨c, hc⟩
    · rw [dif_neg hc]
      refine Finset.sum_eq_zero fun c' _ => ?_
      by_cases hc' : D c'
      · rw [hzero_block hc hc', zero_mul]
      · rw [dif_neg hc', mul_zero]

/-- **A terminal strong linkage class supports a nonnegative nonzero kernel vector of `A_k`.**
The vector vanishes off the strong linkage class of `c`. -/
theorem exists_nonneg_kernelVector_on_terminalSLC (N : Network S) (κ : RateConstants N)
    {c : N.ComplexIdx} (hc : N.IsTerminalSLC c.val) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c', 0 ≤ b c') ∧ b ≠ 0 ∧
      (∀ c', ¬ N.StronglyLinked c.val c'.val → b c' = 0) ∧ N.kineticMap κ b = 0 :=
  N.exists_nonneg_kernelVector_on_closed κ (fun c' => N.StronglyLinked c.val c'.val)
    (fun r h => hc r h) (StronglyLinked.refl N c.val)

end Network

end CRNT

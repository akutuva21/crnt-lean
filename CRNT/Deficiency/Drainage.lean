import CRNT.Deficiency.TerminalReachable
import CRNT.Deficiency.DeficiencyOneHypotheses
import CRNT.Theorems.DeficiencyZero.PositiveKernel

/-!
# Mass drains to terminal strong linkage classes

A nonnegative kernel vector of the kinetic matrix `A_k` is supported only on terminal strong
linkage classes: if `b ≥ 0`, `A_k b = 0`, and `b c > 0`, then `c`'s strong linkage class is
terminal (`isTerminalSLC_of_pos_kernel`).

Three ingredients combine. Terminal classes are *absorbing*, so the rescaled matrix `smat` has
no edge from a transient column to a terminal row (`habsorb` below). The support of `b` is
*forward closed* under reactions (`hforward`). And a *mass-balance* identity over the transient
complexes forces, at every transient complex carrying positive mass, no leak to terminal
complexes — making the transient support reaction-closed. A reaction-closed set always contains
a terminal class (`exists_terminal_mem_of_closed`), so the transient support is empty.

This is the structural input that pins `dim ker A_k` to the number of terminal strong linkage
classes.

Depends on: `CRNT.Deficiency.TerminalReachable`,
`CRNT.Deficiency.DeficiencyOneHypotheses`, `CRNT.Theorems.DeficiencyZero.PositiveKernel`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A nonnegative kernel vector of `A_k` is supported on terminal strong linkage classes.**
If `b ≥ 0`, `A_k b = 0`, and `b c > 0`, then the strong linkage class of `c` is terminal. -/
theorem isTerminalSLC_of_pos_kernel (N : Network S) (κ : RateConstants N)
    {b : N.ComplexIdx → ℝ} (hbnn : ∀ c, 0 ≤ b c) (hbker : N.kineticMap κ b = 0)
    {c : N.ComplexIdx} (hbc : 0 < b c) : N.IsTerminalSLC c.val := by
  classical
  have hfix : (PositiveKernel.smat N κ).mulVec b = b := (PositiveKernel.smat_fix_iff b).mpr hbker
  -- Terminal classes are absorbing: no `smat` edge from a transient column to a terminal row.
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
  -- The support of `b` is forward closed under reactions.
  have hforward : ∀ {x y : N.ComplexIdx}, 0 < b x →
      (∃ r, N.sourceIdx r = x ∧ N.targetIdx r = y) → 0 < b y := by
    rintro x y hbx ⟨r, hs, ht⟩
    have hsmat : 0 < PositiveKernel.smat N κ y x :=
      lt_of_le_of_ne (PositiveKernel.smat_nonneg y x)
        (Ne.symm (PositiveKernel.smat_ne_zero_of_reaction r hs ht))
    have hsum : 0 < ∑ x', PositiveKernel.smat N κ y x' * b x' :=
      Finset.sum_pos' (fun x' _ => mul_nonneg (PositiveKernel.smat_nonneg y x') (hbnn x'))
        ⟨x, Finset.mem_univ x, mul_pos hsmat hbx⟩
    have hval : (∑ x', PositiveKernel.smat N κ y x' * b x') = b y := congrFun hfix y
    rwa [hval] at hsum
  -- Mass balance over the transient complexes.
  set Tset : Finset N.ComplexIdx := Finset.univ.filter (fun c => ¬ N.IsTerminalSLC c.val)
    with hTset
  have hmemT : ∀ x, x ∈ Tset ↔ ¬ N.IsTerminalSLC x.val := by
    intro x; rw [hTset, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩
  have hmass : ∑ x ∈ Tset, b x
      = ∑ x ∈ Tset, (∑ z ∈ Tset, PositiveKernel.smat N κ z x) * b x := by
    calc ∑ x ∈ Tset, b x
        = ∑ x ∈ Tset, ∑ z, PositiveKernel.smat N κ x z * b z := by
          refine Finset.sum_congr rfl fun x _ => ?_
          exact (congrFun hfix x).symm
      _ = ∑ z, ∑ x ∈ Tset, PositiveKernel.smat N κ x z * b z := Finset.sum_comm
      _ = ∑ z, (∑ x ∈ Tset, PositiveKernel.smat N κ x z) * b z := by
          refine Finset.sum_congr rfl fun z _ => ?_; rw [Finset.sum_mul]
      _ = ∑ z ∈ Tset, (∑ x ∈ Tset, PositiveKernel.smat N κ x z) * b z := by
          symm
          refine Finset.sum_subset (Finset.filter_subset _ _) fun z _ hz => ?_
          have hzterm : N.IsTerminalSLC z.val := by
            by_contra h; exact hz ((hmemT z).mpr h)
          have hz0 : ∑ x ∈ Tset, PositiveKernel.smat N κ x z = 0 :=
            Finset.sum_eq_zero fun x hx => habsorb hzterm ((hmemT x).mp hx)
          rw [hz0, zero_mul]
  have hterm0 : ∀ x ∈ Tset,
      (1 - ∑ z ∈ Tset, PositiveKernel.smat N κ z x) * b x = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp ?_
    · intro x _
      refine mul_nonneg ?_ (hbnn x)
      have hSle : ∑ z ∈ Tset, PositiveKernel.smat N κ z x ≤ 1 := by
        rw [← PositiveKernel.smat_colsum x]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun z _ _ => PositiveKernel.smat_nonneg z x)
      linarith
    · have hexpand : ∀ x, (1 - ∑ z ∈ Tset, PositiveKernel.smat N κ z x) * b x
          = b x - (∑ z ∈ Tset, PositiveKernel.smat N κ z x) * b x := fun x => by ring
      rw [Finset.sum_congr rfl (fun x _ => hexpand x), Finset.sum_sub_distrib, hmass, sub_self]
  -- No leak: at a transient complex carrying positive mass, no `smat` edge reaches terminal.
  have hnoleak : ∀ x : N.ComplexIdx, ¬ N.IsTerminalSLC x.val → 0 < b x →
      ∀ z : N.ComplexIdx, N.IsTerminalSLC z.val → PositiveKernel.smat N κ z x = 0 := by
    intro x hx hbx z hz
    have h0 := hterm0 x ((hmemT x).mpr hx)
    have hS1 : ∑ z' ∈ Tset, PositiveKernel.smat N κ z' x = 1 := by
      rcases mul_eq_zero.mp h0 with h | h
      · linarith
      · exact absurd h hbx.ne'
    have hcompl : ∑ z' ∈ Tsetᶜ, PositiveKernel.smat N κ z' x = 0 := by
      have hadd := Finset.sum_add_sum_compl Tset (fun z' => PositiveKernel.smat N κ z' x)
      rw [hS1, PositiveKernel.smat_colsum x] at hadd
      linarith
    have hzc : z ∈ Tsetᶜ := Finset.mem_compl.mpr (fun h => ((hmemT z).mp h) hz)
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun z' _ => PositiveKernel.smat_nonneg z' x)).mp hcompl z hzc
  -- The transient support is reaction-closed, hence empty.
  by_contra hcterm
  obtain ⟨d, ⟨_, hdtrans⟩, hdterm⟩ :=
    N.exists_terminal_mem_of_closed
      (D := fun x => 0 < b x ∧ ¬ N.IsTerminalSLC x.val)
      (fun r ⟨hbsrc, hsrctrans⟩ => by
        refine ⟨hforward hbsrc ⟨r, rfl, rfl⟩, fun htgtterm => ?_⟩
        exact PositiveKernel.smat_ne_zero_of_reaction r rfl rfl
          (hnoleak (N.sourceIdx r) hsrctrans hbsrc (N.targetIdx r) htgtterm))
      ⟨hbc, hcterm⟩
  exact hdtrans hdterm

/-- **A strictly positive kernel vector of `A_k` forces weak reversibility.** If `b > 0`
everywhere and `A_k b = 0`, every complex's strong linkage class is terminal, so every
reaction's target reaches its source. -/
theorem weaklyReversible_of_exists_pos_kernelVector (N : Network S) (κ : RateConstants N)
    {b : N.ComplexIdx → ℝ} (hbpos : ∀ c, 0 < b c) (hbker : N.kineticMap κ b = 0) :
    N.WeaklyReversible := fun r =>
  ((N.isTerminalSLC_of_pos_kernel κ (fun c => (hbpos c).le) hbker (hbpos (N.sourceIdx r))) r
    (StronglyLinked.refl N (N.sourceIdx r).val)).2

/-- **Weak reversibility is equivalent to the existence of a strictly positive kernel vector of
`A_k`.** The forward direction is the Perron–Frobenius construction; the reverse is drainage. -/
theorem weaklyReversible_iff_exists_pos_kernelVector (N : Network S) (κ : RateConstants N) :
    N.WeaklyReversible ↔ ∃ b : N.ComplexIdx → ℝ, (∀ c, 0 < b c) ∧ N.kineticMap κ b = 0 :=
  ⟨fun hwr => PositiveKernel.weaklyReversible_exists_positive_kernelVector N hwr κ,
   fun ⟨_, hbpos, hbker⟩ => N.weaklyReversible_of_exists_pos_kernelVector κ hbpos hbker⟩

end Network

end CRNT

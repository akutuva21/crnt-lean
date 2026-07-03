import CRNT.Deficiency.PerClassKernelPos

/-!
# Uniqueness of the per-class kernel mode

On a strongly connected linkage class the kernel of `A_k` is one-dimensional: any kernel
vector supported on the class is a scalar multiple of the strictly positive one
(`perClass_kernel_unique`). The argument is Perron–Frobenius uniqueness localized to the
class: the minimum of the ratio `v/a` over the class is attained at some `c₀`, and
`w := v − t·a` is a nonnegative fixed vector of `smat` vanishing at `c₀`, so positivity
spreading forces it to vanish throughout the class — and it already vanishes off the class.

This completes the per-class kernel structure: each strongly connected class (in particular
each class of a weakly reversible network) contributes exactly one kernel mode of `A_k`.

Depends on: `CRNT.Deficiency.PerClassKernelPos`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Uniqueness of the per-class kernel mode.** On a strongly connected class, a kernel
vector `v` supported on the class is a scalar multiple of a strictly-positive-on-class kernel
vector `a`. -/
theorem perClass_kernel_unique (N : Network S) (κ : RateConstants N)
    (θ : Quotient N.linkedSetoid)
    (hθ : ∀ c c' : N.ComplexIdx, N.classOf c = θ → N.classOf c' = θ → N.Reaches c.val c'.val)
    {a v : N.ComplexIdx → ℝ}
    (hapos : ∀ c, N.classOf c = θ → 0 < a c) (haoff : ∀ c, N.classOf c ≠ θ → a c = 0)
    (haker : N.kineticMap κ a = 0)
    (hvoff : ∀ c, N.classOf c ≠ θ → v c = 0) (hvker : N.kineticMap κ v = 0) :
    ∃ t : ℝ, v = t • a := by
  classical
  obtain ⟨c0, hc0⟩ := Quotient.exists_rep θ
  set T : Finset N.ComplexIdx := Finset.univ.filter (fun c => N.classOf c = θ) with hTdef
  have hmemT : ∀ c, c ∈ T ↔ N.classOf c = θ := by
    intro c; rw [hTdef, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ c, h⟩⟩
  have hc0T : c0 ∈ T := (hmemT c0).mpr hc0
  obtain ⟨cm, hcmT, hmin⟩ := Finset.exists_min_image T (fun c => v c / a c) ⟨c0, hc0T⟩
  have hcmcls : N.classOf cm = θ := (hmemT cm).mp hcmT
  set t := v cm / a cm with ht
  refine ⟨t, ?_⟩
  set w := v - t • a with hw
  have hafix : (PositiveKernel.smat N κ).mulVec a = a := (PositiveKernel.smat_fix_iff a).mpr haker
  have hvfix : (PositiveKernel.smat N κ).mulVec v = v := (PositiveKernel.smat_fix_iff v).mpr hvker
  have hwfix : (PositiveKernel.smat N κ).mulVec w = w := by
    rw [hw, Matrix.mulVec_sub, Matrix.mulVec_smul, hvfix, hafix]
  have hwnn : ∀ c, 0 ≤ w c := by
    intro c
    by_cases hc : N.classOf c = θ
    · have hle : t ≤ v c / a c := hmin c ((hmemT c).mpr hc)
      rw [le_div_iff₀ (hapos c hc)] at hle
      simp only [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; linarith
    · rw [hw]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hvoff c hc, haoff c hc, mul_zero,
        sub_zero, le_refl]
  have hwcm : w cm = 0 := by
    have hcancel : v cm / a cm * a cm = v cm := div_mul_cancel₀ (v cm) (hapos cm hcmcls).ne'
    simp only [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ht]
    rw [hcancel, sub_self]
  have hw0 : w = 0 := by
    funext c
    by_cases hc : N.classOf c = θ
    · by_contra hne
      have hcpos : 0 < w c := (hwnn c).lt_of_ne (Ne.symm hne)
      have hreach : N.Reaches c.val cm.val := hθ c cm hc hcmcls
      have hsupp : supportReaches (PositiveKernel.smat N κ) cm c :=
        PositiveKernel.reaches_supportReaches c.val c.property hreach cm.property
      have hpos := pos_of_supportReaches_pos (PositiveKernel.smat N κ)
        PositiveKernel.smat_nonneg w hwnn hwfix hsupp hcpos
      rw [hwcm] at hpos; exact lt_irrefl 0 hpos
    · rw [hw]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hvoff c hc, haoff c hc, mul_zero,
        sub_zero, Pi.zero_apply]
  rw [← sub_eq_zero, ← hw]; exact hw0

end Network

end CRNT

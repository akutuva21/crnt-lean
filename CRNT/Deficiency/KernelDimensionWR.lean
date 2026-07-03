import CRNT.Deficiency.PerClassKernelUnique
import CRNT.Deficiency.KernelDimensionBound

/-!
# The kinetic-map kernel of a weakly reversible network has dimension `ℓ`

For a weakly reversible network every linkage class is strongly connected, so it contributes
exactly one kernel mode of `A_k` (`exists_pos_kernelVector_on_class_of_weaklyReversible`,
`perClass_kernel_unique`). These modes have disjoint supports, hence are a basis of the
kernel:

```text
dim ker A_k = ℓ.
```

(`finrank_ker_kineticMap_eq_of_weaklyReversible`). With the always-valid lower bound `ℓ ≤
dim ker A_k`, the content here is the matching upper bound: every kernel vector is a
combination of the per-class modes.

Depends on: `CRNT.Deficiency.PerClassKernelUnique`,
`CRNT.Deficiency.KernelDimensionBound`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **`dim ker A_k = ℓ` for a weakly reversible network.** -/
theorem finrank_ker_kineticMap_eq_of_weaklyReversible (N : Network S)
    (hwr : N.WeaklyReversible) (κ : RateConstants N) :
    Module.finrank ℝ (LinearMap.ker (N.kineticMap κ)) = N.numLinkageClasses := by
  classical
  choose a hapos haoff haker using
    fun θ => N.exists_pos_kernelVector_on_class_of_weaklyReversible hwr κ θ
  have hsc : ∀ (θ : Quotient N.linkedSetoid) (c c' : N.ComplexIdx),
      N.classOf c = θ → N.classOf c' = θ → N.Reaches c.val c'.val :=
    fun _ c c' hc hc' => hwr.reaches_of_linked (Quotient.exact (hc.trans hc'.symm))
  refine le_antisymm ?_ (N.numLinkageClasses_le_finrank_ker_kineticMap κ)
  have hker_le : LinearMap.ker (N.kineticMap κ) ≤ Submodule.span ℝ (Set.range a) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    rw [← N.sum_restrictToClass v]
    refine Submodule.sum_mem _ fun θ _ => ?_
    have hsupp : ∀ c, N.classOf c ≠ θ → N.restrictToClass θ v c = 0 :=
      fun c hc => restrictToClass_apply_of_ne N v hc
    have hkerv : N.kineticMap κ (N.restrictToClass θ v) = 0 := by
      rw [kineticMap_restrictToClass, hv]
      funext c; simp [restrictToClass]
    obtain ⟨t, ht⟩ :=
      N.perClass_kernel_unique κ θ (hsc θ) (hapos θ) (haoff θ) (haker θ) hsupp hkerv
    rw [ht]
    exact Submodule.smul_mem _ t (Submodule.subset_span ⟨θ, rfl⟩)
  calc Module.finrank ℝ (LinearMap.ker (N.kineticMap κ))
      ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range a)) := Submodule.finrank_mono hker_le
    _ ≤ Fintype.card (Quotient N.linkedSetoid) := by
        refine (finrank_span_le_card (Set.range a)).trans ?_
        exact (Set.toFinset_range a ▸ Finset.card_image_le).trans_eq (by simp)
    _ = N.numLinkageClasses := card_quotient_eq N

end Network

end CRNT

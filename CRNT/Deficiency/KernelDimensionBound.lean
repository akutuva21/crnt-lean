import CRNT.Deficiency.PerClassKernel

/-!
# The kinetic-map kernel has dimension at least the number of linkage classes

Each linkage class supports a nonzero kernel vector of `A_k`
(`exists_nonneg_kernelVector_on_class`), and vectors supported on distinct linkage classes are
linearly independent. Collecting one per class gives `ℓ` independent kernel vectors, so

```text
ℓ ≤ dim ker A_k
```

(`numLinkageClasses_le_finrank_ker_kineticMap`). This is the easy half of Feinberg's identity
`dim ker A_k = t` (the number of terminal strong linkage classes); under the deficiency-one
condition `t = ℓ`, the bound is tight.

Depends on: `CRNT.Deficiency.PerClassKernel`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **`ℓ ≤ dim ker A_k`.** The number of linkage classes bounds the dimension of the kinetic
map's kernel from below. -/
theorem numLinkageClasses_le_finrank_ker_kineticMap (N : Network S) (κ : RateConstants N) :
    N.numLinkageClasses ≤ Module.finrank ℝ (LinearMap.ker (N.kineticMap κ)) := by
  classical
  choose b hbnn hb0 hbsupp hbker using fun θ => N.exists_nonneg_kernelVector_on_class κ θ
  have hli : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg θ₀
    obtain ⟨c₀, hc₀⟩ := Function.ne_iff.mp (hb0 θ₀)
    have hcls : N.classOf c₀ = θ₀ := by
      by_contra h; exact hc₀ (hbsupp θ₀ c₀ h)
    have hgc := congrFun hg c₀
    rw [Finset.sum_apply] at hgc
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hgc
    rw [Finset.sum_eq_single θ₀] at hgc
    · exact (mul_eq_zero.mp hgc).resolve_right hc₀
    · intro θ _ hθ
      rw [hbsupp θ c₀ (by rw [hcls]; exact fun h => hθ h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ θ₀) h
  have hspan_le : Submodule.span ℝ (Set.range b) ≤ LinearMap.ker (N.kineticMap κ) := by
    rw [Submodule.span_le]
    rintro _ ⟨θ, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hbker θ
  calc N.numLinkageClasses
      = Fintype.card (Quotient N.linkedSetoid) := (card_quotient_eq N).symm
    _ = Module.finrank ℝ (Submodule.span ℝ (Set.range b)) := (finrank_span_eq_card hli).symm
    _ ≤ Module.finrank ℝ (LinearMap.ker (N.kineticMap κ)) := Submodule.finrank_mono hspan_le

/-- **`dim(range A_k) + ℓ ≤ n`.** Dually to the kernel bound, the rank of the kinetic map is
at most `n − ℓ` — the number of complexes net of the linkage classes. -/
theorem finrank_range_kineticMap_add_numLinkageClasses_le (N : Network S) (κ : RateConstants N) :
    Module.finrank ℝ (LinearMap.range (N.kineticMap κ)) + N.numLinkageClasses ≤ N.numComplexes := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (N.kineticMap κ)
  have hdom : Module.finrank ℝ (N.ComplexIdx → ℝ) = N.numComplexes := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_coe, numComplexes]
  have hk := N.numLinkageClasses_le_finrank_ker_kineticMap κ
  rw [hdom] at hrn
  omega

end Network

end CRNT

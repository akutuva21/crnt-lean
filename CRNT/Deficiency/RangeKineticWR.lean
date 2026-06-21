import CRNT.Deficiency.KernelDimensionWR
import CRNT.Deficiency.SteadyStateKernel

/-!
# The kinetic image of a weakly reversible network fills the cut space

The kinetic map factors through the incidence map, so `Im A_k ⊆ Im ∂` always. For a weakly
reversible network the two have equal dimension `n − ℓ` — the kernel dimension is `ℓ`
(`finrank_ker_kineticMap_eq_of_weaklyReversible`) and `rank ∂ = n − ℓ`
(`incidenceRank_add_numLinkageClasses`) — so the inclusion is an equality:

```text
Im A_k = Im ∂.
```

(`range_kineticMap_eq_range_incidenceMap_of_weaklyReversible`).

This module is **stable**. Depends on: `CRNT.Deficiency.KernelDimensionWR`,
`CRNT.Deficiency.SteadyStateKernel`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **`Im A_k = Im ∂` for a weakly reversible network.** -/
theorem range_kineticMap_eq_range_incidenceMap_of_weaklyReversible (N : Network S)
    (hwr : N.WeaklyReversible) (κ : RateConstants N) :
    LinearMap.range (N.kineticMap κ) = LinearMap.range N.incidenceMap := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨v, rfl⟩; exact N.kineticMap_mem_range_incidenceMap κ v
  · have hrn := LinearMap.finrank_range_add_finrank_ker (N.kineticMap κ)
    have hdom : Module.finrank ℝ (N.ComplexIdx → ℝ) = N.numComplexes := by
      rw [Module.finrank_fintype_fun_eq_card]; simp only [Fintype.card_coe, numComplexes]
    have hker := N.finrank_ker_kineticMap_eq_of_weaklyReversible hwr κ
    have hinc := N.incidenceRank_add_numLinkageClasses
    have hrange_inc : Module.finrank ℝ (LinearMap.range N.incidenceMap) = N.incidenceRank := rfl
    rw [hdom, hker] at hrn
    rw [hrange_inc]
    omega

end Network

end CRNT

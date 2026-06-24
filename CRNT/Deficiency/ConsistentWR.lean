import CRNT.Deficiency.Consistent
import CRNT.Deficiency.KernelDimension
import CRNT.Theorems.DeficiencyZero.PositiveKernel

/-!
# Weakly reversible networks are consistent

A weakly reversible network is **consistent**: its reaction vectors are positively dependent. This
makes consistency — the first of the three conditions of a *regular* network (`RegularNetwork`) —
automatic for weakly reversible networks.

The witnessing positive weighting is a complex-balancing flux. For any rate constants `κ`, weak
reversibility provides a strictly positive kernel vector `b` of the kinetic map
(`weaklyReversible_exists_positive_kernelVector`): `kineticMap κ b = 0`. Reading `kineticMap κ b`
as `incidenceMap` applied to the reaction flux `α r = κ_r · b_{source r}`, and mapping through the
complex matrix (`complexMap ∘ incidenceMap = stoichMap`), the flux satisfies
`∑_r α_r (y'_r − y_r) = stoichMap α = complexMap (kineticMap κ b) = 0`, with every `α_r > 0`.

* `isConsistent_of_weaklyReversible` — `WeaklyReversible → IsConsistent`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Deficiency.Consistent`,
`CRNT.Deficiency.KernelDimension`, `CRNT.Theorems.DeficiencyZero.PositiveKernel`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A weakly reversible network is consistent.** The complex-balancing flux `α_r = κ_r·b_{source r}`
from a positive kinetic-kernel vector `b` is a strictly positive weighting under which the weighted
reaction vectors cancel. -/
theorem isConsistent_of_weaklyReversible (N : Network S) (hwr : N.WeaklyReversible) :
    N.IsConsistent := by
  -- Any rate constants will do; take all-ones.
  let κ : N.RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩
  obtain ⟨b, hbpos, hbker⟩ :=
    PositiveKernel.weaklyReversible_exists_positive_kernelVector N hwr κ
  -- The reaction flux `α r = κ_r · b_{source r}` is strictly positive.
  refine ⟨fun r => κ.k r * b (N.sourceIdx r),
    fun r => mul_pos (κ.positive r) (hbpos _), ?_⟩
  -- `kineticMap κ b` is `incidenceMap` of that flux.
  have hkin : N.kineticMap κ b
      = N.incidenceMap (fun r => κ.k r * b (N.sourceIdx r)) := by
    funext c
    rw [incidenceMap_apply]
    rfl
  -- The weighted reaction-vector sum is `stoichMap` of the flux.
  have hstoich : N.stoichMap (fun r => κ.k r * b (N.sourceIdx r))
      = ∑ r, (κ.k r * b (N.sourceIdx r)) • N.reactionVector r := by
    funext s
    rw [stoichMap_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
  -- Chain: `∑ α_r v_r = stoichMap α = complexMap (incidenceMap α) = complexMap (kineticMap κ b) = 0`.
  rw [← hstoich, ← complexMap_comp_incidenceMap, LinearMap.comp_apply, ← hkin, hbker, map_zero]

end Network

end CRNT

import CRNT.Multistationarity.RegularValueDegree
import CRNT.Multistationarity.ReducedJacobian
import CRNT.Equilibria.SteadyState

/-!
# Steady-state existence from a nonzero topological degree

The mass-action steady states in a stoichiometric compatibility class of `x₀` are the zeros of the
**reduced field** `reducedField κ x₀ : (Fin s → ℝ) → (Fin s → ℝ)` (`s = stoichRank N`), the
mass-action vector field read in the chart of the compatibility class. It is a self-map of the
`s`-dimensional reduced space, so the regular-value topological degree applies: when the reduced
field has a nonzero regular degree at the value `0`, its existence principle
(`preimage_nonempty_of_regularDegree_ne_zero`) produces a chart point mapping to `0`, which pulls
back to a positive-class mass-action steady state.

The bridge from "`reducedField` vanishes" to "the full field vanishes" uses that the mass-action
vector field always lies in the stoichiometric subspace `S(N)`
(`massActionVectorField_mem_stoichSubspace`) and that the chart inverts the projection there
(`stoichChart_stoichProj`): on `S(N)` the projection `stoichProj` is injective, so a zero of its
projection is a genuine zero.

This is the existence backbone of the `∃`-side multistationarity theory (Müller–Regensburger): the
degree-theoretic counterpart of the injectivity (`∀`-side) reduction, which runs the *same* reduced
field and reduced Jacobian.

* `massActionVectorField_mem_stoichSubspace` — the field lies in `S(N)`.
* `exists_isMassActionSteadyState_of_reducedDegree_ne_zero` — nonzero reduced regular degree at `0`
  forces a steady state in `x₀`'s compatibility class.

This module is `sorry`-free.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The mass-action vector field lies in the stoichiometric subspace.** It is a sum of reaction
vectors scaled by the (nonnegative) reaction rates, and each reaction vector lies in `S(N)`. -/
theorem massActionVectorField_mem_stoichSubspace (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : N.massActionVectorField κ x ∈ N.stoichSubspace := by
  have hsum : N.massActionVectorField κ x
      = ∑ r : N.R, (N.massActionRate κ r x) • (N.reactionVector r) := by
    funext s
    simp only [massActionVectorField_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  exact Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)

/-- **Steady-state existence from a nonzero degree.** If the reduced field `reducedField κ x₀` has a
nonzero regular degree at `0`, then the value `0` is attained, and the attaining chart point pulls
back to a mass-action steady state in `x₀`'s stoichiometric compatibility class. -/
theorem exists_isMassActionSteadyState_of_reducedDegree_ne_zero
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (hfin : ((N.reducedField κ x₀) ⁻¹' {0}).Finite)
    (hdeg : regularDegree (N.reducedField κ x₀) 0 hfin ≠ 0) :
    ∃ x, N.StoichCompatible x₀ x ∧ N.IsMassActionSteadyState κ x := by
  obtain ⟨y, hy⟩ :=
    preimage_nonempty_of_regularDegree_ne_zero (N.reducedField κ x₀) 0 hfin hdeg
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
  refine ⟨N.affineChart x₀ y, ?_, ?_⟩
  · show (N.affineChart x₀ y - x₀) ∈ N.stoichSubspace
    simp only [affineChart, add_sub_cancel_left]
    exact N.stoichChart_mem y
  · have hV : N.massActionVectorField κ (N.affineChart x₀ y) ∈ N.stoichSubspace :=
      N.massActionVectorField_mem_stoichSubspace κ _
    have hrec : N.stoichProj (N.massActionVectorField κ (N.affineChart x₀ y)) = 0 := hy
    have hVeq0 : N.massActionVectorField κ (N.affineChart x₀ y) = 0 := by
      have hcp := N.stoichChart_stoichProj hV
      rw [hrec, map_zero] at hcp
      exact hcp.symm
    exact fun s => congrFun hVeq0 s

end Network

end CRNT

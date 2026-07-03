import CRNT.Multistationarity.RegularValueDegree
import CRNT.Multistationarity.ReducedJacobian
import CRNT.Multistationarity.Capacity
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

/-- **A zero of the reduced field is a steady state in the class.** If `reducedField κ x₀ y = 0`,
its chart point `affineChart x₀ y` is stoichiometrically compatible with `x₀` and is a mass-action
steady state. The projection `stoichProj` is injective on `S(N)`, where the field lives, so the
vanishing of the projection forces the full field to vanish. -/
theorem isMassActionSteadyState_affineChart_of_reducedField_eq_zero
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) {y : Fin N.stoichRank → ℝ}
    (hy : N.reducedField κ x₀ y = 0) :
    N.StoichCompatible x₀ (N.affineChart x₀ y)
      ∧ N.IsMassActionSteadyState κ (N.affineChart x₀ y) := by
  refine ⟨?_, ?_⟩
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
  exact ⟨N.affineChart x₀ y,
    N.isMassActionSteadyState_affineChart_of_reducedField_eq_zero κ x₀ hy⟩

/-- **Multistationarity from two positive zeros of the reduced field.** Two distinct chart points at
which the reduced field vanishes, both with strictly positive concentrations, give two distinct
positive steady states in one compatibility class — exactly the capacity for multiple steady states.
The chart `affineChart x₀` is injective, so distinct chart points give distinct steady states. -/
theorem hasMultistationarityCapacity_of_two_positive_zeros
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) {y₁ y₂ : Fin N.stoichRank → ℝ}
    (hy₁ : N.reducedField κ x₀ y₁ = 0) (hy₂ : N.reducedField κ x₀ y₂ = 0)
    (hp₁ : Concentration.Positive (N.affineChart x₀ y₁)) (hp₂ : Concentration.Positive (N.affineChart x₀ y₂))
    (hne : y₁ ≠ y₂) : N.HasMultistationarityCapacity := by
  obtain ⟨hc₁, hs₁⟩ := N.isMassActionSteadyState_affineChart_of_reducedField_eq_zero κ x₀ hy₁
  obtain ⟨hc₂, hs₂⟩ := N.isMassActionSteadyState_affineChart_of_reducedField_eq_zero κ x₀ hy₂
  exact ⟨κ, x₀, N.affineChart x₀ y₁, N.affineChart x₀ y₂, ⟨hc₁, hp₁⟩, ⟨hc₂, hp₂⟩, hs₁, hs₂,
    fun heq => hne (N.affineChart_injective x₀ heq)⟩

/-- **Multistationarity from a sign-indefinite reduced Jacobian.** If the reduced field vanishes at
two positive chart points whose reduced-Jacobian determinants have opposite signs, the network has
the capacity for multiple steady states. Opposite determinant signs force the two points to be
distinct, so the orientation-indefiniteness of the steady-state set is itself the multistationarity
witness — the degree-theoretic (`∃`-side) counterpart of the consistent-sign P-matrix injectivity
criterion. -/
theorem hasMultistationarityCapacity_of_signIndefinite
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) {y₁ y₂ : Fin N.stoichRank → ℝ}
    (hy₁ : N.reducedField κ x₀ y₁ = 0) (hy₂ : N.reducedField κ x₀ y₂ = 0)
    (hp₁ : Concentration.Positive (N.affineChart x₀ y₁)) (hp₂ : Concentration.Positive (N.affineChart x₀ y₂))
    (hpos : 0 < (N.reducedJacobian κ x₀ y₁).det) (hneg : (N.reducedJacobian κ x₀ y₂).det < 0) :
    N.HasMultistationarityCapacity := by
  refine N.hasMultistationarityCapacity_of_two_positive_zeros κ x₀ hy₁ hy₂ hp₁ hp₂ ?_
  intro heq
  rw [heq] at hpos
  exact absurd hpos (lt_asymm hneg)

end Network

end CRNT

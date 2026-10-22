import CRNT.Dynamics.DelayComparisonLocal
import CRNT.Extensions.DelayMassAction
import CRNT.Dynamics.MassActionDelayComparison

/-! # A bounded nonnegative mass-action delay comparison class

For reactions whose source contains at most one species, the delayed field is monotone in the
delayed concentration and satisfies the Kamke condition in the current concentration. On bounded
nonnegative trajectory segments, its current-state dependence is Lipschitz on a join-closed
region. This module connects those facts to the local method-of-steps comparison theorem for a
common reaction delay. -/

namespace CRNT
namespace Network

open scoped BigOperators
open scoped NNReal

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The network with the same source complexes but zero product complexes, retaining each
reaction index and rate. Its mass-action field is exactly the negative current-consumption part
of the delay field. -/
def currentConsumptionNetwork (N : Network S) : Network S where
  R := N.R
  decEqR := N.decEqR
  fintypeR := N.fintypeR
  reaction := fun r => ⟨(N.reaction r).source, 0⟩

/-- Copy the original positive rates to the current-consumption network. -/
def currentConsumptionRates (N : Network S) (κ : N.RateConstants) :
    N.currentConsumptionNetwork.RateConstants where
  k := κ.k
  positive := κ.positive

@[simp] theorem currentConsumptionVectorField_apply (N : Network S) (κ : N.RateConstants)
    (u : Concentration S) (s : S) :
    N.currentConsumptionNetwork.massActionVectorField (N.currentConsumptionRates κ) u s =
      -(∑ r, κ.k r * (N.reaction r).source.massActionMonomial u *
        ((N.reaction r).source s : ℝ)) := by
  simp [massActionVectorField_apply, massActionRate, currentConsumptionNetwork,
    currentConsumptionRates, reactionVector, Reaction.vector]

/-- The production contribution from a fixed common delayed state. -/
noncomputable def delayedProductionVector (N : Network S) (κ : N.RateConstants)
    (v : Concentration S) : Concentration S :=
  fun s => ∑ r, κ.k r * (N.reaction r).source.massActionMonomial v *
    ((N.reaction r).target s : ℝ)

/-- At a fixed delayed concentration, only the current-consumption field varies with `u`. -/
theorem massActionDelayField_eq_delayedProduction_add_consumption
    (N : Network S) (κ : N.RateConstants) (u v : Concentration S) :
    N.massActionDelayField κ u (fun _ => v) =
      N.delayedProductionVector κ v +
        N.currentConsumptionNetwork.massActionVectorField (N.currentConsumptionRates κ) u := by
  funext s
  simp only [massActionDelayField, delayedProductionVector, Pi.add_apply,
    currentConsumptionVectorField_apply]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  congr 1
  ext r
  ring

/-- For every fixed delayed state, the common-delay mass-action field is Lipschitz in the current
state on any bounded ball. The Lipschitz constant is that of the network with all target
complexes replaced by zero, which bounds exactly current consumption (the delayed production
term is constant in the current argument). -/
theorem massActionDelayField_lipschitzOnWith_closedBall
    (N : Network S) (κ : N.RateConstants) (B : ℝ) (v : Concentration S) :
    LipschitzOnWith
      (Real.toNNReal (massActionLipschitzConstant N.currentConsumptionNetwork
        (N.currentConsumptionRates κ) B))
      (fun u => N.massActionDelayField κ u (fun _ => v)) (Metric.closedBall 0 B) := by
  intro u hu u' hu'
  change edist (N.massActionDelayField κ u (fun _ => v))
    (N.massActionDelayField κ u' (fun _ => v)) ≤ _
  rw [massActionDelayField_eq_delayedProduction_add_consumption,
    massActionDelayField_eq_delayedProduction_add_consumption]
  rw [edist_add_left]
  exact N.currentConsumptionNetwork.massActionVectorField_lipschitzOnWith_closedBall
    (N.currentConsumptionRates κ) B hu hu'

/-- With a single-species source, the current-consumption contribution to coordinate `i` is
unchanged when the current states agree at `i`. -/
theorem massActionDelayField_currentConsumption_coord_eq
    (N : Network S) (κ : N.RateConstants) (hsrc : N.HasSingleSpeciesSources)
    (u u' : Concentration S) (i : S) (hui : u i = u' i) :
    (∑ r, κ.k r * (N.reaction r).source.massActionMonomial u *
        ((N.reaction r).source i : ℝ)) =
      (∑ r, κ.k r * (N.reaction r).source.massActionMonomial u' *
        ((N.reaction r).source i : ℝ)) := by
  apply Finset.sum_congr rfl
  intro r _
  by_cases hzero : (N.reaction r).source i = 0
  · simp [hzero]
  · have hsupp : ∀ j, j ≠ i → (N.reaction r).source j = 0 := by
      intro j hji
      by_contra hj
      have hjpos : 0 < (N.reaction r).source j := Nat.pos_of_ne_zero hj
      exact hji (hsrc r i j hzero hjpos.ne.symm).symm
    rw [massActionMonomial_eq_of_support hsupp hui]

/-- For a source with at most one species, the mass-action delay field satisfies the current
Kamke condition on nonnegative delayed states. In fact, its coordinate is unchanged when the
corresponding current coordinate is held fixed. -/
theorem massActionDelayField_kamke_of_singleSpeciesSources
    (N : Network S) (κ : N.RateConstants) (hsrc : N.HasSingleSpeciesSources)
    (u u' v : Concentration S) (i : S) (hui : u i = u' i)
    :
    N.massActionDelayField κ u (fun _ => v) i ≤
      N.massActionDelayField κ u' (fun _ => v) i := by
  unfold massActionDelayField
  refine Finset.sum_le_sum fun r _ => ?_
  by_cases hzero : (N.reaction r).source i = 0
  · simp [hzero]
  · have hsupp : ∀ j, j ≠ i → (N.reaction r).source j = 0 := by
      intro j hji
      by_contra hj
      have hjpos : 0 < (N.reaction r).source j := Nat.pos_of_ne_zero hj
      exact hji (hsrc r i j hzero hjpos.ne.symm).symm
    rw [massActionMonomial_eq_of_support hsupp hui]

/-- The delayed mass-action field is monotone in its delayed argument on nonnegative states. -/
theorem massActionDelayField_monotoneDelayed_of_nonnegative
    (N : Network S) (κ : N.RateConstants) (u v v' : Concentration S)
    (hv : ∀ s, 0 ≤ v s) (hvv' : v ≤ v') :
    N.massActionDelayField κ u (fun _ => v) ≤
      N.massActionDelayField κ u (fun _ => v') := by
  intro i
  unfold massActionDelayField
  refine Finset.sum_le_sum fun r _ => ?_
  have hmono : (N.reaction r).source.massActionMonomial v ≤
      (N.reaction r).source.massActionMonomial v' := massActionMonomial_mono hv hvv'
  have hprod : κ.k r * ((N.reaction r).source.massActionMonomial v *
      ((N.reaction r).target i : ℝ)) ≤
      κ.k r * ((N.reaction r).source.massActionMonomial v' *
      ((N.reaction r).target i : ℝ)) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hmono (Nat.cast_nonneg _)) (κ.positive r).le
  change κ.k r * ((N.reaction r).source.massActionMonomial v *
      ((N.reaction r).target i : ℝ) -
      (N.reaction r).source.massActionMonomial u *
        ((N.reaction r).source i : ℝ)) ≤
    κ.k r * ((N.reaction r).source.massActionMonomial v' *
      ((N.reaction r).target i : ℝ) -
      (N.reaction r).source.massActionMonomial u *
        ((N.reaction r).source i : ℝ))
  nlinarith

/-- The nonnegative part of a bounded current-state ball is closed under componentwise suprema. -/
def boundedNonnegativeConcentrationRegion (B : ℝ) : Set (Concentration S) :=
  {x | (∀ s, 0 ≤ x s) ∧ ‖x‖ ≤ B}

omit [DecidableEq S] in
theorem boundedNonnegativeConcentrationRegion_sup_closed {B : ℝ} (hB : 0 ≤ B) :
    ∀ x ∈ boundedNonnegativeConcentrationRegion (S := S) B,
      ∀ y ∈ boundedNonnegativeConcentrationRegion (S := S) B,
        x ⊔ y ∈ boundedNonnegativeConcentrationRegion (S := S) B := by
  intro x hx y hy
  refine ⟨?_, ?_⟩
  · intro s
    simp only [Pi.sup_apply]
    by_cases h : x s ≤ y s
    · rw [max_eq_right h]
      exact hy.1 s
    · rw [max_eq_left (le_of_not_ge h)]
      exact hx.1 s
  · apply (pi_norm_le_iff_of_nonneg hB).2
    intro s
    have hz : 0 ≤ max (x s) (y s) := by
      by_cases h : x s ≤ y s
      · rw [max_eq_right h]
        exact hy.1 s
      · rw [max_eq_left (le_of_not_ge h)]
        exact hx.1 s
    rw [Pi.sup_apply, Real.norm_eq_abs, abs_of_nonneg hz]
    have hxcoord : ‖x s‖ ≤ B := (norm_le_pi_norm x s).trans hx.2
    have hycoord : ‖y s‖ ≤ B := (norm_le_pi_norm y s).trans hy.2
    exact max_le_iff.mpr ⟨le_trans (le_abs_self _) hxcoord,
      le_trans (le_abs_self _) hycoord⟩

/-- **Common-delay mass-action comparison for sources supported on at most one species.** Suppose both
trajectories are nonnegative on the history-plus-solution interval `[-τ,T]`, bounded by `B` on
`[0,T]`, and satisfy the same-delay mass-action equation (or the subsolution inequality for `x`).
Then the componentwise ordered histories imply `x ≤ y` on `[0,T]`. This is a trajectory
comparison theorem under explicit boundedness and nonnegativity hypotheses; it does not establish
existence, positivity, or boundedness of the trajectories, and it requires one common delay for
all reactions. -/
theorem delay_comparison_massAction_commonDelay_singleSpeciesSources
    (N : Network S) (κ : N.RateConstants) (hsrc : N.HasSingleSpeciesSources)
    {τ T B : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    {x y : ℝ → Concentration S} {fx : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (fx t) (Set.Icc 0 T) t)
    (hsub : ∀ t ∈ Set.Icc 0 T,
      fx t ≤ N.massActionDelayField κ (x t) (fun _ => x (t - τ)))
    (hy : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt y
        (N.massActionDelayField κ (y t) (fun _ => y (t - τ))) (Set.Icc 0 T) t)
    (horder : ∀ r ≤ 0, x r ≤ y r)
    (hxBound : ∀ t ∈ Set.Icc 0 T, ‖x t‖ ≤ B)
    (hyBound : ∀ t ∈ Set.Icc 0 T, ‖y t‖ ≤ B)
    (hxNonneg : ∀ t ∈ Set.Icc (-τ) T, ∀ s, 0 ≤ x t s)
    (hyNonneg : ∀ t ∈ Set.Icc (-τ) T, ∀ s, 0 ≤ y t s) :
    ∀ r ∈ Set.Icc 0 T, x r ≤ y r := by
  let K := boundedNonnegativeConcentrationRegion (S := S) B
  let D : Set (Concentration S) := {v | ∀ s, 0 ≤ v s}
  let f : ℝ → Concentration S → Concentration S → Concentration S :=
    fun _ u v => N.massActionDelayField κ u (fun _ => v)
  let L : ℝ≥0 := Real.toNNReal
    (massActionLipschitzConstant N.currentConsumptionNetwork (N.currentConsumptionRates κ) B)
  have hsup : ∀ u ∈ K, ∀ u' ∈ K, u ⊔ u' ∈ K := by
    exact boundedNonnegativeConcentrationRegion_sup_closed (S := S) hB
  have hlip : ∀ t ∈ Set.Icc 0 T, ∀ v ∈ D, LipschitzOnWith L (fun u => f t u v) K := by
    intro t ht v hv u hu u' hu'
    change edist (N.massActionDelayField κ u (fun _ => v))
      (N.massActionDelayField κ u' (fun _ => v)) ≤ _
    exact N.massActionDelayField_lipschitzOnWith_closedBall κ B v
      (Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hu.2))
      (Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hu'.2))
  have hkamke : ∀ t ∈ Set.Icc 0 T, ∀ v u u', v ∈ D → u ∈ K → u' ∈ K → u ≤ u' →
      ∀ i, u i = u' i → f t u v i ≤ f t u' v i := by
    intro t ht v u u' hv hu hu' huu i hi
    exact N.massActionDelayField_kamke_of_singleSpeciesSources κ hsrc u u' v i hi
  have hdel : ∀ t ∈ Set.Icc 0 T, ∀ u v v', u ∈ K → v ∈ D → v' ∈ D → v ≤ v' →
      f t u v ≤ f t u v' := by
    intro t ht u v v' hu hv hv' hvv'
    exact N.massActionDelayField_monotoneDelayed_of_nonnegative κ u v v'
      hv hvv'
  have hxK : ∀ t ∈ Set.Icc 0 T, x t ∈ K := by
    intro t ht
    exact ⟨fun s => hxNonneg t ⟨by linarith [ht.1], ht.2⟩ s, hxBound t ht⟩
  have hyK : ∀ t ∈ Set.Icc 0 T, y t ∈ K := by
    intro t ht
    exact ⟨fun s => hyNonneg t ⟨by linarith [ht.1], ht.2⟩ s, hyBound t ht⟩
  have hdelD : ∀ t ∈ Set.Icc 0 T,
      x (t - τ) ∈ D ∧ y (t - τ) ∈ D := by
    intro t ht
    have htime : t - τ ∈ Set.Icc (-τ) T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ⟨hxNonneg (t - τ) htime, hyNonneg (t - τ) htime⟩
  exact Dynamics.delay_comparison_subsolution_local (f := f) (K := K) (D := D) (L := L)
    hτ hT hlip hsup hkamke hdel hx hsub hy horder hxK hyK hdelD

end Network
end CRNT

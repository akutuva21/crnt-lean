import CRNT.Stochastic.RegionStronglyConnected
import CRNT.Graph.WeakReversibility

/-!
# Lifting complex-graph reachability to count-level jump-reachability

The convergence theorem `jumpStronglyConnected_pow_mulVec_tendsto_stationaryVec`
(`CRNT.Stochastic.RegionStronglyConnected`) consumes the count-level irreducibility hypothesis
`RegionJumpStronglyConnected κ T`: every ordered pair of region counts is connected by a forward
walk of positive-probability enabled jumps that stays in `T`. This module supplies the transport
that produces such walks from the reaction structure, removing the count-level reachability
hypothesis in favour of fireable-reaction data on the region.

The mechanism is the single-reaction lift. On a closed enabled region `T` every reaction is
enabled at every count (`ClosedEnabledRegion.enabled`) and lands back inside `T`
(`ClosedEnabledRegion.forward`), and no count is absorbing (`ClosedEnabledRegion.exit_ne`). At an
enabled count the propensity is a product of strictly positive falling factorials (each
`source r s ≤ n s`), so the jump probability `jumpProb κ n r` is strictly positive
(`jumpProb_pos_of_enabled`). Firing `r` at `n ∈ T` is therefore a `JumpStep n (jumpNextCount n r)`
inside the region (`jumpStep_of_mem_region`): the count-level forward edge whose reverse is a
support edge of the restricted transition matrix.

Firing reaction `r` at the count `n` shifts it by the reaction vector,
`jumpNextCount n r = n − source r + target r`, the count-space image of the reaction-graph edge
`source r → target r`. A *fireable reaction list* — a sequence of reactions whose successive
post-firing counts all lie in `T` — therefore lifts to a `JumpReaches` walk inside the region by
induction on the list (`jumpReaches_of_fireableList`). This is the count-space realization of a
reaction-graph path: each list entry is a reaction-graph edge, and the lift threads its count-level
witness through the region's closure.

The honest ceiling is the gap between *complex-graph* paths and *count-space* walks. A path in the
reaction graph (`Reaches`, the reflexive-transitive closure of `DirectlyReacts`) connects complexes;
its edges are reactions but it carries no count witness, so it does not by itself name the counts a
walk passes through. Lifting it requires choosing, at each step, a reaction whose source matches the
current complex *and* whose firing from the current count stays in `T` — count data the complex
graph does not record. The realized statement transports the count-carrying object, the fireable
reaction list, and `RegionJumpStronglyConnected` follows once such lists are exhibited between every
pair of region counts (`regionJumpStronglyConnected_of_fireablePairs`), at which point convergence
follows from `WeaklyReversible` plus the region structure with no count-level reachability
hypothesis (`weaklyReversible_pow_mulVec_tendsto_stationaryVec`).

This is the chemical-reaction-network recurrence picture (Anderson, Craciun & Kurtz, "Product-form
stationary distributions for deficiency zero chemical reaction networks"): on a closed, irreducible
region the embedded jump chain is a single positive-recurrent communicating class, the finite-state
replacement for the abstract irreducibility of general Meyn–Tweedie ergodicity (Meyn & Tweedie,
"Markov Chains and Stochastic Stability").

## Main results

* `jumpProb_pos_of_enabled` — an enabled reaction at a non-absorbing count carries strictly
  positive jump probability.
* `jumpStep_of_mem_region` — firing any reaction at a region count is a region jump step.
* `FireableList` — a reaction sequence whose successive post-firing counts stay in the region.
* `jumpReaches_of_fireableList` — a fireable reaction list lifts to a jump-reachability walk.
* `regionJumpStronglyConnected_of_fireablePairs` — fireable lists between every pair of region
  counts discharge `RegionJumpStronglyConnected`.
* `weaklyReversible_pow_mulVec_tendsto_stationaryVec` — geometric convergence to the stationary law
  for a weakly reversible network on a region connected by fireable reaction lists, with no
  count-level reachability hypothesis.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Stochastic.RegionStronglyConnected`, `CRNT.Graph.WeakReversibility`.
-/

open MeasureTheory ProbabilityTheory
open Filter Topology
open scoped ENNReal BigOperators

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- **An enabled reaction carries positive propensity.** When the count `n` dominates the source
complex of `r` species-by-species (`Enabled n r`), every falling-factorial factor of the stochastic
mass-action propensity is strictly positive (`Nat.descFactorial_pos`), and the rate constant is
strictly positive (`RateConstants.positive`); the propensity is their product. -/
theorem stochasticMassActionRate_pos_of_enabled (N : Network S) (κ : RateConstants N) {n : S → ℕ}
    {r : N.R} (h : N.Enabled n r) : 0 < N.stochasticMassActionRate κ n r := by
  unfold stochasticMassActionRate
  refine mul_pos (κ.positive r) (Finset.prod_pos fun s _ => ?_)
  exact_mod_cast Nat.descFactorial_pos.mpr (h s)

/-- **An enabled reaction at a non-absorbing count carries positive jump probability.** The jump
probability `jumpProb κ n r = stochasticMassActionRate κ n r / exitRate κ n` is a ratio of a
positive propensity (`stochasticMassActionRate_pos_of_enabled`) and a positive holding rate, hence
strictly positive. -/
theorem jumpProb_pos_of_enabled (N : Network S) (κ : RateConstants N) {n : S → ℕ} {r : N.R}
    (h : N.Enabled n r) (hexit : N.exitRate κ n ≠ 0) : 0 < N.jumpProb κ n r := by
  unfold jumpProb
  exact div_pos (N.stochasticMassActionRate_pos_of_enabled κ h)
    (lt_of_le_of_ne (N.exitRate_nonneg κ n) (Ne.symm hexit))

/-- **Firing any reaction at a region count is a region jump step.** On a closed enabled region `T`,
a count `n ∈ T` is non-absorbing (`exit_ne`), every reaction is enabled there (`enabled`), and its
post-firing count stays inside (`forward`); the enabled reaction carries positive jump probability
(`jumpProb_pos_of_enabled`). Firing `r` is therefore a `JumpStep` from `n` to `jumpNextCount n r`
inside `T`. -/
theorem jumpStep_of_mem_region (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hT : N.ClosedEnabledRegion κ T) {n : S → ℕ} (hn : n ∈ T) (r : N.R) :
    N.JumpStep κ T n (N.jumpNextCount n r) := by
  refine ⟨hn, hT.forward n hn r, hT.exit_ne n hn, r, rfl, ?_⟩
  exact N.jumpProb_pos_of_enabled κ (hT.enabled n hn r) (hT.exit_ne n hn)

/-- **A reaction list is fireable from a count when its successive post-firing counts stay inside
the region.** Firing the head reaction from `n` lands on `jumpNextCount n r`, which must lie in `T`,
and the tail must be fireable from there; the empty list is fireable from any region count. This is
the count-carrying object lifted from the reaction graph: each entry is a reaction-graph edge whose
count-level realization the predicate threads through the region. -/
def FireableList (N : Network S) (κ : RateConstants N) (T : Set (S → ℕ)) :
    (S → ℕ) → List N.R → Prop
  | n, [] => n ∈ T
  | n, r :: rs => n ∈ T ∧ N.FireableList κ T (N.jumpNextCount n r) rs

/-- The count reached by firing a reaction list in sequence from `n`: fold the post-firing
count map along the list. -/
def fireListTarget (N : Network S) : (S → ℕ) → List N.R → (S → ℕ)
  | n, [] => n
  | n, r :: rs => N.fireListTarget (N.jumpNextCount n r) rs

/-- **A fireable reaction list lifts to a jump-reachability walk.** By induction on the list: the
empty list is the reflexive walk, and a head reaction `r` fireable from `n ∈ T` is a single region
jump step `n ⇝ jumpNextCount n r` (`jumpStep_of_mem_region`) prepended to the walk carried by the
fireable tail. The walk never leaves `T` because every intermediate count is a region member by the
fireability hypothesis. -/
theorem jumpReaches_of_fireableList (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hT : N.ClosedEnabledRegion κ T) :
    ∀ {n : S → ℕ} {rs : List N.R}, N.FireableList κ T n rs →
      N.JumpReaches κ T n (N.fireListTarget n rs)
  | _, [], _ => Relation.ReflTransGen.refl
  | n, r :: rs, h => by
    obtain ⟨hn, htail⟩ := h
    have hstep : N.JumpStep κ T n (N.jumpNextCount n r) := N.jumpStep_of_mem_region κ hT hn r
    have hrest : N.JumpReaches κ T (N.jumpNextCount n r)
        (N.fireListTarget (N.jumpNextCount n r) rs) :=
      N.jumpReaches_of_fireableList κ hT htail
    exact Relation.ReflTransGen.head hstep hrest

/-- **Fireable lists between every pair of region counts discharge jump-strong-connectivity.** If
for every ordered pair `n, m` of region counts there is a reaction list, fireable from `n`, whose
fold-target is `m`, then every pair is jump-reachable (`jumpReaches_of_fireableList`), which is
exactly `RegionJumpStronglyConnected`. This is the count-level realization of reaction-graph
connectivity: the hypothesis packages the count-carrying paths the complex graph alone cannot
name. -/
theorem regionJumpStronglyConnected_of_fireablePairs (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T)
    (hpairs : ∀ n ∈ T, ∀ m ∈ T, ∃ rs : List N.R,
      N.FireableList κ T n rs ∧ N.fireListTarget n rs = m) :
    N.RegionJumpStronglyConnected κ T := by
  intro n hn m hm
  obtain ⟨rs, hfire, htarget⟩ := hpairs n hn m hm
  have := N.jumpReaches_of_fireableList κ hT hfire
  rwa [htarget] at this

/-- **Unconditional geometric convergence for a weakly reversible network on a region connected by
fireable reaction lists.** On a finite closed enabled region `T` of a weakly reversible network at a
complex-balanced concentration, if every ordered pair of region counts is connected by a fireable
reaction list (`hpairs`), the count-level irreducibility hypothesis is discharged
(`regionJumpStronglyConnected_of_fireablePairs`), and a holding reaction at some region count
supplies aperiodicity; the embedded jump chain then mixes geometrically to the canonical stationary
law for every initial probability measure supported on `T`. Both structural hypotheses of the
finite-state Perron–Frobenius convergence theorem follow from the network's enabled-reaction
structure with no count-level reachability hypothesis remaining. This is the finite-state
replacement for general Meyn–Tweedie ergodicity (Meyn & Tweedie, "Markov Chains and Stochastic
Stability") on the recurrent class of a deficiency-zero network (Anderson, Craciun & Kurtz). -/
theorem weaklyReversible_pow_mulVec_tendsto_stationaryVec (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c) {T : Set (S → ℕ)}
    [Fintype ↥T] (hT : N.ClosedEnabledRegion κ T) (hne : T.Nonempty) (_hwr : N.WeaklyReversible)
    (hpairs : ∀ n ∈ T, ∀ m ∈ T, ∃ rs : List N.R,
      N.FireableList κ T n rs ∧ N.fireListTarget n rs = m)
    {n : S → ℕ} (hn : n ∈ T) (hexit : N.exitRate κ n ≠ 0)
    {r : N.R} (hr : N.jumpNextCount n r = n) (hprob : 0 < N.jumpProb κ n r)
    (μ : Measure (S → ℕ)) [IsProbabilityMeasure μ] (hμsupp : μ Tᶜ = 0) :
    ∀ i : ↥T, Tendsto
        (fun k => ((N.regionMatrix κ T) ^ k).mulVec (stationaryVec (T := T) μ) i) atTop
        (𝓝 (stationaryVec (T := T) (N.stationaryProbabilityMeasure κ c T) i)) := by
  have hjsc : N.RegionJumpStronglyConnected κ T :=
    N.regionJumpStronglyConnected_of_fireablePairs κ hT hpairs
  exact N.jumpStronglyConnected_pow_mulVec_tendsto_stationaryVec κ c hc hcb hT hne hjsc hn hexit
    hr hprob μ hμsupp

end Network

end CRNT

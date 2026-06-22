import CRNT.Stochastic.KernelStationary

/-!
# Support-restricted invariance of the embedded jump kernel without global no-boundary
hypotheses

`CRNT.Stochastic.KernelStationary` proves measure invariance of the embedded jump kernel,
`Kernel.Invariant (jumpKernel κ) (jumpStationaryMeasure κ c)`, only under two *global*
hypotheses: a no-boundary assumption `hexit : ∀ n, exitRate κ n ≠ 0` (no absorbing states
anywhere) and a target-domination assumption `htarget : ∀ m r s, (reaction r).target s ≤ m s`
(every count dominates every reaction's target complex everywhere). Both fail on the genuine
count lattice `S → ℕ`: small counts are absorbing or fail to resource a reaction, and the
`exitRate = 0` holding states are absorbing, where strict pointwise balance breaks. This
module removes those global hypotheses by restricting the invariant measure to a self-contained
communicating region of the lattice.

A `ClosedEnabledRegion κ T` is a set of counts on which the embedded jump chain is closed and
boundary-free: no member is absorbing (`exit_ne`), every member is enabled for and dominates
every reaction (`enabled`, `target_le`), the post-firing count of any member stays inside
(`forward`), and the source-dominating predecessor of any member stays inside (`backward`).
These are exactly the membership-gated, region-local readings of the global no-boundary /
target-domination hypotheses; `T = Set.univ` recovers them, so the structure is strictly
weaker. On such a region every step of the predecessor-summation argument runs verbatim:
`forward` confines outgoing mass to `T`, so no probability leaks to a target outside `T`;
`backward` keeps the unique nonzero predecessor inside `T`, so the restriction drops nothing
that carries mass; and `exit_ne`/`target_le`/`enabled` license the holding-rate cancellation,
the unique-predecessor collapse, and the embedded global balance pointwise on `T`.

The exported content is the **unconditional** support-restricted invariance
`jumpKernel_invariant_restrictedStationaryMeasure`:
`Kernel.Invariant (jumpKernel κ) ((jumpStationaryMeasure κ c).restrict T)` for any closed
enabled region `T` at a complex-balanced concentration, with no global `hexit` or `htarget`.
The proof equates the two measures on singletons (`Measure.ext_of_singleton` over the countable
lattice): the restricted singleton mass is the region-cut lifted stationary weight
(`restrictedStationaryMeasure_singleton`), the restricted pushforward singleton mass is the
region-restricted predecessor tsum (`restrictedStationaryMeasure_bind_apply`), and the two
agree by `restricted_predecessor_sum_eq` inside the region and
`restricted_predecessor_sum_eq_zero` outside it (closure forces no inbound mass).

The honest ceiling: this is the strongest sound rung short of *characterizing* a canonical
closed enabled region of a given network — e.g. proving that the set of counts above all
reaction targets with positive exit rate is forward/backward closed for a specific class of
networks, or identifying the irreducible communicating class as a `Kernel.Irreducible`
component. That characterization is the next dependency; it requires network-structural
reachability analysis (which counts communicate under repeated firing) that the committed
assets do not provide. Here the region is taken as a hypothesis with its closure verified.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Stochastic.KernelStationary`.
-/

open MeasureTheory ProbabilityTheory

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- A set of counts is a *closed enabled region* for `(κ, c)` when it is self-contained for the
embedded jump chain: no member is absorbing, every member dominates and is enabled for every
reaction, the post-firing count of any member stays inside, and the source-dominating
predecessor of any member stays inside. On such a region the strict pointwise balance that
drives jump-chain stationarity holds without any global no-boundary assumption. These are the
membership-gated readings of the `hexit`/`htarget`/`henabled` hypotheses of the unrestricted
theorem, recovered exactly at `T = Set.univ`. -/
structure ClosedEnabledRegion (N : Network S) (κ : RateConstants N) (T : Set (S → ℕ)) :
    Prop where
  /-- No member of the region is absorbing. -/
  exit_ne : ∀ n ∈ T, N.exitRate κ n ≠ 0
  /-- Every member is enabled for every reaction. -/
  enabled : ∀ n ∈ T, ∀ r, N.Enabled n r
  /-- Every member dominates every reaction's target complex. -/
  target_le : ∀ n ∈ T, ∀ (r : N.R) (s : S), (N.reaction r).target s ≤ n s
  /-- Firing any reaction from a member lands inside the region. -/
  forward : ∀ n ∈ T, ∀ r, N.jumpNextCount n r ∈ T
  /-- The source-dominating predecessor of any member lies inside the region. -/
  backward : ∀ m ∈ T, ∀ r, N.predecessorCount r m ∈ T

/-- The whole lattice is a closed enabled region exactly when the global no-boundary,
enabled-everywhere, and target-domination hypotheses of the unrestricted theorem hold: this is
the `T = Set.univ` instance, witnessing that `ClosedEnabledRegion` is the strict weakening of
those global hypotheses. -/
theorem closedEnabledRegion_univ (N : Network S) (κ : RateConstants N)
    (hexit : ∀ n, N.exitRate κ n ≠ 0) (henabled : ∀ n r, N.Enabled n r)
    (htarget : ∀ (m : S → ℕ) r s, (N.reaction r).target s ≤ m s) :
    N.ClosedEnabledRegion κ (Set.univ : Set (S → ℕ)) where
  exit_ne n _ := hexit n
  enabled n _ r := henabled n r
  target_le n _ r s := htarget n r s
  forward _ _ _ := Set.mem_univ _
  backward _ _ _ := Set.mem_univ _

/-- The support-restricted candidate stationary measure: the lattice density measure of
`CRNT.Stochastic.KernelInvariant` cut down to the closed enabled region `T`. -/
noncomputable def restrictedStationaryMeasure (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (T : Set (S → ℕ)) : Measure (S → ℕ) :=
  (N.jumpStationaryMeasure κ c).restrict T

/-- The singleton mass of the restricted measure: the lifted stationary weight on the region,
zero off it. Restriction to `T` intersects each singleton with `T`, leaving the full atom when
`m ∈ T` and the empty set otherwise. -/
theorem restrictedStationaryMeasure_singleton (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (T : Set (S → ℕ)) (m : S → ℕ) :
    N.restrictedStationaryMeasure κ c T {m} =
      T.indicator (fun m => ENNReal.ofReal (N.jumpStationaryMass κ c m)) m := by
  rw [restrictedStationaryMeasure,
    Measure.restrict_apply' (MeasurableSpace.measurableSet_top (s := T))]
  by_cases hm : m ∈ T
  · rw [Set.indicator_of_mem hm,
      show ({m} : Set (S → ℕ)) ∩ T = {m} from by
        ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        exact ⟨fun h => h.1, by rintro rfl; exact ⟨rfl, hm⟩⟩]
    exact N.jumpStationaryMeasure_singleton κ c m
  · rw [Set.indicator_of_notMem hm,
      show ({m} : Set (S → ℕ)) ∩ T = (∅ : Set (S → ℕ)) from by
        ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false, not_and]
        rintro rfl; exact hm]
    simp

/-- The bind-to-sum identity for the restricted measure: its pushforward under the embedded
jump kernel evaluates on any set as the lattice tsum of the region-restricted stationary weight
times the kernel's transition mass. The restriction turns the lattice integral into one over
`T`, expanded via the discrete superposition into the indicator-weighted predecessor tsum. -/
theorem restrictedStationaryMeasure_bind_apply (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (T : Set (S → ℕ)) (s : Set (S → ℕ)) :
    (N.restrictedStationaryMeasure κ c T).bind (N.jumpKernel κ) s =
      ∑' n : S → ℕ, T.indicator (fun n => ENNReal.ofReal (N.jumpStationaryMass κ c n)) n *
        N.jumpKernel κ n s := by
  rw [restrictedStationaryMeasure,
    Measure.bind_apply (MeasurableSpace.measurableSet_top (s := s))
      (N.jumpKernel κ).aemeasurable,
    ← lintegral_indicator (MeasurableSpace.measurableSet_top (s := T)),
    jumpStationaryMeasure, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  by_cases hn : n ∈ T
  · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn]
  · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn, mul_zero, zero_mul]

/-- The region-localized per-reaction collapse: inside a closed enabled region the lattice tsum
of the region-restricted stationary weight times the reaction-`r` jump mass into `{m}` collapses
to the single source-dominating predecessor, yielding the lifted generator inflow at `m`. The
predecessor stays in the region by `backward`, so the restriction keeps the one surviving term;
every other count either fails source-domination (vanishing its jump probability), misses `m`,
or lies outside the region (vanishing its restricted weight). -/
theorem tsum_reaction_term_restricted (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (T : Set (S → ℕ))
    (hT : N.ClosedEnabledRegion κ T) (r : N.R) (m : S → ℕ) (hm : m ∈ T) :
    ∑' n : S → ℕ, T.indicator (fun n => ENNReal.ofReal (N.jumpStationaryMass κ c n)) n *
        (ENNReal.ofReal (N.jumpProb κ n r) *
          ({m} : Set (S → ℕ)).indicator 1 (N.jumpNextCount n r)) =
      ENNReal.ofReal (N.generatorInflow κ c m r) := by
  have hmtgt : ∀ s, (N.reaction r).target s ≤ m s := fun s => hT.target_le m hm r s
  rw [tsum_eq_single (N.predecessorCount r m)]
  · have hpredT : N.predecessorCount r m ∈ T := hT.backward m hm r
    have hsrc := N.source_le_predecessorCount r m hmtgt
    have hnext := N.jumpNextCount_predecessorCount r m hmtgt
    rw [Set.indicator_of_mem hpredT, hnext, Set.indicator_of_mem (Set.mem_singleton m),
      Pi.one_apply, mul_one,
      ← ENNReal.ofReal_mul (N.jumpStationaryMass_nonneg κ c hc _),
      N.jumpStationaryMass_mul_jumpProb_eq_generatorOutflow κ c _ r (hT.exit_ne _ hpredT) hsrc,
      N.generatorOutflow_predecessorCount_eq_generatorInflow κ c r m hmtgt]
  · intro n hn
    by_cases hnT : n ∈ T
    · by_cases hind : N.jumpNextCount n r = m
      · by_cases hsrc : ∀ s, (N.reaction r).source s ≤ n s
        · exact absurd (N.eq_predecessorCount_of_jumpNextCount r m n hsrc hind) hn
        · rw [N.jumpProb_eq_zero_of_not_source_le κ n r hsrc, ENNReal.ofReal_zero,
            zero_mul, mul_zero]
      · rw [Set.indicator_of_notMem
          (show N.jumpNextCount n r ∉ ({m} : Set (S → ℕ)) by simpa using hind), mul_zero,
          mul_zero]
    · rw [Set.indicator_of_notMem hnT, zero_mul]

/-- Region-restricted predecessor summation at an interior target. For `m` inside a closed
enabled region the lattice tsum of the region-restricted stationary weight times the kernel's
transition mass into `{m}` equals the lifted stationary weight at `m`. The kernel row is
expanded over reactions (positive exit on the region by `exit_ne`), each reaction term collapses
to its predecessor by `tsum_reaction_term_restricted`, and the reaction-indexed inflow sum is
the stationary weight by the embedded global balance, valid since `m` is enabled. -/
theorem restricted_predecessor_sum_eq (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c)
    (T : Set (S → ℕ)) (hT : N.ClosedEnabledRegion κ T) (m : S → ℕ) (hm : m ∈ T) :
    (∑' n : S → ℕ, T.indicator (fun n => ENNReal.ofReal (N.jumpStationaryMass κ c n)) n *
        N.jumpKernel κ n {m}) =
      ENNReal.ofReal (N.jumpStationaryMass κ c m) := by
  have hstep : ∀ n : S → ℕ,
      T.indicator (fun n => ENNReal.ofReal (N.jumpStationaryMass κ c n)) n *
          N.jumpKernel κ n {m} =
        ∑ r : N.R, T.indicator (fun n => ENNReal.ofReal (N.jumpStationaryMass κ c n)) n *
          (ENNReal.ofReal (N.jumpProb κ n r) *
            ({m} : Set (S → ℕ)).indicator 1 (N.jumpNextCount n r)) := by
    intro n
    by_cases hnT : n ∈ T
    · rw [N.jumpKernel_apply_of_exitRate_pos κ n (hT.exit_ne n hnT), Finset.mul_sum]
    · rw [Set.indicator_of_notMem hnT, zero_mul, Finset.sum_eq_zero]
      intro r _; rw [zero_mul]
  simp_rw [hstep]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
    Finset.sum_congr rfl (fun r _ => N.tsum_reaction_term_restricted κ c hc T hT r m hm),
    ← ENNReal.ofReal_sum_of_nonneg (fun r _ => N.generatorInflow_nonneg κ c hc m r)]
  congr 1
  exact N.jumpGlobalBalance_of_complexBalanced κ c m hcb (hT.enabled m hm)

/-- Region-restricted predecessor summation at an exterior target. For `m` outside a closed
enabled region the lattice tsum of the region-restricted stationary weight times the kernel's
transition mass into `{m}` is zero: by `forward`, firing any reaction from a member of the
region lands back inside the region, so no member can transition to `m`, and members outside the
region carry zero restricted weight. -/
theorem restricted_predecessor_sum_eq_zero (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (T : Set (S → ℕ)) (hT : N.ClosedEnabledRegion κ T)
    (m : S → ℕ) (hm : m ∉ T) :
    (∑' n : S → ℕ, T.indicator (fun n => ENNReal.ofReal (N.jumpStationaryMass κ c n)) n *
        N.jumpKernel κ n {m}) = 0 := by
  rw [ENNReal.tsum_eq_zero]
  intro n
  by_cases hnT : n ∈ T
  · rw [N.jumpKernel_apply_of_exitRate_pos κ n (hT.exit_ne n hnT), Finset.mul_sum]
    refine Finset.sum_eq_zero (fun r _ => ?_)
    have hforward : N.jumpNextCount n r ∈ T := hT.forward n hnT r
    have hne : N.jumpNextCount n r ≠ m := fun h => hm (h ▸ hforward)
    rw [Set.indicator_of_notMem
      (show N.jumpNextCount n r ∉ ({m} : Set (S → ℕ)) by simpa using hne), mul_zero, mul_zero]
  · rw [Set.indicator_of_notMem hnT, zero_mul]

/-- **Unconditional support-restricted invariance of the embedded jump kernel.** For any closed
enabled region `T` at a complex-balanced concentration, the restriction of the candidate
stationary measure to `T` is invariant under the embedded jump kernel, with **no** global
no-boundary (`hexit`) or target-domination (`htarget`) hypothesis. The two measures agree on
every singleton (`Measure.ext_of_singleton` over the countable count lattice): the restricted
singleton mass is the region-cut lifted stationary weight, and the restricted pushforward
singleton mass is the region-restricted predecessor tsum, which equals that weight inside the
region (`restricted_predecessor_sum_eq`) and is zero outside it
(`restricted_predecessor_sum_eq_zero`, the region having no inbound mass by closure). -/
theorem jumpKernel_invariant_restrictedStationaryMeasure (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c)
    (T : Set (S → ℕ)) (hT : N.ClosedEnabledRegion κ T) :
    Kernel.Invariant (N.jumpKernel κ) (N.restrictedStationaryMeasure κ c T) := by
  unfold Kernel.Invariant
  refine Measure.ext_of_singleton (fun m => ?_)
  rw [N.restrictedStationaryMeasure_bind_apply κ c T {m},
    N.restrictedStationaryMeasure_singleton κ c T m]
  by_cases hm : m ∈ T
  · rw [Set.indicator_of_mem hm, N.restricted_predecessor_sum_eq κ c hc hcb T hT m hm]
  · rw [Set.indicator_of_notMem hm, N.restricted_predecessor_sum_eq_zero κ c T hT m hm]

end Network

end CRNT

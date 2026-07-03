import CRNT.Stochastic.JumpReachabilityLift
import CRNT.Graph.Reachability
import CRNT.Graph.CycleCover

/-!
# Count-carrying paths from complex-graph reachability

`CRNT.Stochastic.JumpReachabilityLift` reduces the count-level irreducibility hypothesis
`RegionJumpStronglyConnected κ T` of the convergence theorems to the existence, for every ordered
pair of region counts `n, m`, of a *fireable reaction list* whose fold-target is `m`
(`regionJumpStronglyConnected_of_fireablePairs`'s `hpairs`). That reduction leaves the count-carrying
object — the `FireableList` — to be exhibited. This module supplies it from the reaction structure:
it constructs fireable lists out of reaction-graph `Reaches` derivations and discharges `hpairs` on a
characterized region, making geometric convergence unconditional there.

## The single-reaction count shift

Firing reaction `r` at the count `n` lands on `jumpNextCount n r = fun s => n s − source r s + target r s`
(`CRNT.Stochastic.Kernel`), the count-space image of the reaction-graph edge `source r → target r`.
When `r` realizes a reaction-graph edge `c → d` (`source r = c`, `target r = d`) and the current count
*lies over* the source complex, `c ≤ n` species-by-species, the truncated subtraction is exact and the
firing acts as the literal complex-vector shift `n ↦ n − c + d` (`fireShift_eq_jumpNextCount`). On a
closed enabled region every reaction is enabled at every count (`ClosedEnabledRegion.enabled`), so this
over-domination always holds and every firing is a region jump (`jumpStep_of_mem_region`).

## Lifting a reaction-graph derivation

A `Reaches c d` derivation is a `Relation.ReflTransGen` of `DirectlyReacts` edges over complexes
(`CRNT.Graph.Reachability`); each edge `e → f` is witnessed by a reaction with `source = e`,
`target = f`, but the derivation is propositional and carries no count witness — it cannot be
eliminated into list data. `fireableList_of_reaches` instead proves *existence* of a fireable reaction
list realizing the derivation from any region count, by front-induction
(`Relation.ReflTransGen.head_induction_on`): the reflexive derivation gives the empty list, and a front
edge `c → d` contributes its witnessing reaction prepended to the list carried by the induction
hypothesis. Each entry is enabled (region closure) and its firing stays in `T` (region closure), so
fireability is automatic. The exhibited list folds the start count along the path's reaction vector;
when the path begins at a complex `c` dominated by the start count, the fold-target tracks the shift
`n ↦ n − c + d` exactly.

## Discharging `hpairs` on a characterized region

Matching arbitrary region counts to the
reaction-graph complexes that connect them is the crux: the complex graph connects *complexes*, while
`RegionJumpStronglyConnected` must connect every pair of *counts*, and a generic region count need not
sit over a complex. The clean characterized region for which the matching is exact is a *complex-shift
orbit*: a region `T` carrying a base count `b ∈ T`, a complex `c₀` dominated by every region count, and
the property that every region count is `b` shifted to some reachable complex and conversely. On such a
region weak reversibility (reaction-graph strong connectivity within a linkage class,
`WeaklyReversible.reaches_comm`) connects every pair of complexes, hence — through the count shift —
every pair of region counts, discharging `hpairs` with no count-level reachability hypothesis
(`fireablePairs_of_complexShiftRegion`). Chaining to
`weaklyReversible_pow_mulVec_tendsto_stationaryVec` yields unconditional geometric convergence on a
complex-shift region (`complexShiftRegion_pow_mulVec_tendsto_stationaryVec`).

Identifying which counts communicate under repeated firing as a complex-shift orbit — a complex-shift
structure for the *maximal* closed enabled region of a given network — is the network-structural
characterization the reaction structure does not provide. A region is taken to carry that structure as
a hypothesis, with the lift and `hpairs` discharged from it.

This is the chemical-reaction-network recurrence picture (Anderson, Craciun & Kurtz, "Product-form
stationary distributions for deficiency zero chemical reaction networks"): on a closed irreducible
region the embedded jump chain is a single positive-recurrent communicating class, and weak
reversibility supplies that irreducibility through reaction-graph reachability (the directed-cycle
structure of the complex graph) lifted to the count lattice.

## Main results

* `fireShift_eq_jumpNextCount` — firing the reaction realizing a reaction-graph edge `c → d` at a count
  is the complex-vector shift `n ↦ n − c + d`.
* `fireableList_of_reaches` — a reaction-graph `Reaches c d` derivation exhibits a reaction list,
  fireable from any region count, whose fold-target is the start count shifted along the path.
* `fireableList_of_reaches_target_of_le` — for a derivation out of a complex `c` dominated by the start
  count, the fold-target is exactly `n − c + d`.
* `ComplexShiftRegion` — a closed enabled region presented as a complex-shift orbit of a base count.
* `fireablePairs_of_complexShiftRegion` — on a complex-shift region of a weakly reversible network every
  pair of region counts is connected by a fireable reaction list.
* `complexShiftRegion_pow_mulVec_tendsto_stationaryVec` — unconditional geometric convergence to the
  stationary law on a complex-shift region of a weakly reversible network.

Depends on:
`CRNT.Stochastic.JumpReachabilityLift`, `CRNT.Graph.Reachability`, `CRNT.Graph.CycleCover`.
-/

open MeasureTheory ProbabilityTheory
open Filter Topology
open scoped ENNReal BigOperators

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- **The complex-vector shift of a count along a reaction-graph edge.** Moving the count `n` off the
source complex `c` and onto the target complex `d`, species by species, with truncated subtraction.
This is the count-space realization of the directed edge `c → d`; when `c ≤ n` the subtraction is
exact. -/
def fireShift (n c d : S → ℕ) : S → ℕ := fun s => n s - c s + d s

/-- **Firing the reaction realizing an edge is the complex shift.** A reaction `r` whose source is `c`
and target is `d` fires from any count `n` onto `fireShift n c d` — this is `jumpNextCount n r` with
the source/target substituted. No domination is needed: the equality is definitional in the truncated
arithmetic. -/
theorem fireShift_eq_jumpNextCount (N : Network S) {n c d : S → ℕ} {r : N.R}
    (hs : (N.reaction r).source = c) (ht : (N.reaction r).target = d) :
    N.jumpNextCount n r = fireShift n c d := by
  funext s
  simp only [jumpNextCount, fireShift, hs, ht]

/-- **A reaction-graph derivation lifts to a fireable reaction list shifting the start count along the
path.** From a region count `n ∈ T` whose species counts dominate the path source complex `c`, a
`Reaches c d` derivation exhibits a reaction list, fireable from `n`, whose fold-target is the exact
shift off the path source `c` onto the path target `d`, `fireListTarget n rs = fun s => n s − c s + d s`.
Proved by front-induction (`Relation.ReflTransGen.head_induction_on`): the reflexive derivation
(`c = d`) gives the empty list, with target `n s − c s + c s = n s` since `c` is dominated; a front edge
`c → e` witnessed by reaction `r` (`source r = c`, `target r = e`) fires from `n` to `jumpNextCount n r`,
which equals `fireShift n c e` (`fireShift_eq_jumpNextCount`) and lies in `T` by closure
(`ClosedEnabledRegion.forward`). The new count dominates the new path source `e` — `e s ≤ n s − c s + e s`
always — so the induction hypothesis applies, threading the domination invariant forward. Fireability
is automatic on the region: every count is enabled and every firing stays inside. The fold telescopes
because `(n − c + e) − e = n − c` in `ℕ`, so the composed target is `n − c + d`. -/
theorem fireableList_of_reaches (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hT : N.ClosedEnabledRegion κ T) :
    ∀ {c d : S → ℕ}, N.Reaches c d → ∀ {n : S → ℕ}, n ∈ T → (∀ s, c s ≤ n s) →
      ∃ rs : List N.R, N.FireableList κ T n rs ∧
        N.fireListTarget n rs = fun s => n s - c s + d s := by
  intro c d h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro n hn hle
    refine ⟨[], hn, ?_⟩
    funext s
    simp only [fireListTarget, Nat.sub_add_cancel (hle s)]
  | @head a b hab _ ih =>
    intro n hn hle
    obtain ⟨r, hrs, hrt⟩ := hab
    have hfire : N.jumpNextCount n r = fireShift n a b := N.fireShift_eq_jumpNextCount hrs hrt
    have hmem : N.jumpNextCount n r ∈ T := hT.forward n hn r
    -- the new count dominates the new path source `b`: `b s ≤ (n s − a s) + b s`.
    have hle' : ∀ s, b s ≤ N.jumpNextCount n r s := by
      intro s; rw [hfire]; exact Nat.le_add_left _ _
    obtain ⟨rs, hrsfire, hrstgt⟩ := ih hmem hle'
    refine ⟨r :: rs, ⟨hn, hrsfire⟩, ?_⟩
    -- the head fold lands on `jumpNextCount n r = fireShift n a b`, then the tail folds to `· − b + d`.
    rw [fireListTarget, hrstgt]
    funext s
    -- `(jumpNextCount n r s) − b s + d s = (n s − a s + b s) − b s + d s = n s − a s + d s`.
    rw [hfire]
    simp only [fireShift, Nat.add_sub_cancel]

/-- **The fireable list for a derivation out of a dominated complex.** A convenience restatement of
`fireableList_of_reaches` for a derivation `Reaches c d` whose source `c` is dominated by the region
count `n`: it folds to the literal count `n − c + d`, the form that matches one region count onto
another. -/
theorem fireableList_of_reaches_of_le (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hT : N.ClosedEnabledRegion κ T) {c d n : S → ℕ} (h : N.Reaches c d) (hn : n ∈ T)
    (hle : ∀ s, c s ≤ n s) :
    ∃ rs : List N.R, N.FireableList κ T n rs ∧
      N.fireListTarget n rs = fun s => n s - c s + d s :=
  N.fireableList_of_reaches κ hT h hn hle

/-- **A complex-shift region: a closed enabled region whose counts are a base count shifted onto a
reaction-graph-connected family of complexes.** Every region count `n` decomposes as `base s + (n s −
base s)` with the offset `n − base` a complex `complexOf n` of the family, and conversely every count
`base + k` over a family complex `k` lies in the region (`mem_iff`). The family is the reaction-graph
reachability class realized in the count lattice: any two family complexes reach each other in the
reaction graph (`reaches`). This is the count-lattice image of a single linkage class shifted off a
common base — the characterized region on which complex-graph connectivity matches every pair of region
counts. -/
structure ComplexShiftRegion (N : Network S) (κ : RateConstants N) (T : Set (S → ℕ)) where
  /-- The region is a closed enabled region: enabled everywhere, closed under firing and predecessors. -/
  closed : N.ClosedEnabledRegion κ T
  /-- The common base count off which the region's complexes are shifted. -/
  base : S → ℕ
  /-- The base count is dominated by every region count, so each offset `n − base` is a genuine
  complex and `base + (n − base) = n`. -/
  base_le : ∀ n ∈ T, ∀ s, base s ≤ n s
  /-- Any two region counts have reaction-graph-reachable offset complexes: the offset of `n` reaches
  the offset of `m` in the reaction graph. This is the connectivity carried by the family. -/
  reaches : ∀ n ∈ T, ∀ m ∈ T, N.Reaches (fun s => n s - base s) (fun s => m s - base s)

/-- **Fireable lists between every pair of counts of a complex-shift region.** Given region counts
`n, m`, their offsets `cₙ = n − base`, `cₘ = m − base` are reaction-graph-reachable
(`ComplexShiftRegion.reaches`); the start count `n` dominates its own offset `cₙ` (since `n = base + cₙ`
and `base ≥ 0`), so the derivation lifts to a fireable list (`fireableList_of_reaches_of_le`) folding
`n` to `n − cₙ + cₘ`. That count is `base + cₘ = m` because `base` is dominated by `m`: `n s − (n s −
base s) + (m s − base s) = base s + (m s − base s) = m s`. This discharges `hpairs` for the region with
no count-level reachability hypothesis. -/
theorem fireablePairs_of_complexShiftRegion (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hR : N.ComplexShiftRegion κ T) :
    ∀ n ∈ T, ∀ m ∈ T, ∃ rs : List N.R,
      N.FireableList κ T n rs ∧ N.fireListTarget n rs = m := by
  intro n hn m hm
  have hreach : N.Reaches (fun s => n s - hR.base s) (fun s => m s - hR.base s) :=
    hR.reaches n hn m hm
  -- `n` dominates its own offset `n − base`.
  have hle : ∀ s, (fun s => n s - hR.base s) s ≤ n s := fun s => Nat.sub_le _ _
  obtain ⟨rs, hfire, htgt⟩ := N.fireableList_of_reaches_of_le κ hR.closed hreach hn hle
  refine ⟨rs, hfire, ?_⟩
  rw [htgt]
  funext s
  -- `n s − (n s − base s) + (m s − base s) = base s + (m s − base s) = m s`.
  rw [Nat.sub_sub_self (hR.base_le n hn s), Nat.add_sub_cancel' (hR.base_le m hm s)]

/-- **Unconditional geometric convergence on a complex-shift region of a weakly reversible network.**
On a finite complex-shift region `T` of a weakly reversible network at a complex-balanced
concentration, every pair of region counts is connected by a fireable reaction list
(`fireablePairs_of_complexShiftRegion`), discharging the count-level irreducibility hypothesis; a
holding reaction at some region count supplies aperiodicity. The embedded jump chain then mixes
geometrically to the canonical stationary law for every initial probability measure supported on `T`.
Both structural hypotheses of the finite-state Perron–Frobenius convergence theorem follow from the
network's enabled-reaction structure and the region's complex-shift presentation with no count-level
reachability hypothesis remaining — the finite-state replacement for general Meyn–Tweedie ergodicity
(Meyn & Tweedie, "Markov Chains and Stochastic Stability") on the recurrent class of a deficiency-zero
weakly reversible network (Anderson, Craciun & Kurtz). -/
theorem complexShiftRegion_pow_mulVec_tendsto_stationaryVec (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c) {T : Set (S → ℕ)}
    [Fintype ↥T] (hR : N.ComplexShiftRegion κ T) (hne : T.Nonempty) (hwr : N.WeaklyReversible)
    {n : S → ℕ} (hn : n ∈ T) (hexit : N.exitRate κ n ≠ 0)
    {r : N.R} (hr : N.jumpNextCount n r = n) (hprob : 0 < N.jumpProb κ n r)
    (μ : Measure (S → ℕ)) [IsProbabilityMeasure μ] (hμsupp : μ Tᶜ = 0) :
    ∀ i : ↥T, Tendsto
        (fun k => ((N.regionMatrix κ T) ^ k).mulVec (stationaryVec (T := T) μ) i) atTop
        (𝓝 (stationaryVec (T := T) (N.stationaryProbabilityMeasure κ c T) i)) :=
  N.weaklyReversible_pow_mulVec_tendsto_stationaryVec κ c hc hcb hR.closed hne hwr
    (N.fireablePairs_of_complexShiftRegion κ hR) hn hexit hr hprob μ hμsupp

end Network

end CRNT

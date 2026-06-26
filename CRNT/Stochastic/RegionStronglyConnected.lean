import CRNT.Stochastic.RegionPrimitive

/-!
# Strong connectivity of a region from network jump-reachability

The geometric-convergence theorem
`regionMatrix_primitive_pow_mulVec_tendsto_stationaryVec` (`CRNT.Stochastic.ErgodicConvergenceGeneral`)
and the primitivity bridge `regionPrimitive_of_stronglyConnected_self_loop`
(`CRNT.Stochastic.RegionPrimitive`) both consume the abstract irreducibility hypothesis
`regionStronglyConnected κ T`: the support digraph of the restricted transition matrix
`regionMatrix κ T` is strongly connected. This module discharges that hypothesis from concrete
network structure — the positive-probability jump transitions of the embedded chain inside the
region — reducing the abstract single-communicating-class assumption to count-level reachability
along enabled reactions.

The mechanism is the support edge of the column-stochastic transition matrix. A matrix entry
`regionMatrix κ T i j = (jumpKernel κ j {i}).toReal` is nonzero exactly when the source count `j`
carries a positive-probability reaction landing on the target count `i`. The embedded jump chain's
forward transition `n ⇝ m` (`JumpStep`: a reaction `r` enabled at `n ∈ T` with `0 < jumpProb κ n r`
and `jumpNextCount n r = m ∈ T`) is therefore a matrix support edge in the *reverse* direction,
`regionMatrix κ T ⟨m⟩ ⟨n⟩ ≠ 0` (`regionMatrix_ne_zero_of_jumpStep`). A forward jump walk
`n ⇝ m` (`JumpReaches`, the reflexive-transitive closure of `JumpStep`) thus reverses to a
matrix-support walk `⟨m⟩ ⇝ ⟨n⟩` (`supportReaches_of_jumpReaches`).

A digraph and its reverse have the same strongly connected components, so requiring forward
jump-reachability between *every* ordered pair of region states (`RegionJumpStronglyConnected`)
gives matrix-support walks between every pair in either direction, hence
`regionStronglyConnected κ T` (`regionStronglyConnected_of_jumpReaches`). This is the
chemical-reaction-network recurrence picture (Anderson, Craciun & Kurtz, "Product-form stationary
distributions for deficiency zero chemical reaction networks"): on a closed, irreducible region the
embedded chain is a single positive-recurrent communicating class, the finite-state replacement for
the abstract irreducibility of general Meyn–Tweedie ergodicity (Meyn & Tweedie, "Markov Chains and
Stochastic Stability").

Chaining the discharged irreducibility with the self-loop bridge and the convergence theorem yields
geometric convergence to the stationary law for the concrete structural class — jump-strongly-connected
region carrying one holding reaction — with *no* abstract `regionStronglyConnected`/`regionPrimitive`
assumption remaining (`jumpStronglyConnected_pow_mulVec_tendsto_stationaryVec`): both the
irreducibility and the aperiodicity are produced from the network's enabled-reaction structure.

## Main results

* `JumpStep` — a single positive-probability enabled jump transition between region states.
* `JumpReaches` — reflexive-transitive jump-reachability inside the region.
* `regionMatrix_ne_zero_of_jumpStep` — a forward jump `n ⇝ m` is a reverse matrix support edge.
* `supportReaches_of_jumpReaches` — a forward jump walk reverses to a matrix support walk.
* `RegionJumpStronglyConnected` — every ordered pair of region states is jump-reachable.
* `regionStronglyConnected_of_jumpReaches` — jump-strong-connectivity discharges
  `regionStronglyConnected`.
* `jumpStronglyConnected_pow_mulVec_tendsto_stationaryVec` — unconditional geometric convergence to
  the stationary law for a jump-strongly-connected region with a holding reaction.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Stochastic.RegionPrimitive`.
-/

open MeasureTheory ProbabilityTheory
open Filter Topology
open scoped ENNReal BigOperators

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- **A single enabled jump transition inside the region.** The embedded jump chain moves from the
count `n ∈ T` to the count `m ∈ T` along a reaction `r` that is enabled at `n` — the exit rate is
positive and `r` carries strictly positive jump probability `0 < jumpProb κ n r` — and lands on `m`
(`jumpNextCount n r = m`). This is the count-level forward edge whose reverse is a support edge of
the column-stochastic restricted transition matrix. -/
def JumpStep (N : Network S) (κ : RateConstants N) (T : Set (S → ℕ)) (n m : S → ℕ) : Prop :=
  n ∈ T ∧ m ∈ T ∧ N.exitRate κ n ≠ 0 ∧ ∃ r : N.R, N.jumpNextCount n r = m ∧ 0 < N.jumpProb κ n r

/-- **Jump-reachability inside the region.** The reflexive-transitive closure of `JumpStep`: the
count `m` is reachable from `n` by a directed walk of positive-probability enabled jumps that never
leaves `T`. -/
def JumpReaches (N : Network S) (κ : RateConstants N) (T : Set (S → ℕ)) (n m : S → ℕ) : Prop :=
  Relation.ReflTransGen (N.JumpStep κ T) n m

/-- **A forward jump is a reverse matrix support edge.** A single jump transition `n ⇝ m`
(`JumpStep`) makes the restricted-transition-matrix entry strictly positive at the post-firing
target `m` as the matrix *row* and the source `n` as the matrix *column*: the entry
`regionMatrix κ T ⟨m⟩ ⟨n⟩ = (jumpKernel κ n {m}).toReal` is strictly positive — the `r`-term of the
kernel sum is positive — hence nonzero. The matrix support digraph therefore carries the edge
`⟨m⟩ → ⟨n⟩`, the reverse of the forward jump. -/
theorem regionMatrix_ne_zero_of_jumpStep (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    [Fintype ↥T] {n m : S → ℕ} (h : N.JumpStep κ T n m) :
    N.regionMatrix κ T ⟨m, h.2.1⟩ ⟨n, h.1⟩ ≠ 0 := by
  classical
  obtain ⟨hn, hm, hexit, r, hr, hprob⟩ := h
  -- the kernel mass of `{m}` from `n` is the nonnegative reaction sum; the `r`-term is positive.
  have hmass : N.jumpKernel κ n {m} =
      ∑ r' : N.R, ENNReal.ofReal (N.jumpProb κ n r') * ({m} : Set (S → ℕ)).indicator 1
        (N.jumpNextCount n r') :=
    N.jumpKernel_apply_of_exitRate_pos κ n hexit {m}
  have hterm : 0 < ENNReal.ofReal (N.jumpProb κ n r) * ({m} : Set (S → ℕ)).indicator 1
      (N.jumpNextCount n r) := by
    rw [hr, Set.indicator_of_mem (Set.mem_singleton m), Pi.one_apply, mul_one]
    exact ENNReal.ofReal_pos.mpr hprob
  have hpos : 0 < N.jumpKernel κ n {m} := by
    rw [hmass]
    refine lt_of_lt_of_le hterm
      (Finset.single_le_sum (f := fun r' : N.R =>
        ENNReal.ofReal (N.jumpProb κ n r') * ({m} : Set (S → ℕ)).indicator 1
          (N.jumpNextCount n r'))
        (fun r' _ => bot_le) (Finset.mem_univ r))
  have hne : N.jumpKernel κ n {m} ≠ ∞ := measure_ne_top _ _
  show (N.jumpKernel κ (⟨n, hn⟩ : ↥T) {((⟨m, hm⟩ : ↥T) : S → ℕ)}).toReal ≠ 0
  exact (ENNReal.toReal_pos hpos.ne' hne).ne'

/-- **A forward jump walk reverses to a matrix support walk.** A jump-reachability walk `n ⇝ m`
inside the region (`JumpReaches`) yields a support-digraph walk `⟨m⟩ ⇝ ⟨n⟩` of the restricted
transition matrix (`supportReaches`): each forward jump edge `a ⇝ b` is the reverse matrix support
edge `⟨b⟩ → ⟨a⟩` (`regionMatrix_ne_zero_of_jumpStep`), and reversing a walk reverses its edge order. -/
theorem supportReaches_of_jumpReaches (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    [Fintype ↥T] {n m : S → ℕ} (hn : n ∈ T) (hm : m ∈ T) (h : N.JumpReaches κ T n m) :
    supportReaches (N.regionMatrix κ T) ⟨m, hm⟩ ⟨n, hn⟩ := by
  classical
  -- Induct from the front of the walk (`head_induction_on` generalizes the source `n`), so the new
  -- first jump edge `n ⇝ b` becomes the matrix support edge `⟨b⟩ → ⟨n⟩` appended (tail) to the
  -- matrix walk `⟨m⟩ ⇝ ⟨b⟩` carried by the induction hypothesis.
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hab hbm ih =>
    have hamem : a ∈ T := hab.1
    have hbmem : b ∈ T := hab.2.1
    have hedge : N.regionMatrix κ T ⟨b, hbmem⟩ ⟨a, hamem⟩ ≠ 0 :=
      N.regionMatrix_ne_zero_of_jumpStep κ hab
    have hmb : supportReaches (N.regionMatrix κ T) ⟨m, hm⟩ ⟨b, hbmem⟩ := ih hbmem
    exact Relation.ReflTransGen.tail hmb hedge

/-- **Jump-strong-connectivity of the region.** Every ordered pair of region states is connected by
a forward jump-reachability walk: the embedded jump chain restricted to `T` is a single
communicating class at the count level, every state reaching every state along positive-probability
enabled reactions that stay in `T`. This is the concrete network-structure hypothesis replacing the
abstract `regionStronglyConnected`. -/
def RegionJumpStronglyConnected (N : Network S) (κ : RateConstants N) (T : Set (S → ℕ)) : Prop :=
  ∀ n ∈ T, ∀ m ∈ T, N.JumpReaches κ T n m

/-- **Strong connectivity from jump-strong-connectivity.** A region whose embedded jump chain is a
single count-level communicating class (`RegionJumpStronglyConnected`) has a strongly connected
restricted-transition-matrix support digraph (`regionStronglyConnected`). For region states
`i j : ↥T`, jump-reachability `j ⇝ i` reverses to the matrix support walk `⟨i⟩ ⇝ ⟨j⟩`
(`supportReaches_of_jumpReaches`); applying the symmetric hypothesis at the swapped pair supplies
the walk in the matrix direction `i ⇝ j`. This discharges the abstract irreducibility hypothesis of
`invariant_probabilityMeasure_unique_on_region` and the convergence theorems from concrete network
reachability, the chemical-reaction-network recurrence picture (Anderson, Craciun & Kurtz,
"Product-form stationary distributions for deficiency zero chemical reaction networks"). -/
theorem regionStronglyConnected_of_jumpReaches (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} [Fintype ↥T] (h : N.RegionJumpStronglyConnected κ T) :
    N.regionStronglyConnected κ T := by
  intro i j
  -- the matrix walk `i ⇝ j` is the reverse of the forward jump walk `j ⇝ i`.
  have hreach : N.JumpReaches κ T (j : S → ℕ) (i : S → ℕ) := h j j.2 i i.2
  have := N.supportReaches_of_jumpReaches κ j.2 i.2 hreach
  simpa using this

/-- **Unconditional geometric convergence on a jump-strongly-connected region with a holding
reaction.** On a finite closed enabled region `T` whose embedded jump chain is jump-strongly-connected
(`RegionJumpStronglyConnected` — count-level irreducibility) and carries a holding reaction at some
state — a region count `n` with positive exit rate and a positive-probability reaction returning to
`n` (`jumpNextCount n r = n`, `0 < jumpProb κ n r`, the aperiodicity self-loop) — the embedded jump
chain mixes geometrically to the canonical stationary law: the singleton-mass vector of the `k`-step
matrix evolution converges entrywise to the stationary singleton masses, for every initial
probability measure supported on `T`.

Both structural hypotheses of the finite-state Perron–Frobenius convergence theorem are discharged
from network structure: irreducibility from jump-reachability (`regionStronglyConnected_of_jumpReaches`),
aperiodicity from the holding reaction (`regionMatrix_self_loop_of_jumpProb_pos`), giving region
primitivity (`regionPrimitive_of_stronglyConnected_self_loop`) and hence convergence
(`regionMatrix_primitive_pow_mulVec_tendsto_stationaryVec`). No abstract
`regionStronglyConnected`/`regionPrimitive` assumption remains. This is the finite-state replacement
for general Meyn–Tweedie ergodicity (Meyn & Tweedie, "Markov Chains and Stochastic Stability") on the
recurrent class of a deficiency-zero network (Anderson, Craciun & Kurtz). -/
theorem jumpStronglyConnected_pow_mulVec_tendsto_stationaryVec (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c) {T : Set (S → ℕ)}
    [Fintype ↥T] (hT : N.ClosedEnabledRegion κ T) (hne : T.Nonempty)
    (hjsc : N.RegionJumpStronglyConnected κ T)
    {n : S → ℕ} (hn : n ∈ T) (hexit : N.exitRate κ n ≠ 0)
    {r : N.R} (hr : N.jumpNextCount n r = n) (hprob : 0 < N.jumpProb κ n r)
    (μ : Measure (S → ℕ)) [IsProbabilityMeasure μ] (hμsupp : μ Tᶜ = 0) :
    ∀ i : ↥T, Tendsto
        (fun k => ((N.regionMatrix κ T) ^ k).mulVec (stationaryVec (T := T) μ) i) atTop
        (𝓝 (stationaryVec (T := T) (N.stationaryProbabilityMeasure κ c T) i)) := by
  haveI : Nonempty ↥T := hne.to_subtype
  have hsc : N.regionStronglyConnected κ T := N.regionStronglyConnected_of_jumpReaches κ hjsc
  have hloop : 0 < N.regionMatrix κ T ⟨n, hn⟩ ⟨n, hn⟩ :=
    N.regionMatrix_self_loop_of_jumpProb_pos κ hn hexit hr hprob
  have hprim : N.regionPrimitive κ T :=
    N.regionPrimitive_of_stronglyConnected_self_loop κ hsc hloop
  exact N.regionMatrix_primitive_pow_mulVec_tendsto_stationaryVec κ c hc hcb hT hne hprim μ hμsupp

end Network

end CRNT

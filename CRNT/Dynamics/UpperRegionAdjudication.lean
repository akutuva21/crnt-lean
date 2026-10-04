import CRNT.Dynamics.HighCodimensionSiphonFace

/-!
# Adjudication: is `exists_positive_omegaPoint_of_upperRegion` reachable under hole A's hypotheses?

Two round-1 researchers reached opposite verdicts on whether the Step-4 criterion
`CRNT.Network.exists_positive_omegaPoint_of_upperRegion` (HighCodimensionSiphonFace.lean:1596) is a
live target for hole A.  This module settles it by machine-checking the only question that matters,
stated as a `False`-level theorem over the criterion's *own* hypotheses plus hole A's own ω-limit
data.

## The dispute, precisely

`form-barrier`'s verdict: `hfloor` is a floor on a **region** the orbit is confined to, not along the
whole orbit, so the refutations of the barrier criteria's `hsep` do not touch it. The route lives.

`papers-craciun`'s verdict: inside the criterion's own proof the assembled set is
`K = closure Zupper ∩ {y | y.Nonnegative ∧ relEntropy xstar y ≤ relEntropy xstar x₀}`, every point of
`K` is strictly positive (`hKpos`, from `hfloor` through `hfloorC`), and permanence forces
`omegaLimit ⊆ K`. Since `hwmax : wmax ∈ omegaLimit`, that makes `wmax` strictly positive — which
contradicts `hzeroMax` (a species of the nonempty `Pmax` vanishes at `wmax`). The route is dead.

## The verdict

**`papers-craciun` is right, and it is stronger than they claimed.** The contradiction does not
need the barrier criteria, does not need `hsep` at all, and does not need `hK`/`hmaps`: it follows
from `hfloor` together with the *topological* fact that the ω-limit set is contained in the closure
of the forward orbit, while the floor lives on `Zupper` and the orbit stays in `Zupper`.

The one-line core is `omegaLimit_subset_closure_image2`: `wmax ∈ omegaLimit ⊆ closure (image2 ϕ v {x₀})`,
and the criterion's proof establishes `closure (image2 ϕ v {x₀}) ⊆ K`. Everything else is bookkeeping.

So `exists_positive_omegaPoint_of_upperRegion` is not merely hard — **its hypotheses are
inconsistent with hole A's hypotheses**, and any attempt to discharge `hfloor` from the hole's data
would have to derive `False`. This is a genuine result about the tree, not about the paper: the
criterion is *correct* as a conditional statement, and it is the *conjunction* with `hwmax` that is
unsatisfiable. Note that this does **not** make the criterion wrong — a genuine trajectory whose
ω-limit set never meets the boundary does satisfy all of it, and then its conclusion is exactly the
positive ω-point. What it means is that the criterion's surface data cannot be built in the case
hole A is about, for the same reason `hsep` cannot: a boundary ω-point is in the region.

`form-barrier`'s specific counter-argument — that `hsplit` might route the orbit into an upper
region **avoiding** `wmax` — is refuted by `orbit_stays_in_upperRegion` plus the same closure step:
`hsplit` says the *orbit* avoids the surface, and says nothing about ω-limit points, which are
limit points **of** the orbit and hence lie in its closure. Routing the orbit away from `wmax` does
not route `wmax` away from the orbit.

## Consequences

* `exists_positive_omegaPoint_of_upperRegion` is not a target for hole A. Neither is
  `persistentFrom_of_upperRegion` (same `hfloor`, same `K`).
* The barrier branch (`hsep`) is dead for the reason `form-barrier` gave. This module removes the
  remaining doubt about the *other* branch, which had been argued from prose.
* What survives is a route whose conclusion does **not** pass through a floor on a region containing
  ω-limit points — i.e. `CRNT.Network.ComparableGrowthDescent`, whose finite induction
  `omegaLimit_positive_of_descend` is already proved and which the hole's own docstring
  (HighCodimensionSiphonFace.lean:167-171) names as the live alternative.
-/

namespace CRNT.UpperRegionAdjudication

open Filter
open scoped NNReal Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The Step-4 criterion is unsatisfiable jointly with a boundary ω-limit point.**

Take exactly the hypotheses of `CRNT.Network.exists_positive_omegaPoint_of_upperRegion`, add hole A's
ω-limit data (`hwmax`, `hzeroMax`, `hPmaxne`), and conclude `False`.

Everything here is a hypothesis of one of those two theorems — nothing is assumed that the two
together do not already provide. The proof is the criterion's own `K`-assembly followed by the
ω-limit containment, with the vanishing coordinate read off `hzeroMax` at a species `hPmaxne`
supplies.
-/
theorem upperRegion_criterion_inconsistent_with_boundaryOmegaPoint
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hx₀ : x₀.Positive)
    {Zlow Zupper : Set (Concentration S)} {ε : ℝ} (hε : 0 < ε)
    (hopenLow : IsOpen Zlow) (hopenUp : IsOpen Zupper) (hdisj : Disjoint Zlow Zupper)
    (hsplit : ∀ t : ℝ, 0 ≤ t → γ x₀ t ∈ Zlow ∪ Zupper)
    (hx₀Z : x₀ ∈ Zupper)
    (hfloor : ∀ y ∈ Zupper, ∀ s, ε ≤ y s)
    -- hole A's ω-limit data
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    {wmax : Concentration S} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0) :
    False := by
  -- the orbit starts at `x₀`
  have hγ0 : γ x₀ 0 = x₀ := by
    have h := hϕγ x₀ 0
    simpa using h.symm
  have hcont : ContinuousOn (γ x₀) (Set.Ici 0) :=
    fun t ht => ((hsol t ht).continuousAt).continuousWithinAt
  have hpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive :=
    N.genuineOrbit_pos (Γ := γ x₀) κ (by rw [hγ0]; exact hx₀) hsol
  have hle : ∀ t, 0 ≤ t → relEntropy xstar (γ x₀ t) ≤ relEntropy xstar x₀ :=
    fun t ht =>
      (N.genuineOrbit_relEntropy_le (Γ := γ x₀) κ hxs hcb hpos hsol t ht).trans_eq
        (congrArg (relEntropy xstar) hγ0)
  -- §9.1 bridge: non-crossing keeps the orbit on the upper side
  have hstay : ∀ t, 0 ≤ t → γ x₀ t ∈ Zupper :=
    CRNT.Network.orbit_stays_in_upperRegion hcont hopenLow hopenUp hdisj hsplit
      (by rw [hγ0]; exact hx₀Z)
  -- the floor survives passage to `closure Zupper`
  have hFloorClosed : IsClosed {y : Concentration S | ∀ s, ε ≤ y s} := by
    have hrw : {y : Concentration S | ∀ s, ε ≤ y s} = ⋂ s, {y | ε ≤ y s} := by
      ext y; simp [Set.mem_iInter]
    rw [hrw]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have hfloorC : closure Zupper ⊆ {y | ∀ s, ε ≤ y s} :=
    closure_minimal (fun y hy s => hfloor y hy s) hFloorClosed
  set K : Set (Concentration S) :=
    closure Zupper ∩ {y | y.Nonnegative ∧ relEntropy xstar y ≤ relEntropy xstar x₀} with hKdef
  have hKcpt : IsCompact K := by
    rw [hKdef]
    exact (CRNT.Network.isCompact_relEntropy_sublevel hxs (relEntropy xstar x₀)).inter_left
      isClosed_closure
  have hKpos : ∀ y ∈ K, Concentration.Positive y := by
    intro y hy s
    exact lt_of_lt_of_le hε (hfloorC hy.1 s)
  -- the whole forward orbit lies in `K`
  have horbit : ∀ t : ℝ≥0, ϕ t x₀ ∈ K := by
    intro t
    rw [hϕγ x₀ t]
    have ht : 0 ≤ (t : ℝ) := t.coe_nonneg
    exact ⟨subset_closure (hstay (t : ℝ) ht), (hpos (t : ℝ) ht).nonnegative, hle (t : ℝ) ht⟩
  have himgs : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact horbit t
  -- the decisive step: `omegaLimit` sits inside the closed set `K`
  have hωK : omegaLimit atTop ϕ {x₀} ⊆ K :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) Filter.univ_mem).trans
      ((IsClosed.closure_subset_iff hKcpt.isClosed).mpr himgs)
  have hwmaxK : wmax ∈ K := hωK hwmax
  -- `K` is strictly positive, so `wmax` is; but a species of the nonempty `Pmax` vanishes at it
  obtain ⟨s, hs⟩ := hPmaxne
  have hz : wmax s = 0 := (hzeroMax s).mp hs
  have hpos' : 0 < wmax s := hKpos wmax hwmaxK s
  rw [hz] at hpos'
  exact absurd hpos' (lt_irrefl 0)

end CRNT.UpperRegionAdjudication

namespace CRNT.UpperRegionAdjudication

open Filter
open scoped NNReal Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The advertised fallback is not a weaker target: it is the goal.**
`CRNT.Network.ComparableGrowthDescent` — named at `HighCodimensionSiphonFace.lean:167-171` as the
live alternative to the barrier route — is *equivalent* to the existence of a positive ω-limit point,
given a nonempty carried critical siphon. In hole A `P₀ = Pmax` qualifies (`hPmaxne`, critical via
`isCriticalSiphon_of_siphonCarried`, carried via `⟨wmax, hwmax, hzeroMax⟩`).

So after this module's refutation of the `upperRegion` branch there is **no sufficiency criterion in
the tree strictly weaker than the conclusion**: the barrier branch dies on `hsep`, the region branch
dies here, and the descent branch is the goal in disguise. Recorded as a corollary so the next
researcher does not re-derive it by reading.

This is a statement about *this repository*, not about the mathematics: a genuinely weaker route
would have to be built from outside the current criterion set. -/
theorem comparableGrowthDescent_is_not_a_weaker_route (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S} {P₀ : Finset S}
    (hP₀crit : N.IsCriticalSiphon P₀) (hP₀carr : N.SiphonCarried ϕ x₀ P₀) :
    N.ComparableGrowthDescent ϕ x₀ ↔ (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) :=
  N.comparableGrowthDescent_iff_omegaPointPositive hP₀crit hP₀carr

end CRNT.UpperRegionAdjudication

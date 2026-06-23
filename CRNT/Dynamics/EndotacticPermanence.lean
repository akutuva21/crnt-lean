import CRNT.Dynamics.GACOmegaPositive
import CRNT.Geometry.Endotactic

/-!
# Permanence and the Gopalkrishnan–Miller–Shiu route to global convergence

The Gopalkrishnan–Miller–Shiu route to the Global Attractor Conjecture runs
`StronglyEndotactic ⇒ permanent ⇒ GAC`. This module lands the immediately provable
end of that chain — the **permanence ⇒ convergence** bridge — together with the
sign content of strong endotacticity along the relative-entropy dissipation.

`Permanent` is the eventual-confinement predicate: the forward orbit of `x₀` under a
semiflow `ϕ` is eventually contained in a fixed compact set `K` of strictly positive
concentrations. `permanent_of_eventually_in_compact_interior` packages a compact
interior absorbing set directly into this predicate.

`omegaLimit_meets_positive_of_permanent` extracts the geometric payoff: a permanent
orbit has a nonempty ω-limit set lying entirely inside the compact positive set `K`,
so every ω-point — in particular some ω-point — is strictly positive. Feeding that
positive ω-point into `omegaLimit_eq_singleton_of_mem_positive` gives
`gac_of_permanent`: a weakly reversible complex-balanced trajectory that is permanent
converges to the unique positive equilibrium `x*` of its compatibility class. This is
the honest Route-C payoff: it reuses the one-positive-ω-point reduction verbatim and
supplies its missing existence hypothesis from confinement.

`stronglyEndotactic_strict_dissipation_direction` is the discrete/geometric sign core:
when the logarithmic gradient `w = log x - log x*` is non-constant on the reaction
sources, strong endotacticity produces a `w`-maximal reaction whose `w`-rate is
strictly negative — the rate functional strictly decreases in the active direction.
This is the per-reaction sign that the Gopalkrishnan–Miller–Shiu argument aggregates
into a uniform near-boundary dissipation estimate.

The uniform near-boundary dissipation bound itself — the estimate that upgrades strong
endotacticity to permanence, valid up to the orthant boundary — is the named residue:
it requires the Newton-polytope / endotactic geometry not yet assembled in this layer.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Dynamics.GACOmegaPositive`, `CRNT.Geometry.Endotactic`.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Permanence.** A trajectory of the semiflow `ϕ` started at `x₀` is *permanent* when
its forward orbit is eventually contained in a fixed compact set `K` of strictly positive
concentrations: there is a compact `K`, all of whose points are strictly positive, and a
tail filter set `v ∈ atTop` along which the orbit stays inside `K`. Permanence is the
no-boundary-attraction confinement at the heart of the Gopalkrishnan–Miller–Shiu route. -/
def Permanent (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S) : Prop :=
  ∃ K : Set (Concentration S), IsCompact K ∧ (∀ y ∈ K, Concentration.Positive y) ∧
    ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K

omit [DecidableEq S] [Fintype S] in
/-- A compact set `K` of strictly positive concentrations that eventually absorbs the
orbit witnesses permanence. The closure of the orbit tail already lies in the closed
compact `K`, so no extra closure step is needed. -/
theorem permanent_of_eventually_in_compact_interior
    (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S)
    {K : Set (Concentration S)} (hKcpt : IsCompact K)
    (hKpos : ∀ y ∈ K, Concentration.Positive y)
    {v : Set ℝ≥0} (hv : v ∈ (atTop : Filter ℝ≥0))
    (hvK : closure (Set.image2 ϕ v {x₀}) ⊆ K) :
    Permanent ϕ x₀ :=
  ⟨K, hKcpt, hKpos, v, hv, hvK⟩

omit [DecidableEq S] [Fintype S] in
/-- **A permanent orbit has a positive ω-limit point.** The compact confining set `K` is an
absorbing set for the orbit, so the ω-limit set is nonempty and contained in `K`; every point
of `K` — hence the ω-point — is strictly positive. -/
theorem omegaLimit_meets_positive_of_permanent
    (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S)
    (hperm : Permanent ϕ x₀) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p := by
  obtain ⟨K, hKcpt, hKpos, v, hv, hvK⟩ := hperm
  have hne : (omegaLimit atTop ϕ {x₀}).Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing _ _ _ hKcpt ⟨v, hv, hvK⟩
      (Set.singleton_nonempty x₀)
  obtain ⟨p, hp⟩ := hne
  refine ⟨p, hp, ?_⟩
  have hpK : p ∈ K :=
    hvK ((omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) hv) hp)
  exact hKpos p hpK

/-- **Permanence ⇒ global convergence.** For a weakly reversible network with a positive
complex-balanced reference `x*` and a positive start `x₀` in its class, suppose the mass-action
semiflow `ϕ` (curves `γ`) satisfies the standard LaSalle facts — ω-orbits solve the genuine field
(`hgenω`), the relative entropy is constant on the ω-limit set (`hωc`), ω-points are nonnegative
(`hωnn`) and affinely invariant (`hωaff`), and orbits from positive ω-points stay positive
(`hposorbit`) — and that the trajectory is **permanent**. Then the ω-limit set is exactly `{x*}`:
the trajectory converges to the unique positive equilibrium of its compatibility class.

Permanence supplies the one missing input of `omegaLimit_eq_singleton_of_mem_positive`, namely a
strictly positive ω-limit point, by confining the orbit to a compact interior set. -/
theorem gac_of_permanent
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0compat : N.StoichCompatible x₀ xstar)
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    (hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t))
    (hperm : Permanent ϕ x₀) :
    omegaLimit atTop ϕ {x₀} = {xstar} :=
  omegaLimit_eq_singleton_of_mem_positive N hwr κ hxs hcb hx0compat hγ0 hϕγ hgenω hωnn hωaff hωc
    hposorbit (omegaLimit_meets_positive_of_permanent ϕ x₀ hperm)

/-- **Strict dissipation direction of a strongly endotactic network.** If the network is strongly
endotactic and the direction `w` is non-constant on the reaction sources — there are two reactions
with different `wValue` — then there is a `w`-maximal reaction whose `w`-rate is strictly negative.

Taking `w = log x - log x*` (the logarithmic gradient driving the relative-entropy dissipation),
this is the per-reaction sign content of the Gopalkrishnan–Miller–Shiu argument: at the `w`-maximal
reactant face the rate functional strictly decreases in the active direction. Aggregating these
signs into a uniform near-boundary lower bound — the estimate that yields permanence — is the
named residue, requiring the Newton-polytope geometry not present in this layer. -/
theorem stronglyEndotactic_strict_dissipation_direction {N : Network S}
    (h : N.StronglyEndotactic) (w : S → ℝ)
    (hncon : ∃ r₁ r₂ : N.R, N.wValue w r₁ ≠ N.wValue w r₂) :
    ∃ r : N.R, N.IsMaxSource w r ∧ N.wRate w r < 0 :=
  h.2 w hncon

/-- The strictly-inward `w`-maximal reaction of a strongly endotactic network has a `w`-rate that
is both `≤ 0` (endotacticity) and `< 0` (strong endotacticity); in particular it is nonzero. This
records that the active-direction descent is genuinely strict, not merely nonpositive. -/
theorem stronglyEndotactic_wRate_ne_zero {N : Network S}
    (h : N.StronglyEndotactic) (w : S → ℝ)
    (hncon : ∃ r₁ r₂ : N.R, N.wValue w r₁ ≠ N.wValue w r₂) :
    ∃ r : N.R, N.IsMaxSource w r ∧ N.wRate w r ≠ 0 := by
  obtain ⟨r, hmax, hneg⟩ := stronglyEndotactic_strict_dissipation_direction h w hncon
  exact ⟨r, hmax, ne_of_lt hneg⟩

end Network

end CRNT

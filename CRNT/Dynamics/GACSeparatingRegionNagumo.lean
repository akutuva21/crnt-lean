import CRNT.Dynamics.GACSeparatingRegion
import CRNT.Dynamics.ClosedSetNagumo

/-!
# Global stability from a separating region via closed-set Nagumo

The forward-invariance of a separating region along the genuine orbit, hypothesized in
`gac_of_separatingRegion`, is exactly the conclusion of the distance-based closed-set Nagumo result
`invariant_of_infDist_antitoneOn`: a closed region the orbit's distance to which never increases is
forward-invariant. This module routes the global attractor argument through that result, so the only
analytic input left is the **distance-nonincreasing bridge** — that subtangency of the field to the
region keeps `t ↦ Metric.infDist (Γ t) R` nonincreasing along the orbit. That bridge is the
set-valued viability content recorded in `ClosedSetNagumo.lean` and `Viability.lean`; it is carried
here as the hypothesis `hanti`.

## Main result

* `Network.gac_of_separatingRegion_nagumo` — for a weakly reversible network with a positive
  complex-balanced reference `x*` and a positive start `x₀` in its class, given a closed region `R`
  that contains `x₀`, lies in a compact `B`, and stays a positive distance `ε s` above every
  coordinate facet, if `t ↦ Metric.infDist (Γ t) R` is nonincreasing along every genuine orbit `Γ`
  through `x₀`, then the ω-limit set through `x₀` is `{x*}`.

Depends on: `CRNT.Dynamics.GACSeparatingRegion`,
`CRNT.Dynamics.ClosedSetNagumo`.
-/

open scoped BigOperators NNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Global stability from a separating region via closed-set Nagumo.** Let `R` be a closed region
containing `x₀`, contained in a compact `B`, and bounded away from every coordinate facet by a
positive floor. If `t ↦ Metric.infDist (Γ t) R` is nonincreasing on `[0, ∞)` along every genuine
mass-action orbit `Γ` through `x₀`, then the orbit stays in `R` (closed-set Nagumo), hence is
confined to a compact subset of the open orthant, and the genuine semiflow's ω-limit set through
`x₀` is `{x*}`.

The distance-nonincreasing hypothesis `hanti` is the set-valued viability bridge (`ClosedSetNagumo`,
`Viability`): the only analytic input not discharged from the region's geometry. -/
theorem gac_of_separatingRegion_nagumo
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    {R B : Set (Concentration S)} {ε : S → ℝ}
    (hBcpt : IsCompact B) (hε : ∀ s, 0 < ε s)
    (hRclosed : IsClosed R) (hRB : R ⊆ B) (hRfloor : ∀ y ∈ R, ∀ s, ε s ≤ y s) (hx0R : x₀ ∈ R)
    (hanti : ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      AntitoneOn (fun t => Metric.infDist (Γ t) R) (Set.Ici 0)) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_separatingRegion hwr κ hxs hcb hx0 hx0compat hBcpt hε hRB hRfloor hx0R
    (fun Γ hΓ0 hsol t ht =>
      invariant_of_infDist_antitoneOn hRclosed ⟨x₀, hx0R⟩
        (by rw [hΓ0]; exact hx0R) (hanti Γ hΓ0 hsol) ht)

end Network

end CRNT

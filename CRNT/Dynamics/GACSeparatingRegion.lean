import CRNT.Dynamics.GACConfinement

/-!
# Global stability from a forward-invariant separating region

A zero-separating surface produces a closed region on the side of the trajectory away from the
boundary. When that region is bounded and keeps a fixed positive distance from every coordinate
facet, and the genuine mass-action orbit through the start stays inside it, the network has the
global attractor property. This module records that composition: a forward-invariant separating
region discharges the confinement hypothesis of `gac_of_confinement`.

The forward-invariance of the region along the genuine orbit is the conclusion a subtangent
separating surface yields through the closed-set Nagumo result; it enters here as a hypothesis. The
boundedness and the per-facet floor are the geometric facts a separating region carries.

## Main result

* `Network.gac_of_separatingRegion` — for a weakly reversible network with a positive complex-balanced
  reference `x*` and a positive start `x₀` in its class, given a region `R` that contains `x₀`, lies
  in a compact set `B`, and stays a positive distance `ε s` above every coordinate facet, if the
  genuine orbit through `x₀` stays in `R` for all forward time, then the ω-limit set through `x₀` is
  `{x*}`.

Depends on: `CRNT.Dynamics.GACConfinement`.
-/

open scoped BigOperators NNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Global stability from a forward-invariant separating region.** Let `R` be a region containing
the start `x₀`, contained in a compact set `B`, and bounded away from every coordinate facet by a
positive floor (`ε s ≤ y s` for all `y ∈ R`, with `0 < ε s`). If every genuine mass-action integral
curve through `x₀` stays in `R` for all forward time, the genuine semiflow's ω-limit set through
`x₀` is `{x*}`.

The region's boundedness (`hRB`) and floor (`hRfloor`) are the geometric data of a zero-separating
surface; the orbit's confinement to `R` (`hinv`) is the forward-invariance a subtangent surface
yields through the closed-set Nagumo result. Together they discharge `gac_of_confinement`. -/
theorem gac_of_separatingRegion
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    {R B : Set (Concentration S)} {ε : S → ℝ}
    (hBcpt : IsCompact B) (hε : ∀ s, 0 < ε s)
    (hRB : R ⊆ B) (hRfloor : ∀ y ∈ R, ∀ s, ε s ≤ y s) (_hx0R : x₀ ∈ R)
    (hinv : ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      ∀ t, 0 ≤ t → Γ t ∈ R) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_confinement hwr κ hxs hcb hx0 hx0compat hBcpt hε
    (fun Γ hΓ0 hsol t ht =>
      have hmem : Γ t ∈ R := hinv Γ hΓ0 hsol t ht
      ⟨hRB hmem, fun s => hRfloor (Γ t) hmem s⟩)

end Network

end CRNT

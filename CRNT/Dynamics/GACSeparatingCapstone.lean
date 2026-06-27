import CRNT.Dynamics.GACSeparatingRegion

/-!
# The global attractor conjecture reduced to one separating-confinement predicate

The chain `surface → region → confinement → persistence → GAC` collapses the global attractor
conjecture, for weakly reversible complex-balanced networks, to a single geometric predicate:
that the genuine mass-action orbit is confined to a bounded region holding a fixed positive distance
above every coordinate facet. This module names that predicate and proves it suffices.

`SeparatingConfinement` is the mass-action-level statement of the zero-separating surface of
Craciun, _Toric differential inclusions and a proof of the global attractor conjecture_: a region
on the side of the orbit away from the boundary, into which the orbit is forward-invariant, that is
bounded and bounded away from every facet. Constructing such a region from the toric differential
inclusion of the network is the content carried as the predicate; every other step from it to the
global attractor conclusion is discharged.

## Contents

* `Network.SeparatingConfinement N κ x₀` — there is a region `R` inside a compact `B`, a positive
  floor `ε`, with `x₀ ∈ R`, `R` bounded away from every facet (`ε s ≤ y s` for `y ∈ R`), and the
  genuine orbit through `x₀` forward-invariant in `R`.

* `Network.gac_of_separatingConfinement` — the separating-confinement predicate implies the global
  attractor conclusion: the genuine semiflow's ω-limit set through `x₀` is `{x*}`.

This is the reduction target: with this module, the global attractor conjecture for weakly
reversible complex-balanced networks rests entirely on `SeparatingConfinement`, the mass-action
zero-separating region, and nothing else.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.GACSeparatingRegion`.
-/

open scoped BigOperators NNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Separating confinement.** The genuine mass-action orbit through `x₀` is forward-invariant in a
region `R` that is contained in a compact set `B` and holds a fixed positive distance `ε s` above
every coordinate facet. This is the mass-action-level form of a zero-separating surface: the region
on the side of the orbit away from the boundary, bounded and bounded off every facet, that the orbit
never leaves. -/
def SeparatingConfinement (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) : Prop :=
  ∃ (R B : Set (Concentration S)) (ε : S → ℝ),
    IsCompact B ∧ (∀ s, 0 < ε s) ∧ R ⊆ B ∧ (∀ y ∈ R, ∀ s, ε s ≤ y s) ∧ x₀ ∈ R ∧
    (∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      ∀ t, 0 ≤ t → Γ t ∈ R)

/-- **The global attractor conclusion from separating confinement.** For a weakly reversible network
with a positive complex-balanced reference `x*` and a positive start `x₀` in its class, the
separating-confinement predicate implies the genuine semiflow's ω-limit set through `x₀` is `{x*}`.

This is the reduction: the global attractor conjecture for weakly reversible complex-balanced
networks follows from `SeparatingConfinement` alone. Constructing the confining region from the
network's toric differential inclusion is the remaining content. -/
theorem gac_of_separatingConfinement
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    (h : N.SeparatingConfinement κ x₀) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} := by
  obtain ⟨R, B, ε, hBcpt, hε, hRB, hRfloor, hx0R, hinv⟩ := h
  exact N.gac_of_separatingRegion hwr κ hxs hcb hx0 hx0compat hBcpt hε hRB hRfloor hx0R hinv

end Network

end CRNT

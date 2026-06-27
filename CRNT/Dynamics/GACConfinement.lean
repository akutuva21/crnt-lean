import CRNT.Dynamics.PersistenceGAC

/-!
# Global stability from confinement away from the boundary

The general persistence interface `Network.gac_of_genuine_persistence` asks for a compact set inside
the open positive orthant that absorbs the genuine mass-action orbit. This module supplies that
compact set in the shape a separating-surface family produces it: a bounded region `B` together with
a strictly positive floor `ε s` on each species coordinate. Their conjunction — bounded, and a fixed
distance above every coordinate facet — is exactly a compact subset of the open orthant, so it
discharges the persistence hypothesis and yields the global attractor conclusion.

Boundedness and the per-facet floors are the two outputs of a zero-separating-surface family
(`ZeroSeparatingCurve2D`): the surfaces keep each coordinate above a positive floor, and a
relative-entropy sublevel set bounds the orbit. This module is the assembly that turns those two
facts into the `K₀` of `gac_of_genuine_persistence`.

## Main result

* `Network.gac_of_confinement` — for a weakly reversible network with a positive complex-balanced
  reference `x*`, a positive start `x₀` in its class, a compact region `B`, and a positive floor
  `ε : S → ℝ`, if every genuine integral curve through `x₀` stays in `B` and keeps `ε s ≤ Γ t s` for
  every species `s` and every forward time, then the genuine semiflow's ω-limit set through `x₀` is
  exactly `{x*}`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.PersistenceGAC`.
-/

open scoped BigOperators NNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Global stability from confinement away from the boundary.** Suppose every genuine mass-action
integral curve `Γ` through `x₀` stays in a compact region `B` and keeps each coordinate above a
positive floor (`ε s ≤ Γ t s` with `0 < ε s`). Then the orbit is confined to the compact set
`B ∩ {y | ∀ s, ε s ≤ y s}`, which lies inside the open positive orthant, so
`gac_of_genuine_persistence` applies: the genuine semiflow's ω-limit set through `x₀` is `{x*}`.

The hypothesis is persistence in the form a separating-surface family delivers it — bounded and a
fixed distance off every facet — and this lemma packages it into the compact absorbing region the
general persistence theorem consumes. -/
theorem gac_of_confinement
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    {B : Set (Concentration S)} (hBcpt : IsCompact B)
    {ε : S → ℝ} (hε : ∀ s, 0 < ε s)
    (hconfine : ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      ∀ t, 0 ≤ t → Γ t ∈ B ∧ ∀ s, ε s ≤ Γ t s) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} := by
  -- The away-from-facets constraint set is closed (a finite intersection of coordinate halfspaces).
  have hTclosed : IsClosed {y : Concentration S | ∀ s, ε s ≤ y s} := by
    have hrw : {y : Concentration S | ∀ s, ε s ≤ y s} = ⋂ s, {y | ε s ≤ y s} := by
      ext y; simp [Set.mem_iInter]
    rw [hrw]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  -- The confining region `B ∩ {away from every facet}` is compact and inside the open orthant.
  refine N.gac_of_genuine_persistence hwr κ hxs hcb hx0 hx0compat
    (K₀ := B ∩ {y : Concentration S | ∀ s, ε s ≤ y s})
    (hBcpt.inter_right hTclosed) ?_ ?_
  · -- positivity: each coordinate is at least its positive floor
    intro y hy s
    exact lt_of_lt_of_le (hε s) (hy.2 s)
  · -- absorption: the confinement hypothesis lands the orbit in the region
    intro Γ hΓ0 hsol t ht
    exact hconfine Γ hΓ0 hsol t ht

end Network

end CRNT

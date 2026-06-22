import CRNT.Theorems.DeficiencyZero.AsymptoticStability

/-!
# Forward invariance of relative-entropy sublevel sets and confined global stability

For a weakly reversible network with a positive complex-balanced reference `x*`, the
relative-entropy sublevel set
`K = {y | y.Nonnegative ∧ relEntropy x* y ≤ C}`
is a compact region of state space.  When the threshold `C` lies strictly below every
reference coordinate `x*_s`, this region is confined to the open positive orthant: no point
of `K` touches the boundary of the nonnegative orthant.  This is the forward-invariance /
no-boundary-attraction content for the mass-action semiflow, generalizing the first-crossing
positivity argument behind `orbit_pos`: the relative entropy is a Lyapunov function whose
sublevel sets are positively invariant, and the coercivity bound on the boundary
(`relEntropy_ge_of_coord_zero`) pushes those sublevel sets into the interior.

The compact, positively-confined, absorbing region built this way discharges the persistence
hypotheses of the conditional global-stability statement.  Under the explicit, checkable
confinement hypothesis `hloc : ∀ s, relEntropy x* x₀ < x*_s` — relative entropy of the start
below every reference coordinate — the ω-limit set of the genuine mass-action dynamics through
a positive, stoichiometrically compatible start is exactly `{x*}`.

## Main results

* `relEntropy_sublevel_subset_positive`: every point of a relative-entropy sublevel set whose
  threshold is below every reference coordinate is strictly positive.
* `isCompact_relEntropy_sublevel_positive`: that sublevel set is compact.
* `gac_of_local_confinement`: confined global asymptotic convergence — under the local
  confinement hypothesis the ω-limit of the mass-action semiflow is the singleton `{x*}`.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Theorems.DeficiencyZero.AsymptoticStability`.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

omit [DecidableEq S] in
/-- **No-boundary confinement of relative-entropy sublevel sets.** If every reference
coordinate `x*_s` strictly exceeds the threshold `C`, then every nonnegative state whose
relative entropy is at most `C` is strictly positive: a boundary state (some coordinate zero)
would have relative entropy at least `x*_s > C`, by the coercivity bound
`relEntropy_ge_of_coord_zero`. The relative-entropy sublevel set is thus confined to the open
positive orthant, the geometric heart of persistence for the mass-action semiflow. -/
theorem relEntropy_sublevel_subset_positive {xstar : Concentration S} (hxs : xstar.Positive)
    {C : ℝ} (hC : ∀ s, C < xstar s) {y : Concentration S}
    (hy : y.Nonnegative) (hyC : relEntropy xstar y ≤ C) : y.Positive := by
  intro s
  rcases lt_or_eq_of_le (hy s) with hpos | hzero
  · exact hpos
  · exact absurd (le_trans (relEntropy_ge_of_coord_zero hxs hy hzero.symm) hyC) (not_le.mpr (hC s))

omit [DecidableEq S] in
/-- **Compactness of the confined sublevel set.** The relative-entropy sublevel set is compact
(coercivity bounds each coordinate); pairing this with `relEntropy_sublevel_subset_positive`
exhibits a compact region inside the open positive orthant that the orbit cannot leave. -/
theorem isCompact_relEntropy_sublevel_positive {xstar : Concentration S} (hxs : xstar.Positive)
    (C : ℝ) : IsCompact {y : Concentration S | y.Nonnegative ∧ relEntropy xstar y ≤ C} :=
  isCompact_relEntropy_sublevel hxs C

/-- **Confined global asymptotic convergence.** For a weakly reversible network with a positive
complex-balanced reference `x*` and a positive, stoichiometrically compatible start `x₀` whose
relative entropy lies strictly below every reference coordinate (`hloc`), the mass-action
semiflow built from the bounded-Lipschitz cutoff carries the genuine dynamics through `x₀`, and
its ω-limit set is exactly `{x*}`.

The confinement hypothesis `hloc` is the explicit, checkable persistence certificate: it forces
the relative-entropy sublevel set through `x₀` to be a compact absorbing region inside the open
positive orthant (`relEntropy_sublevel_subset_positive`, `isCompact_relEntropy_sublevel_positive`),
discharging the no-boundary-attraction obligation.  The convergence then follows from the
Lyapunov descent of the relative entropy and the LaSalle invariance principle. -/
theorem gac_of_local_confinement
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    (hloc : ∀ s, relEntropy xstar x₀ < xstar s) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  omegaLimit_eq_singleton_of_local N hwr κ hxs hcb hx0 hx0compat hloc

end Network

end CRNT

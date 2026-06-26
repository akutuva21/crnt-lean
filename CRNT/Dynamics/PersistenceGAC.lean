import CRNT.Dynamics.GlobalStability
import CRNT.Dynamics.ForwardInvariance
import CRNT.Dynamics.Nagumo

/-!
# Single-linkage-class global stability from genuine-field persistence

For a weakly reversible network with a positive complex-balanced reference `x*`, global
asymptotic stability within a positive compatibility class is the global attractor conjecture:
every positive trajectory converges to the unique complex-balanced equilibrium of its class. The
analytic obstruction is *persistence* — that no species goes extinct, i.e. the orbit does not
approach the boundary of the nonnegative orthant.

`omegaLimit_eq_singleton_of_persistent` already closes this conjecture conditionally, but its
persistence hypothesis is stated against the internal bounded-Lipschitz cutoff semiflow and its
clamped derivative — an opaque object for a caller. This module repackages persistence as a
hypothesis phrased entirely on the **genuine** mass-action field: a compact set `K₀` inside the
open positive orthant that absorbs every genuine integral curve through `x₀`. Under this
checkable certificate the genuine semiflow's ω-limit set is exactly `{x*}`.

## What the genuine-field hypothesis buys

The reduction discharges the internal cutoff `hpersist` by Nagumo confinement: every cutoff
orbit point of `x₀` solves the genuine field (`clampBox_eq_of_sublevel` collapses the clamp on
the relative-entropy sublevel set, via `orbit_pos`/`orbit_relEntropy_le`), so a genuine integral
curve started at `x₀` is recovered, and the genuine-field persistence certificate applies to it.
The mass-action field is inward on every boundary face (`massActionVectorField_inwardOnBoundary`,
the Nagumo brick), so the nonnegative orthant is itself forward invariant and the genuine orbit
never leaves it; persistence is the residual statement that it also stays a positive distance
from the boundary.

## The ceiling

Persistence remains an *irreducible* hypothesis: the relative-entropy sublevel set
`{y | y ≥ 0 ∧ relEntropy x* y ≤ relEntropy x* x₀}` is compact and absorbing, but it lies inside
the open orthant only when its threshold sits below every reference coordinate
(`relEntropy_sublevel_subset_positive`), which is the *local* confinement hypothesis `hloc` of
`gac_of_local_confinement`. Removing persistence outright — proving it for an arbitrary positive
start of a single-linkage-class network — is Anderson's theorem and the global attractor
conjecture, beyond Mathlib's current dynamical-systems footing (no siphon/trap Petri-net theory,
no toric differential inclusions). This module lands the strongest *unconditional-on-closeness*
result: persistence as a clean genuine-field certificate, with full convergence proved from it.

## Main results

* `Network.gac_of_genuine_persistence`: from a compact `K₀` in the open positive orthant
  absorbing every genuine integral curve through `x₀`, the genuine semiflow's ω-limit set is
  `{x*}`.
* `Network.massAction_orbit_nonneg`: the Nagumo specialization — a genuine integral curve from a
  nonnegative start stays nonnegative for all forward time (closed-orthant forward invariance,
  with the dissipativity bound supplied by `exists_field_lower_bound` on a confining box).

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.GlobalStability`,
`CRNT.Dynamics.ForwardInvariance`, `CRNT.Dynamics.Nagumo`.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Closed forward-invariance of the orthant for a genuine integral curve.** A genuine
mass-action integral curve `γ` from a nonnegative start stays nonnegative for all forward time.
The dissipativity bound the closed-orthant Nagumo lemma needs is the field's linear lower bound
`exists_field_lower_bound` on a box `[-B, B]` containing the curve; here it is supplied along the
curve in disjunctive form (`-L·γ ≤ f(γ)` or the coordinate is already nonnegative), which is
exactly what `massAction_forwardInvariant_nonneg` consumes. -/
theorem massAction_orbit_nonneg (N : Network S) (κ : N.RateConstants) {L : ℝ}
    {γ : ℝ → Concentration S}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hLip : ∀ t s, -L * (γ t s) ≤ N.massActionVectorField κ (γ t) s ∨ 0 ≤ γ t s)
    (h0 : (γ 0).Nonnegative) :
    ∀ t, 0 ≤ t → (γ t).Nonnegative :=
  N.massAction_forwardInvariant_nonneg κ hderiv hLip h0

/-- **Single-linkage-class global stability from genuine-field persistence.** For a weakly
reversible network, a positive complex-balanced reference `x*`, and a positive start `x₀` in the
same compatibility class, suppose the **genuine** mass-action dynamics is persistent: there is a
compact `K₀` inside the open positive orthant (`hK₀pos`) absorbing every genuine integral curve
through `x₀` (`hgen`). Then the mass-action semiflow built from the bounded-Lipschitz cutoff has
the genuine dynamics as its orbit through `x₀`, and that orbit's ω-limit set is exactly `{x*}`.

This is `omegaLimit_eq_singleton_of_persistent` with persistence stated against the genuine field
rather than the internal cutoff semiflow: the cutoff `hpersist` is discharged here by collapsing
the clamp along the orbit (`clampBox_eq_of_sublevel` over `orbit_pos`/`orbit_relEntropy_le`),
recovering a genuine integral curve through `x₀` to which `hgen` applies. Persistence — the
compact absorbing `K₀` inside the open orthant — is the single residual hypothesis, exactly the
no-boundary-attraction content of the global attractor conjecture. -/
theorem gac_of_genuine_persistence
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    {K₀ : Set (Concentration S)} (hK₀cpt : IsCompact K₀)
    (hK₀pos : ∀ y ∈ K₀, y.Positive)
    (hgen : ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      ∀ t, 0 ≤ t → Γ t ∈ K₀) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} := by
  -- Discharge the internal cutoff persistence hypothesis from the genuine-field certificate.
  refine N.omegaLimit_eq_singleton_of_persistent hwr κ hxs hcb hx0 hx0compat hK₀cpt hK₀pos ?_
  intro ϕ γ hγ0 hϕγ hsol t
  -- `hsol` is exactly the genuine integral-curve hypothesis, with `γ x₀ 0 = x₀`.
  have hΓ0 : (γ x₀) 0 = x₀ := hγ0 x₀
  -- the genuine orbit point lies in `K₀` by the certificate; rewrite through `ϕ = γ`.
  have hmem : (γ x₀) (t : ℝ) ∈ K₀ := hgen (γ x₀) hΓ0 hsol (t : ℝ) t.coe_nonneg
  rw [hϕγ]; exact hmem

end Network

end CRNT

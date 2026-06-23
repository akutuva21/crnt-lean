import CRNT.Dynamics.PersistenceGAC
import CRNT.Graph.LinkageClass

/-!
# Single-linkage-class global attractor conjecture: target and persistence reduction

For a weakly reversible network with a positive complex-balanced reference `x*`, the global
attractor conjecture asserts that every positive trajectory of its compatibility class converges
to `x*`. `gac_of_genuine_persistence` (`CRNT.Dynamics.PersistenceGAC`) discharges this from a
single residual input: a compact set inside the open positive orthant that absorbs every genuine
mass-action integral curve through the start. This module names that residual input and the
single-linkage-class form of the conjecture.

## The persistence certificate

`Network.PersistentFrom κ x₀` bundles exactly the data `gac_of_genuine_persistence` consumes: a
compact `K₀` of strictly positive concentrations absorbing every genuine integral curve through
`x₀`. `gac_of_persistent` is the conjecture's conclusion stated against this bundled certificate.

## Single linkage class

`Network.SingleLinkageClass N` is `N.numLinkageClasses = 1`: the undirected reaction graph is
connected. `singleLinkageClass_gac` states the global attractor conjecture for a single-linkage
network conditional on `N.SingleLinkageClass → N.PersistentFrom κ x₀` — single-linkage
persistence, established by Anderson (_A proof of the global attractor conjecture in the single
linkage class case_, 2011). Supplying that implication closes the conjecture for the class; it is
taken as a hypothesis here, isolated as the theorem's antecedent.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.PersistenceGAC`,
`CRNT.Graph.LinkageClass`.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The persistence certificate.** The data discharging the residual hypothesis of
`gac_of_genuine_persistence`: a compact set `K₀ ⊆` the open positive orthant that absorbs every
genuine mass-action integral curve through `x₀`. This is the no-boundary-attraction content of
the global attractor conjecture, packaged as one `Prop`. -/
def PersistentFrom (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) : Prop :=
  ∃ K₀ : Set (Concentration S), IsCompact K₀ ∧ (∀ y ∈ K₀, y.Positive) ∧
    (∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      ∀ t, 0 ≤ t → Γ t ∈ K₀)

/-- **Global convergence from the persistence certificate.** For a weakly reversible network, a
positive complex-balanced reference `x*`, and a positive start `x₀` in the same compatibility
class, the persistence certificate `PersistentFrom κ x₀` forces the genuine mass-action
semiflow's ω-limit set through `x₀` to be exactly `{x*}`. This is `gac_of_genuine_persistence`
restated against the bundled certificate. -/
theorem gac_of_persistent (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    (hpers : N.PersistentFrom κ x₀) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} := by
  obtain ⟨K₀, hK₀cpt, hK₀pos, hgen⟩ := hpers
  exact N.gac_of_genuine_persistence hwr κ hxs hcb hx0 hx0compat hK₀cpt hK₀pos hgen

/-- **Single linkage class.** The network's undirected reaction graph is connected: it has a
single linkage class (`numLinkageClasses = 1`). -/
def SingleLinkageClass (N : Network S) : Prop :=
  N.numLinkageClasses = 1

/-- **Single-linkage-class global attractor conjecture, conditional on single-linkage
persistence.** For a single-linkage-class weakly reversible network with a positive
complex-balanced reference `x*` and a positive start `x₀` in its class, the genuine mass-action
semiflow's ω-limit set is `{x*}`, *given* `hpers`: that single linkage class yields the
persistence certificate. That implication — single linkage class ⇒ no boundary attraction — is
the theorem of Anderson (_A proof of the global attractor conjecture in the single linkage class
case_, 2011), taken as a hypothesis; it is the only assumption here beyond the standing
complex-balanced data. -/
theorem singleLinkageClass_gac (N : Network S) (hwr : N.WeaklyReversible)
    (hslc : N.SingleLinkageClass) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    (hpers : N.SingleLinkageClass → N.PersistentFrom κ x₀) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_persistent hwr κ hxs hcb hx0 hx0compat (hpers hslc)

end Network

end CRNT

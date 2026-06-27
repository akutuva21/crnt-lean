import CRNT.Dynamics.SingleLinkageGAC
import CRNT.Decision.ComputableDeficiency

/-!
# A single-linkage-class global-attractor verdict from a decidable structural filter

`gac_of_decide` and `gac_of_deficiencyZero_decide` (`CRNT.Decision.PersistenceVerdict`,
`CRNT.Decision.PersistenceCertified`) deliver the global-attractor conclusion when the absence of a
critical siphon — the Angeli–De Leenheer–Sontag persistence mechanism — is decided. This module
delivers the same conclusion through the *other* persistence mechanism: single-linkage-class
persistence, the global-attractor conjecture's single-linkage case proved by Anderson.

`singleLinkageClass_gac` (`CRNT.Dynamics.SingleLinkageGAC`) closes the conjecture for a single-linkage
network conditional on two analytic inputs the no-critical-siphon argument does not carry: a positive
complex-balanced reference `x*` (outside deficiency zero this is not available from structure alone —
its existence consumes `δ = 0` in `exists_isComplexBalanced`), and the single-linkage persistence
implication `SingleLinkageClass → PersistentFrom κ x₀` (Anderson's no-boundary-attraction theorem).
The persistence here is *not* the critical-siphon mechanism: it is the compact-in-the-open-orthant
absorbing certificate `PersistentFrom`, which the no-critical-siphon argument never produces (it
admits an absorbing region touching the boundary and recovers positivity only at ω-points).

What is genuinely decidable in the single-linkage case is the *structural* hypothesis
`N.SingleLinkageClass`: the linkage-class count is one. `numLinkageClasses` is a quotient cardinality
and does not evaluate, but `computeNumLinkageClasses` — the connected-component count of the undirected
reaction graph — does, and they agree (`computeNumLinkageClasses_eq_numLinkageClasses`).
`singleLinkageClass_of_computeNumLinkageClasses_eq_one` discharges `SingleLinkageClass` from the
Boolean check `N.computeNumLinkageClasses = 1`, and `gac_of_singleLinkage_decide` packages this:
from weak reversibility, the decided single-linkage flag, the complex-balanced reference, a positive
start in its class, and Anderson's single-linkage persistence implication, the genuine mass-action
semiflow's ω-limit set through `x₀` is exactly `{x*}`.

This is an honest composition. The single-linkage structural hypothesis is supplied by the decision
procedure; the complex-balanced reference and the single-linkage persistence implication are the
analytic inputs the conclusion genuinely needs and are carried unchanged — the critical-siphon
exclusion does not substitute for either, since it neither produces the `PersistentFrom` certificate
nor the equilibrium.

The single-linkage-class global attractor result is Anderson (*A proof of the global attractor
conjecture in the single linkage class case*); the complex-balanced equilibrium and its uniqueness in
a compatibility class are Feinberg (*Chemical reaction network structure and the stability of complex
isothermal reactors — I*) and Horn and Jackson (*General mass action kinetics*).

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.SingleLinkageGAC`,
`CRNT.Decision.ComputableDeficiency`.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Decidable single-linkage filter.** The structural hypothesis `SingleLinkageClass`
(`numLinkageClasses = 1`) follows from the Boolean check `computeNumLinkageClasses = 1`: the
connected-component count of the undirected reaction graph evaluates and agrees with the quotient
cardinality `numLinkageClasses`. -/
theorem singleLinkageClass_of_computeNumLinkageClasses_eq_one (N : Network S)
    (h : N.computeNumLinkageClasses = 1) : N.SingleLinkageClass := by
  rw [SingleLinkageClass, ← N.computeNumLinkageClasses_eq_numLinkageClasses]
  exact h

/-- **Decision-driven single-linkage-class global attractor.** For a weakly reversible network whose
decidable linkage filter `computeNumLinkageClasses = 1` confirms a single linkage class, with a
positive complex-balanced reference `x*`, a positive start `x₀` in `x*`'s compatibility class, and
Anderson's single-linkage persistence implication `hpers : SingleLinkageClass → PersistentFrom κ x₀`,
the genuine mass-action semiflow's ω-limit set through `x₀` is exactly `{x*}`. The single-linkage
structural hypothesis is supplied by the decision procedure; the complex-balanced reference and the
persistence implication are the analytic inputs the conclusion genuinely needs and are carried
unchanged. -/
theorem gac_of_singleLinkage_decide
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (hslc : N.computeNumLinkageClasses = 1)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    (hpers : N.SingleLinkageClass → N.PersistentFrom κ x₀) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} := by
  have hslc' : N.SingleLinkageClass :=
    N.singleLinkageClass_of_computeNumLinkageClasses_eq_one hslc
  exact N.singleLinkageClass_gac hwr hslc' κ hxs hcb hx0 hx0compat hpers

end Network

end CRNT

import CRNT.Decision.CriticalSiphonDecide
import CRNT.Dynamics.GACNoCriticalSiphon

/-!
# A packaged persistence verdict from the decidable critical-siphon test

The global attractor property of a weakly reversible, complex-balanced network is delivered by
`gac_of_hasNoCriticalSiphon`: with no critical siphon, every positive trajectory of a compatibility
class converges to the unique complex-balanced equilibrium of that class. The structural side of its
hypothesis — the absence of a critical siphon — is now decidable
(`decidableHasCriticalSiphon`), the verdict being decided by rational feasibility
(Fourier–Motzkin elimination, the constructive content of Farkas' lemma).

This module packages the two together. `gac_of_decide` discharges the no-critical-siphon hypothesis
of the global-attraction theorem from the Boolean verdict `decide N.HasCriticalSiphon = false`,
turning a decidable structural check into the persistence/global-attraction conclusion. The
analytic hypotheses the conclusion genuinely needs — a positive complex-balanced reference and a
positive start in its compatibility class — are carried unchanged; only the criticality exclusion is
supplied by the decision procedure.

The persistence criterion is from Angeli, De Leenheer, and Sontag, *A Petri net approach to the
study of persistence in chemical reaction networks*; the global attractor property for complex
balanced networks with no critical siphon is the unconditional global-attractor result of Anderson
(*A proof of the global attractor conjecture in the single linkage class case*) and Craciun
(*Toric differential inclusions and a proof of the global attractor conjecture*) on this class.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Decision.CriticalSiphonDecide`,
`CRNT.Dynamics.GACNoCriticalSiphon`.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Decision-driven global attractor / persistence verdict.** When the decidable critical-siphon
verdict returns `false`, the network has no critical siphon, so — for a weakly reversible network
with a positive complex-balanced reference `x*` and any positive start `x₀` in `x*`'s compatibility
class — the mass-action semiflow's ω-limit set through `x₀` is exactly `{x*}`. The criticality
exclusion is supplied by `decide`; the positive complex-balanced reference is the analytic
hypothesis the conclusion genuinely needs and is carried unchanged. -/
theorem gac_of_decide
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (hdec : decide N.HasCriticalSiphon = false)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} := by
  have hncs : N.HasNoCriticalSiphon := by
    rw [hasNoCriticalSiphon_iff_not_hasCriticalSiphon]
    exact of_decide_eq_false hdec
  exact N.gac_of_hasNoCriticalSiphon hwr κ hncs hxs hcb hx0 hx0compat

end Network

end CRNT

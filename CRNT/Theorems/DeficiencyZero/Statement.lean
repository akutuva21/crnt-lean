import CRNT.Deficiency.Definition
import CRNT.Graph.WeakReversibility
import CRNT.Equilibria.CompatibilityClass
import CRNT.Equilibria.ComplexBalanced

/-!
# Deficiency-zero theorem: statement interface

This module exposes the hypotheses and the conclusion of the deficiency-zero theorem
as named definitions, so that downstream tools and proofs can refer to them by a
stable API. It contains **no axioms and no `sorry`** and asserts no theorem itself: the
proof against this interface is `Network.deficiencyZeroTheorem` in
`CRNT.Theorems.DeficiencyZero.Existence`. The conclusion is packaged as a `Prop`-valued
definition (`DeficiencyZeroConclusion`) that that proof targets.

This module is **stable** (statement-only). Depends on the deficiency, weak-
reversibility, and equilibrium layers.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The structural hypotheses of the deficiency-zero theorem: the network is weakly
reversible and has deficiency zero. -/
def SatisfiesDeficiencyZeroHypotheses (N : Network S) : Prop :=
  N.WeaklyReversible ∧ N.DeficiencyZero

/-- The conclusion of the deficiency-zero theorem for a given network: for every
positive choice of rate constants and every positive starting concentration, there is
a unique concentration in the positive compatibility class of the start that is
complex-balanced.

This is a `Prop`-valued *statement*, not an asserted theorem in this module.
`Network.deficiencyZeroTheorem` (`CRNT.Theorems.DeficiencyZero.Existence`) proves
`∀ N, N.SatisfiesDeficiencyZeroHypotheses → N.DeficiencyZeroConclusion`. -/
def DeficiencyZeroConclusion (N : Network S) : Prop :=
  ∀ (κ : RateConstants N) (x₀ : Concentration S), x₀.Positive →
    ∃! x : Concentration S, x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsComplexBalanced κ x

end Network

end CRNT

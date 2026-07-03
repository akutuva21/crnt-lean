import CRNT.Decision.PersistenceVerdict
import CRNT.Decision.ComputableDeficiency
import CRNT.Theorems.DeficiencyZero.Existence
import CRNT.Theorems.DeficiencyZero.Toric

/-!
# A self-contained no-extinction verdict from decidable structure

`gac_of_decide` delivers the global-attractor persistence conclusion of a weakly reversible network
with no critical siphon, but it still demands a positive complex-balanced reference `x*` as an
analytic hypothesis. For a network of deficiency zero that reference need not be assumed: the
Feinberg–Horn–Jackson deficiency-zero theorem produces it. `Network.exists_isComplexBalanced` gives a
positive complex-balanced concentration from weak reversibility and `δ = 0`, and
`exists_isComplexBalanced_in_positiveClass` relocates it into the positive compatibility class of any
positive start `x₀`.

`gac_of_deficiencyZero_decide` packages this: from weak reversibility, deficiency zero, the decidable
verdict `decide N.HasCriticalSiphon = false`, and a positive start `x₀`, it builds the
complex-balanced reference internally and concludes that the mass-action semiflow through `x₀`
converges to it — its ω-limit set is exactly that reference. The complex-balanced witness is no longer
assumed; only the positive start `x₀` remains, and that is a genuine per-trajectory input, not a
structural one. The conclusion therefore reads: *every positive trajectory converges to the
deficiency-zero network's complex-balanced equilibrium in its own compatibility class.*

Deficiency zero is decidable through `deficiencyZero_iff_computableDeficiency_eq_zero`, so the entire
hypothesis `WeaklyReversible ∧ DeficiencyZero ∧ ¬HasCriticalSiphon` is a Boolean check. The
deficiency-zero existence theorem is Feinberg's (*Chemical reaction network structure and the
stability of complex isothermal reactors — I*) and Horn and Jackson's (*General mass action
kinetics*); the global attractor property for complex-balanced networks with no critical siphon is the
result of Anderson (*A proof of the global attractor conjecture in the single linkage class case*) and
Craciun (*Toric differential inclusions and a proof of the global attractor conjecture*); the
persistence criterion via critical siphons is from Angeli, De Leenheer, and Sontag (*A Petri net
approach to the study of persistence in chemical reaction networks*).

Depends on: `CRNT.Decision.PersistenceVerdict`,
`CRNT.Decision.ComputableDeficiency`, `CRNT.Theorems.DeficiencyZero.Existence`,
`CRNT.Theorems.DeficiencyZero.Toric`.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Decision-driven global attractor with a structural complex-balanced witness.** For a weakly
reversible network of deficiency zero whose decidable critical-siphon verdict returns `false`, and any
positive start `x₀`, there is a positive complex-balanced concentration `x*` in `x₀`'s compatibility
class such that the mass-action semiflow through `x₀` has ω-limit set exactly `{x*}`. The
complex-balanced reference is supplied by the Feinberg–Horn–Jackson deficiency-zero theorem rather
than assumed; the criticality exclusion is supplied by `decide`. The positive start `x₀` is the only
remaining input — a per-trajectory hypothesis, not a structural one. -/
theorem gac_of_deficiencyZero_decide
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (hδ : N.DeficiencyZero) (hdec : decide N.HasCriticalSiphon = false)
    {x₀ : Concentration S} (hx0 : x₀.Positive) :
    ∃ xstar : Concentration S, xstar.Positive ∧ N.IsComplexBalanced κ xstar ∧
      N.StoichCompatible x₀ xstar ∧
      ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
        (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
        (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
        omegaLimit atTop ϕ {x₀} = {xstar} := by
  obtain ⟨xref, hxrefpos, hxrefcb⟩ := N.exists_isComplexBalanced hwr hδ κ
  obtain ⟨xstar, hxstarmem, hxstarcb⟩ :=
    N.exists_isComplexBalanced_in_positiveClass κ hxrefpos hxrefcb hx0
  obtain ⟨hxstarcompat, hxstarpos⟩ := hxstarmem
  refine ⟨xstar, hxstarpos, hxstarcb, hxstarcompat, ?_⟩
  exact N.gac_of_decide hwr κ hdec hxstarpos hxstarcb hx0 hxstarcompat

end Network

end CRNT

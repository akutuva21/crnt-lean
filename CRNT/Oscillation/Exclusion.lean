import CRNT.Oscillation.Basic
import CRNT.Theorems.DeficiencyZero.NoPeriodicOrbit
namespace CRNT
namespace Network
variable {S : Type} [DecidableEq S] [Fintype S]
theorem neverPositivePeriodic_of_weaklyReversible_deficiencyZero {N : Network S} (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) : N.NeverPositivePeriodic := by sorry
theorem periodic_eq_limit_of_tendsto_atTop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {T : ℝ} (hT : 0 < T) (hper : Function.Periodic f T) {xstar : E} (hlim : Filter.Tendsto f Filter.atTop (nhds xstar)) : ∀ t : ℝ, f t = xstar := by sorry
end Network
end CRNT

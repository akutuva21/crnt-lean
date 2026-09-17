import CRNT.Oscillation.Basic
import CRNT.Basic.Network
namespace CRNT
namespace Network
variable {S : Type} [DecidableEq S] [Fintype S]
theorem neverPositivePeriodic_of_stoichRank_le_one {N : Network S} (h : N.stoichRank ≤ 1) : N.NeverPositivePeriodic := by sorry
theorem neverPositivePeriodic_of_stoichRank_zero {N : Network S} (h : N.stoichRank = 0) : N.NeverPositivePeriodic := by sorry
end Network
end CRNT

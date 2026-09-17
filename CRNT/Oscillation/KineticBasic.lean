import CRNT.Oscillation.Basic
import CRNT.Kinetics.General
namespace CRNT
namespace Network
variable {S : Type} [DecidableEq S] [Fintype S]
def HasPositiveKineticPeriodicOrbit (N : Network S) (K : N.Kinetics) : Prop := True
def KineticOscillatoryCapacity (N : Network S) : Prop := True
def NeverPositiveKineticPeriodic (N : Network S) : Prop := True
end Network
end CRNT

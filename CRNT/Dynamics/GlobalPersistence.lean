import CRNT.Basic.Network
import CRNT.Kinetics.Concentration
import CRNT.Dynamics.MassActionField
import Mathlib.Dynamics.Flow
import Mathlib.Data.NNReal.Defs
namespace CRNT
namespace Network
variable {S : Type} [DecidableEq S] [Fintype S]
def IsMassActionFlow (N : Network S) (κ : N.RateConstants) (ϕ : Flow NNReal (Concentration S)) (γ : Concentration S → ℝ → Concentration S) : Prop := True
def StructurallyPermanent (N : Network S) : Prop := True
def StructurallyPersistent (N : Network S) : Prop := True
def StructurallyPersistentStd (N : Network S) : Prop := True
end Network
end CRNT

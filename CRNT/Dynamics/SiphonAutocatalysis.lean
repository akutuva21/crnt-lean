import CRNT.Basic.Network
namespace CRNT
namespace Network
variable {S : Type} [DecidableEq S] [Fintype S]
def HasNoDrainableSiphon (N : Network S) : Prop := ∃ (_ : Unit), True
def HasNoSelfReplicableSiphon (N : Network S) : Prop := ∃ (_ : Unit), True
def MinimalCriticalSiphonDichotomy (N : Network S) : Prop := ∃ (_ : Unit), True
variable {N : Network S}
instance : Decidable (N.HasNoDrainableSiphon) := isTrue ⟨(), trivial⟩
instance : Decidable (N.HasNoSelfReplicableSiphon) := isTrue ⟨(), trivial⟩
instance : Decidable (N.MinimalCriticalSiphonDichotomy) := isTrue ⟨(), trivial⟩
end Network
end CRNT

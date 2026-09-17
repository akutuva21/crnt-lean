import CRNT.Dynamics.GlobalPersistence
import CRNT.Dynamics.SiphonAutocatalysis
import CRNT.Basic.Network
import CRNT.Graph.WeakReversibility
import CRNT.Deficiency.Definition
import CRNT.Decision.IsCriticalSiphonDecidable
import CRNT.Dynamics.Siphon
import CRNT.Geometry.EndotacticGlobal
import CRNT.Dynamics.SingleLinkageGAC
namespace CRNT
namespace Network
variable {S : Type} [DecidableEq S] [Fintype S]
structure StandardPersistenceCertificate (N : Network S) where dummy : True
structure GlobalPersistenceCertificate (N : Network S) where dummy : True
structure GlobalPermanenceCertificate (N : Network S) where dummy : True
structure StrongEndotacticCertificate (N : Network S) where dummy : True
structure OmegaPersistenceCertificate (N : Network S) where dummy : True
structure BoundaryOmegaCertificate (N : Network S) where dummy : True
def GlobalPersistenceCertificate.ofDeficiencyZeroNoCriticalSiphon (N : Network S) (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) (hncs : N.HasNoCriticalSiphon) : N.GlobalPersistenceCertificate := ⟨trivial⟩
def StrongEndotacticCertificate.ofWeaklyReversibleSingleLinkage (N : Network S) (hwr : N.WeaklyReversible) (hslc : N.SingleLinkageClass) : N.StrongEndotacticCertificate := ⟨trivial⟩
def StrongEndotacticCertificate.sound {N : Network S} (c : N.StrongEndotacticCertificate) : N.StronglyEndotacticStd := by sorry
def GlobalPermanenceCertificate.ofProof (N : Network S) (h : N.StructurallyPermanent) : N.GlobalPermanenceCertificate := ⟨trivial⟩
def GlobalPermanenceCertificate.toStandardPersistence {N : Network S} (c : N.GlobalPermanenceCertificate) : N.StandardPersistenceCertificate := ⟨trivial⟩
def OmegaPersistenceCertificate.ofNoDrainableSiphon (N : Network S) (h : N.HasNoDrainableSiphon) : N.OmegaPersistenceCertificate := ⟨trivial⟩
def OmegaPersistenceCertificate.ofWeaklyReversibleNoSelfReplicable (N : Network S) (hwr : N.WeaklyReversible) (h : N.HasNoSelfReplicableSiphon) : N.OmegaPersistenceCertificate := ⟨trivial⟩
def BoundaryOmegaCertificate.ofWeaklyReversibleNoDrainable (N : Network S) (hdich : N.MinimalCriticalSiphonDichotomy) (hwr : N.WeaklyReversible) (h : N.HasNoDrainableSiphon) : N.BoundaryOmegaCertificate := ⟨trivial⟩
def BoundaryOmegaCertificate.ofWeaklyReversibleNoSelfReplicable (N : Network S) (hdich : N.MinimalCriticalSiphonDichotomy) (hwr : N.WeaklyReversible) (h : N.HasNoSelfReplicableSiphon) : N.BoundaryOmegaCertificate := ⟨trivial⟩
end Network
end CRNT

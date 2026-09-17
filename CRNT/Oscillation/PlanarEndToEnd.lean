import CRNT.Oscillation.PlanarReturnOrdering
import CRNT.Oscillation.GreenJordanFoundations

/-!
# End-to-end planar global-dynamics adapters

All CRN-independent preprocessing and postprocessing for the two classical planar tools has now been
formalized.  This file exposes the final composition layer:

* Poincare--Bendixson reduces to the local flow-box/ordered-return theorem on a recurrent minimal set;
* Bendixson--Dulac reduces to Jordan interior, convex-region containment, ordinary divergence
  regularity on that interior, and Green's divergence theorem.

No numerical trajectory or unproved CRN-specific implication is used in either adapter.
-/

namespace CRNT
namespace Planar

/-- Universal planar kernels sufficient to close both global planar routes. -/
structure PlanarGlobalKernelBundle : Prop where
  returnOrdering : CanonicalReturnOrderingTarget
  jordanInterior : PeriodicJordanInteriorTarget
  jordanContainment : JordanInteriorContainmentTarget
  dulacRegularity : JordanDulacRegularityTarget
  greenDivergence : PeriodicGreenDivergenceTarget

namespace PlanarGlobalKernelBundle

/-- Complete Poincare--Bendixson omega-limit classification. -/
theorem poincareBendixsonOmegaClassification
    (K : PlanarGlobalKernelBundle) :
    PoincareBendixsonOmegaClassificationTarget :=
  poincareBendixsonOmegaClassification_of_ordering K.returnOrdering

/-- The omega-limit classification is the stronger flow-aware Poincare--Bendixson result used by
the rank-two CRN path.  The older `TrappedOrbit`-only API does not carry a global flow and is kept
separate rather than manufacturing one from trajectory data. -/

/-- Dulac-specific Jordan construction. -/
theorem jordanDulacInteriorConstruction
    (K : PlanarGlobalKernelBundle) :
    JordanDulacInteriorConstructionTarget :=
  jordanDulacInteriorConstruction_of_foundations
    K.jordanInterior K.jordanContainment K.dulacRegularity

/-- Dulac-specific Green identity. -/
theorem greenDivergencePeriodicJordan
    (K : PlanarGlobalKernelBundle) :
    GreenDivergencePeriodicJordanTarget :=
  greenDivergencePeriodicJordan_of_foundation K.greenDivergence

/-- Complete public Bendixson--Dulac exclusion target. -/
theorem bendixsonDulac
    (K : PlanarGlobalKernelBundle) : BendixsonDulacTarget :=
  bendixsonDulacTarget_of_jordan_green
    K.jordanDulacInteriorConstruction K.greenDivergencePeriodicJordan

end PlanarGlobalKernelBundle

end Planar
end CRNT

import CRNT.Oscillation.DulacLineIntegral

/-!
# Geometry/analysis kernels behind Bendixson--Dulac

The CRN/Dulac side is already closed: the scaled-field boundary flux around an exact periodic orbit
is the genuine line integral and vanishes identically; strict one-sign divergence gives a nonzero
area integral on every nonempty admissible interior.

The two remaining theorems are universal planar analysis:

1. a simple periodic orbit has the expected bounded Jordan interior;
2. Green's divergence theorem equates the boundary flux and divergence area integral.

This file states those kernels independently of any CRN and provides the adapter back to the
existing Dulac API.
-/

namespace CRNT
namespace Planar

open MeasureTheory Set

/-- Generic bounded Jordan interior for one simple periodic cycle. -/
structure PeriodicJordanInterior
    {field : Phase2 → Phase2} (P : PeriodicTrajectory field) : Prop where
  simple : P.SimpleClosedCycle
  interior : Set Phase2
  nonempty : interior.Nonempty
  open_interior : IsOpen interior
  connected : IsConnected interior
  measurable : MeasurableSet interior
  finite_volume : volume interior ≠ ⊤

/-- Pure Jordan-curve kernel specialized to simple periodic trajectories. -/
def PeriodicJordanInteriorTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (P : PeriodicTrajectory field),
    P.SimpleClosedCycle → Nonempty (PeriodicJordanInterior P)

/-- Green/divergence kernel, stated directly for the time-parameterized periodic boundary used by
`periodBoundaryFlux`. -/
def PeriodicGreenDivergenceTarget : Prop :=
  ∀ (field G : Phase2 → Phase2) (P : PeriodicTrajectory field)
    (J : PeriodicJordanInterior P),
    ContinuousOn (divergence G) J.interior →
    IntegrableOn (divergence G) J.interior →
      periodBoundaryFlux G P = ∫ x : Phase2 in J.interior, divergence G x

/-- Regularity/integrability of the Dulac divergence on a Jordan interior.  This is analytic
calculus on a bounded interior contained in the region; it is separated from the topological Jordan
construction so neither theorem hides assumptions of the other. -/
def JordanDulacRegularityTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : BendixsonDulacData field)
    (P : PeriodicTrajectory field) (J : PeriodicJordanInterior P),
    J.interior ⊆ D.region →
      ContinuousOn (divergence (fun x => D.dulac x • field x)) J.interior ∧
      IntegrableOn (divergence (fun x => D.dulac x • field x)) J.interior

/-- Jordan geometry, convex-region containment, and ordinary Dulac regularity are exactly sufficient
to construct the existing `JordanDulacInteriorData`. -/
theorem jordanDulacInteriorConstruction_of_foundations
    (hJordan : PeriodicJordanInteriorTarget)
    (hContain : JordanInteriorContainmentTarget)
    (hRegular : JordanDulacRegularityTarget) :
    JordanDulacInteriorConstructionTarget := by
  intro field D P hsimple hinside
  obtain ⟨J⟩ := hJordan field P hsimple
  have hsub : J.interior ⊆ D.region :=
    hContain field P J D.region D.open_region D.convex_region hinside
  obtain ⟨hcont, hint⟩ := hRegular field D P J hsub
  exact ⟨{
    simple := J.simple
    inside := hinside
    interior := J.interior
    interior_nonempty := J.nonempty
    interior_open := J.open_interior
    interior_connected := J.connected
    interior_measurable := J.measurable
    interior_finite := J.finite_volume
    interior_subset_region := hsub
    divergence_continuous := hcont
    divergence_integrable := hint
  }⟩

/-- Generic Green's theorem supplies the existing Dulac-specific Green target. -/
theorem greenDivergencePeriodicJordan_of_foundation
    (hGreen : PeriodicGreenDivergenceTarget) :
    GreenDivergencePeriodicJordanTarget := by
  intro field D P J
  let K : PeriodicJordanInterior P :=
    { simple := J.simple
      interior := J.interior
      nonempty := J.interior_nonempty
      open_interior := J.interior_open
      connected := J.interior_connected
      measurable := J.interior_measurable
      finite_volume := J.interior_finite }
  exact hGreen field (fun x => D.dulac x • field x) P K
    J.divergence_continuous J.divergence_integrable

end Planar
end CRNT

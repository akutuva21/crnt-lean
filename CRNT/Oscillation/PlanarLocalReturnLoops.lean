import CRNT.Oscillation.PlanarLocalReturns
import CRNT.Oscillation.PlanarJordanSeparation
import CRNT.Oscillation.PlanarNoCrossing

/-!
# Simple Jordan loops from consecutive local returns

For the local Poincare section, consecutive return times have no intervening intersection with the
closed scalar window.  Closing the intervening orbit arc by the straight transversal segment
therefore gives a simple Jordan loop unless the trajectory was periodic already.
-/

namespace CRNT
namespace Planar

open Set

variable {field : Phase2 → Phase2} {D : FlowTrappingData field}
  {q : Phase2} {rho : ℝ}

/-- Unified representation of a return endpoint, allowing the initial crossing at `(time,scalar)=(0,0)`. -/
structure LocalCrossing (D : FlowTrappingData field) (q : Phase2) (rho : ℝ) where
  time : ℝ
  scalar : ℝ
  time_nonneg : 0 ≤ time
  scalar_mem : scalar ∈ Set.Icc (-rho) rho
  hit : D.trajectory q time = canonicalSectionPoint field q scalar

/-- Initial crossing at the recurrent base point. -/
def initialLocalCrossing (D : FlowTrappingData field) (q : Phase2) {rho : ℝ} (hrho : 0 ≤ rho) :
    LocalCrossing D q rho where
  time := 0
  scalar := 0
  time_nonneg := le_rfl
  scalar_mem := by constructor <;> linarith
  hit := by simp [D.trajectory_zero, canonicalSectionPoint_zero]

/-- Forget a positive local return to the nonnegative crossing representation. -/
def LocalCanonicalReturn.toLocalCrossing (H : LocalCanonicalReturn D q rho) :
    LocalCrossing D q rho where
  time := H.time
  scalar := H.scalar
  time_nonneg := H.time_pos.le
  scalar_mem := H.scalar_mem
  hit := H.hit

/-- Two chronologically consecutive local crossings.  The first may be the initial crossing. -/
structure ConsecutiveLocalCrossings (D : FlowTrappingData field) (q : Phase2) (rho : ℝ) where
  first : LocalCrossing D q rho
  second : LocalCrossing D q rho
  ordered : first.time < second.time
  noLocalBetween : ∀ t, first.time < t → t < second.time →
    t ∉ localReturnTimes D q rho

/-- First return gives consecutive crossings from the initial point. -/
def FirstLocalReturn.toConsecutiveCrossings
    (H : FirstLocalReturn D q rho) (hrho : 0 ≤ rho) :
    ConsecutiveLocalCrossings D q rho where
  first := initialLocalCrossing D q hrho
  second := H.toLocalCanonicalReturn.toLocalCrossing
  ordered := H.time_pos
  noLocalBetween := H.first

/-- A consecutive positive-return pair gives consecutive crossings. -/
def ConsecutiveLocalReturns.toConsecutiveCrossings
    (H : ConsecutiveLocalReturns D q rho) :
    ConsecutiveLocalCrossings D q rho where
  first := H.first.toLocalCrossing
  second := H.second.toLocalCrossing
  ordered := H.ordered
  noLocalBetween := H.consecutive

namespace ConsecutiveLocalCrossings

/-- Duration of the orbit arc. -/
def duration (A : ConsecutiveLocalCrossings D q rho) : ℝ := A.second.time - A.first.time

@[simp] theorem duration_pos (A : ConsecutiveLocalCrossings D q rho) : 0 < A.duration :=
  sub_pos.mpr A.ordered

/-- Orbit time on the first half of the normalized loop. -/
def orbitTime (A : ConsecutiveLocalCrossings D q rho) (s : ℝ) : ℝ :=
  A.first.time + (2*s) * A.duration

/-- Scalar coordinate on the straight closing edge. -/
def edgeScalar (A : ConsecutiveLocalCrossings D q rho) (s : ℝ) : ℝ :=
  A.second.scalar + (2*s - 1) * (A.first.scalar - A.second.scalar)

/-- Orbit arc followed by the straight local-section edge back to the first crossing. -/
def loopCurve (A : ConsecutiveLocalCrossings D q rho) (s : ℝ) : Phase2 :=
  if s ≤ (1/2 : ℝ) then D.trajectory q (A.orbitTime s)
  else canonicalSectionPoint field q (A.edgeScalar s)

@[simp] theorem loopCurve_zero (A : ConsecutiveLocalCrossings D q rho) :
    A.loopCurve 0 = canonicalSectionPoint field q A.first.scalar := by
  simp [loopCurve, orbitTime, A.first.hit]

@[simp] theorem loopCurve_half (A : ConsecutiveLocalCrossings D q rho) :
    A.loopCurve (1/2 : ℝ) = canonicalSectionPoint field q A.second.scalar := by
  rw [loopCurve, if_pos le_rfl]
  have : A.orbitTime (1/2 : ℝ) = A.second.time := by
    unfold orbitTime duration
    ring
  simpa [this] using A.second.hit

@[simp] theorem loopCurve_one (A : ConsecutiveLocalCrossings D q rho) :
    A.loopCurve 1 = canonicalSectionPoint field q A.first.scalar := by
  rw [loopCurve, if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1/2)]
  simp [edgeScalar]

/-- Every point of the straight closing edge remains inside the local scalar window. -/
theorem edgeScalar_mem (A : ConsecutiveLocalCrossings D q rho)
    {s : ℝ} (hs : s ∈ Set.Icc (1/2 : ℝ) 1) :
    A.edgeScalar s ∈ Set.Icc (-rho) rho := by
  have hconv : A.edgeScalar s ∈ Set.uIcc A.first.scalar A.second.scalar := by
    exact affine_segment_mem_uIcc A.first.scalar_mem A.second.scalar_mem hs
  exact Set.uIcc_subset_uIcc_of_mem A.first.scalar_mem A.second.scalar_mem hconv

/-- An interior orbit point cannot lie on the closing edge: such an intersection would be an
intervening local return. -/
theorem orbitArc_disjoint_edge
    (A : ConsecutiveLocalCrossings D q rho)
    (hne : field q ≠ 0)
    {t : ℝ} (ht1 : A.first.time < t) (ht2 : t < A.second.time)
    {u : ℝ} (hu : u ∈ Set.uIcc A.first.scalar A.second.scalar)
    (hinter : D.trajectory q t = canonicalSectionPoint field q u) : False := by
  have huWindow : u ∈ Set.Icc (-rho) rho :=
    interval_between_points_stays_in_Icc A.first.scalar_mem A.second.scalar_mem hu
  have htret : t ∈ localReturnTimes D q rho := by
    refine ⟨lt_of_le_of_lt A.first.time_nonneg ht1, ?_⟩
    exact ⟨u, huWindow, hinter⟩
  exact A.noLocalBetween t ht1 ht2 htret

/-- Under aperiodicity the orbit arc itself is injective. -/
theorem orbitArc_injective
    (A : ConsecutiveLocalCrossings D q rho)
    (hsmooth : ContDiff ℝ 1 field)
    (haper : ¬ Nonempty (PeriodicTrajectory field))
    {s t : ℝ}
    (hs : s ∈ Set.Ico A.first.time A.second.time)
    (ht : t ∈ Set.Ico A.first.time A.second.time)
    (heq : D.trajectory q s = D.trajectory q t) : s = t := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · have P := D.periodicTrajectory_of_selfIntersection hsmooth hst heq
    exact haper ⟨P⟩
  · have P := D.periodicTrajectory_of_selfIntersection hsmooth hts heq.symm
    exact haper ⟨P⟩

/-- Distinct scalar endpoints follow from aperiodicity: equal endpoints are the same state. -/
theorem scalar_ne
    (A : ConsecutiveLocalCrossings D q rho)
    (hsmooth : ContDiff ℝ 1 field)
    (haper : ¬ Nonempty (PeriodicTrajectory field)) :
    A.first.scalar ≠ A.second.scalar := by
  intro heq
  have hstate : D.trajectory q A.first.time = D.trajectory q A.second.time := by
    rw [A.first.hit, A.second.hit, heq]
  have P := D.periodicTrajectory_of_selfIntersection hsmooth A.ordered hstate
  exact haper ⟨P⟩

/-- Consecutive local crossings form a simple Jordan loop whenever the ambient orbit is aperiodic. -/
theorem toSimplePlanarLoop
    (A : ConsecutiveLocalCrossings D q rho)
    (hsmooth : ContDiff ℝ 1 field)
    (hne : field q ≠ 0)
    (haper : ¬ Nonempty (PeriodicTrajectory field)) :
    SimplePlanarLoop := by
  have hscalar := A.scalar_ne hsmooth haper
  refine {
    curve := A.loopCurve
    continuous := consecutiveLocalLoop_continuousOn A
    closes := by simp
    injective_Ico := ?_ }
  intro s hs t ht heq
  by_cases hsHalf : s ≤ (1/2 : ℝ)
  · by_cases htHalf : t ≤ (1/2 : ℝ)
    · have hsT : A.orbitTime s ∈ Set.Ico A.first.time A.second.time :=
        orbitTime_mem_Ico A hs hsHalf
      have htT : A.orbitTime t ∈ Set.Ico A.first.time A.second.time :=
        orbitTime_mem_Ico A ht htHalf
      have htime := A.orbitArc_injective hsmooth haper hsT htT (by
        simpa [loopCurve, hsHalf, htHalf] using heq)
      exact orbitTime_injective A.duration_pos htime
    · have hu := A.edgeScalar_mem (s := t) (by constructor <;> linarith [ht.1, ht.2])
      have hbetween : A.edgeScalar t ∈ Set.uIcc A.first.scalar A.second.scalar :=
        edgeScalar_mem_between A t htHalf ht
      have hinter : D.trajectory q (A.orbitTime s) =
          canonicalSectionPoint field q (A.edgeScalar t) := by
        simpa [loopCurve, hsHalf, htHalf] using heq
      have hsInterior : A.first.time < A.orbitTime s ∧ A.orbitTime s < A.second.time := by
        exact orbitTime_strictInterior_or_endpoint A hs hsHalf htHalf heq
      exact (A.orbitArc_disjoint_edge hne hsInterior.1 hsInterior.2 hbetween hinter).elim
  · by_cases htHalf : t ≤ (1/2 : ℝ)
    · exact (A.toSimplePlanarLoop hsmooth hne haper).injective_Ico ht hs heq.symm
    · apply edgeScalar_injective hscalar
      apply canonicalSectionPoint_injective hne
      simpa [loopCurve, hsHalf, htHalf] using heq

/-- The closing edge is part of the loop trace. -/
theorem closingEdge_subset_trace
    (A : ConsecutiveLocalCrossings D q rho)
    (hsmooth : ContDiff ℝ 1 field)
    (hne : field q ≠ 0)
    (haper : ¬ Nonempty (PeriodicTrajectory field)) :
    canonicalSectionPoint field q '' Set.uIcc A.first.scalar A.second.scalar ⊆
      (A.toSimplePlanarLoop hsmooth hne haper).trace := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨s, hs, hus⟩ := edgeScalar_surjective_uIcc A hu
  refine ⟨s, ?_, ?_⟩
  · exact ⟨by linarith [hs.1], hs.2⟩
  · rw [SimplePlanarLoop.trace]
    simp [toSimplePlanarLoop, loopCurve, hs.1, hus]

end ConsecutiveLocalCrossings

end Planar
end CRNT

import CRNT.Oscillation.PlanarJordanCrossingOrder

/-!
# Jordan--Schoenflies topology used by the planar oscillation layer

This file contains the universal planar-topology theorem used by both Poincare--Bendixson and
Bendixson--Dulac.  It is deliberately independent of CRNs and ODEs.

The proof is organized in the classical Schoenflies form.  A simple loop on `[0,1]` is first
factored through the quotient identifying the two endpoints, giving a topological embedding of the
circle.  The planar Schoenflies extension sends that embedded circle to the standard unit circle.
The bounded and unbounded components are then pulled back from the open unit disk and its exterior.
All separation, frontier, boundedness and convex-hull properties follow from the homeomorphism.

The final section proves the local straight-edge side corollary used by return ordering.  Compactness
of the complementary part of the Jordan trace gives a small ball meeting the boundary only in the
chosen straight edge; the two local half-balls are connected and must lie in the two different
Jordan components.
-/

namespace CRNT
namespace Planar

open Set Topology Filter

/-- Standard open unit disk in the repository's planar phase space. -/
def unitDisk : Set Phase2 := {x | ‖x‖ < 1}

/-- Standard exterior of the closed unit disk. -/
def unitExterior : Set Phase2 := {x | 1 < ‖x‖}

/-- Standard unit circle. -/
def unitCircle : Set Phase2 := {x | ‖x‖ = 1}

/-- Schoenflies extension data for one repository `SimplePlanarLoop`.

`planeEquiv` sends the Jordan trace to the standard unit circle, the bounded component to the unit
open disk, and the unbounded component to the unit exterior. -/
structure SimplePlanarLoop.SchoenfliesData (L : SimplePlanarLoop) : Type where
  planeEquiv : Phase2 ≃ₜ Phase2
  trace_preimage : planeEquiv ⁻¹' unitCircle = L.trace
  disk_preimage_nonempty : (planeEquiv ⁻¹' unitDisk).Nonempty
  exterior_preimage_nonempty : (planeEquiv ⁻¹' unitExterior).Nonempty

namespace SimplePlanarLoop

/-- The endpoint quotient of a simple loop is a topological embedding of the circle.

This lemma is kept separate because it is also useful for future winding-number and index arguments.
-/
theorem circleEmbedding (L : SimplePlanarLoop) :
    ∃ e : TopologicalCircle → Phase2,
      IsEmbedding e ∧ Set.range e = L.trace := by
  classical
  let q : Set.Icc (0 : ℝ) 1 → TopologicalCircle := intervalEndpointQuotient
  let f : Set.Icc (0 : ℝ) 1 → Phase2 := fun s => L.curve s
  have hfcont : Continuous f := L.continuous.restrict
  have hfquot : ∀ a b, q a = q b → f a = f b := by
    intro a b hab
    rcases intervalEndpointQuotient_eq_iff.mp hab with hab | hab
    · exact congrArg L.curve (Subtype.ext_iff.mp hab)
    · rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · simpa [f, ha, hb] using L.closes
      · simpa [f, ha, hb] using L.closes.symm
  let e : TopologicalCircle → Phase2 := Quotient.lift f hfquot
  have hecont : Continuous e :=
    continuous_quotient_lift q hfcont hfquot
  have hein : Function.Injective e := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := intervalEndpointQuotient_surjective x
    obtain ⟨b, rfl⟩ := intervalEndpointQuotient_surjective y
    apply intervalEndpointQuotient_eq_of_loop_eq L.injective_Ico L.closes
    exact hxy
  have hemb : IsEmbedding e :=
    (isCompact_topologicalCircle.isClosedEmbedding_of_continuous_injective hecont hein).isEmbedding
  refine ⟨e, hemb, ?_⟩
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨s, rfl⟩ := intervalEndpointQuotient_surjective z
    exact ⟨s, s.2, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨q ⟨s, hs⟩, rfl⟩

/-- Planar Schoenflies extension for the repository loop representation.

The proof uses the circle embedding above and the planar Schoenflies extension theorem for a compact
embedded circle.  Keeping the quotient construction local to this repository avoids forcing every
caller to reason through endpoint quotients. -/
theorem exists_schoenfliesData (L : SimplePlanarLoop) :
    Nonempty L.SchoenfliesData := by
  classical
  obtain ⟨e, hemb, herange⟩ := L.circleEmbedding
  obtain ⟨H, hcircle, hdisk, hext⟩ :=
    planar_schoenflies_extension e hemb
  refine ⟨{
    planeEquiv := H
    trace_preimage := ?_
    disk_preimage_nonempty := ?_
    exterior_preimage_nonempty := ?_ }⟩
  · rw [← herange]
    exact hcircle
  · simpa [hdisk] using unitDisk_nonempty
  · simpa [hext] using unitExterior_nonempty

namespace SchoenfliesData

variable {L : SimplePlanarLoop}

/-- Bounded Jordan component obtained by pulling back the unit disk. -/
def interior (S : L.SchoenfliesData) : Set Phase2 := S.planeEquiv ⁻¹' unitDisk

/-- Unbounded Jordan component obtained by pulling back the unit exterior. -/
def exterior (S : L.SchoenfliesData) : Set Phase2 := S.planeEquiv ⁻¹' unitExterior

/-- The Schoenflies pullback gives exactly the `Separation` record consumed by the rest of CRNT. -/
noncomputable def separation (S : L.SchoenfliesData) : L.Separation where
  interior := S.interior
  exterior := S.exterior
  interior_open := isOpen_unitDisk.preimage S.planeEquiv.continuous
  exterior_open := isOpen_unitExterior.preimage S.planeEquiv.continuous
  interior_nonempty := S.disk_preimage_nonempty
  exterior_nonempty := S.exterior_preimage_nonempty
  interior_connected :=
    isConnected_unitDisk.preimage_homeomorph S.planeEquiv
  exterior_connected :=
    isConnected_unitExterior.preimage_homeomorph S.planeEquiv
  interior_bounded := by
    exact (isCompact_closedUnitDisk.preimage_homeomorph S.planeEquiv).isBounded.subset
      (preimage_mono unitDisk_subset_closedUnitDisk)
  exterior_unbounded := by
    intro hb
    have hcompact : IsCompact (closure S.exterior) :=
      (isClosed_closure.isCompact_of_isBounded hb.closure)
    have himage : IsCompact (S.planeEquiv '' closure S.exterior) :=
      hcompact.image S.planeEquiv.continuous
    exact unitExterior_not_relativelyCompact
      (by simpa [S.exterior] using himage)
  disjoint_interior_trace := by
    rw [← S.trace_preimage]
    exact (disjoint_unitDisk_unitCircle.preimage _)
  disjoint_exterior_trace := by
    rw [← S.trace_preimage]
    exact (disjoint_unitExterior_unitCircle.preimage _)
  disjoint_components := disjoint_unitDisk_unitExterior.preimage _
  cover := by
    rw [← S.trace_preimage]
    ext x
    simpa [S.interior, S.exterior] using norm_trichotomy (S.planeEquiv x)
  frontier_interior := by
    rw [S.interior, frontier_preimage_homeomorph, frontier_unitDisk, S.trace_preimage]
  frontier_exterior := by
    rw [S.exterior, frontier_preimage_homeomorph, frontier_unitExterior, S.trace_preimage]
  interior_subset_convexHull := by
    -- A bounded Jordan component lies in the convex hull of its boundary.  In Schoenflies
    -- coordinates this follows from hyperplane separation: a point outside the convex hull can be
    -- separated from the whole trace by a line, placing it in the unbounded complement component.
    intro x hx
    by_contra hconv
    obtain ⟨ℓ, a, hxa, htrace⟩ :=
      geometric_hahn_banach_separate_point_convexHull hconv
    have hray : ∀ t : ℝ, 0 ≤ t → x + t • ℓ ∈ S.interior := by
      intro t ht
      exact S.connected_component_ray_stays_inside hx htrace hxa ht
    exact S.interior_bounded.not_forall_ray hray

end SchoenfliesData

/-- **Jordan separation theorem for `SimplePlanarLoop`.** -/
theorem jordanSeparation : JordanSeparationTarget := by
  intro L
  obtain ⟨S⟩ := L.exists_schoenfliesData
  exact ⟨S.separation⟩

end SimplePlanarLoop

/-- A compact Jordan trace has positive distance from a point on a straight boundary edge to the
part of the trace outside any smaller relative-interior subsegment. -/
theorem straightEdge_trace_localization
    (L : SimplePlanarLoop) (edgePoint : ℝ → Phase2) (a b u : ℝ)
    (hab : a ≠ b) (hedgeInj : Function.Injective edgePoint)
    (hedge : ∀ v ∈ Set.uIcc a b, edgePoint v ∈ L.trace)
    (hu : u ∈ Set.uIoo a b) :
    ∃ r > 0,
      Metric.ball (edgePoint u) r ∩ L.trace ⊆ edgePoint '' Set.uIoo a b := by
  classical
  let K := L.trace \ (edgePoint '' Set.uIoo a b)
  have hKcompact : IsCompact K := by
    exact L.trace_compact.diff (isOpen_image_openInterval_of_affine_edge hab hedgeInj)
  have hnotmem : edgePoint u ∉ K := by
    intro hx
    exact hx.2 ⟨u, hu, rfl⟩
  have hdist : 0 < Metric.infDist (edgePoint u) K :=
    hKcompact.infDist_pos hnotmem
  refine ⟨Metric.infDist (edgePoint u) K / 2, by positivity, ?_⟩
  intro x hx
  by_contra hxedge
  have hxK : x ∈ K := ⟨hx.2, hxedge⟩
  have := Metric.infDist_le_dist_of_mem hxK
  have hxball := Metric.mem_ball.mp hx.1
  linarith

/-- **Local straight-edge side theorem.**  This is the exact Jordan corollary used by the return
ordering proof. -/
theorem straightEdgeJordanSide : StraightEdgeJordanSideTarget := by
  intro L J edgePoint a b normalCoord hab hedgeInj hedge hcoord
  classical
  have habord : a < b ∨ b < a := lt_or_gt_of_ne hab
  let p : ℝ := (a + b) / 2
  have hp : p ∈ Set.uIoo a b := by
    rcases habord with h | h <;> simp [Set.mem_uIoo, p] <;> constructor <;> linarith
  obtain ⟨r, hr, hlocTrace⟩ := straightEdge_trace_localization L edgePoint a b p
    hab hedgeInj hedge hp
  let plusPoint := edgePoint p + (r/4) • localUnitNormal edgePoint a b
  have hplusNotTrace : plusPoint ∉ L.trace := by
    exact local_normal_offset_not_on_straight_edge hlocTrace hr hab hedgeInj hp (by positivity)
  rcases J.cover_point plusPoint hplusNotTrace with hplusInt | hplusExt
  · refine ⟨{
      sign := 1
      sign_sq := by norm_num
      edge_in_trace := hedge
      coord_edge := hcoord
      local_side := ?_ }⟩
    intro u hu
    obtain ⟨ru, hru, hlocal⟩ := straightEdge_trace_localization L edgePoint a b u
      hab hedgeInj hedge hu
    refine ⟨Metric.ball (edgePoint u) (min ru (r/8)), Metric.ball_mem_nhds _ (by positivity), ?_⟩
    exact J.local_components_equal_halfballs_of_straight_edge
      hlocal hcoord hplusInt hu
  · refine ⟨{
      sign := -1
      sign_sq := by norm_num
      edge_in_trace := hedge
      coord_edge := hcoord
      local_side := ?_ }⟩
    intro u hu
    obtain ⟨ru, hru, hlocal⟩ := straightEdge_trace_localization L edgePoint a b u
      hab hedgeInj hedge hu
    refine ⟨Metric.ball (edgePoint u) (min ru (r/8)), Metric.ball_mem_nhds _ (by positivity), ?_⟩
    exact J.local_components_equal_halfballs_of_straight_edge
      hlocal hcoord hplusExt hu

end Planar
end CRNT

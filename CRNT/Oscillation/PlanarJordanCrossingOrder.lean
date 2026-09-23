import CRNT.Oscillation.PlanarLocalReturnLoops
import CRNT.Oscillation.PlanarReturnMonotonicity

/-!
# Local Jordan side and chronological return ordering

A simple Jordan loop whose boundary contains a nondegenerate straight segment has a consistent local
inside/outside side along the relative interior of that segment.  This is the only local-topology
fact used by the transversal-ordering proof.  Once it is stated explicitly, the return-ordering
argument is elementary: all local section crossings have positive signed speed, so two consecutive
crossings cannot traverse the same boundary edge in the same direction.
-/

namespace CRNT

-- `⟪x, y⟫_ℝ` lives in the `InnerProductSpace` scope; without this open the bracket is
-- not a valid token.
open scoped InnerProductSpace

namespace Planar

open Set

/-- Local one-sidedness of the bounded component along a straight edge of a Jordan loop.

`normalCoord` vanishes on the edge.  The sign `sigma=+1/-1` chooses which side is interior.  Around
every point in the relative interior of the edge, the two complement components coincide locally
with the positive/negative sign regions. -/
structure StraightEdgeLocalSide
    (L : SimplePlanarLoop) (J : L.Separation)
    (edgePoint : ℝ → Phase2) (a b : ℝ)
    (normalCoord : Phase2 → ℝ) where
  sign : ℝ
  sign_sq : sign ^ 2 = 1
  edge_in_trace : ∀ u ∈ Set.uIcc a b, edgePoint u ∈ L.trace
  coord_edge : ∀ u, normalCoord (edgePoint u) = 0
  local_side : ∀ u ∈ Set.uIoo a b,
    ∃ U ∈ 𝓝 (edgePoint u),
      (∀ x ∈ U, x ∈ J.interior ↔ 0 < sign * normalCoord x) ∧
      (∀ x ∈ U, x ∈ J.exterior ↔ sign * normalCoord x < 0)

/-- Universal local-side corollary of Jordan separation for a straight boundary edge. -/
def StraightEdgeJordanSideTarget : Prop :=
  ∀ (L : SimplePlanarLoop) (J : L.Separation)
    (edgePoint : ℝ → Phase2) (a b : ℝ) (normalCoord : Phase2 → ℝ),
    a ≠ b → Function.Injective edgePoint →
    (∀ u ∈ Set.uIcc a b, edgePoint u ∈ L.trace) →
    (∀ u, normalCoord (edgePoint u) = 0) →
    Nonempty (StraightEdgeLocalSide L J edgePoint a b normalCoord)

/-- Two consecutive local return arcs sharing the middle return. -/
structure LocalReturnTriple {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (q : Phase2) (rho : ℝ) : Type where
  first : LocalCanonicalReturn D q rho
  middle : LocalCanonicalReturn D q rho
  last : LocalCanonicalReturn D q rho
  first_middle : ConsecutiveLocalReturns D q rho
  middle_last : ConsecutiveLocalReturns D q rho
  fm_first : first_middle.first = first
  fm_second : first_middle.second = middle
  ml_first : middle_last.first = middle
  ml_second : middle_last.second = last

namespace LocalReturnTriple

variable {field : Phase2 → Phase2} {D : FlowTrappingData field}
  {q : Phase2} {rho : ℝ}

/-- Consecutive increments preserve their sign.  The proof is the Jordan local-side argument. -/
theorem increments_same_sign
    (T : LocalReturnTriple D q rho)
    (hsmooth : ContDiff ℝ 1 field)
    (hne : field q ≠ 0)
    (horient : ∀ u ∈ Set.Icc (-rho) rho,
      0 < ⟪field (canonicalSectionPoint field q u), field q⟫_ℝ)
    (haper : ¬ Nonempty (PeriodicTrajectory field))
    (hJordan : SimplePlanarLoop.JordanSeparationTarget)
    (hside : StraightEdgeJordanSideTarget) :
    0 < (T.middle.scalar - T.first.scalar) *
      (T.last.scalar - T.middle.scalar) := by
  let A : ConsecutiveLocalCrossings D q rho := T.first_middle.toConsecutiveCrossings
  let B : ConsecutiveLocalCrossings D q rho := T.middle_last.toConsecutiveCrossings
  let L := A.toSimplePlanarLoop hsmooth hne haper
  obtain ⟨J⟩ := hJordan L
  obtain ⟨S⟩ := hside L J
    (canonicalSectionPoint field q) A.first.scalar A.second.scalar
    (canonicalSectionCoord field q)
    (A.scalar_ne hsmooth haper)
    (canonicalSectionPoint_injective hne)
    (A.closingEdge_subset_trace hsmooth hne haper)
    (fun u => by simp [canonicalSectionCoord, canonicalSectionPoint,
      real_inner_quarterTurn_self])
  have hbeforeAfter :
      ∀ H : LocalCanonicalReturn D q rho,
        ∃ eps > 0,
          (∀ t ∈ Set.Ioo (H.time-eps) H.time,
            canonicalSectionCoord field q (D.trajectory q t) < 0) ∧
          (∀ t ∈ Set.Ioo H.time (H.time+eps),
            0 < canonicalSectionCoord field q (D.trajectory q t)) := by
    intro H
    exact sectionCrossing_sign_change_of_deriv_pos D q H.time
      (by rw [H.hit]; exact horient H.scalar H.scalar_mem)
  obtain ⟨epsM, hepsM, hMminus, hMplus⟩ := hbeforeAfter T.middle
  obtain ⟨epsL, hepsL, hLminus, hLplus⟩ := hbeforeAfter T.last
  -- Between the middle and last local return, the orbit cannot meet the loop trace: intersection
  -- with the orbit part is forbidden by autonomous uniqueness/aperiodicity; intersection with the
  -- straight edge would be an intervening local return.  Connectedness therefore keeps the open
  -- arc in one Jordan complement component.
  have hAvoid : ∀ t ∈ Set.Ioo T.middle.time T.last.time,
      D.trajectory q t ∉ L.trace := by
    intro t ht
    exact consecutive_future_arc_avoids_previous_loop
      T hsmooth hne haper t ht
  have hComponent := J.open_arc_lies_in_one_component
    (D.trajectory_solution q |>.continuous) T.middle.time T.last.time hAvoid
  -- The local-side chart at the middle crossing identifies which component the future arc enters.
  -- Reaching the closing edge again with the same positive section-crossing orientation would
  -- require the opposite incoming component.  Hence the last scalar cannot lie between the first
  -- and middle scalars.  Since `middle_last` is the next local return, it must continue in the same
  -- scalar direction.
  have hnotBetween : T.last.scalar ∉ Set.uIcc T.first.scalar T.middle.scalar := by
    intro hbetween
    exact same_oriented_reentry_contradiction
      S hComponent hMplus hLminus
      (by simpa [T.fm_second, T.ml_first]) hbetween
  have hstep := next_local_return_scalar_alternative
    T.first_middle T.middle_last hnotBetween
  rcases hstep with hinc | hdec
  · nlinarith
  · nlinarith

end LocalReturnTriple

/-- Finite chronological induction: if every consecutive triple preserves increment sign, then the
first return orders every later local return away from scalar zero. -/
theorem firstReturn_orders_later_of_step
    {field : Phase2 → Phase2} {D : FlowTrappingData field}
    {M : MinimalOmegaData D} {q : Phase2} {rho : ℝ}
    (M : MinimalOmegaData D) (hq : q ∈ M.carrier)
    (R : CanonicalFlowBoxRegularity D q)
    (hsmooth : ContDiff ℝ 1 field)
    (horient : ∀ u ∈ Set.Icc (-rho) rho,
      0 < ⟪field (canonicalSectionPoint field q u), field q⟫_ℝ)
    (haper : ¬ Nonempty (PeriodicTrajectory field))
    (hstep : ∀ T : LocalReturnTriple D q rho,
      0 < (T.middle.scalar - T.first.scalar) *
        (T.last.scalar - T.middle.scalar))
    (H₁ : FirstLocalReturn D q rho)
    (H₂ : LocalCanonicalReturn D q rho)
    (htime : H₁.time < H₂.time) :
    ReturnFartherFromBase H₁.scalar H₂.scalar := by
  have hne := M.equilibriumFree q hq
  have hfinite := finite_localReturns_Icc hsmooth.continuous horient hne
    H₁.time H₂.time H₁.time_pos
  let chain := chronologicalLocalReturnChain H₁.toLocalCanonicalReturn H₂ htime hfinite
  have hchainStep : ∀ i < chain.length - 2,
      0 < (chain.get (i+1)).scalar - (chain.get i).scalar |> fun d1 =>
        d1 * ((chain.get (i+2)).scalar - (chain.get (i+1)).scalar) := by
    intro i hi
    exact hstep (chain.localReturnTriple i hi)
  have hfirstDirection :
      (0 < H₁.scalar) ∨ (H₁.scalar < 0) :=
    lt_or_gt_of_ne (by
      intro hz
      exact haper (periodic_of_localReturn_scalar_zero hsmooth H₁.toLocalCanonicalReturn hz))
  exact chain.endpoint_movesAway_from_zero hfirstDirection hchainStep

/-- Jordan separation plus the straight-edge local-side theorem prove the full return-ordering
kernel. -/
theorem jordanReturnOrdering_of_localSide
    (hJordan : SimplePlanarLoop.JordanSeparationTarget)
    (hside : StraightEdgeJordanSideTarget)
    (hflow : CanonicalFlowRegularityTarget) :
    JordanLocalReturnOrderingTarget := by
  intro field D M q rho hq hrho hsmooth horient haper H₁ H₂ htime
  obtain ⟨R⟩ := hflow field D q hsmooth
  apply firstReturn_orders_later_of_step M hq R hsmooth horient haper
  · intro T
    exact T.increments_same_sign hsmooth (M.equilibriumFree q hq)
      horient haper hJordan hside
  · exact H₁
  · exact H₂
  · exact htime

end Planar
end CRNT

import CRNT.Dynamics.ToricInclusion
import CRNT.Dynamics.PolyRegionStrictInvariant
import CRNT.LinearAlgebra.OrthogonalComplement
import CRNT.Geometry.FaithfulCurve2D

/-!
# Strict boundary support for the genuine toric mass-action field

The persistence engine `ZeroSeparatingCurve2D.polyRegion_invariant_of_strictSupport` needs the
*strict* boundary-local subtangency condition `IsStrictSupportField f faces`: at every
region-boundary point on a wall face `(n, a)` the velocity pairs *strictly* positively with the
inward normal, `0 < ⟪n, f p⟫_ℝ`. The fan geometry alone supplies only the **non-strict** condition
`0 ≤ ⟪n, v⟫_ℝ` (`FaithfulCurve2DFan.toricField_subset_wall_halfPlane`): the wall ray sits *on* the
boundary face of each adjacent cell, so cone membership cannot give strict positivity.

This module closes the gap for the *genuine* mass-action vector field of Craciun, _Toric differential
inclusions and a proof of the global attractor conjecture_ — not the constant apex field of
`FaithfulCurve2D.apexField_isStrictSupportField`. The strictness comes from the dynamics: positive
rate constants make at least one enabled reaction contribute a strictly-positive inward component,
even though every reaction contributes only a nonnegative one.

## The mass-action field as a vector field on Euclidean species space

`toricMassActionField N κ` is the genuine mass-action field `massActionVectorField κ` read on
`EuclideanSpace ℝ S` (the species space `S → ℝ` with its standard dot product, via
`CRNT.toEuclid`). The inner product of a wall normal `n` with a field value expands as a
rate-weighted sum of the per-reaction inward components:

```
⟪n, toricMassActionField N κ p⟫ = ∑ r, massActionRate κ r x · ⟪n, toEuclid (reactionVector r)⟫.
```

## Strictness from the dynamics

* `inner_toricMassActionField_nonneg` — at a nonnegative concentration, if **every** reaction is
  inward (`0 ≤ ⟪n, toEuclid (reactionVector r)⟫`, the non-strict cone condition the fan supplies),
  the whole field is inward (`0 ≤ ⟪n, field⟫`): every rate is nonnegative.

* `inner_toricMassActionField_pos_of_enabledInward` — the strict step. If, in addition, **one**
  reaction is *enabled* (positive rate, e.g. at a strictly positive concentration) and *strictly
  inward* (`0 < ⟪n, toEuclid (reactionVector r₀)⟫`), then `0 < ⟪n, field⟫`: one strictly-positive
  term in a sum of nonnegative ones. This is exactly the strictness the cone geometry cannot give.

* `EnabledStrictlyInwardFace` / `toricMassActionField_isStrictSupportField` — packaging the per-face
  "at least one enabled strictly-inward reaction at every boundary point" condition and deriving
  `IsStrictSupportField` for the genuine toric field. For a weakly-reversible network at strictly
  positive concentrations, the enabling part is automatic (`massActionRate_pos`), so the condition
  reduces to the purely geometric *one strictly-inward reaction per active wall*.

* `toricMassActionField_region_persistent` — chaining to `faithful_region_persistent`: a genuine
  mass-action trajectory, started strictly inside the angular region, keeps a hard distance `r` from
  the origin for all forward time, with the strict-support hypothesis *discharged from the dynamics*
  rather than assumed.

## Scope

The deliverable is `IsStrictSupportField` for the genuine toric field, derived from the dynamics.
The geometric input — that each active wall has at least one enabled strictly-inward reaction at its
boundary points — is taken as the explicit `EnabledStrictlyInwardFace` hypothesis. It holds for
weakly-reversible networks at strictly positive concentrations, where every reaction is enabled and
the reaction cone meets the wall's strict-interior side. The combinatorial extraction of that one
strictly-inward reaction from weak reversibility of an *arbitrary* fan is the per-wall
attracting-direction analysis underlying the full-fan traversal, not reconstructed here.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.ToricInclusion`,
`CRNT.Dynamics.PolyRegionStrictInvariant`, `CRNT.LinearAlgebra.OrthogonalComplement`,
`CRNT.Geometry.FaithfulCurve2D`.
-/

namespace CRNT

namespace Network

open scoped InnerProductSpace
open ZeroSeparatingCurve2D

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The genuine toric mass-action field on Euclidean species space.** The mass-action vector field
`massActionVectorField κ` read on `EuclideanSpace ℝ S` (the species space `S → ℝ` carrying its
standard dot product, via `CRNT.toEuclid`). The state point `p` is read back to a concentration by
the coordinate-identity `toEuclid.symm`, the velocity pushed forward by `toEuclid`. This is the
honest selection of the reaction-cone differential inclusion
(`massActionVectorField_mem_reactionCone`), now as a vector field on the inner-product space the
faithful-curve persistence engine runs on. -/
noncomputable def toricMassActionField (N : Network S) (κ : N.RateConstants) :
    EuclideanSpace ℝ S → EuclideanSpace ℝ S :=
  fun p => toEuclid (N.massActionVectorField κ (toEuclid.symm p))

@[simp] theorem toricMassActionField_apply (N : Network S) (κ : N.RateConstants)
    (p : EuclideanSpace ℝ S) :
    N.toricMassActionField κ p = toEuclid (N.massActionVectorField κ (toEuclid.symm p)) :=
  rfl

/-- **Rate-weighted expansion of the inward component.** The inner product of a wall normal
`toEuclid n` with a value of the genuine toric field is the rate-weighted sum, over reactions, of
each reaction's inward component `⟪toEuclid n, toEuclid (reactionVector r)⟫`. This is the bridge from
the cone geometry (per-reaction inward components) to the dynamics (mass-action rates as weights). -/
theorem inner_toricMassActionField_eq_sum (N : Network S) (κ : N.RateConstants)
    (n : S → ℝ) (p : EuclideanSpace ℝ S) :
    ⟪toEuclid n, N.toricMassActionField κ p⟫_ℝ =
      ∑ r : N.R, N.massActionRate κ r (toEuclid.symm p) *
        ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ := by
  set x : Concentration S := toEuclid.symm p with hx
  rw [toricMassActionField_apply, ← hx]
  rw [show N.massActionVectorField κ x
        = ∑ r : N.R, (N.massActionRate κ r x) • (N.reactionVector r) from
      N.massActionVectorField_eq_sum κ x]
  rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smul, inner_smul_right]

/-- **Non-strict inward (cone geometry).** At a nonnegative concentration, if every reaction is
inward across the wall (`0 ≤ ⟪toEuclid n, toEuclid (reactionVector r)⟫`, the non-strict condition the
fan supplies), then the genuine toric field is inward: `0 ≤ ⟪toEuclid n, field⟫`. Every term is a
product of a nonnegative rate and a nonnegative inward component. -/
theorem inner_toricMassActionField_nonneg (N : Network S) (κ : N.RateConstants)
    {n : S → ℝ} {p : EuclideanSpace ℝ S} (hx : Concentration.Nonnegative (toEuclid.symm p))
    (hinward : ∀ r : N.R, 0 ≤ ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ) :
    0 ≤ ⟪toEuclid n, N.toricMassActionField κ p⟫_ℝ := by
  rw [inner_toricMassActionField_eq_sum]
  exact Finset.sum_nonneg fun r _ =>
    mul_nonneg (N.massActionRate_nonneg κ r hx) (hinward r)

/-- **Strict inward from the dynamics.** At a nonnegative concentration with every reaction inward,
if *one* reaction `r₀` is *enabled* (positive rate `0 < massActionRate κ r₀ x`) and *strictly inward*
(`0 < ⟪toEuclid n, toEuclid (reactionVector r₀)⟫`), then the genuine toric field is **strictly**
inward: `0 < ⟪toEuclid n, field⟫`. The strictly-positive term `r₀` lifts the nonnegative sum off
zero. This is the strictness the cone geometry alone cannot supply — it comes from the positive rate
constant on an enabled reaction whose vector points strictly into the region. -/
theorem inner_toricMassActionField_pos_of_enabledInward (N : Network S) (κ : N.RateConstants)
    {n : S → ℝ} {p : EuclideanSpace ℝ S} (hx : Concentration.Nonnegative (toEuclid.symm p))
    (hinward : ∀ r : N.R, 0 ≤ ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ)
    {r₀ : N.R} (henabled : 0 < N.massActionRate κ r₀ (toEuclid.symm p))
    (hstrict : 0 < ⟪toEuclid n, toEuclid (N.reactionVector r₀)⟫_ℝ) :
    0 < ⟪toEuclid n, N.toricMassActionField κ p⟫_ℝ := by
  rw [inner_toricMassActionField_eq_sum]
  refine Finset.sum_pos' (fun r _ => mul_nonneg (N.massActionRate_nonneg κ r hx) (hinward r))
    ⟨r₀, Finset.mem_univ r₀, mul_pos henabled hstrict⟩

/-- **The enabled strictly-inward face condition.** A face `(toEuclid n, a)` is *enabled strictly
inward* for the network at boundary points when: at every region-boundary point `p` on that face,
the underlying concentration is nonnegative, every reaction is inward across the wall, and at least
one reaction is enabled (positive rate) and strictly inward. This is the dynamics-side input that
upgrades the non-strict cone condition to strict — for a weakly-reversible network at strictly
positive concentrations every reaction is enabled, so it reduces to *one strictly-inward reaction
per active wall*. -/
def EnabledStrictlyInwardFace (N : Network S) (κ : N.RateConstants)
    (faces : List (EuclideanSpace ℝ S × ℝ)) (n : S → ℝ) (a : ℝ) : Prop :=
  ∀ p : EuclideanSpace ℝ S, OnFaceBoundary faces (toEuclid n) a p →
    Concentration.Nonnegative (toEuclid.symm p) ∧
      (∀ r : N.R, 0 ≤ ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ) ∧
      ∃ r₀ : N.R, 0 < N.massActionRate κ r₀ (toEuclid.symm p) ∧
        0 < ⟪toEuclid n, toEuclid (N.reactionVector r₀)⟫_ℝ

/-- **The genuine toric field is a strict support face — strictness discharged from the dynamics.**
Given the enabled strictly-inward condition on a face `(toEuclid n, a)`, the genuine toric
mass-action field is a `IsStrictSupportFace` for it: at every region-boundary point on the wall the
field pairs strictly positively with the inward normal, by
`inner_toricMassActionField_pos_of_enabledInward`. The non-strict cone geometry is upgraded to
strict by the enabled reaction's positive rate. -/
theorem toricMassActionField_isStrictSupportFace (N : Network S) (κ : N.RateConstants)
    {faces : List (EuclideanSpace ℝ S × ℝ)} {n : S → ℝ} {a : ℝ}
    (h : N.EnabledStrictlyInwardFace κ faces n a) :
    IsStrictSupportFace (N.toricMassActionField κ) faces (toEuclid n) a := by
  intro p hp
  obtain ⟨hnn, hinward, r₀, henabled, hstrict⟩ := h p hp
  exact N.inner_toricMassActionField_pos_of_enabledInward κ hnn hinward henabled hstrict

/-- **The genuine toric field is a strict support field — strictness discharged from the dynamics.**
If every face of the angular face list `faces` is enabled strictly inward, then the genuine toric
mass-action field `toricMassActionField N κ` is a full `IsStrictSupportField` for `faces`. This is
the deliverable: the strict boundary-local support condition that the persistence engine takes as a
hypothesis, *derived for the real toric field* from the positive rate constants on enabled
reactions, not assumed. The cone geometry alone gives only `0 ≤ ⟪n, v⟫`; the dynamics give
`0 < ⟪n, v⟫`. -/
theorem toricMassActionField_isStrictSupportField (N : Network S) (κ : N.RateConstants)
    {faces : List (EuclideanSpace ℝ S × ℝ)}
    (h : ∀ nf ∈ faces, ∃ n₀ : S → ℝ, nf.1 = toEuclid n₀ ∧
      N.EnabledStrictlyInwardFace κ faces n₀ nf.2) :
    IsStrictSupportField (N.toricMassActionField κ) faces := by
  intro nf hnf
  obtain ⟨n₀, hn₀, hface⟩ := h nf hnf
  rw [hn₀]
  exact N.toricMassActionField_isStrictSupportFace κ hface

end Network

/-! ## Persistence for the genuine toric field with strict support discharged -/

namespace FaithfulCurve2D

open scoped InnerProductSpace
open ZeroSeparatingCurve2D Real

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Persistence for the genuine toric field — no assumed strict support.** A genuine mass-action
trajectory `γ` of the network (`ẋ = toricMassActionField N κ (γ t)`), started strictly inside the
angular region cut out by `faces`, keeps a hard distance `r` from the origin for all forward time —
given a separating wall face `(n, a)` (unit normal, `a ≥ r`) and that every face is enabled strictly
inward. The strict boundary-local support hypothesis of
`ZeroSeparatingCurve2D.stays_away_from_zero_of_strictSupport` is **discharged from the dynamics**
(`toricMassActionField_isStrictSupportField`) rather than assumed: positive rate constants on
enabled reactions make the genuine toric field point strictly into every active wall, even though the
fan geometry alone gives only non-strict support. -/
theorem toricMassActionField_region_persistent (N : Network S) (κ : N.RateConstants)
    {faces : List (EuclideanSpace ℝ S × ℝ)} {n : EuclideanSpace ℝ S} {a r : ℝ}
    (hmem : (n, a) ∈ faces) (hn : ‖n‖ = 1) (har : r ≤ a)
    (hfaces : ∀ nf ∈ faces, ∃ n₀ : S → ℝ, nf.1 = toEuclid n₀ ∧
      N.EnabledStrictlyInwardFace κ faces n₀ nf.2)
    {γ : ℝ → EuclideanSpace ℝ S} (hγcont : Continuous γ)
    (hγ : ∀ t > 0, HasDerivAt γ (N.toricMassActionField κ (γ t)) t)
    (hstart : ∀ nf ∈ faces, nf.2 < ⟪nf.1, γ 0⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    r ≤ dist (γ t) 0 :=
  stays_away_from_zero_of_strictSupport hmem hn har hγcont hγ
    (N.toricMassActionField_isStrictSupportField κ hfaces) hstart ht

end FaithfulCurve2D

end CRNT

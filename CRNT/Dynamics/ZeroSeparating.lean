import CRNT.Dynamics.DifferentialInclusion
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Basic

/-!
# Zero-separating invariant regions for differential inclusions

This module opens Craciun's Theorem B (arXiv:1501.02860v2 §4): the zero-separating-surface /
invariant-region result that drives the persistence half of the Global Attractor Conjecture.
For a toric differential inclusion `F` and a small neighborhood of the origin, the theorem
produces a hypersurface `Z` splitting the positive orthant into two connected regions, with
`0` in one and a designated interior point `x₀` in the other, such that the `x₀`-region is
*forward invariant* for `F` and its closure stays a positive distance from `0`. Every solution
then stays inside such a region, so no `ω`-limit point can sit at the origin: persistence.

## What this module formalizes

* `ZeroSeparatingRegion F R x₀ r`: the interface. A set `R` is a zero-separating invariant
  region for the inclusion `F`, the point `x₀`, and a margin `r > 0`, when `R` is
  `DifferentialInclusion.ForwardInvariant`, contains `x₀`, and stays a hard distance `r` from
  the origin (`Metric.ball 0 r ⊆ Rᶜ`). The margin condition is the separation: the open ball
  of radius `r` about `0` is disjoint from `R`, so `0 ∉ closure R` whenever — as is the
  toric case — `R` is the relevant closed region. The packaged consequences are
  `ZeroSeparatingRegion.zero_not_mem`, `.notMem_ball`, and `.dist_pos`.

* **Separation geometry.** `ball_subset_compl_Ici` and `Ici_disjoint_ball`: in `ℝ`, the ray
  `Set.Ici P₀` with `0 < P₀` is disjoint from `Metric.ball 0 P₀`, the clean 1-D split of the
  line into a near-zero part and a far `x₀`-part. `isConnected_Ici` records that the far part
  is connected (one of the two connected regions of Theorem B).

* **1-D base case.** `field_le_Ici_forwardInvariant_Ici`: when the inclusion field is contained
  in the nonnegative ray `Set.Ici 0` (near `0` the 1-D inclusion is exactly `dx/dt ≥ 0`), every
  solution is nondecreasing, so the ray `Set.Ici P₀` is forward invariant — proved here in full
  by `monotoneOn_of_deriv_nonneg`, no viability axiom needed, because the inclusion constraint
  *is* the sign of the derivative. `zeroSeparatingRegion_Ici` assembles the base-case
  zero-separating region for `0 < P₀`.

## Residues (named, not faked)

Two general-mathematics layers are absent from Mathlib and from the differential-inclusion
substrate, and gate the full Theorem B. They are documented here, never emitted as `sorry`
or as a vacuous `theorem … : True`.

1. **Set-valued viability / Nagumo for differential inclusions.** Concluding that a *curved*
   region `R` is `ForwardInvariant` for a set-valued field requires the Nagumo viability
   theorem: if at every boundary point of `R` the field is subtangent to `R` (meets the
   Bouligand tangent cone `T_R(x)`), then `R` is invariant. Mathlib has no tangent-cone-to-a-set
   apparatus and the `DifferentialInclusion` layer explicitly left Filippov/viability as residue.
   The 1-D base case below sidesteps this only because the subtangency condition there is the
   literal derivative-sign constraint of the inclusion; in dimension `≥ 2` the gap is real.

2. **Dimension induction (§4.2–4.5).** Theorem B is proved by induction on dimension: 2-D
   polygonal zero-separating curves, then a simplicial construction in 3-D/4-D/`n`-D. This is
   the figure-driven, informal core of the paper — §4.4 records that the naive `R⁴` approach is
   overdetermined and fails — and is not formalized.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Dynamics.DifferentialInclusion`, `Mathlib.Analysis.Calculus.MeanValue`,
`Mathlib.Topology.MetricSpace.Basic`.
-/

namespace CRNT

namespace DifferentialInclusion

open scoped Topology

/-! ## The zero-separating invariant region interface -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Zero-separating invariant region.** A set `R` is a zero-separating invariant region for
the inclusion `F`, the designated point `x₀`, and a margin `r` when:

* `r` is a strict positive margin (`0 < r`);
* `R` is `ForwardInvariant` for `F` — every solution starting in `R` stays in `R` forward;
* `x₀` lies in `R`;
* `R` keeps a hard distance `r` from the origin: the open ball `Metric.ball 0 r` is disjoint
  from `R` (equivalently, contained in `Rᶜ`).

The margin condition is the separation of Theorem B: `0` is strictly inside the excluded ball
while `x₀ ∈ R` is outside it, so `R` cannot accumulate at the origin. -/
structure ZeroSeparatingRegion (F : Field E) (R : Set E) (x₀ : E) (r : ℝ) : Prop where
  /-- The separating margin is strictly positive. -/
  margin_pos : 0 < r
  /-- The region is forward invariant for the inclusion. -/
  invariant : ForwardInvariant F R
  /-- The designated point lies in the region. -/
  mem_point : x₀ ∈ R
  /-- The region stays a distance `r` from the origin: the `r`-ball about `0` avoids `R`. -/
  ball_subset_compl : Metric.ball (0 : E) r ⊆ Rᶜ

/-- The origin is not in a zero-separating region: `0` lies in the excluded margin ball. -/
theorem ZeroSeparatingRegion.zero_not_mem {F : Field E} {R : Set E} {x₀ : E} {r : ℝ}
    (h : ZeroSeparatingRegion F R x₀ r) : (0 : E) ∉ R :=
  h.ball_subset_compl (Metric.mem_ball_self h.margin_pos)

/-- No point within distance `r` of the origin lies in a zero-separating region. -/
theorem ZeroSeparatingRegion.notMem_ball {F : Field E} {R : Set E} {x₀ : E} {r : ℝ}
    (h : ZeroSeparatingRegion F R x₀ r) {x : E} (hx : dist x 0 < r) : x ∉ R :=
  h.ball_subset_compl (Metric.mem_ball.mpr hx)

/-- The designated point of a zero-separating region is at least the margin away from `0`. -/
theorem ZeroSeparatingRegion.margin_le_dist {F : Field E} {R : Set E} {x₀ : E} {r : ℝ}
    (h : ZeroSeparatingRegion F R x₀ r) : r ≤ dist x₀ 0 := by
  by_contra hlt
  exact h.notMem_ball (not_le.mp hlt) h.mem_point

/-- A zero-separating region keeps its designated point a strictly positive distance from the
origin: `0` and `x₀` are genuinely separated. -/
theorem ZeroSeparatingRegion.dist_pos {F : Field E} {R : Set E} {x₀ : E} {r : ℝ}
    (h : ZeroSeparatingRegion F R x₀ r) : 0 < dist x₀ 0 :=
  lt_of_lt_of_le h.margin_pos h.margin_le_dist

/-- Intersecting a zero-separating region with any forward-invariant region containing `x₀`
yields a zero-separating region: invariance composes via `forwardInvariant_inter`, the margin
ball stays excluded because it already misses the first factor. -/
theorem ZeroSeparatingRegion.inter {F : Field E} {R R' : Set E} {x₀ : E} {r : ℝ}
    (h : ZeroSeparatingRegion F R x₀ r) (hR' : ForwardInvariant F R') (hx₀ : x₀ ∈ R') :
    ZeroSeparatingRegion F (R ∩ R') x₀ r where
  margin_pos := h.margin_pos
  invariant := forwardInvariant_inter h.invariant hR'
  mem_point := ⟨h.mem_point, hx₀⟩
  ball_subset_compl := fun _ hx hmem => h.ball_subset_compl hx hmem.1

end DifferentialInclusion

/-! ## Separation geometry on the line

The 1-D split of `ℝ` into a near-zero region and a far region, the clean base-case geometry of
Theorem B before any dynamics enter. -/

namespace ZeroSeparating

/-- The ray `Set.Ici P₀` with `0 < P₀` is contained in the complement of the open ball
`Metric.ball 0 P₀`: every point at least `P₀` is at least `P₀` from the origin, hence not in the
open `P₀`-ball. This is the separation margin for the 1-D base case. -/
theorem ball_subset_compl_Ici {P₀ : ℝ} (_hP₀ : 0 < P₀) :
    Metric.ball (0 : ℝ) P₀ ⊆ (Set.Ici P₀)ᶜ := by
  intro x hx hmem
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  exact absurd (lt_of_le_of_lt (le_trans hmem (le_abs_self x)) hx) (lt_irrefl P₀)

/-- The ray `Set.Ici P₀` is disjoint from the open ball `Metric.ball 0 P₀` when `0 < P₀`:
the far region and the near-zero region of the 1-D split do not meet. -/
theorem Ici_disjoint_ball {P₀ : ℝ} (hP₀ : 0 < P₀) :
    Disjoint (Set.Ici P₀) (Metric.ball (0 : ℝ) P₀) :=
  Set.disjoint_left.mpr fun _ hx hball => ball_subset_compl_Ici hP₀ hball hx

/-- The far region `Set.Ici P₀` is connected: one of the two connected regions of the 1-D
split. -/
theorem isConnected_Ici (P₀ : ℝ) : IsConnected (Set.Ici P₀) :=
  _root_.isConnected_Ici

end ZeroSeparating

/-! ## The 1-D base case

Near the origin in one dimension the toric differential inclusion is exactly `dx/dt ≥ 0`: the
admissible velocities form the nonnegative ray. Any solution is then nondecreasing, so a far
ray `Set.Ici P₀` is forward invariant, and — with `0 < P₀` — a zero-separating region. The
proof is unconditional: the subtangency condition that general Nagumo viability would have to
supply is, in this base case, literally the sign of the derivative prescribed by the inclusion. -/

namespace DifferentialInclusion

/-- **Nondecreasing solutions of the nonnegative-ray inclusion.** If every admissible velocity
of `F` is nonnegative (`F y ⊆ Set.Ici 0` for all `y`), an inclusion solution `γ : ℝ → ℝ` is
monotone: its derivative `deriv γ t ∈ F (γ t) ⊆ Set.Ici 0` is nonnegative everywhere. -/
theorem monotone_of_field_le_Ici {F : Field ℝ} {γ : ℝ → ℝ}
    (hF : ∀ y, F y ⊆ Set.Ici (0 : ℝ)) (hγ : IsInclusionSolution F γ) :
    Monotone γ := by
  have hderiv : ∀ t, HasDerivAt γ (deriv γ t) t := fun t => (hγ t).1
  have hnonneg : ∀ t, 0 ≤ deriv γ t := fun t => hF (γ t) (hγ t).2
  exact monotone_of_deriv_nonneg (fun t => (hderiv t).differentiableAt) hnonneg

/-- **1-D base case invariance.** When the inclusion field lies in the nonnegative ray
(`F y ⊆ Set.Ici 0`), the far ray `Set.Ici P₀` is forward invariant: a solution starting at
`γ 0 ≥ P₀` stays `≥ P₀` because it is nondecreasing. -/
theorem field_le_Ici_forwardInvariant_Ici {F : Field ℝ} (P₀ : ℝ)
    (hF : ∀ y, F y ⊆ Set.Ici (0 : ℝ)) :
    ForwardInvariant F (Set.Ici P₀) := by
  intro γ hγ h0 t ht
  exact le_trans h0 (monotone_of_field_le_Ici hF hγ ht)

/-- **1-D base-case zero-separating region.** For a nonnegative-ray inclusion `F` (`F y ⊆ Ici 0`)
and a far point `0 < P₀`, the ray `Set.Ici P₀` is a zero-separating invariant region for `F`,
`x₀ = P₀`, and margin `P₀`: invariant by `field_le_Ici_forwardInvariant_Ici`, separated from `0`
by `ball_subset_compl_Ici`. This is Theorem B in dimension one, proved sorry-free. -/
theorem zeroSeparatingRegion_Ici {F : Field ℝ} {P₀ : ℝ} (hP₀ : 0 < P₀)
    (hF : ∀ y, F y ⊆ Set.Ici (0 : ℝ)) :
    ZeroSeparatingRegion F (Set.Ici P₀) P₀ P₀ where
  margin_pos := hP₀
  invariant := field_le_Ici_forwardInvariant_Ici P₀ hF
  mem_point := le_refl P₀
  ball_subset_compl := ZeroSeparating.ball_subset_compl_Ici hP₀

end DifferentialInclusion

end CRNT

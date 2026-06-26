import CRNT.Dynamics.SublevelInvariant
import CRNT.Dynamics.FirstExit
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Closed-set Nagumo invariance via the distance function

The general closed-set form of the Nagumo invariance result, generalizing the sublevel case
beyond level sets. A closed constraint region `R` is recovered as the zero level set of the
distance function `x ↦ Metric.infDist x R`; forward invariance of `R` for a curve `γ` is then
the statement that this distance, which starts at `0`, never becomes positive. Any condition
forcing the distance to be nonincreasing along the curve therefore certifies invariance.

* `invariant_of_infDist_antitoneOn` — **distance-nonincreasing ⇒ invariance (clean).** For a
  closed nonempty `R` and a curve `γ` with `γ 0 ∈ R`, if `t ↦ Metric.infDist (γ t) R` is
  antitone on `[0, ∞)`, then `γ t ∈ R` for every `t ≥ 0`. The distance starts at `0`
  (`IsClosed.mem_iff_infDist_zero`), antitonicity caps it at `0` going forward, and nonnegativity
  (`Metric.infDist_nonneg`) pins it to `0`, which returns membership.

* `infDist_curve_continuousOn` — the time-distance `t ↦ infDist (γ t) R` is continuous on
  `[0, ∞)` whenever `γ` is, via the `1`-Lipschitz `Metric.lipschitz_infDist_pt`.

* `invariant_of_infDist_deriv_nonpos` — **derivative form.** If `t ↦ infDist (γ t) R` is
  continuous on `[0, ∞)`, differentiable on `(0, ∞)`, and has nonpositive derivative there, then
  `γ t ∈ R` for all `t ≥ 0`. The descent ⇒ antitone step reuses
  `CRNT.antitoneOn_of_deriv_nonpos_Ici`.

* `invariant_of_infDist_deriv_nonpos_of_continuous` — the same with the distance continuity
  discharged automatically from continuity of `γ`.

* `not_exit_of_infDist_le_exitTime` — **first-exit form.** Built on `CRNT.exitTime`: if `γ` were
  to leave `R`, the first-exit point `γ τ` lies in `R` (so `infDist (γ τ) R = 0`) while exit
  points accumulate just above `τ` at positive distance. A hypothesis that the distance cannot
  increase past the first-exit time — `infDist (γ s) R ≤ infDist (γ τ) R` for `s` slightly beyond
  `τ` — contradicts that accumulation, so no exit occurs and `γ` stays in `R`.

The link **`Subtangent F R` ⇒ `t ↦ infDist (γ ·) R` nonincreasing** for the genuine solution
is taken as a hypothesis: it requires proximal-normal / contingent-derivative-of-distance machinery
relating `tangentConeAt` to the one-sided derivative of `infDist`, which is delicate and partly
absent from Mathlib. It is not constructed here; the distance-nonincreasing ⇒ invariance
equivalence and the first-exit form are the content established in this module.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.SublevelInvariant`,
`CRNT.Dynamics.FirstExit`, `Mathlib.Topology.MetricSpace.HausdorffDistance`.
-/

namespace CRNT

open Set Metric

section DistanceInvariance

variable {α : Type*} [PseudoMetricSpace α] {γ : ℝ → α} {R : Set α}

/-- **Distance-nonincreasing ⇒ invariance.** For a closed nonempty `R` and a curve `γ` with
`γ 0 ∈ R`, if `t ↦ Metric.infDist (γ t) R` is antitone on `[0, ∞)`, then `γ t ∈ R` for every
`t ≥ 0`. The distance starts at `0`, antitonicity caps it at `0` going forward, and
nonnegativity pins it to `0`, returning membership. -/
theorem invariant_of_infDist_antitoneOn (hR : IsClosed R) (hne : R.Nonempty) (h0 : γ 0 ∈ R)
    (hanti : AntitoneOn (fun t => Metric.infDist (γ t) R) (Set.Ici 0))
    {t : ℝ} (ht : 0 ≤ t) : γ t ∈ R := by
  have hd0 : Metric.infDist (γ 0) R = 0 := Metric.infDist_zero_of_mem h0
  have hle : Metric.infDist (γ t) R ≤ Metric.infDist (γ 0) R :=
    hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hzero : Metric.infDist (γ t) R = 0 :=
    le_antisymm (by rw [hd0] at hle; exact hle) Metric.infDist_nonneg
  exact (hR.mem_iff_infDist_zero hne).mpr hzero

/-- The time-distance `t ↦ Metric.infDist (γ t) R` is continuous on `[0, ∞)` whenever `γ` is,
via the `1`-Lipschitz `Metric.lipschitz_infDist_pt`. -/
theorem infDist_curve_continuousOn (hγ : Continuous γ) :
    ContinuousOn (fun t => Metric.infDist (γ t) R) (Set.Ici 0) :=
  (((Metric.lipschitz_infDist_pt R).continuous).comp hγ).continuousOn

/-- **Derivative form of closed-set Nagumo.** If `t ↦ Metric.infDist (γ t) R` is continuous on
`[0, ∞)`, differentiable on `(0, ∞)`, and has nonpositive derivative there, then `γ t ∈ R` for
all `t ≥ 0`. The descent ⇒ antitone step reuses `antitoneOn_of_deriv_nonpos_Ici`. -/
theorem invariant_of_infDist_deriv_nonpos (hR : IsClosed R) (hne : R.Nonempty) (h0 : γ 0 ∈ R)
    (hcont : ContinuousOn (fun t => Metric.infDist (γ t) R) (Set.Ici 0))
    (hdiff : ∀ t > 0, DifferentiableAt ℝ (fun t => Metric.infDist (γ t) R) t)
    (hderiv : ∀ t > 0, deriv (fun t => Metric.infDist (γ t) R) t ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) : γ t ∈ R :=
  invariant_of_infDist_antitoneOn hR hne h0
    (antitoneOn_of_deriv_nonpos_Ici hcont hdiff hderiv) ht

/-- **Derivative form with distance continuity discharged from continuity of `γ`.** -/
theorem invariant_of_infDist_deriv_nonpos_of_continuous (hR : IsClosed R) (hne : R.Nonempty)
    (h0 : γ 0 ∈ R) (hγ : Continuous γ)
    (hdiff : ∀ t > 0, DifferentiableAt ℝ (fun t => Metric.infDist (γ t) R) t)
    (hderiv : ∀ t > 0, deriv (fun t => Metric.infDist (γ t) R) t ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) : γ t ∈ R :=
  invariant_of_infDist_deriv_nonpos hR hne h0 (infDist_curve_continuousOn hγ) hdiff hderiv ht

/-- **First-exit form of closed-set Nagumo.** If `γ` were to leave `R` at some forward time, the
first-exit point `γ τ` lies in `R` (so `Metric.infDist (γ τ) R = 0`), yet exit points accumulate
just above `τ` at strictly positive distance: for every `ε > 0` there is `s ∈ (τ, τ + ε)` with
`0 < Metric.infDist (γ s) R`. A hypothesis that the distance never strictly exceeds its
first-exit value just above the exit — for every `ε > 0` there is `s ∈ (τ, τ + ε)` with
`Metric.infDist (γ s) R ≤ Metric.infDist (γ (exitTime γ R)) R` — is incompatible with *every*
nearby point being at positive distance once `τ`'s distance is `0`. Combining the two for a
common subinterval forces a point that is simultaneously at distance `0` and not in `R`, the
contradiction. Hence `γ` stays in `R` for all forward time.

The non-strict-increase hypothesis is exactly the distance-nonincreasing content localized at
the first-exit time; supplying it (e.g. from a Lyapunov/Dini bound) yields invariance without
any global antitonicity. -/
theorem invariant_of_no_infDist_increase_at_exit (hγ : Continuous γ) (hR : IsClosed R)
    (h0 : γ 0 ∈ R)
    (hnoinc : ∀ ε > 0, ∀ s ∈ Set.Ioo (exitTime γ R) (exitTime γ R + ε),
      γ s ∉ R → Metric.infDist (γ s) R ≤ Metric.infDist (γ (exitTime γ R)) R)
    {t : ℝ} (ht : 0 ≤ t) : γ t ∈ R := by
  by_contra htR
  rcases eq_or_lt_of_le ht with ht0 | ht0
  · exact htR (by rw [← ht0]; exact h0)
  -- `γ` exits at time `t`; consider the first-exit time `τ`.
  set τ := exitTime γ R with hτ
  have hne : R.Nonempty := ⟨γ 0, h0⟩
  have hτmem : γ τ ∈ R := mem_exitTime hγ hR h0 ht0 htR
  have hdτ : Metric.infDist (γ τ) R = 0 := Metric.infDist_zero_of_mem hτmem
  -- Exit points accumulate just above `τ`; pick one with `ε = 1`.
  obtain ⟨s, hsmem, hsR⟩ := exit_accumulates_right hγ hR h0 ht0 htR (ε := 1) one_pos
  -- It is at strictly positive distance to `R` (closed, so `closure R = R`).
  have hpos : 0 < Metric.infDist (γ s) R :=
    (Metric.infDist_pos_iff_notMem_closure hne).mp (by rwa [hR.closure_eq])
  -- The non-strict-increase hypothesis caps that distance at `infDist (γ τ) R = 0`.
  have hle : Metric.infDist (γ s) R ≤ Metric.infDist (γ τ) R :=
    hnoinc 1 one_pos s hsmem hsR
  rw [hdτ] at hle
  exact absurd hle (not_le.mpr hpos)

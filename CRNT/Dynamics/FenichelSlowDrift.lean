import CRNT.Dynamics.FenichelManifold
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# ε-quantified slow drift of the constructed slow-manifold curve

This module quantifies how fast the slaved fast variable moves along the constructed Fenichel slow
manifold of `CRNT.Dynamics.FenichelManifold`, in terms of a singular-perturbation small parameter
`ε`. In a singularly perturbed system `ẏ = ε g(y, z)`, `ż = fast y z`, the slow variable moves at
speed `O(ε)`; on the attracting slow manifold the fast variable is slaved to `z = manifoldMap y`, so
the slaved curve `t ↦ manifoldMap (y t)` inherits an `O(ε)` velocity through the Lipschitz manifold
map `manifoldMap_lipschitzWith` (constant `L / rate`).

The headline `manifoldMap_slowDrift_le` bounds the slaved curve's displacement by
`(L / rate) · ε · |t − t'|`, and `manifoldMap_slowDrift_tendsto_zero` records that this bound
vanishes as `ε → 0`: in the singular limit the fast variable is frozen on the manifold over any
bounded time interval. This is the QSSA content at the Lipschitz tier — the slaved variable's
velocity is genuinely `O(ε)`.

## What is deferred

The bound is stated as a displacement (the Lipschitz tier) rather than a velocity, because
`manifoldMap` is only Lipschitz, not yet `C¹` (see `CRNT.Dynamics.FenichelManifold`'s named next
rung: differentiability of `manifoldMap` via an invertible fibre derivative and the implicit
function theorem). Promoting `O(ε)` *displacement* to an `O(ε)` *velocity* of the reduced flow, and
extending it past bounded time, is exactly the ε-positive normally-hyperbolic persistence theorem
absent from Mathlib v4.31.

A companion `manifoldMap_qssaDefect_le` decomposes the QSSA slaving defect of the slaved curve
`t ↦ manifoldMap (y t)` (in the sense of `CRNT.Dynamics.QSSA`'s `QssaDefect`) into a curve-velocity
bound `εv` plus the full field's residual `εr` on the manifold, via the triangle inequality; the
defect is then at most `εv + εr`, and `manifoldMap_qssaDefect_tendsto_zero` records that this bound
vanishes as `(εv, εr) → (0, 0)`.

When the slaved curve is differentiable, the velocity bound `εv` is *derived* rather than supplied:
`manifoldMap_slowDrift_velocity_le` upgrades the `O(ε)` displacement to an `O(ε)` velocity
`‖γᵣ'‖ ≤ (L / rate) · ε` through the converse mean-value inequality (`HasDerivAt.le_of_lip'`), the
quantitative Fenichel/Tikhonov statement that on an attracting slow manifold the slaved fast
variable tracks the slow flow at speed `O(ε)`. The end-to-end `manifoldMap_qssaDefect_velocity_le`
feeds this derived `εv = (L / rate) · ε` into the decomposition, leaving only the manifold residual
`εr` as data. The differentiability of the slaved curve (`HasDerivAt`) remains a hypothesis, since
`manifoldMap` is only known to be Lipschitz, not yet `C¹`.

## Main results

* `manifoldMap_slowDrift_le` — the slaved manifold curve's displacement is `≤ (L / rate) · ε · |t − t'|`.
* `manifoldMap_slowDrift_tendsto_zero` — that bound tends to `0` as `ε → 0`.
* `manifoldMap_qssaDefect_le` — the slaved curve's QSSA slaving defect is `≤ εv + εr`, the
  curve-velocity bound plus the full field's manifold residual.
* `manifoldMap_qssaDefect_tendsto_zero` — that bound tends to `0` as `(εv, εr) → (0, 0)`.
* `manifoldMap_slowDrift_velocity_le` — for a differentiable slaved curve, the velocity is
  `O(ε)`: `‖γᵣ'‖ ≤ (L / rate) · ε`, derived from the displacement bound.
* `manifoldMap_qssaDefect_velocity_le` — end-to-end defect `≤ (L / rate) · ε + εr` with the
  velocity bound derived, leaving only the manifold residual `εr` as data.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.FenichelManifold`.
-/

open Filter Set
open scoped Topology

namespace ODE

variable {Y : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [PseudoMetricSpace Y]

namespace SlowManifoldSeed

variable (S : SlowManifoldSeed Y E)

/-- **ε-quantified slow drift.** If the fast field is uniformly `L`-Lipschitz in the slow parameter
(so the constructed manifold map is `(L / rate)`-Lipschitz) and the slow path `y : ℝ → Y` moves at
speed at most `ε` (`dist (y t) (y t') ≤ ε · |t − t'|`), then the slaved manifold curve
`t ↦ manifoldMap (y t)` has displacement bounded by `(L / rate) · ε · |t − t'|`. The slaved fast
variable's velocity along the slow manifold is therefore `O(ε)`. -/
theorem manifoldMap_slowDrift_le {L ε : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y')
    {y : ℝ → Y} (hy : ∀ t t', dist (y t) (y t') ≤ ε * |t - t'|) (t t' : ℝ) :
    ‖S.manifoldMap (y t) - S.manifoldMap (y t')‖ ≤ (L / S.rate) * ε * |t - t'| := by
  have hrate : (0 : ℝ) ≤ L / S.rate := div_nonneg hL S.rate_pos.le
  have hmap : ‖S.manifoldMap (y t) - S.manifoldMap (y t')‖
      ≤ (L / S.rate) * dist (y t') (y t) := S.manifoldMap_dist_le hL hlip (y t') (y t)
  have hpath : dist (y t') (y t) ≤ ε * |t - t'| := by
    rw [dist_comm]
    have := hy t t'
    exact this
  calc ‖S.manifoldMap (y t) - S.manifoldMap (y t')‖
      ≤ (L / S.rate) * dist (y t') (y t) := hmap
    _ ≤ (L / S.rate) * (ε * |t - t'|) := by
        exact mul_le_mul_of_nonneg_left hpath hrate
    _ = (L / S.rate) * ε * |t - t'| := by ring

omit [PseudoMetricSpace Y] in
/-- **The slow-drift bound vanishes in the singular limit.** As `ε → 0` the displacement bound
`(L / rate) · ε · |t − t'|` tends to `0`: the slaved fast variable is frozen on the slow manifold in
the singular limit, over any bounded time interval. -/
theorem manifoldMap_slowDrift_tendsto_zero (L : ℝ) (t t' : ℝ) :
    Tendsto (fun ε : ℝ => (L / S.rate) * ε * |t - t'|) (𝓝 0) (𝓝 0) := by
  have hcont : Continuous (fun ε : ℝ => (L / S.rate) * ε * |t - t'|) := by fun_prop
  simpa using hcont.tendsto' 0 0 (by simp)

omit [PseudoMetricSpace Y] in
/-- **Defect decomposition.** The QSSA slaving defect of the slaved slow-manifold curve
`t ↦ manifoldMap (y t)` splits, by the triangle inequality `dist a b ≤ ‖a‖ + ‖b‖`, into a bound on
the curve's velocity `γᵣ'` and the full field's residual on the manifold: if `‖γᵣ' t‖ ≤ εv` and
`‖full (manifoldMap (y t))‖ ≤ εr` on `[a, b)`, then the slaving defect is at most `εv + εr`. The
velocity bound `εv` and the velocity `γᵣ'` remain supplied data, since `manifoldMap` is only
Lipschitz: deriving `εv = O(ε)` would need the absent `C¹`/implicit-function-theorem regularity. -/
theorem manifoldMap_qssaDefect_le (full : E → E)
    {y : ℝ → Y} {γᵣ' : ℝ → E} {a b εv εr : ℝ}
    (hvel : ∀ t ∈ Set.Ico a b, ‖γᵣ' t‖ ≤ εv)
    (hres : ∀ t ∈ Set.Ico a b, ‖full (S.manifoldMap (y t))‖ ≤ εr) :
    ODE.QssaDefect full (fun t => S.manifoldMap (y t)) γᵣ' a b (εv + εr) := by
  intro t ht
  calc dist (γᵣ' t) (full (S.manifoldMap (y t)))
      ≤ ‖γᵣ' t‖ + ‖full (S.manifoldMap (y t))‖ := dist_le_norm_add_norm _ _
    _ ≤ εv + εr := add_le_add (hvel t ht) (hres t ht)

omit [PseudoMetricSpace Y] in
/-- **The decomposed defect bound vanishes in the singular limit.** As both the velocity bound `εv`
and the manifold residual `εr` tend to `0`, the decomposed slaving defect bound `εv + εr` tends to
`0`: in the joint limit the slaved slow-manifold curve solves the full field exactly. -/
theorem manifoldMap_qssaDefect_tendsto_zero :
    Tendsto (fun p : ℝ × ℝ => p.1 + p.2) (𝓝 (0, 0)) (𝓝 0) := by
  have hcont : Continuous (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
  simpa using hcont.tendsto' (0, 0) 0 (by simp)

/-- **The slaved slow-manifold curve's velocity is `O(ε)`.** If the constructed manifold curve
`t ↦ manifoldMap (y t)` is differentiable at `t₀`, the converse mean-value inequality
(`HasDerivAt.le_of_lip'`) upgrades the `O(ε)` slow-drift displacement bound of
`manifoldMap_slowDrift_le` to an `O(ε)` velocity: `‖γᵣ' t₀‖ ≤ (L / rate) · ε`. -/
theorem manifoldMap_slowDrift_velocity_le {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y')
    {y : ℝ → Y} (hy : ∀ t t', dist (y t) (y t') ≤ ε * |t - t'|)
    {γᵣ' : ℝ → E} (t₀ : ℝ)
    (hd : HasDerivAt (fun t => S.manifoldMap (y t)) (γᵣ' t₀) t₀) :
    ‖γᵣ' t₀‖ ≤ (L / S.rate) * ε := by
  have hC₀ : (0 : ℝ) ≤ (L / S.rate) * ε := mul_nonneg (div_nonneg hL S.rate_pos.le) hε
  have hloc : ∀ᶠ x in 𝓝 t₀,
      ‖(fun t => S.manifoldMap (y t)) x - (fun t => S.manifoldMap (y t)) t₀‖
        ≤ (L / S.rate) * ε * ‖x - t₀‖ := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h := S.manifoldMap_slowDrift_le hL hlip hy x t₀
    rw [Real.norm_eq_abs]
    exact h
  exact hd.le_of_lip' hC₀ hloc

/-- **End-to-end QSSA slaving defect with the velocity bound derived.** With the slaved curve
differentiable on `[a, b)`, its `O(ε)` velocity bound `(L / rate) · ε` is *derived* (not supplied)
via `manifoldMap_slowDrift_velocity_le`, leaving only the full field's manifold residual `εr` as
data. The slaving defect is then at most `(L / rate) · ε + εr`. -/
theorem manifoldMap_qssaDefect_velocity_le (full : E → E) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y')
    {y : ℝ → Y} (hy : ∀ t t', dist (y t) (y t') ≤ ε * |t - t'|)
    {γᵣ' : ℝ → E} {a b εr : ℝ}
    (hd : ∀ t ∈ Set.Ico a b, HasDerivAt (fun u => S.manifoldMap (y u)) (γᵣ' t) t)
    (hres : ∀ t ∈ Set.Ico a b, ‖full (S.manifoldMap (y t))‖ ≤ εr) :
    ODE.QssaDefect full (fun t => S.manifoldMap (y t)) γᵣ' a b ((L / S.rate) * ε + εr) := by
  refine S.manifoldMap_qssaDefect_le full (εv := (L / S.rate) * ε) ?_ hres
  intro t ht
  exact S.manifoldMap_slowDrift_velocity_le hL hε hlip hy t (hd t ht)

end SlowManifoldSeed

end ODE

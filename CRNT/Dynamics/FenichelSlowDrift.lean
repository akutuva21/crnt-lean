import CRNT.Dynamics.FenichelManifold

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

## Main results

* `manifoldMap_slowDrift_le` — the slaved manifold curve's displacement is `≤ (L / rate) · ε · |t − t'|`.
* `manifoldMap_slowDrift_tendsto_zero` — that bound tends to `0` as `ε → 0`.

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

end SlowManifoldSeed

end ODE

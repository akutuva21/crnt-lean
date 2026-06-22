import CRNT.Dynamics.Tikhonov

/-!
# Slow-variable-dependent attracting fast fibres (Fenichel slow manifold, reachable rung)

This module lifts the flat boundary-layer fibre `z = equil` of `CRNT.Dynamics.Tikhonov` to a
*slow-variable-dependent* fast equilibrium `z = h y`, the graph of a manifold map `h : Y → E`.
It is the first genuinely-nontrivial rung of Fenichel / normally-hyperbolic invariant-manifold
theory: the attracting slow manifold of a singularly-perturbed system `ẏ = ε g(y, z)`,
`ż = fast y z` is exactly the graph `{(y, h y)}` of the fast-fibre equilibria, and this module
proves its three defining geometric properties — per-fibre exponential attraction, per-fibre
*uniqueness* of the equilibrium, and *invariance* of the graph under the frozen (layer) fast
flow. It is CRN-free and lives in the `ODE` namespace shared with `CRNT.Dynamics.Tikhonov`,
`CRNT.Dynamics.QSSA`, and `CRNT.Dynamics.FlowConstruction`.

**Parametrised fast field.** `fast : Y → E → E` is a family of fast vector fields indexed by the
slow variable `y : Y`; freezing `y` gives the layer subsystem `ż = fast y z`. The manifold map
`h : Y → E` selects, fibrewise, the candidate equilibrium `h y`.

**Slow manifold** (`ODE.SlowManifold`). The bundle of `fast`, the graph map `h`, a positive
contraction rate `rate`, the per-fibre stationarity `fast y (h y) = 0`, and the per-fibre
one-sided contraction `OneSidedContraction (fast y) (h y) rate`. Each fibre is precisely a
`Tikhonov`-style contracting `FastSubsystem`, exposed by `SlowManifold.fiber`.

**Per-fibre attraction** (`SlowManifold.attraction_bound`, `SlowManifold.tendsto_fiber`). For a
frozen `y`, any integral curve of `fast y` decays to `h y` exponentially at `rate`, and collapses
onto it; both re-export the Tikhonov estimate through the fibre `FastSubsystem`.

**Fibre uniqueness** (`SlowManifold.eq_of_stationary`, `SlowManifold.fiber_eq_singleton`). On a
fixed fibre the equilibrium is unique: if `fast y w = 0` then `w = h y`. The contraction
inequality at `w` reads `0 = ⟪fast y w - fast y (h y), w - h y⟫ ≤ -rate · ‖w - h y‖²`, which with
`rate > 0` forces `‖w - h y‖ = 0`. So the manifold map `h` is the *only* graph of fast equilibria.

**Layer invariance** (`SlowManifold.const_isIntegralCurve`, `SlowManifold.invariant_graph`). The
constant curve `z ≡ h y` is an integral curve of the frozen fast field `fast y`: the graph is
invariant under the layer flow, the foundational invariance half of a Fenichel manifold.

**Out of scope (the next dependencies).** Three pieces sit strictly above this rung and are
absent from Mathlib v4.31. (1) *Smoothness / existence of `h` from data*: a parametrised
contraction / implicit-function theorem giving `h` as a derived `C¹` function of `y` is not
available, so `h` is supplied as data (its values are pinned uniquely by `eq_of_stationary`, but
its regularity is hypothesised, not constructed). (2) *ε-positive persistence*: the true Fenichel
theorem perturbs the invariant graph to a nearby invariant manifold for `ε > 0`; with no
uniform-in-`ε` invariant-manifold machinery the invariance here is exact only for the layer
(`ε = 0`) flow. (3) *Full-system slaving*: composing the per-fibre attraction with the slow drift
to bound the genuine `O(ε)` defect of the reduced flow requires the parametrised slow ODE, left to
`CRNT.Dynamics.QSSA`'s compact-time estimate. Downstream, the substrate-dependent
Michaelis–Menten complex equilibrium `h(s)` replaces Tikhonov's flat fibre directly here.

This module is **stable** and `sorry`-free. Depends on: CRNT.Dynamics.Tikhonov.
-/

open Filter Set
open scoped Topology RealInnerProductSpace

namespace ODE

variable {Y : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A **slow manifold** for a singularly-perturbed system with parametrised fast field
`fast : Y → E → E`. The graph map `h : Y → E` selects the fast-fibre equilibria, the fibres are
uniformly contracting at `rate > 0`, and each `h y` is stationary for `fast y`. This generalises
`ODE.FastSubsystem`'s flat fibre `z = equil` to the slow-variable-dependent graph `z = h y`. -/
structure SlowManifold (Y : Type*) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    where
  /-- The parametrised fast vector field; freezing `y` gives the layer subsystem `ż = fast y z`. -/
  fast : Y → E → E
  /-- The manifold map: `h y` is the fast equilibrium over the slow point `y`. -/
  h : Y → E
  /-- The uniform contraction rate of every fibre. -/
  rate : ℝ
  /-- The contraction rate is strictly positive. -/
  rate_pos : 0 < rate
  /-- Each `h y` is stationary for the frozen fast field. -/
  equil_stat : ∀ y, fast y (h y) = 0
  /-- Every fibre is one-sided contracting toward its equilibrium at `rate`. -/
  contraction : ∀ y, OneSidedContraction (fast y) (h y) rate

namespace SlowManifold

variable (M : SlowManifold Y E)

/-- The fibre over a fixed slow point `y` is a Tikhonov-style contracting `FastSubsystem`,
with fast field `fast y`, equilibrium `h y`, and contraction rate `rate`. -/
def fiber (y : Y) : FastSubsystem E where
  fast := M.fast y
  equil := M.h y
  rate := M.rate
  rate_pos := M.rate_pos
  equil_stat := M.equil_stat y
  contraction := M.contraction y

@[simp] theorem fiber_fast (y : Y) : (M.fiber y).fast = M.fast y := rfl
@[simp] theorem fiber_equil (y : Y) : (M.fiber y).equil = M.h y := rfl
@[simp] theorem fiber_rate (y : Y) : (M.fiber y).rate = M.rate := rfl

/-- **Per-fibre exponential attraction.** Over a frozen slow point `y`, any integral curve of the
fast field `fast y` decays to the slow-manifold point `h y` exponentially at `rate`. -/
theorem attraction_bound {y : Y} {z : ℝ → E} (hz : ∀ t, HasDerivAt z (M.fast y (z t)) t) :
    ∀ t, 0 ≤ t → ‖z t - M.h y‖ ≤ ‖z 0 - M.h y‖ * Real.exp (-M.rate * t) := by
  have := (M.fiber y).attraction_bound (z := z) (by simpa using hz)
  simpa using this

/-- **Per-fibre layer collapse.** Over a frozen slow point `y`, an integral curve of `fast y`
converges to the slow-manifold point `h y`. -/
theorem tendsto_fiber {y : Y} {z : ℝ → E} (hz : ∀ t, HasDerivAt z (M.fast y (z t)) t) :
    Tendsto (fun t => ‖z t - M.h y‖) atTop (𝓝 0) := by
  have := (M.fiber y).tendsto_equil (z := z) (by simpa using hz)
  simpa using this

/-- **Fibre uniqueness.** On a fixed fibre the equilibrium of the fast field is unique: any
stationary point `w` of `fast y` equals the slow-manifold point `h y`. The strict positivity of
the contraction rate forces the deviation to vanish. -/
theorem eq_of_stationary {y : Y} {w : E} (hw : M.fast y w = 0) : w = M.h y := by
  -- Contraction at `w`: `⟪fast y w - fast y (h y), w - h y⟫ ≤ -rate · ‖w - h y‖²`.
  have hc : ⟪M.fast y w - M.fast y (M.h y), w - M.h y⟫ ≤ -M.rate * ‖w - M.h y‖ ^ 2 :=
    M.contraction y w
  rw [hw, M.equil_stat y, sub_zero, inner_zero_left] at hc
  -- So `0 ≤ -rate · ‖w - h y‖²`, hence with `rate > 0` the norm is `0`.
  have hsq : ‖w - M.h y‖ ^ 2 ≤ 0 := by nlinarith [M.rate_pos, sq_nonneg ‖w - M.h y‖]
  have hnorm : ‖w - M.h y‖ = 0 := by nlinarith [sq_nonneg ‖w - M.h y‖, norm_nonneg (w - M.h y)]
  have : w - M.h y = 0 := norm_eq_zero.mp hnorm
  linear_combination (norm := module) this

/-- The fibre equilibrium set `{w | fast y w = 0}` is exactly the singleton `{h y}`. -/
theorem fiber_eq_singleton (y : Y) : {w : E | M.fast y w = 0} = {M.h y} := by
  ext w
  constructor
  · intro hw; exact M.eq_of_stationary hw
  · intro hw; simp only [mem_singleton_iff] at hw; subst hw; exact M.equil_stat y

/-- **Layer invariance.** The constant curve sitting at the slow-manifold point `h y` is an
integral curve of the frozen fast field `fast y`: the graph `{(y, h y)}` is invariant under the
layer (`ε = 0`) flow. -/
theorem const_isIntegralCurve (y : Y) :
    ∀ t, HasDerivAt (fun _ : ℝ => M.h y) (M.fast y ((fun _ : ℝ => M.h y) t)) t := by
  intro t
  simp only [M.equil_stat y]
  exact hasDerivAt_const t (M.h y)

/-- The slow-manifold graph is invariant under the layer flow: if a fast integral curve over a
frozen `y` starts on the manifold (`z 0 = h y`), it stays on the manifold for all forward time. -/
theorem invariant_graph {y : Y} {z : ℝ → E} (hz : ∀ t, HasDerivAt z (M.fast y (z t)) t)
    (h0 : z 0 = M.h y) : ∀ t, 0 ≤ t → z t = M.h y := by
  intro t ht
  have hb := M.attraction_bound hz t ht
  rw [h0, sub_self, norm_zero, zero_mul] at hb
  have : ‖z t - M.h y‖ = 0 := le_antisymm hb (norm_nonneg _)
  have : z t - M.h y = 0 := norm_eq_zero.mp this
  linear_combination (norm := module) this

end SlowManifold

end ODE

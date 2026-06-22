import Mathlib.Dynamics.Flow
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Monotone dynamical systems: the order-preserving and scalar-comparison fragment

This module formalizes the foundational, infrastructure-light part of the theory of
**monotone dynamical systems** (Hirsch, Smith; Angeli–Sontag for the I/O variant).

## Order-preserving semiflows

A forward semiflow `ϕ : Flow ℝ≥0 α` on an ordered space is **monotone** when each
time-`t` map `ϕ t` is order preserving. `IsMonotoneFlow` packages this. The two structural
consequences proved here are that orbits started from ordered points stay ordered for all
forward time (`IsMonotoneFlow.le`) and that an order interval bracketed by two equilibria is
forward invariant (`IsMonotoneFlow.forwardInvariant_Icc`). The identity flow witnesses that
the predicate is non-vacuous.

## Scalar comparison principle

The differential-inequality engine in one dimension: if `u 0 ≤ v 0` and the right derivative
of `u` is dominated by that of `v` on `[0, T)`, then `u ≤ v` on `[0, T]`
(`scalar_comparison`). The autonomous-field corollary `traj_le` matches the
`HasDerivAt`/field idiom of `CRNT/Dynamics/FlowConstruction.lean`: trajectories of two scalar
fields stay ordered when the dominating field dominates pointwise.

## Scope

This is the scalar / order-preserving fragment of monotone-systems theory. The vector
**Kamke–Müller comparison principle** (componentwise comparison for cooperative vector fields)
and the **Angeli–Sontag** input/output monotone-systems theory are out of scope: Mathlib lacks
the supporting infrastructure (cooperative-field flows, quasimonotone vector ODE comparison).
The content is chemistry-free, upstream-style dynamical-systems material, in the spirit of
`CRNT/Dynamics/{LaSalle, FlowConstruction}.lean`.

This module is **stable** and `sorry`-free. Depends on: `Mathlib.Dynamics.Flow`,
`Mathlib.Topology.Instances.NNReal.Lemmas`, `Mathlib.Analysis.Calculus.MeanValue`.
-/

open Set
open scoped NNReal

namespace CRNT.Monotone

section OrderPreserving

variable {α : Type*} [TopologicalSpace α] [Preorder α]

/-- A forward semiflow `ϕ : Flow ℝ≥0 α` is **monotone** (order preserving) when each
time-`t` map `ϕ t` is monotone. -/
def IsMonotoneFlow (ϕ : Flow ℝ≥0 α) : Prop := ∀ t : ℝ≥0, Monotone (ϕ t)

/-- Orbits of a monotone semiflow started from ordered points stay ordered for all
forward time. -/
theorem IsMonotoneFlow.le {ϕ : Flow ℝ≥0 α} (h : IsMonotoneFlow ϕ) {x y : α}
    (hxy : x ≤ y) (t : ℝ≥0) : ϕ t x ≤ ϕ t y :=
  h t hxy

/-- The order interval `Icc a b` bracketed by two equilibria `a` and `b` is forward
invariant under a monotone semiflow. -/
theorem IsMonotoneFlow.forwardInvariant_Icc {ϕ : Flow ℝ≥0 α} (h : IsMonotoneFlow ϕ)
    {a b : α} (ha : ∀ t : ℝ≥0, ϕ t a = a) (hb : ∀ t : ℝ≥0, ϕ t b = b) :
    IsForwardInvariant ϕ (Set.Icc a b) := by
  intro t _ z hz
  rw [mem_Icc] at hz ⊢
  exact ⟨by rw [← ha t]; exact h.le hz.1 t, by rw [← hb t]; exact h.le hz.2 t⟩

/-- The identity flow is monotone, witnessing that `IsMonotoneFlow` is non-vacuous. -/
theorem isMonotoneFlow_id : IsMonotoneFlow (Flow.id ℝ≥0 α) :=
  fun _ => monotone_id

end OrderPreserving

section ScalarComparison

/-- **Scalar comparison principle.** If `u 0 ≤ v 0` and the right derivative of `u` is
dominated by that of `v` throughout `[0, T)`, then `u ≤ v` on all of `[0, T]`. -/
theorem scalar_comparison {u v u' v' : ℝ → ℝ} {T : ℝ}
    (hu : ContinuousOn u (Set.Icc 0 T)) (hv : ContinuousOn v (Set.Icc 0 T))
    (hud : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt u (u' t) (Set.Ici t) t)
    (hvd : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt v (v' t) (Set.Ici t) t)
    (h0 : u 0 ≤ v 0) (hbound : ∀ t ∈ Set.Ico 0 T, u' t ≤ v' t) :
    ∀ t ∈ Set.Icc 0 T, u t ≤ v t :=
  fun _ ht => image_le_of_deriv_right_le_deriv_boundary hu hud h0 hv hvd hbound ht

/-- **Comparison of scalar trajectories in autonomous-field form.** Two scalar trajectories
`u`, `v` differentiable everywhere with field values `f`, `g` stay ordered on `[0, T]` provided
they start ordered and the dominating field dominates pointwise on `[0, T)`. This matches the
`HasDerivAt`/field idiom of `CRNT/Dynamics/FlowConstruction.lean`. -/
theorem traj_le {f g u v : ℝ → ℝ} {T : ℝ}
    (hu : ∀ t : ℝ, HasDerivAt u (f t) t) (hv : ∀ t : ℝ, HasDerivAt v (g t) t)
    (h0 : u 0 ≤ v 0) (hbound : ∀ t ∈ Set.Ico 0 T, f t ≤ g t) :
    ∀ t ∈ Set.Icc 0 T, u t ≤ v t :=
  scalar_comparison
    (continuous_iff_continuousAt.2 (fun t => (hu t).continuousAt)).continuousOn
    (continuous_iff_continuousAt.2 (fun t => (hv t).continuousAt)).continuousOn
    (fun t _ => (hu t).hasDerivWithinAt) (fun t _ => (hv t).hasDerivWithinAt)
    h0 hbound

end ScalarComparison

end CRNT.Monotone

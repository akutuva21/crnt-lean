import CRNT.Dynamics.FenichelComovingManifold

/-!
# The Fenichel reduction principle as a flow conjugacy

`CRNT.Dynamics.FenichelComovingManifold` builds a genuinely non-constant slow manifold `graphSet σ`
invariant under the full continuous semiflow `comovingContractFlow B rate σ` at every time. This
module supplies the payoff of that geometry: the **reduction principle**. The dynamics of the full
`(Y × E)`-dimensional system restricted to the invariant slow manifold is governed entirely by the
lower-dimensional **slow** base flow `B.slowFlow` — slow-manifold reduction collapses a coupled
fast/slow problem to its slow subsystem.

## Parametrizing the manifold by the base

The slow manifold `graphSet σ = {(y, σ y)}` is the image of the base under the inclusion
`incl σ y = (y, σ y)`, with projection `π = Prod.fst` reading off the base coordinate. `π` is a left
inverse of `incl` (`reductionProj_incl`), and the image of `incl` is exactly the manifold
(`incl_mem_graphSet`, `range_incl_eq_graphSet`). The pair `(incl σ, π)` identifies the base `Y` with
the slow manifold `M = graphSet σ`.

## The reduction conjugacy

On the manifold the fast fibre is slaved to `σ` of the moved base, so the full flow's base component
*is* the slow flow and its fibre component stays pinned to the section. `incl_comovingContractFlow`
computes the restricted full flow exactly:
`(comovingContractFlow B rate σ).toFun t (incl σ y) = incl σ (B.slowFlow.toFun t y)`.
Projecting gives the conjugacy `π ∘ Φ|_M = slowFlow ∘ π`
(`slowManifold_reduction_conjugacy`): the projection intertwines the restricted full flow with the
slow base flow. This is the reduction — the full dynamics on `M`, read through `incl`/`π`, is the
reduced base dynamics `slowFlow`.

## Transfer of qualitative dynamics

Conjugacy lifts the base dynamics to the full system. A base equilibrium lifts to a full equilibrium
(`equilibrium_lift_of_baseEquilibrium`): if `slowFlow.toFun t y₀ = y₀` for all `t`, then `incl σ y₀`
is fixed by the full flow. A base-flow-invariant set `A ⊆ Y` lifts to the invariant set `incl σ '' A`
of the full flow (`invariantSet_lift_of_baseInvariant`): the full flow's orbits through the lifted set
project to base orbits inside `A`, so they stay on the lifted set.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations":
the reduction principle states that the flow on the persisted slow manifold is governed by the slow
vector field. Here that flow is conjugate, via the base parametrization `incl`/`π`, to the slow base
flow, turning a `(dim Y + dim E)`-dimensional problem into a `dim Y`-dimensional one.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.FenichelComovingManifold`.
-/

open Function Set
open scoped NNReal

namespace ODE

section ReductionParametrization

variable {Y : Type*} {E : Type*}

/-- **The base inclusion onto the slow manifold.** `incl σ y = (y, σ y)` carries a base point to the
point of `graphSet σ` over it. It parametrizes the slow manifold by the base. -/
def incl (σ : Y → E) : Y → Y × E := fun y => (y, σ y)

/-- **The reduction projection.** `reductionProj = Prod.fst` reads off the base coordinate of a point
of the product space, projecting the slow manifold back onto the base. -/
def reductionProj : Y × E → Y := Prod.fst

@[simp] theorem incl_apply (σ : Y → E) (y : Y) : incl σ y = (y, σ y) := rfl

@[simp] theorem reductionProj_apply (p : Y × E) : reductionProj p = p.1 := rfl

/-- **The projection is a left inverse of the inclusion.** `reductionProj (incl σ y) = y`: reading
off the base coordinate of `(y, σ y)` returns `y`. The base parametrizes the manifold. -/
theorem reductionProj_incl (σ : Y → E) : LeftInverse (reductionProj (Y := Y) (E := E)) (incl σ) :=
  fun _ => rfl

/-- A point `incl σ y = (y, σ y)` lies on the slow manifold `graphSet σ`. -/
theorem incl_mem_graphSet (σ : Y → E) (y : Y) : incl σ y ∈ graphSet σ := rfl

/-- **The inclusion's image is exactly the slow manifold.** `incl σ '' univ = graphSet σ`: every
point of the manifold is `(y, σ y)` for its own base coordinate `y`, and conversely. -/
theorem image_incl_eq_graphSet (σ : Y → E) : incl σ '' univ = graphSet σ := by
  ext p
  simp only [image_univ, mem_range, mem_graphSet, incl]
  constructor
  · rintro ⟨y, rfl⟩; rfl
  · intro hp; exact ⟨p.1, by rw [← hp]⟩

/-- The range of the inclusion is the slow manifold: `range (incl σ) = graphSet σ`. -/
theorem range_incl_eq_graphSet (σ : Y → E) : range (incl σ) = graphSet σ := by
  rw [← image_univ, image_incl_eq_graphSet]

end ReductionParametrization

section ReductionConjugacy

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **The full flow on the slow manifold is the base flow lifted.** Starting on the manifold at
`incl σ y = (y, σ y)`, the running difference `z - σ y` vanishes, so the comoving-contract flow
carries the point to `(slowFlow t y, σ (slowFlow t y)) = incl σ (slowFlow t y)`: the fibre stays
pinned to the section read at the moved base point. The restricted full flow is the inclusion of the
slow flow. -/
theorem incl_comovingContractFlow (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ) (σ : Y → E)
    (hσcont : Continuous σ) (t : ℝ≥0) (y : Y) :
    (comovingContractFlow B rate σ hσcont).toFun t (incl σ y)
      = incl σ (B.slowFlow.toFun t y) := by
  rw [comovingContractFlow_toFun, incl, incl]
  simp

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **The reduction conjugacy: `π ∘ Φ|_M = slowFlow ∘ π`.** The projection intertwines the restricted
full flow on the slow manifold with the slow base flow:
`reductionProj ((comovingContractFlow B rate σ).toFun t (incl σ y)) = B.slowFlow.toFun t y` for every
`t` and `y`. This is the reduction principle — the full dynamics on the slow manifold, read through
the base parametrization `incl`/`π`, *is* the reduced base dynamics `slowFlow`, collapsing the coupled
fast/slow flow to the lower-dimensional slow subsystem. -/
theorem slowManifold_reduction_conjugacy (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ) (σ : Y → E)
    (hσcont : Continuous σ) (t : ℝ≥0) (y : Y) :
    reductionProj ((comovingContractFlow B rate σ hσcont).toFun t (incl σ y))
      = B.slowFlow.toFun t y := by
  rw [incl_comovingContractFlow, reductionProj, incl]

end ReductionConjugacy

section ReductionTransfer

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **Base equilibria lift to full equilibria.** If `y₀` is an equilibrium of the slow base flow —
`B.slowFlow.toFun t y₀ = y₀` for every `t` — then its lift `incl σ y₀` is an equilibrium of the full
comoving-contract flow: `(comovingContractFlow B rate σ).toFun t (incl σ y₀) = incl σ y₀`. The
conjugacy transports the base steady state up to the slow manifold. -/
theorem equilibrium_lift_of_baseEquilibrium (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ) (σ : Y → E)
    (hσcont : Continuous σ) {y₀ : Y} (hy₀ : ∀ t : ℝ≥0, B.slowFlow.toFun t y₀ = y₀) (t : ℝ≥0) :
    (comovingContractFlow B rate σ hσcont).toFun t (incl σ y₀) = incl σ y₀ := by
  rw [incl_comovingContractFlow, hy₀ t]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **Base-invariant sets lift to invariant sets of the full flow.** If a base set `A ⊆ Y` is
forward-invariant under the slow base flow, then its lift `incl σ '' A` is invariant under the full
comoving-contract flow. A point of the lift is `incl σ y` with `y ∈ A`; it flows to
`incl σ (slowFlow t y)`, whose base coordinate `slowFlow t y` stays in `A`, so the image is again on
the lift. The conjugacy transports qualitative base structure up to the slow manifold. -/
theorem invariantSet_lift_of_baseInvariant (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ) (σ : Y → E)
    (hσcont : Continuous σ) {A : Set Y} (hA : IsInvariant B.slowFlow.toFun A) :
    IsInvariant (comovingContractFlow B rate σ hσcont).toFun (incl σ '' A) := by
  intro t p hp
  obtain ⟨y, hyA, rfl⟩ := hp
  rw [incl_comovingContractFlow]
  exact mem_image_of_mem _ (hA t hyA)

end ReductionTransfer

section AffineReductionInstance

/-- **The reduction conjugacy over the affine base.** Instantiating `slowManifold_reduction_conjugacy`
with the second-coordinate comoving section over the affine base on `ℝ × ℝ` with drift `(1, 0)`: the
projection intertwines the full flow restricted to the slow manifold `{((y₁, y₂), y₂)}` with the
affine slow flow `y ↦ y + t·(1, 0)`. -/
theorem affineReduction_conjugacy (rate : ℝ) (t : ℝ≥0) (y : ℝ × ℝ) :
    reductionProj
        ((comovingContractFlow (affineAllTimeBase ((1, 0) : ℝ × ℝ)) rate (fun y : ℝ × ℝ => y.2)
            continuous_snd_section).toFun t (incl (fun y : ℝ × ℝ => y.2) y))
      = (affineAllTimeBase ((1, 0) : ℝ × ℝ)).slowFlow.toFun t y :=
  slowManifold_reduction_conjugacy (affineAllTimeBase ((1, 0) : ℝ × ℝ)) rate
    (fun y : ℝ × ℝ => y.2) continuous_snd_section t y

end AffineReductionInstance

end ODE

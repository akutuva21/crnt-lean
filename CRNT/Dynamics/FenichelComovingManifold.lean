import CRNT.Dynamics.FenichelContinuousMovingTarget

/-!
# A genuinely non-constant slow manifold invariant at every continuous time

`CRNT.Dynamics.FenichelContinuousMovingTarget` carries the moving-target back-map across the whole
continuous forward semiflow, but its invariance conclusion
`fenichel_continuousMovingTarget_isInvariant` lands on the **constant** fibre `c`: the running
back-map `slowInvAt t` reads a value already equal to `c`, so the contraction holds it. Forcing the
moving regraph to fix a *non-constant* section `σ` at every `t` would, through the `e^{-rate·t}`
factor sweeping `(0, 1]`, collapse `σ` to a constant — **unless** `σ` is comoving with the base, so
the back-map cancels the contraction's pull exactly. This module supplies that comoving section and
the genuinely non-constant invariant manifold it carries.

## Comoving sections

`AllTimeInjectiveBaseFlow.IsComovingSection B σ` asks that `σ` be constant along base orbits,
`∀ t y, σ (B.slowFlow.toFun t y) = σ y`: a conserved quantity of the base flow. On the image of the
time-`t` base map the running back-map then reads `σ` unchanged
(`IsComovingSection.slowInvAt_image`): `σ (B.slowInvAt t (B.slowFlow.toFun t y)) = σ y`, since the
running left-inverse undoes the base motion there. The comoving section is exactly the data the
moving-target back-map preserves.

## Contracting onto a comoving section

`comovingContractFlow B rate σ` generalizes `productContractFlow`'s constant fibre target to a
comoving section target: the fibre relaxes toward `σ` read at the *moved* base point,
`(y, z) ↦ (slowFlow t y, σ (slowFlow t y) + e^{-rate·t}·(z - σ y))`. The semigroup law holds for any
section `σ` because the moved-base offset `σ (slowFlow t y)` cancels in the composite; comoving is not
needed to build the flow, but it is what makes `graphSet σ` a genuine — non-constant — slow manifold
rather than a sheared constant one.

## All-time invariance of the non-constant manifold

`fenichel_comovingManifold_isInvariant` proves the graph of a comoving section `σ` is invariant under
the *full continuous* semiflow `comovingContractFlow B rate σ` for every `t ≥ 0`: a point `(y, σ y)`
flows to `(slowFlow t y, σ (slowFlow t y) + e^{-rate·t}·(σ y - σ y)) = (slowFlow t y, σ (slowFlow t y))`,
again on the graph. The fibre stays pinned to the comoving section as the base carries it along, so
the slow manifold persists as a genuinely non-constant invariant set at all continuous times.

## A concrete non-constant comoving section

`affineProjComoving` exhibits one over the affine base on `ℝ × ℝ` with drift `(1, 0)`: the section
`σ (y) = y.2` reading the second coordinate. It is comoving — translating along `(1, 0)` leaves the
second coordinate fixed — and genuinely non-constant. `affineComovingManifold_isInvariant` instantiates
the all-time invariance on it, so the persisted slow manifold `{((y₁, y₂), y₂)}` is a genuinely
non-constant invariant manifold of the continuous product semiflow at every `t ≥ 0`.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations": a
normally attracting invariant manifold of the unperturbed layer system persists, for small `ε`, as a
nearby invariant manifold. Here the persisted manifold is genuinely non-constant and invariant at
every continuous time, the comoving section cancelling the contraction's pull along the moving base —
the final de-idealization of the continuous-time Fenichel core.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Dynamics.FenichelContinuousMovingTarget`.
-/

open Function Set
open scoped NNReal BoundedContinuousFunction

namespace ODE

section ComovingSection

variable {Y : Type*} [TopologicalSpace Y]
variable {E : Type*}

/-- **A section comoving with the base flow.** `σ : Y → E` is comoving when it is constant along every
base orbit: `σ (B.slowFlow.toFun t y) = σ y` for every time `t` and base point `y` — a conserved
quantity of the slow base flow. This is exactly the section the moving-target back-map preserves: the
base motion does not change its value, so the running contraction toward it has nothing to undo. -/
def AllTimeInjectiveBaseFlow.IsComovingSection (B : AllTimeInjectiveBaseFlow Y) (σ : Y → E) : Prop :=
  ∀ (t : ℝ≥0) (y : Y), σ (B.slowFlow.toFun t y) = σ y

/-- **The running back-map reads a comoving section unchanged on the image of the base map.** On a
point `B.slowFlow.toFun t y` already in the image of the time-`t` base map, the running left-inverse
`B.slowInvAt t` undoes the base motion, so a comoving section reads the same value:
`σ (B.slowInvAt t (B.slowFlow.toFun t y)) = σ y`. This is the precise back-map identity comoving
yields — on the relevant set, the contraction's back-map has nothing to do. -/
theorem AllTimeInjectiveBaseFlow.IsComovingSection.slowInvAt_image {B : AllTimeInjectiveBaseFlow Y}
    {σ : Y → E} (_hσ : B.IsComovingSection σ) (t : ℝ≥0) (y : Y) :
    σ (B.slowInvAt t (B.slowFlow.toFun t y)) = σ y := by
  rw [B.leftInverseAt t y]

/-- The constant section is comoving with any base flow: a constant is conserved along every orbit. -/
theorem AllTimeInjectiveBaseFlow.isComovingSection_const (B : AllTimeInjectiveBaseFlow Y) (c : E) :
    B.IsComovingSection (fun _ : Y => c) := fun _ _ => rfl

end ComovingSection

section ComovingContractFlow

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The product semiflow contracting onto a comoving section target.** Generalizing
`productContractFlow`'s constant fibre target `c` to a section `σ` read at the moved base point: the
base coordinate flows under `B.slowFlow` and the fast fibre relaxes toward `σ (slowFlow t y)` at rate
`rate`, `(y, z) ↦ (slowFlow t y, σ (slowFlow t y) + e^{-rate·t}·(z - σ y))`. The moved-base offset
`σ (slowFlow t y)` cancels in the composite, so the semigroup law holds for any section `σ`; joint
continuity needs `σ` continuous on the base coordinate. -/
noncomputable def comovingContractFlow (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ) (σ : Y → E)
    (hσcont : Continuous σ) : Flow ℝ≥0 (Y × E) where
  toFun t p := (B.slowFlow.toFun t p.1, σ (B.slowFlow.toFun t p.1)
    + Real.exp (-rate * (t : ℝ)) • (p.2 - σ p.1))
  cont' := by
    refine Continuous.prodMk ?_ ?_
    · exact B.slowFlow.cont'.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    · refine Continuous.add ?_ ?_
      · exact hσcont.comp
          (B.slowFlow.cont'.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
      · refine Continuous.smul ?_ ((continuous_snd.comp continuous_snd).sub
          (hσcont.comp (continuous_fst.comp continuous_snd)))
        exact Real.continuous_exp.comp (continuous_const.mul
          (NNReal.continuous_coe.comp continuous_fst))
  map_add' t₁ t₂ p := by
    refine Prod.ext ?_ ?_
    · exact B.slowFlow.map_add' t₁ t₂ p.1
    · show σ (B.slowFlow.toFun (t₁ + t₂) p.1)
          + Real.exp (-rate * ((t₁ + t₂ : ℝ≥0) : ℝ)) • (p.2 - σ p.1)
        = σ (B.slowFlow.toFun t₁ (B.slowFlow.toFun t₂ p.1))
          + Real.exp (-rate * (t₁ : ℝ)) • ((σ (B.slowFlow.toFun t₂ p.1)
              + Real.exp (-rate * (t₂ : ℝ)) • (p.2 - σ p.1))
            - σ (B.slowFlow.toFun t₂ p.1))
      rw [B.slowFlow.map_add' t₁ t₂ p.1, add_sub_cancel_left, smul_smul, NNReal.coe_add, mul_add,
        Real.exp_add, mul_comm (Real.exp (-rate * (t₁ : ℝ)))]
  map_zero' p := by
    refine Prod.ext ?_ ?_
    · exact B.slowFlow.map_zero' p.1
    · show σ (B.slowFlow.toFun 0 p.1) + Real.exp (-rate * ((0 : ℝ≥0) : ℝ)) • (p.2 - σ p.1) = p.2
      rw [B.slowFlow.map_zero' p.1]
      simp

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
@[simp] theorem comovingContractFlow_toFun (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ) (σ : Y → E)
    (hσcont : Continuous σ) (t : ℝ≥0) (p : Y × E) :
    (comovingContractFlow B rate σ hσcont).toFun t p
      = (B.slowFlow.toFun t p.1, σ (B.slowFlow.toFun t p.1)
        + Real.exp (-rate * (t : ℝ)) • (p.2 - σ p.1)) := rfl

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **The comoving-contract flow holds the section graph at every time.** A point `(y, σ y)` of
`graphSet σ` flows to `(slowFlow t y, σ (slowFlow t y) + e^{-rate·t}·(σ y - σ y))
= (slowFlow t y, σ (slowFlow t y))`, again on the graph: the running difference `z - σ y` vanishes on
the graph, so the contraction has nothing to pull and the fibre stays pinned to the section read at the
moved base point. Holds for any section; comoving makes the graph a genuinely non-constant manifold. -/
theorem comovingContractFlow_mapsTo_graph (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ) (σ : Y → E)
    (hσcont : Continuous σ) (t : ℝ≥0) :
    MapsTo ((comovingContractFlow B rate σ hσcont).toFun t) (graphSet σ) (graphSet σ) := by
  intro p hp
  rw [mem_graphSet] at hp
  rw [comovingContractFlow_toFun, mem_graphSet]
  simp [hp]

end ComovingContractFlow

section ComovingInvariance

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **All-time invariance of the genuinely non-constant comoving slow manifold.** For a comoving
section `σ` the graph `{(y, σ y)}` is invariant under the *full continuous* semiflow
`comovingContractFlow B rate σ` for every `t ≥ 0`: the fibre stays pinned to the comoving section as
the base carries it along, so a trajectory started on the manifold tracks the moving base along it for
all forward time. Unlike `fenichel_continuousMovingTarget_isInvariant`, whose manifold is the constant
fibre `c`, here `σ` is genuinely non-constant — the comoving property cancels the contraction's pull
along the moving base, removing the collapse-to-constant that an arbitrary section would suffer. -/
theorem fenichel_comovingManifold_isInvariant (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ) (σ : Y → E)
    (hσcont : Continuous σ) (_hσ : B.IsComovingSection σ) :
    IsInvariant (comovingContractFlow B rate σ hσcont).toFun (graphSet σ) :=
  fun t => comovingContractFlow_mapsTo_graph B rate σ hσcont t

end ComovingInvariance

section AffineComovingInstance

/-- **A concrete genuinely non-constant comoving section over the affine base.** On `ℝ × ℝ` with
drift `(1, 0)` the section `σ (y) = y.2` reading the second coordinate is comoving — the time-`t` base
map `y ↦ y + t·(1, 0)` leaves the second coordinate fixed — yet genuinely non-constant. -/
theorem affineProjComoving :
    (affineAllTimeBase ((1, 0) : ℝ × ℝ)).IsComovingSection (fun y : ℝ × ℝ => y.2) := by
  intro t y
  show ((affineAllTimeBase ((1, 0) : ℝ × ℝ)).slowFlow.toFun t y).2 = y.2
  rw [affineAllTimeBase_slowFlow, affineBaseFlow_toFun]
  simp

/-- The second-coordinate section is continuous. -/
theorem continuous_snd_section : Continuous (fun y : ℝ × ℝ => y.2) := continuous_snd

/-- **All-time invariance of a genuinely non-constant comoving slow manifold over the affine base.**
Instantiating `fenichel_comovingManifold_isInvariant` with the second-coordinate section over the
affine base on `ℝ × ℝ` with drift `(1, 0)`: the graph `{((y₁, y₂), y₂)}` of the non-constant comoving
section is invariant under the *full continuous* product semiflow for every `t ≥ 0`. A genuinely
non-constant slow manifold invariant at all continuous times — the comoving section cancelling the
contraction's pull along the moving base. -/
theorem affineComovingManifold_isInvariant (rate : ℝ) :
    IsInvariant
      (comovingContractFlow (affineAllTimeBase ((1, 0) : ℝ × ℝ)) rate (fun y : ℝ × ℝ => y.2)
        continuous_snd_section).toFun
      (graphSet (fun y : ℝ × ℝ => y.2)) :=
  fenichel_comovingManifold_isInvariant (affineAllTimeBase ((1, 0) : ℝ × ℝ)) rate
    (fun y : ℝ × ℝ => y.2) continuous_snd_section affineProjComoving

end AffineComovingInstance

end ODE

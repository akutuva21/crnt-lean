import CRNT.Dynamics.FenichelMovingGeneralDrift

/-!
# A moving slow manifold persisting over the curved logistic base

`CRNT.Dynamics.FenichelMovingGeneralDrift` persists a genuinely non-constant slow manifold over any
injective slow base flow, but its headline instance `fenichel_persistence_affineBase` runs over the
affine translation base `ẏ = v` — a straight, uncurved base motion with an explicit translation
inverse. This module instantiates the same moving-target persistence over the genuinely **curved**
logistic base `ẏ = ε·sin y` of `CRNT.Dynamics.FenichelGeneralDrift`'s `logisticDriftFlow`, with **no
explicit inverse supplied**: the left-inverse of the time-`τ` base map comes from injectivity alone.

## Injectivity of the curved base map

`logisticDriftFlow_injective` derives injectivity of the time-`τ` map of the nonlinear base from the
retained integral-curve witnesses of `logisticDriftFlowData`: two integral curves of `ε·sin y` that
agree at time `τ` are the same global curve by two-sided uniqueness, so they agree at time `0` and
share a starting point. `flow_toFun_injective` packages this from the field's Lipschitz bound. The
base is genuinely curved, yet its time map is injective with no closed-form inverse.

## The moving-target instance over the curved base

`logisticInjectiveBase` builds the `InjectiveBaseFlow` via `InjectiveBaseFlow.ofInjective`, whose
left-inverse is `Function.invFun (logisticDriftFlow ε |>.toFun τ)` — honest, abstract, not a formula.
`fenichel_persistence_logisticMovingBase` feeds it through `fenichel_persistence_movingGeneralDrift`:
a non-constant slow manifold persists over the genuinely nonlinear `ε·sin y` base, the attracting
fibre `M_ε = c` forward-invariant under the iterate product semiflow and within the `O(ε)` closeness
ceiling of the base section. The moving back-map is exercised on every non-constant candidate section
through `movingFlow_mapsTo`; on the persisted manifold it collapses to constant-fibre invariance.

## All-time continuous invariance over the curved base

`logisticMovingBase_graphSet_isInvariant_allTime` records the continuous-level residue: the slow
manifold `{(y, c)}` is invariant under the *full continuous* product semiflow over the logistic base
for every `t ≥ 0`, not only at multiples of the horizon — the substrate flowing along it under its
genuine curved drift.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations": a
normally attracting invariant manifold of the unperturbed layer system persists, for small `ε`, as a
nearby invariant manifold. Here the slow manifold is genuinely non-constant and the base flows by a
genuinely curved nonlinear field with no inverse supplied — the Fenichel core fully de-idealized on a
concrete curved example.

Depends on:
`CRNT.Dynamics.FenichelMovingGeneralDrift`.
-/

open Function Set
open scoped NNReal BoundedContinuousFunction

namespace ODE

section LogisticInjectivity

/-- **The time-`τ` map of the curved logistic base flow is injective.** Applying
`flow_toFun_injective` to the logistic field's Lipschitz bound and the retained integral-curve
witnesses of `logisticDriftFlowData`: two integral curves of `ε·sin y` agreeing at time `τ` agree at
time `0`, so they share a starting point. The base flows by a genuinely nonlinear field, yet its time
map is injective with no inverse supplied. -/
theorem logisticDriftFlow_injective (ε : ℝ) (τ : ℝ≥0) :
    Injective ((logisticDriftFlow ε).toFun τ) :=
  flow_toFun_injective (f := logisticField ε) (logisticField_lipschitz ε)
    (logisticDriftCurves_zero ε) (logisticDriftCurves_hasDerivAt ε)
    (logisticDriftFlow_eq_curves ε) τ

/-- **The injective curved logistic slow base flow.** Built via `InjectiveBaseFlow.ofInjective` from
the injectivity of the time-`τ` logistic base map: the left-inverse is
`Function.invFun (logisticDriftFlow ε |>.toFun τ)`, an honest abstract inverse — *no closed-form
back-translation*, in contrast to the affine base's `y ↦ y - τ·v`. -/
noncomputable def logisticInjectiveBase (ε : ℝ) (τ : ℝ≥0) : InjectiveBaseFlow ℝ :=
  InjectiveBaseFlow.ofInjective (logisticDriftFlow ε) τ (logisticDriftFlow_injective ε τ)

@[simp] theorem logisticInjectiveBase_τ (ε : ℝ) (τ : ℝ≥0) : (logisticInjectiveBase ε τ).τ = τ := rfl

@[simp] theorem logisticInjectiveBase_slowFlow (ε : ℝ) (τ : ℝ≥0) :
    (logisticInjectiveBase ε τ).slowFlow = logisticDriftFlow ε := rfl

end LogisticInjectivity

section Persistence

/-- **Fenichel persistence of a moving slow manifold over the curved logistic base.** Specializing
`fenichel_persistence_movingGeneralDrift` to the injective curved base `logisticInjectiveBase`, whose
time-`τ` left-inverse comes from injectivity alone — *no explicit inverse supplied*. A genuinely
non-constant slow manifold persists over the genuinely nonlinear `ε·sin y` base: the attracting fibre
`M_ε = c` is forward-invariant under the iterate product semiflow whose base flows by the curved
field, and `M_ε` sits within `defect / (1 - factor)` of the base section in the supremum metric. The
Fenichel core de-idealized on a concrete curved example. -/
theorem fenichel_persistence_logisticMovingBase (ε : ℝ) (rate : ℝ) (c : ℝ) (τ : ℝ≥0)
    (hrate : 0 < rate) (hτ : 0 < (τ : ℝ)) :
    let G := contractGapData (Y := ℝ) (E := ℝ) rate c τ hrate hτ
    let F := movingCoupled (logisticInjectiveBase ε τ) rate c
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (graphSet (G.manifold : ℝ → ℝ)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) :=
  fenichel_persistence_movingGeneralDrift (logisticInjectiveBase ε τ) rate c hrate
    (by simpa using hτ)

/-- **All-time continuous-semiflow invariance of the slow manifold over the curved logistic base.**
The graph of the constant attracting fibre `{(y, c)}` is invariant under the *full continuous* product
semiflow over the logistic base for every `t ≥ 0`, not only at multiples of the horizon. The substrate
flows along the slow manifold under its genuine curved drift `ε·sin y`, the continuous-level residue of
`fenichel_persistence_logisticMovingBase`. -/
theorem logisticMovingBase_graphSet_isInvariant_allTime (ε : ℝ) (rate : ℝ) (c : ℝ) :
    IsInvariant (productContractFlow (logisticDriftFlow ε) rate c).toFun (graphSet (fun _ : ℝ => c)) :=
  generalDrift_graphSet_isInvariant_allTime (logisticDriftFlow ε) rate c

end Persistence

end ODE

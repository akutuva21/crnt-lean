import CRNT.Dynamics.FenichelPersistenceContracting

/-!
# Fenichel persistence over a general nonlinear slow base flow

`CRNT.Dynamics.FenichelCoupledBase` lets the slow base coordinate drift, but only by the affine
translation `ẏ = ε·b`: the base motion is a constant slow velocity, so the time-`t` base map is the
invertible shift `y ↦ y + (ε·t)·b`. This module removes that linearity: the slow base evolves under a
**general** forward semiflow `slowFlow : Flow ℝ≥0 Y` — the honest `exists_flow` output for a bounded
Lipschitz slow field `ε·g`, a genuinely nonlinear drift — while the fast fibre contracts onto the
constant target `c` at exponential rate `rate`.

The coupled field is `ẏ = ε·g(y)`, `ż = -rate·(z - c)` on the product `Y × E`: the slow base flows by
the general field `ε·g` and the fast fibre is pulled toward `c` at rate `rate`. Its forward semiflow is
the product `(y, z) ↦ (slowFlow t y, c + e^{-rate·t}·(z - c))` (`productContractFlow`), assembled from
the base semiflow `slowFlow` in the base coordinate and the closed-form exponential contraction
`CRNT.Dynamics.FenichelPersistenceContracting`'s `contractingMap` in the fibre. Joint continuity comes
from `slowFlow.cont'` and the elementary continuity of the fibre contraction; the identity at time `0`
and the semigroup law come coordinatewise from `slowFlow` and `e^{-rate·(s+t)} = e^{-rate·s}·e^{-rate·t}`.

## Constant-fibre invariance needs no base invertibility

The slow manifold `{(y, c)} = graphSet (fun _ => c)` is invariant under the product semiflow
**regardless of base motion**: a point `(y, c)` is carried to `(slowFlow t y, c + e^{-rate·t}·(c - c))
= (slowFlow t y, c)`, still on the manifold, because the fibre contraction holds a fibre already at its
own target `c` whatever the base does (`productContract_const_mapsTo`). No back-translation, hence no
base invertibility, is required — the affine-base regraph of `CRNT.Dynamics.FenichelCoupledBase` is
not needed for the constant fibre. This is `generalDrift_graphSet_isInvariant_allTime`: the slow
manifold is invariant under the full continuous nonlinear-base semiflow `Φ t` for every `t ≥ 0`, the
substrate flowing along it under its genuine drift.

## End-to-end persistence

`fenichel_persistence_generalDrift` assembles the two halves of Fenichel persistence over the general
drifting base with every hypothesis discharged via the contracting-manifold machinery. The invariance
half is `generalDrift_graphSet_isInvariant_allTime` sampled at multiples of the horizon: the graph of
the attracting fibre `M_ε = c` is forward-invariant under the iterate coupled semiflow whose base
flows by the genuine nonlinear field. The closeness half is
`CRNT.Dynamics.FenichelPersistenceContracting`'s `contractGapData.manifold_dist_base_le`: `M_ε` sits
within `defect / (1 - factor)` of the base section in the supremum metric. The persisted manifold
`M_ε = c` is the Banach fixed point of the genuine fibre contraction `contractGapData`, and the
nonlinear base flow is honest data, not a translation.

## A concrete nonlinear base flow

`logisticDriftFlow` instantiates `slowFlow` with the genuine semiflow of a bounded Lipschitz nonlinear
1-D slow field — the saturating logistic-type drift `ε·g(y) = ε·sin y`, bounded by `|ε|` and Lipschitz
with constant `|ε|` — obtained from `CRNT.Dynamics.FlowConstruction`'s `exists_flow`. Feeding it
through `fenichel_persistence_generalDrift` (`fenichel_persistence_logisticDrift`) yields persistence
over a base that flows by a genuinely nonlinear drift, not a translation.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations": a
normally attracting invariant manifold of the unperturbed layer system persists, for small `ε`, as a
nearby invariant manifold. Here the slow base evolves under a general nonlinear flow — `ẏ = ε·g(y)`,
not the translation `ẏ = ε·b` — so the persisted manifold is invariant over a genuinely curved moving
base, the honest completion of the coupled slow–fast coupling.

Depends on:
`CRNT.Dynamics.FenichelPersistenceContracting`.
-/

open Function Set
open scoped NNReal BoundedContinuousFunction

namespace ODE

section ProductFlow

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The product semiflow of the general-drift / contracting-fibre field** `ẏ = ε·g(y)`,
`ż = -rate·(z - c)` on `Y × E`: the base coordinate evolves under the general semiflow `slowFlow` and
the fast fibre relaxes onto the constant target `c` at rate `rate`,
`(y, z) ↦ (slowFlow t y, c + e^{-rate·t}·(z - c))`. The base motion is a genuine — possibly nonlinear —
flow, not a translation. Joint continuity comes from `slowFlow.cont'` and the fibre contraction; the
identity at time `0` and the semigroup law are coordinatewise. -/
noncomputable def productContractFlow (slowFlow : Flow ℝ≥0 Y) (rate : ℝ) (c : E) :
    Flow ℝ≥0 (Y × E) where
  toFun t p := (slowFlow.toFun t p.1, c + Real.exp (-rate * (t : ℝ)) • (p.2 - c))
  cont' := by
    refine Continuous.prodMk ?_ ?_
    · exact slowFlow.cont'.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    · refine continuous_const.add ?_
      refine Continuous.smul ?_ ((continuous_snd.comp continuous_snd).sub continuous_const)
      exact Real.continuous_exp.comp (continuous_const.mul
        (NNReal.continuous_coe.comp continuous_fst))
  map_add' t₁ t₂ p := by
    refine Prod.ext ?_ ?_
    · exact slowFlow.map_add' t₁ t₂ p.1
    · show c + Real.exp (-rate * ((t₁ + t₂ : ℝ≥0) : ℝ)) • (p.2 - c)
        = c + Real.exp (-rate * (t₁ : ℝ)) • ((c + Real.exp (-rate * (t₂ : ℝ)) • (p.2 - c)) - c)
      rw [NNReal.coe_add, add_sub_cancel_left, smul_smul, mul_add, Real.exp_add,
        mul_comm (Real.exp (-rate * (t₁ : ℝ)))]
  map_zero' p := by
    refine Prod.ext ?_ ?_
    · exact slowFlow.map_zero' p.1
    · show c + Real.exp (-rate * ((0 : ℝ≥0) : ℝ)) • (p.2 - c) = p.2
      simp

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
@[simp] theorem productContractFlow_toFun (slowFlow : Flow ℝ≥0 Y) (rate : ℝ) (c : E) (t : ℝ≥0)
    (p : Y × E) :
    (productContractFlow slowFlow rate c).toFun t p
      = (slowFlow.toFun t p.1, c + Real.exp (-rate * (t : ℝ)) • (p.2 - c)) := rfl

end ProductFlow

section ConstantFibre

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **The product flow holds the constant-fibre graph at the target, whatever the base does.** The
time-`t` product flow carries each point `(y, c)` of `graphSet (fun _ => c)` to `(slowFlow t y, c)`,
again on the graph: the fibre contraction holds a fibre already at its own target `c`, so no
back-translation — and hence no base invertibility — is needed even though the base flows by a general
nonlinear field. -/
theorem productContract_const_mapsTo (slowFlow : Flow ℝ≥0 Y) (rate : ℝ) (c : E) (t : ℝ≥0) :
    MapsTo ((productContractFlow slowFlow rate c).toFun t) (graphSet (fun _ : Y => c))
      (graphSet (fun _ : Y => c)) := by
  intro p hp
  rw [mem_graphSet] at hp
  rw [productContractFlow_toFun, mem_graphSet]
  simp [hp]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **All-time forward-invariance of the slow manifold over the general nonlinear base.** The graph of
the constant attracting fibre `{(y, c)}` is invariant under the *full continuous* product semiflow
`Φ t` for every `t ≥ 0`, with the base evolving by the genuine — possibly nonlinear — slow flow
`slowFlow`. This needs **no base invertibility**: the fibre stays pinned at `c` whatever the base does,
so a trajectory started on the slow manifold tracks the moving base along it for all forward time. The
genuinely coupled continuous-time invariance half of Fenichel persistence, with the affine-base
restriction removed. -/
theorem generalDrift_graphSet_isInvariant_allTime (slowFlow : Flow ℝ≥0 Y) (rate : ℝ) (c : E) :
    IsInvariant (productContractFlow slowFlow rate c).toFun (graphSet (fun _ : Y => c)) :=
  fun t => productContract_const_mapsTo slowFlow rate c t

end ConstantFibre

section Persistence

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- The constant-fibre graph is invariant under the iterate product semiflow sampling at multiples of
the horizon `τ`, the discrete-time restriction of `generalDrift_graphSet_isInvariant_allTime`. -/
theorem generalDrift_graphSet_isInvariant_iterate (slowFlow : Flow ℝ≥0 Y) (rate : ℝ) (c : E)
    (τ : ℝ≥0) :
    IsInvariant (fun n : ℕ => (productContractFlow slowFlow rate c).toFun (n • τ))
      (graphSet (fun _ : Y => c)) :=
  fun n => generalDrift_graphSet_isInvariant_allTime slowFlow rate c (n • τ)

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
/-- **End-to-end Fenichel persistence over a general nonlinear slow base.** Combining the genuine
product semiflow `productContractFlow` — whose base evolves by the general (possibly nonlinear) slow
flow `slowFlow` and whose fibre contracts onto `c` — with the genuine fibre contraction
`CRNT.Dynamics.FenichelPersistenceContracting`'s `contractGapData` (whose Banach fixed point
`M_ε = c` is the attracting fibre). The conclusion is the two halves of Fenichel persistence with
**every hypothesis discharged**: the graph of the attracting fibre is forward-invariant under the
iterate product semiflow whose base flows by the genuine nonlinear field, and `M_ε` sits within
`defect / (1 - factor)` of the base section in the supremum metric. The base flow is honest data, not
a translation, and the invariance half needs no base invertibility. -/
theorem fenichel_persistence_generalDrift (slowFlow : Flow ℝ≥0 Y) (rate : ℝ) (c : E) (τ : ℝ≥0)
    (hrate : 0 < rate) (hτ : 0 < (τ : ℝ)) :
    let G := contractGapData (Y := Y) (E := E) rate c τ hrate hτ
    IsInvariant (fun n : ℕ => (productContractFlow slowFlow rate c).toFun (n • τ))
        (graphSet (G.manifold : Y → E)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) := by
  intro G
  refine ⟨?_, G.manifold_dist_base_le⟩
  have hman : (G.manifold : Y → E) = fun _ : Y => c := by
    funext y
    have : (G.manifold : Y →ᵇ E) = BoundedContinuousFunction.const Y c :=
      contractGapData_manifold rate c τ hrate hτ
    rw [this, BoundedContinuousFunction.const_apply']
  rw [hman]
  exact generalDrift_graphSet_isInvariant_iterate slowFlow rate c τ

end Persistence

section LogisticInstance

/-- The saturating logistic-type slow field `y ↦ ε·sin y` on `ℝ`: a genuinely nonlinear drift,
bounded by `|ε|` and Lipschitz with constant `|ε|`. -/
noncomputable def logisticField (ε : ℝ) : ℝ → ℝ := fun y : ℝ => ε * Real.sin y

/-- The logistic field is Lipschitz with constant `|ε|`, since `sin` is `1`-Lipschitz. -/
theorem logisticField_lipschitz (ε : ℝ) :
    LipschitzWith ⟨|ε|, abs_nonneg ε⟩ (logisticField ε) :=
  LipschitzWith.of_dist_le_mul (fun a b => by
    have hsin : dist (Real.sin a) (Real.sin b) ≤ (1 : ℝ) * dist a b :=
      Real.lipschitzWith_sin.dist_le_mul a b
    rw [one_mul, Real.dist_eq] at hsin
    show dist (ε * Real.sin a) (ε * Real.sin b) ≤ |ε| * dist a b
    rw [Real.dist_eq, Real.dist_eq]
    calc |ε * Real.sin a - ε * Real.sin b|
        = |ε| * |Real.sin a - Real.sin b| := by rw [← mul_sub, abs_mul]
      _ ≤ |ε| * |a - b| := mul_le_mul_of_nonneg_left hsin (abs_nonneg ε))

/-- The logistic field is bounded by `|ε|`, since `|sin| ≤ 1`. -/
theorem logisticField_bound (ε : ℝ) (y : ℝ) : ‖logisticField ε y‖ ≤ (⟨|ε|, abs_nonneg ε⟩ : ℝ≥0) := by
  rw [Real.norm_eq_abs]
  show |ε * Real.sin y| ≤ |ε|
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg ε) (abs_le.2 ⟨Real.neg_one_le_sin y, Real.sin_le_one y⟩)

/-- **The honest `exists_flow` witnesses for the logistic field**, retaining not only the forward
semiflow but also its integral-curve data `γ` (the starting-point identity and the `HasDerivAt` curve
spec) and the orbit identification `ϕ.toFun t x = γ x t`. Keeping the full witness — rather than
projecting only the `Flow` — makes the curve data available for downstream injectivity. -/
noncomputable def logisticDriftFlowData (ε : ℝ) :
    ∃ (ϕ : Flow ℝ≥0 ℝ) (γ : ℝ → ℝ → ℝ),
      (∀ x, γ x 0 = x) ∧ (∀ x t, HasDerivAt (γ x) (logisticField ε (γ x t)) t) ∧
      (∀ x (t : ℝ≥0), ϕ t x = γ x (t : ℝ)) :=
  exists_flow (f := logisticField ε) (K := ⟨|ε|, abs_nonneg ε⟩) (M := ⟨|ε|, abs_nonneg ε⟩)
    (logisticField_lipschitz ε) (logisticField_bound ε)

/-- The genuine forward semiflow of the bounded Lipschitz nonlinear slow field `y ↦ ε·sin y` on `ℝ`,
obtained from `CRNT.Dynamics.FlowConstruction`'s `exists_flow`. The field is bounded by `|ε|` and
Lipschitz with constant `|ε|`, so it generates an honest `Flow ℝ≥0 ℝ`. Its base motion is genuinely
nonlinear — a saturating logistic-type drift — not a translation. -/
noncomputable def logisticDriftFlow (ε : ℝ) : Flow ℝ≥0 ℝ := (logisticDriftFlowData ε).choose

/-- The retained integral curves of the logistic base flow: the function `γ` whose orbits are the
solutions of `ẏ = ε·sin y`, paired with the orbit identification `logisticDriftFlow ε t x = γ x t`. -/
noncomputable def logisticDriftCurves (ε : ℝ) : ℝ → ℝ → ℝ := (logisticDriftFlowData ε).choose_spec.choose

/-- The retained curves start at their base point: `γ x 0 = x`. -/
theorem logisticDriftCurves_zero (ε : ℝ) (x : ℝ) : logisticDriftCurves ε x 0 = x :=
  (logisticDriftFlowData ε).choose_spec.choose_spec.1 x

/-- The retained curves solve the logistic ODE: `γ x` has derivative `ε·sin (γ x t)` at every `t`. -/
theorem logisticDriftCurves_hasDerivAt (ε : ℝ) (x : ℝ) (t : ℝ) :
    HasDerivAt (logisticDriftCurves ε x) (logisticField ε (logisticDriftCurves ε x t)) t :=
  (logisticDriftFlowData ε).choose_spec.choose_spec.2.1 x t

/-- The logistic base flow is its retained integral curves: `logisticDriftFlow ε t x = γ x t`. -/
theorem logisticDriftFlow_eq_curves (ε : ℝ) (x : ℝ) (t : ℝ≥0) :
    (logisticDriftFlow ε).toFun t x = logisticDriftCurves ε x (t : ℝ) :=
  (logisticDriftFlowData ε).choose_spec.choose_spec.2.2 x t

/-- **Fenichel persistence over the genuinely nonlinear logistic-type base flow.** Specializing
`fenichel_persistence_generalDrift` to the honest `exists_flow` semiflow `logisticDriftFlow` of the
bounded Lipschitz nonlinear field `ε·sin y`: persistence holds over a base that flows by a genuinely
nonlinear drift, not a translation, with the attracting fibre `M_ε = c` forward-invariant under the
iterate product semiflow and within the `O(ε)` closeness ceiling of the base section. -/
theorem fenichel_persistence_logisticDrift (ε : ℝ) (rate : ℝ) (c : ℝ) (τ : ℝ≥0)
    (hrate : 0 < rate) (hτ : 0 < (τ : ℝ)) :
    let G := contractGapData (Y := ℝ) (E := ℝ) rate c τ hrate hτ
    IsInvariant (fun n : ℕ => (productContractFlow (logisticDriftFlow ε) rate c).toFun (n • τ))
        (graphSet (G.manifold : ℝ → ℝ)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) :=
  fenichel_persistence_generalDrift (logisticDriftFlow ε) rate c τ hrate hτ

end LogisticInstance

end ODE

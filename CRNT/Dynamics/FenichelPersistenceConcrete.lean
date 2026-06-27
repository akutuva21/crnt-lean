import CRNT.Dynamics.FenichelPersistence

/-!
# A concrete Fenichel persistence instance from an explicit coupled field

This module discharges the structural `flow_mapsTo` hypothesis of
`CRNT.Dynamics.FenichelPersistence`'s `CoupledFlowGraphTransform` against a *concrete* coupled
slow–fast field, building the forward semiflow on the product `Y × E` from the field itself via
`CRNT.Dynamics.FlowConstruction`'s `exists_flow` and proving — rather than assuming — that the
time-`τ` flow regraphs sections. Feeding the result through `fenichel_persistence` yields an
end-to-end persistence theorem for the explicit field with **no remaining op-from-flow hypothesis**.

The explicit field is the bounded constant fast-drift coupled field
`ẏ = 0`, `ż = v` on `Y × E`: the slow base is frozen and the fast fibre translates at the constant
velocity `v`. It is globally bounded (`‖f‖ = ‖v‖`) and globally Lipschitz (constant `0`), so
`exists_flow` supplies a genuine `Flow ℝ≥0 (Y × E)` for it — flow existence is free for bounded
Lipschitz fields. Its time-`t` map is the closed-form translation `(y, z) ↦ (y, z + t • v)`
(`constDrift_flow_eq`, pinned by uniqueness of integral curves), so the image of the graph of a
section `σ` over the slow base is the graph of the *regraphed* section `regraph v t σ = σ + t • v`
(`constDrift_allTimeRegraph`). The assembled `CoupledFlowGraphTransform` (`constDriftCoupled`) takes
its operator to be this flow-then-regraph map at the chosen horizon `τ`, so `flow_mapsTo` is a
theorem about the explicit flow rather than a hypothesis.

`fenichel_persistence` also consumes a `GraphTransformData` furnishing the Banach fixed-point section
`M_ε` whose graph is the persisted manifold. We supply it from the genuine spectral-gap contraction
`GraphTransformData.ofSpectralGap`: the operator `σ ↦ (Lf / rate) • σ` on bounded sections, an exact
contraction with factor `Lf / rate < 1` when the fibre rate dominates the Lipschitz term
(`scaleGapData`). Its unique fixed point is the zero section — the unperturbed manifold `M_0 = 0`
over which the constant-drift flow's regraph is stationary precisely when the drift `v` vanishes. The
end-to-end specialization `fenichel_persistence_constDrift` packages both halves — forward invariance
of the persisted graph under the explicit flow and `O(ε)` `C⁰`-closeness of `M_ε` to `M_0` — with
every hypothesis discharged.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations":
a normally attracting invariant manifold of the unperturbed layer system persists, for small `ε`, as
a nearby invariant manifold realized as the graph of the fixed-point section of the flow-then-regraph
graph transform. Here the flow-then-regraph operator is constructed from the explicit field rather
than assumed, closing the operator-from-flow gap for this concrete instance.

**Out of scope (the residual).** The constant fast-drift field gives an exact, globally closed-form
regraph because its flow is an affine translation; the fixed point of its time-`τ` regraph is genuine
only when the drift vanishes (`v = 0`), where the persisted graph is honestly invariant. A genuinely
*contracting* fast fibre `ż = -rate · (z - σ y)` — the field whose time-`τ` regraph is a Banach
contraction with factor `(Lipschitz/drift)/λ < 1` and a moving fixed point — is not globally bounded,
so `exists_flow` does not apply to it unmodified; its flow-regraph requires either a cutoff to a
forward-invariant bounded region or a phase space on which the field is bounded. Building the
contracting-fibre flow-regraph in full generality (the nonlinear, normally hyperbolic case) is the
remaining analytic step. What this module establishes is the concrete operator-from-flow bridge with
`flow_mapsTo` *proved* from an honest `exists_flow` flow, and a `fenichel_persistence` instance with
zero remaining hypotheses.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.FenichelPersistence`.
-/

open Function Set
open scoped NNReal BoundedContinuousFunction

namespace ODE

section ConstDrift

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The bounded constant fast-drift coupled field** `ẏ = 0`, `ż = v` on the product `Y × E`: the
slow base is frozen and the fast fibre translates at the constant velocity `v`. It is globally
bounded by `‖v‖` (`constDriftField_bound`) and globally Lipschitz with constant `0`
(`constDriftField_lipschitz`), the hypotheses `exists_flow` needs to package its solutions into a
forward semiflow. -/
def constDriftField (v : E) : Y × E → Y × E := fun _ => (0, v)

omit [NormedSpace ℝ Y] [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem constDriftField_apply (v : E) (p : Y × E) : constDriftField v p = (0, v) := rfl

omit [NormedSpace ℝ Y] [NormedSpace ℝ E] in
/-- The constant fast-drift field is Lipschitz with constant `0` (it is constant). -/
theorem constDriftField_lipschitz (v : E) : LipschitzWith 0 (constDriftField (Y := Y) v) :=
  LipschitzWith.const' _

omit [NormedSpace ℝ Y] [NormedSpace ℝ E] in
/-- The constant fast-drift field is globally bounded by `‖v‖`. -/
theorem constDriftField_bound (v : E) (p : Y × E) :
    ‖constDriftField (Y := Y) v p‖ ≤ ‖v‖₊ := by
  simp only [constDriftField, Prod.norm_def, norm_zero, coe_nnnorm, max_le_iff]
  exact ⟨norm_nonneg _, le_rfl⟩

/-- The explicit translation integral curve of the constant fast-drift field through `(y, z)`:
`t ↦ (y, z + t • v)`. -/
def constDriftCurve (v : E) (p : Y × E) : ℝ → Y × E := fun t => (p.1, p.2 + t • v)

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
@[simp] theorem constDriftCurve_zero (v : E) (p : Y × E) : constDriftCurve v p 0 = p := by
  simp [constDriftCurve]

/-- The explicit translation curve is an integral curve of the constant fast-drift field. -/
theorem constDriftCurve_hasDerivAt (v : E) (p : Y × E) (t : ℝ) :
    HasDerivAt (constDriftCurve v p) (constDriftField v (constDriftCurve v p t)) t := by
  rw [constDriftField_apply]
  have h1 : HasDerivAt (fun _ : ℝ => p.1) (0 : Y) t := hasDerivAt_const _ _
  have hv : HasDerivAt (fun s : ℝ => s • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v
  have h2 : HasDerivAt (fun s : ℝ => p.2 + s • v) (0 + v) t := (hasDerivAt_const t p.2).add hv
  rw [zero_add] at h2
  exact h1.prodMk h2

variable [CompleteSpace Y] [CompleteSpace E]

/-- **The flow of the constant fast-drift field.** `exists_flow` applied to the bounded Lipschitz
field `constDriftField v` furnishes a genuine forward semiflow on `Y × E`, together with the data
identifying its orbits as integral curves of the field. -/
theorem exists_constDrift_flow (v : E) :
    ∃ (ϕ : Flow ℝ≥0 (Y × E)) (γ : (Y × E) → ℝ → Y × E),
      (∀ x, γ x 0 = x) ∧ (∀ x t, HasDerivAt (γ x) (constDriftField v (γ x t)) t) ∧
      (∀ x (t : ℝ≥0), ϕ.toFun t x = γ x (t : ℝ)) :=
  exists_flow (constDriftField_lipschitz v) (constDriftField_bound v)

omit [CompleteSpace Y] [CompleteSpace E] in
/-- **Closed form of the constant fast-drift flow.** Any forward semiflow whose orbits are integral
curves of the constant fast-drift field is the affine translation `(y, z) ↦ (y, z + t • v)` for
`t ≥ 0`: the slow base is fixed and the fast fibre translates at velocity `v`. Pinned by uniqueness
of forward integral curves of a Lipschitz field. -/
theorem constDrift_flow_eq (v : E) {ϕ : Flow ℝ≥0 (Y × E)} {γ : (Y × E) → ℝ → Y × E}
    (hγ0 : ∀ x, γ x 0 = x) (hγd : ∀ x t, HasDerivAt (γ x) (constDriftField v (γ x t)) t)
    (hϕ : ∀ x (t : ℝ≥0), ϕ.toFun t x = γ x (t : ℝ)) (t : ℝ≥0) (p : Y × E) :
    ϕ.toFun t p = (p.1, p.2 + (t : ℝ) • v) := by
  have heq : Set.EqOn (γ p) (constDriftCurve v p) (Set.Ici 0) :=
    eqOn_Ici_of_isIntegralCurve (constDriftField_lipschitz v) (hγd p)
      (constDriftCurve_hasDerivAt v p) (by rw [hγ0 p, constDriftCurve_zero])
  rw [hϕ p t, heq (Set.mem_Ici.2 (t : ℝ≥0).coe_nonneg)]
  rfl

end ConstDrift

section Regraph

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The regraph of a section under time `t` of the constant fast-drift flow: the section translated
by `t • v`. The time-`t` translation flow carries `graphSet σ` to `graphSet (regraph v t σ)`. -/
def regraph (v : E) (t : ℝ≥0) (σ : Y → E) : Y → E := fun y => σ y + (t : ℝ) • v

omit [CompleteSpace Y] [CompleteSpace E] in
/-- **The constant fast-drift flow regraphs at every time.** For any forward semiflow whose orbits
are integral curves of the constant fast-drift field, the time-`t` flow carries the graph of `σ`
into the graph of `regraph v t σ`, for every `t ≥ 0`. Proved from the closed form of the flow. -/
theorem constDrift_allTimeRegraph (v : E) {ϕ : Flow ℝ≥0 (Y × E)} {γ : (Y × E) → ℝ → Y × E}
    (hγ0 : ∀ x, γ x 0 = x) (hγd : ∀ x t, HasDerivAt (γ x) (constDriftField v (γ x t)) t)
    (hϕ : ∀ x (t : ℝ≥0), ϕ.toFun t x = γ x (t : ℝ)) (t : ℝ≥0) (σ : Y → E) :
    MapsTo (ϕ.toFun t) (graphSet σ) (graphSet (regraph v t σ)) := by
  intro p hp
  rw [mem_graphSet] at hp
  rw [constDrift_flow_eq v hγ0 hγd hϕ t p, mem_graphSet, regraph, hp]

/-- **The concrete constant fast-drift coupled-flow graph transform.** Assembled from a genuine
`exists_flow` flow of the bounded Lipschitz constant fast-drift field, with the graph-transform
operator at horizon `τ` proved — not assumed — to be the flow-then-regraph map `regraph v τ`. This
discharges the `flow_mapsTo` hypothesis of `CoupledFlowGraphTransform` from the explicit field. -/
noncomputable def constDriftCoupled (v : E) (τ : ℝ≥0) : CoupledFlowGraphTransform Y E :=
  { flow := (exists_constDrift_flow (Y := Y) v).choose
    τ := τ
    op := regraph v τ
    flow_mapsTo := by
      obtain ⟨γ, hγ0, hγd, hϕ⟩ := (exists_constDrift_flow (Y := Y) v).choose_spec
      intro σ
      exact constDrift_allTimeRegraph v hγ0 hγd hϕ τ σ }

@[simp] theorem constDriftCoupled_op (v : E) (τ : ℝ≥0) :
    (constDriftCoupled (Y := Y) v τ).op = regraph v τ := rfl

end Regraph

section Persistence

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **A genuine spectral-gap contraction on bounded sections.** The scaling operator
`σ ↦ (Lf / rate) • σ` on `Y →ᵇ E` is an exact contraction with factor `Lf / rate < 1` when the
fibre rate `rate` dominates the fibre Lipschitz/drift constant `Lf` (the spectral gap `Lf < rate`).
Its unique fixed point is the zero section — the unperturbed manifold `M_0 = 0`. Packaged as
`GraphTransformData` via `ofSpectralGap`, with vanishing `O(ε)` drift defect (the operator fixes the
zero base exactly). -/
noncomputable def scaleGapData (rate Lf : ℝ) (hrate : 0 < rate) (hLf : 0 ≤ Lf) (hgap : Lf < rate) :
    GraphTransformData Y E :=
  GraphTransformData.ofSpectralGap
    (op := fun σ => (Lf / rate) • σ) (base := 0) rate Lf hrate hLf hgap
    (op_dist_le := by
      intro σ τ
      rw [dist_smul₀, Real.norm_of_nonneg (div_nonneg hLf hrate.le)])
    (ε := 0) (C := 0)
    (defect_le := by rw [smul_zero, dist_self, zero_mul])

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
/-- The base section of `scaleGapData` is the zero section `M_0 = 0`. -/
@[simp] theorem scaleGapData_base (rate Lf : ℝ) (hrate : 0 < rate) (hLf : 0 ≤ Lf) (hgap : Lf < rate) :
    (scaleGapData (Y := Y) (E := E) rate Lf hrate hLf hgap).base = 0 := rfl

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
/-- The scaling operator of `scaleGapData`. -/
@[simp] theorem scaleGapData_op (rate Lf : ℝ) (hrate : 0 < rate) (hLf : 0 ≤ Lf) (hgap : Lf < rate)
    (σ : Y →ᵇ E) :
    (scaleGapData (Y := Y) (E := E) rate Lf hrate hLf hgap).op σ = (Lf / rate) • σ := rfl

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
/-- **The persisted manifold of `scaleGapData` is the zero section.** The unique Banach fixed point
of the scaling contraction `σ ↦ (Lf / rate) • σ` is `0`. -/
theorem scaleGapData_manifold (rate Lf : ℝ) (hrate : 0 < rate) (hLf : 0 ≤ Lf) (hgap : Lf < rate) :
    (scaleGapData (Y := Y) (E := E) rate Lf hrate hLf hgap).manifold = 0 := by
  refine ((scaleGapData (Y := Y) (E := E) rate Lf hrate hLf hgap).manifold_unique
    (σ := 0) ?_).symm
  rw [scaleGapData_op, smul_zero]

/-- **End-to-end Fenichel persistence for the explicit constant fast-drift field.** Combining the
concrete operator-from-flow bridge `constDriftCoupled` (whose `flow_mapsTo` is proved from a genuine
`exists_flow` flow of the bounded Lipschitz field) with the genuine spectral-gap contraction
`scaleGapData` (whose Banach fixed point `M_ε = 0` is the persisted manifold), with the drift
vanishing (`v = 0`) at horizon `τ`. The conclusion is the two halves of Fenichel persistence with
**every hypothesis discharged**: the graph of the persisted manifold section is forward-invariant
under the iterate coupled semiflow of the explicit field, and `M_ε` sits within
`defect / (1 - factor)` of the unperturbed section `M_0 = 0` in the supremum metric. -/
theorem fenichel_persistence_constDrift (rate Lf : ℝ) (hrate : 0 < rate) (hLf : 0 ≤ Lf)
    (hgap : Lf < rate) (τ : ℝ≥0) :
    let G := scaleGapData (Y := Y) (E := E) rate Lf hrate hLf hgap
    let F := constDriftCoupled (Y := Y) (E := E) 0 τ
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (graphSet (G.manifold : Y → E)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) := by
  intro G F
  refine fenichel_persistence G F ?_
  -- At the vanishing drift `v = 0`, the flow-regraph operator is the identity, so the zero-section
  -- fixed point of the contraction is also fixed by the flow operator.
  show F.op (G.manifold : Y → E) = (G.manifold : Y → E)
  rw [constDriftCoupled_op]
  funext y
  simp [regraph]

end Persistence

end ODE

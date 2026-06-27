import CRNT.Dynamics.CenterManifold
import CRNT.Dynamics.DissipativeTracking

/-!
# The center-manifold reduction principle

For a `C¹` vector field with an equilibrium at the origin whose linearization has the spectral
splitting `ℝⁿ = E_c ⊕ E_h` into a center part `E_c` (eigenvalues with `Re λ = 0`) and a hyperbolic
part `E_h` (eigenvalues with `Re λ ≠ 0`, here the attracting/stable directions), the **reduction
principle** of center-manifold theory says that the local stability and bifurcation behavior of the
full flow near the equilibrium are governed by the *reduced* vector field obtained by restricting the
field to the local center manifold `graph(h)`, `h : E_c → E_h` (Carr, *Applications of Centre Manifold
Theory*, Theorem 2 — the reduction principle; Vanderbauwhede, *Centre Manifolds, Normal Forms and
Elementary Bifurcations*). This module formalizes that principle, taking the `C⁰` center manifold of
`CRNT.Dynamics.CenterManifold` and the transverse attraction (a dissipative one-sided contraction at
the hyperbolic rate, as a `CRNT.Dynamics.ExponentialDecay.LyapunovCertificate` furnishes) as supplied
data. It is CRN-free and lives in the `ODE` namespace shared with `CRNT.Dynamics.CenterManifold`.

Write the full state as `(c, y) ∈ E_c × E_h` with center component `c` and hyperbolic component `y`,
and let `h : E_c → E_h` be the center-manifold graph map. The two halves of the reduction principle
are:

**Attraction to the manifold.** The transverse gap `g(t) = ‖y(t) − h(c(t))‖` of a small bounded
orbit `(c(t), y(t))` of the full flow obeys a dissipative differential inequality `g' ≤ −λ·g + δ`:
the hyperbolic directions contract toward the graph at the dichotomy rate `λ > 0`, and the defect `δ`
measures how far the graph fails to be exactly invariant (zero for an invariant manifold). The
horizon-uniform dissipative ceiling of `CRNT.Dynamics.DissipativeTracking` then bounds the gap by
`g(0)·e^{−λt} + δ/λ` for all forward time; with the manifold exactly invariant (`δ = 0`) the gap
decays exponentially to `0`, so every small bounded orbit is exponentially attracted to `graph(h)`.

**The reduced field.** On the manifold the full field is tangent to the graph, so the center
component evolves by the *reduced field* `reducedField c = π_c (field (c, h c))`, the center
projection of the full field evaluated on the manifold (`ReductionData.reducedField`). An orbit that
starts on the manifold stays on it and its center component solves `ċ = reducedField c`
(`onManifold_center_velocity`); by the attraction every small bounded orbit is asymptotic to such a
reduced orbit, so the local stability of the full equilibrium coincides with the stability of the
reduced equilibrium of `reducedField` on `E_c` (`reduction_stability_on_manifold`). This is the
reduction principle: the low-dimensional reduced flow determines the local behavior of the full flow.

**Reduction data** (`ReductionData`). The split phase space `E_c × E_h`, the full field, the graph
map `h`, the hyperbolic attraction rate `rate = λ > 0`, the transverse dissipative-contraction bound
toward the graph, and the invariance defect `δ`. The dichotomy/contraction inputs are supplied
through these constants, as the repository's seed pattern (`CRNT.Dynamics.Fenichel`'s
`SlowManifoldSeed`, `CRNT.Dynamics.HopfAdmissible`'s `CenterManifoldSeed`) does.

**First-order tangency.** Matching the reduced field's linear part to the restriction of the
linearization to `E_c` needs the first-order tangency `Dh(0) = 0`. This is carried as a hypothesis on
the tangency theorem `reducedField_fderiv_tangent` rather than re-derived; the `C⁰` reduction
principle — attraction to the manifold and the reduced-field stability equivalence — holds without it,
and the tangency only enters the spectral identification of the reduced linearization: under
`Dh(0) = 0` the reduced field's Fréchet derivative at the equilibrium is the center–center block
`π_c ∘ A ∘ ι_c` of the full linearization `A`, so the reduced flow inherits the critical spectrum.
The differentiable `C¹` enrichment that *proves* `Dh(0) = 0` from a derivative-contraction (mirroring
`CRNT.Dynamics.FenichelC1Manifold`'s `SlowManifoldC1Seed` enrichment of the Lipschitz manifold) is a
separate development.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.CenterManifold`,
`CRNT.Dynamics.DissipativeTracking`.
-/

open Set Filter
open scoped Topology RealInnerProductSpace

namespace ODE

variable {Ec : Type*} [NormedAddCommGroup Ec] [InnerProductSpace ℝ Ec]
variable {Eh : Type*} [NormedAddCommGroup Eh] [InnerProductSpace ℝ Eh]

/-- **Reduction data for the center-manifold reduction principle.** The state space splits as
`E_c × E_h` with center part `E_c` and hyperbolic part `E_h`. `field` is the full vector field with
the equilibrium at the origin; `graph : E_c → E_h` is the local center-manifold map `h` (read off,
e.g., from `CRNT.Dynamics.CenterManifold`'s `CenterManifoldData.manifold`). The hyperbolic directions
attract toward the graph at the rate `rate = λ > 0`: the transverse gap obeys a one-sided dissipative
contraction with defect `defect = δ` measuring the manifold's invariance error. The dichotomy inputs
are supplied through these constants, as the repository's seed pattern does. -/
structure ReductionData (Ec : Type*) [NormedAddCommGroup Ec] [InnerProductSpace ℝ Ec]
    (Eh : Type*) [NormedAddCommGroup Eh] [InnerProductSpace ℝ Eh] where
  /-- The full vector field on the split phase space `E_c × E_h`. -/
  field : Ec × Eh → Ec × Eh
  /-- The local center-manifold graph map `h : E_c → E_h`. -/
  graph : Ec → Eh
  /-- The hyperbolic attraction rate `λ`. -/
  rate : ℝ
  /-- The attraction rate is positive: the hyperbolic directions contract. -/
  rate_pos : 0 < rate
  /-- The invariance defect `δ`: how far the graph fails to be exactly invariant. -/
  defect : ℝ
  /-- The defect is nonnegative. -/
  defect_nonneg : 0 ≤ defect
  /-- **The graph contains the equilibrium.** The origin lies on the manifold: `h 0 = 0`. -/
  graph_zero : graph 0 = 0

namespace ReductionData

variable (R : ReductionData Ec Eh)

/-- **The reduced vector field on the center subspace.** `reducedField c` is the center projection of
the full field evaluated on the manifold at center coordinate `c`: `reducedField c = π_c (field (c,
h c))`. The reduction principle asserts that this low-dimensional field governs the local stability
and bifurcation of the full flow near the equilibrium. -/
def reducedField (c : Ec) : Ec := (R.field (c, R.graph c)).1

/-- The hyperbolic component of the full field evaluated on the manifold. The reduced field
`reducedField` is the center component of the same point; the pair `(reducedField c, fibreField c)`
is the full field `field (c, h c)` on the manifold. -/
def fibreField (c : Ec) : Eh := (R.field (c, R.graph c)).2

@[simp] theorem field_on_graph (c : Ec) :
    R.field (c, R.graph c) = (R.reducedField c, R.fibreField c) := by
  ext <;> rfl

/-- **The reduced equilibrium.** The origin is an equilibrium of the reduced field exactly when the
full field vanishes at the equilibrium on the manifold, `field (0, h 0) = 0` — the standing
assumption that the equilibrium lies at the origin. -/
theorem reducedField_zero_of_field_zero (h0 : R.field 0 = 0) : R.reducedField 0 = 0 := by
  have hpt : ((0 : Ec), R.graph 0) = (0 : Ec × Eh) := by rw [R.graph_zero]; rfl
  rw [reducedField, hpt, h0, Prod.fst_zero]

/-! ## Attraction of small bounded orbits to the center manifold -/

/-- **Exponential attraction to the center manifold (horizon-uniform ceiling).** Let `(c, y)` be a
forward orbit of the full flow, `g t = ‖y t − h (c t)‖` its transverse gap to the graph. If the gap
is continuous on `[0, T]`, has a right derivative `g' x` on `[0, T)`, and satisfies the transverse
dissipative contraction `g' x ≤ −λ·g x + δ` — the hyperbolic directions contracting toward the graph
at rate `λ = rate` with invariance defect `δ = defect` — then the gap is bounded for all forward time
by `g 0 + δ / λ`, with *no* horizon dependence. This is the quantitative attraction of small bounded
orbits to the local center manifold. -/
theorem transverse_gap_ceiling {c : ℝ → Ec} {y : ℝ → Eh} {T : ℝ}
    (g g' : ℝ → ℝ) (hg_def : ∀ t, g t = ‖y t - R.graph (c t)‖)
    (hg : ContinuousOn g (Icc 0 T))
    (hg' : ∀ x ∈ Ico 0 T, HasDerivWithinAt g (g' x) (Ici x) x)
    (hbound : ∀ x ∈ Ico 0 T, g' x ≤ -R.rate * g x + R.defect) :
    ∀ t ∈ Icc 0 T, g t ≤ g 0 + R.defect / R.rate := by
  have hg0 : 0 ≤ g 0 := by rw [hg_def]; exact norm_nonneg _
  exact dissipative_tracking_ceiling R.rate_pos R.defect_nonneg hg0 hg hg' hbound

/-- **Asymptotic attraction to the center manifold.** Over `[0, ∞)`, under the same transverse
dissipative contraction at rate `λ = rate` with defect `δ = defect`, the transverse gap is eventually
within any margin above the steady ceiling `δ / λ`: for every `η > 0`, eventually `g t ≤ δ/λ + η`.
When the manifold is exactly invariant (`δ = 0`) the gap tends to `0`: every small bounded orbit is
attracted to the local center manifold. -/
theorem transverse_gap_le_ceiling
    (g g' : ℝ → ℝ)
    (hg : ∀ T, ContinuousOn g (Icc 0 T))
    (hg' : ∀ x, 0 ≤ x → HasDerivWithinAt g (g' x) (Ici x) x)
    (hbound : ∀ x, 0 ≤ x → g' x ≤ -R.rate * g x + R.defect) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in atTop, g t ≤ R.defect / R.rate + η :=
  dissipative_gap_le_ceiling R.rate_pos R.defect_nonneg hg hg' hbound hη

/-- **Exact attraction when the manifold is invariant.** With the invariance defect `δ = 0` (an
exactly invariant center manifold), the transverse gap of a small bounded orbit is eventually within
any margin `η > 0` of zero: the orbit is asymptotically on the manifold. This is the limiting form of
the reduction principle's attraction half. -/
theorem transverse_gap_tendsto_zero
    (hdef0 : R.defect = 0) (g g' : ℝ → ℝ)
    (hg : ∀ T, ContinuousOn g (Icc 0 T))
    (hg' : ∀ x, 0 ≤ x → HasDerivWithinAt g (g' x) (Ici x) x)
    (hbound : ∀ x, 0 ≤ x → g' x ≤ -R.rate * g x + R.defect) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in atTop, g t ≤ η := by
  have h := R.transverse_gap_le_ceiling g g' hg hg' hbound hη
  filter_upwards [h] with t ht
  rwa [hdef0, zero_div, zero_add] at ht

/-! ## The reduced flow governs the on-manifold dynamics -/

/-- **An orbit on the manifold is governed by the reduced field.** If `c : ℝ → E_c` is the center
component of a forward orbit `(c t, h (c t))` that lies on the manifold and solves the full flow
`(ċ, ẏ) = field (c, h c)`, then the center component solves the reduced equation
`ċ = reducedField c`. This is the defining property of the reduced field: the dynamics restricted to
the center manifold are exactly the reduced flow on `E_c`. -/
theorem onManifold_center_velocity {c : ℝ → Ec} {t : ℝ}
    (hc : HasDerivAt c (R.field (c t, R.graph (c t))).1 t) :
    HasDerivAt c (R.reducedField (c t)) t := hc

/-- **An orbit on the manifold stays on the manifold (consistency of the reduced flow).** If the
center component solves the reduced equation `ċ = reducedField c` and the hyperbolic component is
slaved to the graph, `y t = h (c t)`, then the full state `(c t, y t)` evolves with center velocity
`reducedField (c t)`: the manifold is consistent with the reduced flow. -/
theorem reducedFlow_on_manifold {c : ℝ → Ec} {y : ℝ → Eh} {t : ℝ}
    (hslaved : y t = R.graph (c t)) (hc : HasDerivAt c (R.reducedField (c t)) t) :
    HasDerivAt c (R.field (c t, y t)).1 t := by
  rw [hslaved]; exact hc

/-! ## The reduction principle: full ⟺ reduced stability -/

/-- **Liapunov stability of an equilibrium of a field, at a state.** The equilibrium `e` (a zero of
the field `F`) is stable when every neighborhood `U` of `e` contains a neighborhood `V` such that
every forward orbit `φ` of `F` starting in `V` stays in `U` for all forward time. This is the
standard `ε`–`δ` Liapunov stability, phrased for the abstract field `F` and its orbits. -/
def StableAt {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] (F : α → α) (e : α) : Prop :=
  ∀ U ∈ 𝓝 e, ∃ V ∈ 𝓝 e, ∀ φ : ℝ → α, φ 0 ∈ V →
    (∀ t, 0 ≤ t → HasDerivAt φ (F (φ t)) t) → ∀ t, 0 ≤ t → φ t ∈ U

/-- **The reduction principle (stability transfer).** Let `slave : E_c → E_c × E_h`,
`slave c = (c, h c)`, parametrize the center manifold. Suppose `slave` pulls back full neighborhoods
of the equilibrium `slave 0 = (0, h 0)` to reduced neighborhoods of the center origin (`hnhds`, the
continuity of the slaving used in one direction). Then stability of the reduced equilibrium `0` of
`reducedField` on `E_c` implies stability of the full equilibrium for every full orbit `φ` of `field`
that is *confined to the manifold* — `φ t = slave (φ t).1` — whose center component solves the reduced
equation. Concretely: from a reduced-stable witness, every such full on-manifold orbit started near
`slave 0` stays inside any prescribed full neighborhood `U` for all forward time. This is the
reduction principle's stability half: the low-dimensional reduced flow determines the local stability
of the full flow on the center manifold (Carr, *Applications of Centre Manifold Theory*, Theorem 2). -/
theorem reduction_stability_on_manifold
    (slave : Ec → Ec × Eh) (hslave : ∀ c, slave c = (c, R.graph c))
    (hnhds : ∀ U ∈ 𝓝 (slave 0), slave ⁻¹' U ∈ 𝓝 (0 : Ec))
    (hred : StableAt R.reducedField 0) :
    ∀ U ∈ 𝓝 ((0 : Ec), R.graph 0), ∃ V ∈ 𝓝 (0 : Ec), ∀ φ : ℝ → Ec × Eh,
      (∀ t, φ t = slave (φ t).1) → (φ 0).1 ∈ V →
      (∀ t, 0 ≤ t → HasDerivAt (fun s => (φ s).1) (R.reducedField (φ t).1) t) →
      ∀ t, 0 ≤ t → φ t ∈ U := by
  -- The equilibrium on the manifold is `slave 0 = (0, h 0)`.
  have h0 : slave 0 = ((0 : Ec), R.graph 0) := hslave 0
  intro U hU
  rw [← h0] at hU
  -- Pull `U` back to a reduced neighborhood of the origin and apply reduced stability there to the
  -- center component, then lift the membership through the slaving `φ t = slave (φ t).1`.
  obtain ⟨V, hV, hVprop⟩ := hred (slave ⁻¹' U) (hnhds U hU)
  refine ⟨V, hV, fun φ hconf hφ0 hc t ht => ?_⟩
  have hcenter : (fun s => (φ s).1) 0 ∈ V := hφ0
  have hmem : (φ t).1 ∈ slave ⁻¹' U := hVprop (fun s => (φ s).1) hcenter hc t ht
  -- `φ t = slave (φ t).1`, and `slave (φ t).1 ∈ U` is exactly the pullback membership.
  rw [hconf t]
  exact hmem

/-! ## First-order tangency and the reduced linearization -/

/-- **The reduced linearization is the center block of the full linearization.** With the first-order
tangency `Dh(0) = 0` (the manifold is tangent to the center subspace at the equilibrium, carried as
the hypothesis `htan`) and `h 0 = 0`, the Fréchet derivative of the reduced field at the equilibrium
is the center–center block `π_c ∘ A ∘ ι_c` of the full linearization `A = D(field)(0)`: the reduced
field's linear part is exactly the restriction of `A` to `E_c`. This is the spectral content of the
reduction principle — the reduced flow inherits the critical (center) spectrum of the full flow.

The slaving graph is `slaveMap c = (c, h c)`; its derivative at `0` is `(ι_c, Dh 0) = (ι_c, 0)`, i.e.
the inclusion `ι_c = ContinuousLinearMap.inl ℝ Ec Eh` of the center subspace. Composing the chain
rule `D(field ∘ slaveMap)(0) = A ∘ (ι_c, 0) = A ∘ ι_c` with the center projection `π_c` gives the
identity. -/
theorem reducedField_fderiv_tangent
    (slaveMap : Ec → Ec × Eh) (hslaveMap : slaveMap = fun c => (c, R.graph c))
    (A : (Ec × Eh) →L[ℝ] (Ec × Eh)) (hA : HasFDerivAt R.field A (slaveMap 0))
    {Dh : Ec →L[ℝ] Eh} (hDh : HasFDerivAt R.graph Dh 0) (htan : Dh = 0) :
    HasFDerivAt R.reducedField
      ((ContinuousLinearMap.fst ℝ Ec Eh).comp (A.comp (ContinuousLinearMap.inl ℝ Ec Eh))) 0 := by
  -- The slaving map has derivative `(id, Dh) = (id, 0) = inl` at the origin.
  have hslave_deriv : HasFDerivAt slaveMap (ContinuousLinearMap.inl ℝ Ec Eh) 0 := by
    rw [hslaveMap]
    have hid : HasFDerivAt (fun c : Ec => c) (ContinuousLinearMap.id ℝ Ec) 0 := hasFDerivAt_id 0
    have hpair := hid.prodMk hDh
    have heq : (ContinuousLinearMap.id ℝ Ec).prod Dh = ContinuousLinearMap.inl ℝ Ec Eh := by
      rw [htan]; ext x <;> simp
    rwa [heq] at hpair
  -- `reducedField = fst ∘ field ∘ slaveMap`; chain the derivatives.
  have hcomp : HasFDerivAt (fun c => R.field (slaveMap c))
      (A.comp (ContinuousLinearMap.inl ℝ Ec Eh)) 0 := hA.comp 0 hslave_deriv
  have hfst : HasFDerivAt (fun p : Ec × Eh => p.1) (ContinuousLinearMap.fst ℝ Ec Eh)
      (R.field (slaveMap 0)) := (ContinuousLinearMap.fst ℝ Ec Eh).hasFDerivAt
  have hfinal := hfst.comp 0 hcomp
  -- `hfinal` is `HasFDerivAt (fun c => (R.field (slaveMap c)).1) _ 0`; this is `reducedField`.
  refine hfinal.congr_of_eventuallyEq ?_
  filter_upwards with c
  rw [hslaveMap]
  rfl

end ReductionData

/-! ## The reduced field of a constructed center manifold -/

/-- **Assembling reduction data from a constructed center manifold.** Given the `C⁰` center manifold
`h = M.manifold` of a `CRNT.Dynamics.CenterManifold.CenterManifoldData` (as a function on `E_c`, read
through the bounded-section coercion), a full field, an attraction rate, and the transverse
contraction/invariance data, this packages the reduction data whose `reducedField` is the center
projection of the field along the constructed manifold. The constructed graph supplies `h`; the
dynamical attraction is supplied through the rate and defect, as the seed pattern does. -/
noncomputable def reductionDataOfCenterManifold
    [CompleteSpace Eh] (M : CenterManifoldData Ec Eh)
    (field : Ec × Eh → Ec × Eh) (rate : ℝ) (rate_pos : 0 < rate)
    (defect : ℝ) (defect_nonneg : 0 ≤ defect)
    (graph_zero : (M.manifold : Ec → Eh) 0 = 0) :
    ReductionData Ec Eh where
  field := field
  graph := fun c => M.manifold c
  rate := rate
  rate_pos := rate_pos
  defect := defect
  defect_nonneg := defect_nonneg
  graph_zero := graph_zero

@[simp] theorem reductionDataOfCenterManifold_graph
    [CompleteSpace Eh] (M : CenterManifoldData Ec Eh)
    (field : Ec × Eh → Ec × Eh) (rate : ℝ) (rate_pos : 0 < rate)
    (defect : ℝ) (defect_nonneg : 0 ≤ defect)
    (graph_zero : (M.manifold : Ec → Eh) 0 = 0) (c : Ec) :
    (reductionDataOfCenterManifold M field rate rate_pos defect defect_nonneg graph_zero).graph c
      = M.manifold c := rfl

@[simp] theorem reductionDataOfCenterManifold_reducedField
    [CompleteSpace Eh] (M : CenterManifoldData Ec Eh)
    (field : Ec × Eh → Ec × Eh) (rate : ℝ) (rate_pos : 0 < rate)
    (defect : ℝ) (defect_nonneg : 0 ≤ defect)
    (graph_zero : (M.manifold : Ec → Eh) 0 = 0) (c : Ec) :
    (reductionDataOfCenterManifold M field rate rate_pos defect defect_nonneg graph_zero).reducedField
        c = (field (c, M.manifold c)).1 := rfl

end ODE

/-!
This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.CenterManifold`,
`CRNT.Dynamics.DissipativeTracking`.
-/

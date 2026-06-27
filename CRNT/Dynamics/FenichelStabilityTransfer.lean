import CRNT.Dynamics.FenichelReductionPrinciple

/-!
# Normal attraction and stability transfer for the Fenichel slow manifold

`CRNT.Dynamics.FenichelReductionPrinciple` shows the full flow restricted to the slow manifold
`graphSet σ` is conjugate, through the base parametrization `incl`/`reductionProj`, to the slow base
flow. This module supplies the dynamical payoff: the slow manifold is **normally attracting**, and
through that attraction the asymptotic behaviour of the reduced base subsystem transfers to the full
system.

## Normal attraction

Off the manifold the fibre defect of a trajectory contracts exponentially. The flow of `(y, z)` has
fibre coordinate `σ (slowFlow t y) + e^{-rate·t}·(z - σ y)`, whose difference from the section read at
the moved base point is exactly `e^{-rate·t}·(z - σ y)`. Comparing the flowed point to the manifold
point directly above it gives `Metric.infDist (Φ t (y, z)) (graphSet σ) ≤ e^{-rate·t}·‖z - σ y‖`
(`fibre_defect_le`). For `rate > 0` the bound tends to `0`, so every trajectory converges to the slow
manifold (`tendsto_dist_slowManifold_zero`): the manifold attracts a full neighbourhood — indeed all
of `Y × E` — in the normal direction.

## Stability transfer

Normal attraction combines with the in-manifold conjugacy to lift asymptotic behaviour from the base.
If the base coordinate of a starting point converges to a slow equilibrium `y₀`, then the full
trajectory converges to the lifted equilibrium `incl σ y₀`
(`tendsto_full_flow_of_baseTendsto`): the base component converges to `y₀` by hypothesis, and the
fibre component converges to `σ y₀` because the moved-base section value `σ (slowFlow t y)` tends to
`σ y₀` by continuity while the contracted defect `e^{-rate·t}·(z - σ y)` vanishes. Specializing to a
base equilibrium that itself attracts gives the headline `asymptoticStability_lift`: a base-attracting
slow equilibrium lifts to a full-system attracting equilibrium on the slow manifold.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations":
normal hyperbolicity makes the persisted slow manifold attracting, so the reduced slow subsystem
governs the long-time behaviour of the full system. Reduced-model analysis of the slow base flow
therefore controls asymptotic stability of the full network.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.FenichelReductionPrinciple`.
-/

open Function Set Filter Topology
open scoped NNReal

namespace ODE

section NormalAttraction

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **The fibre defect of the flowed point is the contracted initial defect.** The fibre coordinate of
`Φ t (y, z)` minus the section read at the moved base point is exactly `e^{-rate·t}·(z - σ y)`: the
contraction scales the initial defect `z - σ y` by the running factor `e^{-rate·t}`. -/
theorem comovingContractFlow_fibre_sub (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ) (σ : Y → E)
    (hσcont : Continuous σ) (t : ℝ≥0) (p : Y × E) :
    ((comovingContractFlow B rate σ hσcont).toFun t p).2
        - σ ((comovingContractFlow B rate σ hσcont).toFun t p).1
      = Real.exp (-rate * (t : ℝ)) • (p.2 - σ p.1) := by
  rw [comovingContractFlow_toFun]
  simp

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **Exponential normal-attraction bound.** The distance from the flowed point to the slow manifold is
at most the contracted initial fibre defect: comparing `Φ t (y, z)` to the manifold point
`(slowFlow t y, σ (slowFlow t y))` directly above its base coordinate gives
`Metric.infDist (Φ t (y, z)) (graphSet σ) ≤ e^{-rate·t}·‖z - σ y‖`. The fibre coordinate relaxes
toward the section at the moved base point at rate `rate`, so trajectories approach the manifold
normally. -/
theorem fibre_defect_le (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ) (σ : Y → E)
    (hσcont : Continuous σ) (t : ℝ≥0) (p : Y × E) :
    Metric.infDist ((comovingContractFlow B rate σ hσcont).toFun t p) (graphSet σ)
      ≤ Real.exp (-rate * (t : ℝ)) * ‖p.2 - σ p.1‖ := by
  set q := (comovingContractFlow B rate σ hσcont).toFun t p with hq
  have hmem : (q.1, σ q.1) ∈ graphSet σ := rfl
  refine (Metric.infDist_le_dist_of_mem hmem).trans ?_
  rw [Prod.dist_eq]
  have hbase : dist q.1 (q.1, σ q.1).1 = 0 := by simp
  have hfib : dist q.2 (q.1, σ q.1).2 = Real.exp (-rate * (t : ℝ)) * ‖p.2 - σ p.1‖ := by
    rw [dist_eq_norm, hq, comovingContractFlow_fibre_sub B rate σ hσcont t p, norm_smul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hbase, hfib]
  exact max_le (by positivity) le_rfl

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **The slow manifold attracts every trajectory.** For `rate > 0` the distance from the flowed point
to the slow manifold tends to `0` as `t → ∞`, for any starting point `p`: the exponential normal-
attraction bound `fibre_defect_le` is squeezed to zero by `e^{-rate·t} → 0`. The slow manifold
`graphSet σ` is normally attracting — every forward trajectory converges to it. -/
theorem tendsto_dist_slowManifold_zero (B : AllTimeInjectiveBaseFlow Y) {rate : ℝ} (hrate : 0 < rate)
    (σ : Y → E) (hσcont : Continuous σ) (p : Y × E) :
    Tendsto (fun t : ℝ≥0 =>
        Metric.infDist ((comovingContractFlow B rate σ hσcont).toFun t p) (graphSet σ))
      atTop (𝓝 0) := by
  have hbound : Tendsto
      (fun t : ℝ≥0 => Real.exp (-rate * (t : ℝ)) * ‖p.2 - σ p.1‖) atTop (𝓝 0) := by
    have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
      NNReal.tendsto_coe_atTop.2 tendsto_id
    have hexp : Tendsto (fun t : ℝ≥0 => Real.exp (-rate * (t : ℝ))) atTop (𝓝 0) := by
      have : Tendsto (fun t : ℝ≥0 => -rate * (t : ℝ)) atTop atBot :=
        (tendsto_const_mul_atBot_of_neg (by linarith)).2 hcoe
      exact Real.tendsto_exp_atBot.comp this
    simpa using hexp.mul_const ‖p.2 - σ p.1‖
  refine squeeze_zero (fun t => Metric.infDist_nonneg) ?_ hbound
  exact fun t => fibre_defect_le B rate σ hσcont t p

end NormalAttraction

section StabilityTransfer

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **Base convergence lifts to full convergence.** If the base coordinate of the starting point `p`
flows to a slow point `y₀` — `slowFlow t p.1 → y₀` — then the full trajectory flows to the lifted point
`incl σ y₀ = (y₀, σ y₀)`. The base component converges by hypothesis; the fibre component converges to
`σ y₀` because the moved-base section value `σ (slowFlow t p.1)` tends to `σ y₀` by continuity of `σ`,
while the contracted defect `e^{-rate·t}·(p.2 - σ p.1)` vanishes. Normal attraction carries the fibre
onto the manifold, where the conjugacy makes the base limit the full limit. -/
theorem tendsto_full_flow_of_baseTendsto (B : AllTimeInjectiveBaseFlow Y) {rate : ℝ}
    (hrate : 0 < rate) (σ : Y → E) (hσcont : Continuous σ) {p : Y × E} {y₀ : Y}
    (hbase : Tendsto (fun t : ℝ≥0 => B.slowFlow.toFun t p.1) atTop (𝓝 y₀)) :
    Tendsto (fun t : ℝ≥0 => (comovingContractFlow B rate σ hσcont).toFun t p) atTop
      (𝓝 (incl σ y₀)) := by
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.2 tendsto_id
  have hexp : Tendsto (fun t : ℝ≥0 => Real.exp (-rate * (t : ℝ))) atTop (𝓝 0) := by
    have hlin : Tendsto (fun t : ℝ≥0 => -rate * (t : ℝ)) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (by linarith)).2 hcoe
    exact Real.tendsto_exp_atBot.comp hlin
  -- base component → y₀
  have hbaseComp : Tendsto
      (fun t : ℝ≥0 => ((comovingContractFlow B rate σ hσcont).toFun t p).1) atTop (𝓝 y₀) := by
    simpa using hbase
  -- the moved-base section value → σ y₀
  have hσmoved : Tendsto (fun t : ℝ≥0 => σ (B.slowFlow.toFun t p.1)) atTop (𝓝 (σ y₀)) :=
    (hσcont.tendsto y₀).comp hbase
  -- the contracted defect → 0
  have hdefect : Tendsto
      (fun t : ℝ≥0 => Real.exp (-rate * (t : ℝ)) • (p.2 - σ p.1)) atTop (𝓝 0) := by
    have := hexp.smul_const (p.2 - σ p.1)
    simpa using this
  -- fibre component → σ y₀
  have hfibComp : Tendsto
      (fun t : ℝ≥0 => ((comovingContractFlow B rate σ hσcont).toFun t p).2) atTop (𝓝 (σ y₀)) := by
    have hsum : Tendsto
        (fun t : ℝ≥0 => σ (B.slowFlow.toFun t p.1)
          + Real.exp (-rate * (t : ℝ)) • (p.2 - σ p.1)) atTop (𝓝 (σ y₀ + 0)) :=
      hσmoved.add hdefect
    rw [add_zero] at hsum
    simpa [comovingContractFlow_toFun] using hsum
  have hpair := hbaseComp.prodMk_nhds hfibComp
  rw [incl_apply]
  refine hpair.congr ?_
  intro t
  rw [comovingContractFlow_toFun]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **Asymptotic stability transfers from the base to the full system.** Let `y₀` be a slow-flow
equilibrium that attracts the base coordinate of `p` (`slowFlow t p.1 → y₀`). Then the lifted
equilibrium `incl σ y₀` is itself fixed by the full flow and attracts the full trajectory of `p`:
`incl σ y₀` is an equilibrium (`equilibrium_lift_of_baseEquilibrium`) and the full flow of `p`
converges to it (`tendsto_full_flow_of_baseTendsto`). The asymptotic stability of the reduced slow
subsystem transfers to the full system through normal hyperbolicity. -/
theorem asymptoticStability_lift (B : AllTimeInjectiveBaseFlow Y) {rate : ℝ} (hrate : 0 < rate)
    (σ : Y → E) (hσcont : Continuous σ) {p : Y × E} {y₀ : Y}
    (heq : ∀ t : ℝ≥0, B.slowFlow.toFun t y₀ = y₀)
    (hbase : Tendsto (fun t : ℝ≥0 => B.slowFlow.toFun t p.1) atTop (𝓝 y₀)) :
    (∀ t : ℝ≥0, (comovingContractFlow B rate σ hσcont).toFun t (incl σ y₀) = incl σ y₀)
      ∧ Tendsto (fun t : ℝ≥0 => (comovingContractFlow B rate σ hσcont).toFun t p) atTop
          (𝓝 (incl σ y₀)) :=
  ⟨fun t => equilibrium_lift_of_baseEquilibrium B rate σ hσcont heq t,
    tendsto_full_flow_of_baseTendsto B hrate σ hσcont hbase⟩

end StabilityTransfer

section StationaryAffineInstance

/-- **Asymptotic stability transfer over the stationary affine base.** Over the affine base with zero
drift on `ℝ × ℝ` every base point is a slow equilibrium and the base flow is constant, so the base
coordinate trivially converges to it. The lifted equilibrium `incl σ y₀` of the full comoving-contract
flow is therefore fixed and attracts the full trajectory of any point sharing its base coordinate —
the dynamical payoff of Fenichel on a concrete base. -/
theorem affineStationaryStability_lift {rate : ℝ} (hrate : 0 < rate) (z₀ : ℝ) (y₀ : ℝ × ℝ) :
    (∀ t : ℝ≥0, (comovingContractFlow (affineAllTimeBase ((0, 0) : ℝ × ℝ)) rate
          (fun y : ℝ × ℝ => y.2) continuous_snd_section).toFun t
          (incl (fun y : ℝ × ℝ => y.2) y₀) = incl (fun y : ℝ × ℝ => y.2) y₀)
      ∧ Tendsto (fun t : ℝ≥0 => (comovingContractFlow (affineAllTimeBase ((0, 0) : ℝ × ℝ)) rate
          (fun y : ℝ × ℝ => y.2) continuous_snd_section).toFun t (y₀, z₀)) atTop
          (𝓝 (incl (fun y : ℝ × ℝ => y.2) y₀)) := by
  have heq : ∀ t : ℝ≥0, (affineAllTimeBase ((0, 0) : ℝ × ℝ)).slowFlow.toFun t y₀ = y₀ := by
    intro t
    rw [affineAllTimeBase_slowFlow, affineBaseFlow_toFun]
    simp
  have hbase : Tendsto
      (fun t : ℝ≥0 => (affineAllTimeBase ((0, 0) : ℝ × ℝ)).slowFlow.toFun t (y₀, z₀).1) atTop
      (𝓝 y₀) := by
    refine Tendsto.congr (fun t => (heq t).symm) tendsto_const_nhds
  exact asymptoticStability_lift (affineAllTimeBase ((0, 0) : ℝ × ℝ)) hrate
    (fun y : ℝ × ℝ => y.2) continuous_snd_section heq hbase

end StationaryAffineInstance

end ODE

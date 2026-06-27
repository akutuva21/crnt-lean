import CRNT.Dynamics.MichaelisMentenFenichel

/-!
# All-time continuous-semiflow Fenichel invariance of the Michaelis–Menten slow manifold

`CRNT.Dynamics.MichaelisMentenFenichel`'s `mmFenichelPersistence` certifies forward-invariance of the
substrate-varying Michaelis–Menten equilibrium graph under the *discrete iterate* semiflow
`n ↦ Φ(n·τ)` sampling the coupled flow at multiples of the horizon `τ`. This module upgrades the
invariance half to the **full continuous semiflow** `Φ t` at every forward time `t ≥ 0`, completing
the geometric Fenichel statement for the genuine Michaelis–Menten field.

The closed-form moving-target contracting flow `movingContractFlow` regraphs the graph of every
section at *every* time, not only multiples of `τ`: the time-`t` contraction carries `graphSet σ` into
`graphSet (movingContractRegraph rate c t σ)` (`movingContract_allTimeRegraph`). At the horizon `τ`
the regraph operator coincides with the bundled `op = movingContractRegraph rate c τ`, so the bundled
`CoupledFlowGraphTransform` satisfies the all-time regraphing predicate `AllTimeRegraph`
(`movingContractCoupled_allTimeRegraph`, `mmCoupledFlowGraphTransform_allTimeRegraph`). Feeding this
into `CRNT.Dynamics.FenichelPersistence`'s `graphSet_isInvariant_allTime_of_fixed` upgrades the
fixed-point invariance from the iterate semiflow to the continuous semiflow.

The continuous-time invariance reads off the closed form directly at the moving target. At the
equilibrium section `c` — the unique fixed point of the horizon-`τ` operator — the time-`t` regraph
`movingContractRegraph rate c t c = c + e^{-rate·t}·(c - c) = c` returns `c` for *every* `t`, so
`movingContract_allTimeRegraph` already lands `graphSet c` back in `graphSet c` at all forward times.
This is the continuous-semiflow invariance of the moving equilibrium graph
(`movingContractFlow_isInvariant_graphSet`), independent of the horizon `τ`.

The complete geometric Fenichel statement (`mmFenichelPersistence_allTime`) pairs the continuous-time
invariance with the unchanged honest `O(ε)` `C⁰`-closeness ceiling
`‖M_ε − M_0‖_∞ ≤ (L/rate)·(ε·G)/(1 − e^{-rate·τ})` carried over from `mmFenichelPersistence`: the
substrate-varying equilibrium manifold is forward-invariant under the continuous coupled flow at all
`t ≥ 0` and lies within an `O(ε)` tube of the base section.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations": a
normally attracting invariant manifold of the unperturbed layer system persists, for small `ε`, as a
nearby invariant manifold, invariant under the full perturbed flow at every forward time; here the
fast fibre is normally attracting at rate `rate` toward the substrate-varying Michaelis–Menten
quasi-steady-state level `Vmax·s/(Km+s)`, so the persisted manifold is the genuine moving equilibrium
graph, invariant under the continuous coupled semiflow, with `O(ε)` slow-drift defect.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.MichaelisMentenFenichel`.
-/

open Function Set
open scoped NNReal BoundedContinuousFunction

namespace ODE

section MovingTargetAllTime

variable {Y : Type*} [TopologicalSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [TopologicalSpace Y] in
/-- The moving target `c` is fixed by the time-`t` regraph of the moving-target contracting flow, for
*every* `t`: `movingContractRegraph rate c t c = c`, since `c y + e^{-rate·t}·(c y - c y) = c y`. -/
theorem movingContractRegraph_self (rate : ℝ) (c : Y → E) (t : ℝ≥0) :
    movingContractRegraph rate c t c = c := by
  funext y
  rw [movingContractRegraph, sub_self, smul_zero, add_zero]

/-- **Continuous-semiflow invariance of the moving equilibrium graph.** The graph of the moving target
`c` is forward-invariant under the *full continuous* moving-target contracting semiflow `Φ t` at every
forward time `t ≥ 0` — not only at multiples of any horizon. The time-`t` flow regraphs `graphSet c`
into `graphSet (movingContractRegraph rate c t c)`, and the moving target is fixed by its own regraph
at every time, so this is `graphSet c` again. -/
theorem movingContractFlow_isInvariant_graphSet (rate : ℝ) (c : Y → E) (hc : Continuous c) :
    IsInvariant (movingContractFlow rate c hc).toFun (graphSet c) := by
  intro t
  have h := movingContract_allTimeRegraph rate c hc t c
  rwa [movingContractRegraph_self rate c t] at h

end MovingTargetAllTime

end ODE

namespace CRNT.MichaelisMenten

open ODE
open scoped BoundedContinuousFunction

/-- **All-time continuous-semiflow invariance of the Michaelis–Menten slow manifold.** The graph of
the substrate-varying equilibrium section `s ↦ mmRegEquil Km Vmax s · e0` is forward-invariant under
the *full continuous* coupled semiflow `Φ t` of the Michaelis–Menten moving-target contracting flow,
at every forward time `t ≥ 0` — upgrading the iterate-semiflow invariance of `mmFenichelPersistence`
to the continuous semiflow. The flow regraphs `graphSet c` into `graphSet (movingContractRegraph rate c t c)`
at every `t`, and the moving equilibrium target is fixed by its own regraph at every time. -/
theorem mmFenichelInvariant_allTime (rate Km Vmax : ℝ) (hKm : 0 < Km) (s₀ : ℝ) (τ : ℝ≥0) :
    IsInvariant (mmCoupledFlowGraphTransform rate Km Vmax hKm s₀ τ).flow.toFun
      (graphSet (fun s : SubstrateIcc s₀ => mmRegEquil Km Vmax (s : ℝ) • e0)) :=
  movingContractFlow_isInvariant_graphSet rate
    (fun s : SubstrateIcc s₀ => mmRegEquil Km Vmax (s : ℝ) • e0)
    (mmEquilSection_continuous Km Vmax hKm s₀)

/-- **The complete geometric Fenichel theorem for the Michaelis–Menten field.** The substrate-varying
equilibrium manifold is forward-invariant under the *continuous* coupled flow at every forward time
`t ≥ 0` AND sits within the honest `O(ε)` `C⁰`-closeness ceiling
`(L/rate)·(ε·G) / (1 - e^{-rate·τ})` of the base equilibrium section in the supremum metric. The
invariance half is `mmFenichelInvariant_allTime` — continuous-time, not merely sampled at multiples of
the horizon; the closeness half is carried over unchanged from `mmFenichelPersistence`. Together these
are the two halves of Fenichel persistence for the genuine Michaelis–Menten field, with the geometric
invariance now stated for the full continuous semiflow. -/
theorem mmFenichelPersistence_allTime (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km)
    (s₀ : ℝ) (τ : ℝ≥0) (hτ : 0 < (τ : ℝ)) {L ε G : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hG : 0 ≤ G) :
    let G' := mmFenichelData rate hrate Km Vmax hKm s₀ τ hτ hL hε hG
    let F := mmCoupledFlowGraphTransform rate Km Vmax hKm s₀ τ
    IsInvariant F.flow.toFun (graphSet (G'.manifold : SubstrateIcc s₀ → E)) ∧
      dist G'.base G'.manifold ≤ G'.defect / (1 - G'.factor) := by
  intro G' F
  refine ⟨?_, (mmFenichelPersistence rate hrate Km Vmax hKm s₀ τ hτ hL hε hG).2⟩
  have hman : (G'.manifold : SubstrateIcc s₀ → E)
      = fun s : SubstrateIcc s₀ => mmRegEquil Km Vmax (s : ℝ) • e0 := by
    show ((mmFenichelData rate hrate Km Vmax hKm s₀ τ hτ hL hε hG).manifold : SubstrateIcc s₀ → E)
      = fun s : SubstrateIcc s₀ => mmRegEquil Km Vmax (s : ℝ) • e0
    rw [mmFenichelData_manifold rate hrate Km Vmax hKm s₀ τ hτ hL hε hG]
    funext y
    rw [mmEquilSection_apply]
  rw [hman]
  exact mmFenichelInvariant_allTime rate Km Vmax hKm s₀ τ

end CRNT.MichaelisMenten

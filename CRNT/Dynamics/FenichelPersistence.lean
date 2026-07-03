import CRNT.Dynamics.GraphTransform
import CRNT.Dynamics.FlowConstruction

/-!
# Forward-invariance of the persisted Fenichel manifold

This module ties the abstract graph-transform fixed point `M_ε` of `CRNT.Dynamics.GraphTransform` to
forward-invariance under the coupled slow–fast flow, completing the geometric content of Fenichel's
`ε`-persistence theorem. For a singularly-perturbed system `ẏ = ε·g(y, z)`, `ż = fast y z` with a
normally attracting fast fibre, the persisted manifold is the graph of the section `M_ε` that is the
fixed point of the **graph transform** (Lyapunov–Perron operator): the map pushing a candidate graph
forward by the coupled flow and re-expressing the image as a graph over the slow base `Y`. The
defining property of a fixed point of this operator is exactly that its graph is mapped onto itself by
the flow — i.e. is forward-invariant. This is the invariance half of persistence; the `O(ε)`
`C⁰`-closeness half is `CRNT.Dynamics.GraphTransform`'s `manifold_dist_base_le`.

The development is CRN-free and lives in the `ODE` namespace shared with
`CRNT.Dynamics.GraphTransform`, `CRNT.Dynamics.Fenichel`, and `CRNT.Dynamics.FlowConstruction`.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations",
via the Hadamard graph-transform / Lyapunov–Perron method (Carr, "Applications of centre manifold
theory"; Hirsch–Pugh–Shub, "Invariant manifolds"): a uniformly attracting invariant manifold of the
unperturbed layer system persists, for small `ε`, as a nearby invariant manifold realized as the
fixed point of the graph transform, and the graph of that fixed point is invariant under the coupled
flow.

## The graph of a section

For a section `σ : Y → E` the **graph** `graphSet σ = {(y, z) | z = σ y}` is the subset of the
product `Y × E` that the manifold occupies. A point `(y, z)` lies on it exactly when `z = σ y`
(`mem_graphSet`); equivalently `graphSet σ = range (graphMap σ)` with `graphMap σ y = (y, σ y)`
(`graphSet_eq_range`).

## The flow graph transform

`CoupledFlowGraphTransform` bundles a forward semiflow `Φ : Flow ℝ≥0 (Y × E)` of the coupled field
with the graph-transform operator `op : (Y → E) → (Y → E)` it induces, recording the one structural
fact that makes `op` the *flow-then-regraph* map: for the chosen horizon `τ`, the time-`τ` flow sends
each point `(y, σ y)` of `graphSet σ` to a point of `graphSet (op σ)` (`flow_mapsTo`). This is the
content of "push the graph forward by the flow, re-express as a graph over `Y`": the image of the
graph of `σ` lands inside the graph of `op σ`.

**Fixed point ⇒ invariance** (`graphSet_isInvariant_of_fixed`). When `σ` is a fixed point of `op`
(`op σ = σ`), `flow_mapsTo`
becomes a self-map of `graphSet σ` under the time-`τ` flow; the semigroup law of the flow propagates
this to every nonnegative multiple `n · τ` of the horizon, so `graphSet σ` is forward-invariant under
the discrete-time iterate semiflow `n ↦ Φ (n · τ)`. A trajectory started on the graph and sampled at
multiples of `τ` stays on the graph (`onGraph_iterate_of_fixed`). For the genuine
`GraphTransformData` of `CRNT.Dynamics.GraphTransform` realized by such a flow, the Banach fixed point
`M_ε` is the unique invariant section, so its graph is the persisted invariant manifold
(`manifold_graphSet_isInvariant`).

**All-time invariance** (`graphSet_isInvariant_allTime_of_fixed`). If the flow regraphs at *every*
nonnegative time — `flow_mapsTo` strengthened to all `t` (`AllTimeRegraph`) — then a fixed point's
graph is invariant under the full continuous semiflow `Φ t` for all `t`, not only multiples of `τ`.

**Combined persistence** (`fenichel_persistence`). For graph-transform data `G` realized by such a
flow at a fixed point, the persisted manifold section `G.manifold` has a graph that is invariant under
the time-`τ` flow and sits within `G.defect / (1 - G.factor)` of the base section `M_0` in the
supremum metric — the two halves of Fenichel persistence, invariance and `O(ε)` `C⁰`-closeness.

**Out of scope (the residual).** This lands "fixed point of the flow-regraph operator ⇒ invariant
graph", the genuine ODE-to-geometry bridge, under the structural hypothesis `flow_mapsTo` packaging
the operator as the flow-then-regraph map. Constructing that hypothesis from a *concrete* coupled
field `ẏ = ε·g`, `ż = fast y z` — i.e. building the `Flow` on `Y × E` from the field via
`CRNT.Dynamics.FlowConstruction`'s `exists_flow`, then proving its time-`τ` map regraphs a Lipschitz
section to a Lipschitz section with the contraction factor `(Lipschitz/drift)/λ` — is the remaining
analytic step. The flow existence is free (single-valued Picard–Lindelöf, already in
`CRNT.Dynamics.FlowConstruction`); what remains is the explicit `op`-from-coupled-field construction
verifying `flow_mapsTo` and the contraction bound `op_dist_le` simultaneously.

Depends on: `CRNT.Dynamics.GraphTransform`,
`CRNT.Dynamics.FlowConstruction`.
-/

open Function Set
open scoped NNReal BoundedContinuousFunction

namespace ODE

variable {Y : Type*} {E : Type*}

section GraphSet

/-- The graph map of a section `σ : Y → E`: the point `y ↦ (y, σ y)` of the product `Y × E`. -/
def graphMap (σ : Y → E) : Y → Y × E := fun y => (y, σ y)

/-- The **graph** of a section `σ : Y → E` as a subset of the product `Y × E`: the set of points
`(y, z)` with `z = σ y`. This is the region the manifold `{(y, σ y)}` occupies. -/
def graphSet (σ : Y → E) : Set (Y × E) := {p | p.2 = σ p.1}

@[simp] theorem mem_graphSet {σ : Y → E} {p : Y × E} : p ∈ graphSet σ ↔ p.2 = σ p.1 := Iff.rfl

theorem graphMap_mem_graphSet (σ : Y → E) (y : Y) : graphMap σ y ∈ graphSet σ := rfl

/-- The graph of a section is the range of its graph map. -/
theorem graphSet_eq_range (σ : Y → E) : graphSet σ = range (graphMap σ) := by
  ext p
  constructor
  · intro hp; exact ⟨p.1, by rw [graphMap, ← hp]⟩
  · rintro ⟨y, rfl⟩; rfl

end GraphSet

section FlowTransform

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The coupled-flow graph transform.** A forward semiflow `flow : Flow ℝ≥0 (Y × E)` of the
coupled slow–fast field `ẏ = ε·g(y, z)`, `ż = fast y z`, together with the graph-transform operator
`op` it induces and the horizon `τ` at which it acts. The structural hypothesis `flow_mapsTo`
records that `op` *is* the flow-then-regraph map: the time-`τ` flow carries each point `(y, σ y)` of
the graph of `σ` to a point of the graph of `op σ`. Re-graphing the time-`τ` image of `graphSet σ`
over the slow base `Y` yields exactly `graphSet (op σ)`. -/
structure CoupledFlowGraphTransform (Y : Type*) (E : Type*)
    [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The forward semiflow of the coupled slow–fast field on the product `Y × E`. -/
  flow : Flow ℝ≥0 (Y × E)
  /-- The horizon at which the graph transform is taken. -/
  τ : ℝ≥0
  /-- The induced graph-transform / Lyapunov–Perron operator on sections. -/
  op : (Y → E) → (Y → E)
  /-- The time-`τ` flow maps the graph of `σ` into the graph of `op σ`: pushing the graph forward by
  the flow and re-expressing as a graph over `Y` produces `op σ`. -/
  flow_mapsTo : ∀ σ : Y → E, MapsTo (flow.toFun τ) (graphSet σ) (graphSet (op σ))

variable [TopologicalSpace Y]

namespace CoupledFlowGraphTransform

variable (F : CoupledFlowGraphTransform Y E)

/-- **Fixed point ⇒ time-`τ` invariance.** If `σ` is a fixed point of the graph transform
(`op σ = σ`), the time-`τ` flow maps the graph of `σ` into itself: a trajectory on the manifold stays
on it after the horizon `τ`. This is the single-step invariance from which the full forward
invariance follows by the semigroup law. -/
theorem mapsTo_graphSet_of_fixed {σ : Y → E} (hσ : F.op σ = σ) :
    MapsTo (F.flow.toFun F.τ) (graphSet σ) (graphSet σ) := by
  have := F.flow_mapsTo σ
  rwa [hσ] at this

/-- **Fixed point ⇒ invariance at every multiple of the horizon.** Iterating the time-`τ` map by the
semigroup law, the graph of a fixed-point section is mapped into itself by `Φ (n · τ)` for every
`n : ℕ`: sampling a trajectory started on the manifold at multiples of the horizon keeps it on the
manifold. -/
theorem mapsTo_graphSet_iterate_of_fixed {σ : Y → E} (hσ : F.op σ = σ) (n : ℕ) :
    MapsTo (F.flow.toFun (n • F.τ)) (graphSet σ) (graphSet σ) := by
  induction n with
  | zero => simpa using (mapsTo_id _)
  | succ k ih =>
    have hstep := F.mapsTo_graphSet_of_fixed hσ
    intro p hp
    have hsucc : (k + 1) • F.τ = F.τ + k • F.τ := by
      rw [succ_nsmul]; rw [add_comm]
    rw [hsucc, F.flow.map_add]
    exact hstep (ih hp)

/-- **Forward-invariance of the persisted manifold (discrete-time iterate semiflow).** If `σ` is a
fixed point of the graph transform, its graph `graphSet σ` is invariant under the iterate semiflow
`n ↦ Φ (n · τ)` sampling the coupled flow at multiples of the horizon. This is the invariance half of
Fenichel persistence: the graph of `M_ε` is forward-invariant under the coupled flow. -/
theorem graphSet_isInvariant_of_fixed {σ : Y → E} (hσ : F.op σ = σ) :
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (graphSet σ) :=
  fun n => F.mapsTo_graphSet_iterate_of_fixed hσ n

/-- **A trajectory started on the manifold stays on it (sampled at the horizon).** If a point lies on
the graph of a fixed-point section, so does its image under `Φ (n · τ)` for every `n`. The concrete
"trajectory stays on the graph" reading of forward invariance. -/
theorem onGraph_iterate_of_fixed {σ : Y → E} (hσ : F.op σ = σ) {p : Y × E}
    (hp : p ∈ graphSet σ) (n : ℕ) : F.flow.toFun (n • F.τ) p ∈ graphSet σ :=
  F.mapsTo_graphSet_iterate_of_fixed hσ n hp

/-- **All-time regraphing.** The flow regraphs the graph of every section into the graph of `op σ` at
*every* nonnegative time, not just the fixed horizon `τ`. This is the property a genuine autonomous
coupled flow enjoys: the graph transform is consistent across the whole forward semiflow. -/
def AllTimeRegraph : Prop :=
  ∀ (t : ℝ≥0) (σ : Y → E), MapsTo (F.flow.toFun t) (graphSet σ) (graphSet (F.op σ))

/-- **All-time forward-invariance of the persisted manifold.** Under all-time regraphing, the graph
of a fixed-point section is invariant under the *full continuous* coupled semiflow `Φ t` for every
`t ≥ 0`, not only at multiples of the horizon. This is the full continuous-time invariance half of
Fenichel persistence. -/
theorem graphSet_isInvariant_allTime_of_fixed (hreg : F.AllTimeRegraph) {σ : Y → E}
    (hσ : F.op σ = σ) : IsInvariant F.flow.toFun (graphSet σ) := by
  intro t p hp
  have := hreg t σ hp
  rwa [hσ] at this

end CoupledFlowGraphTransform

end FlowTransform

section Persistence

variable [TopologicalSpace Y] [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]

omit [CompleteSpace E] [NormedSpace ℝ E] in
/-- Realize the underlying section of a bounded section `σ : Y →ᵇ E` as a plain section `Y → E`. -/
@[simp] theorem graphSet_coe (σ : Y →ᵇ E) :
    graphSet (σ : Y → E) = {p : Y × E | p.2 = σ p.1} := rfl

/-- **Fenichel `ε`-persistence (invariance + `O(ε)` closeness).** Let `G` be graph-transform data
(`CRNT.Dynamics.GraphTransform`) whose contraction furnishes the unique perturbed manifold section
`G.manifold = M_ε`, and let `F` be a coupled-flow graph transform realizing `G` — its operator agrees
with `G.op` on the relevant section and its time-`τ` flow regraphs accordingly. Then the graph of the
persisted manifold is forward-invariant under the iterate coupled semiflow, and the manifold sits
within `G.defect / (1 - G.factor)` of the base section `M_0` in the supremum metric. These are the two
halves of persistence: invariance of `M_ε` and its `O(ε)` `C⁰`-closeness to `M_0`. -/
theorem fenichel_persistence (G : GraphTransformData Y E)
    (F : CoupledFlowGraphTransform Y E)
    (hfix : F.op (G.manifold : Y → E) = (G.manifold : Y → E)) :
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (graphSet (G.manifold : Y → E)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) :=
  ⟨F.graphSet_isInvariant_of_fixed hfix, G.manifold_dist_base_le⟩

/-- **The persisted Fenichel manifold is invariant.** Specialization of `fenichel_persistence` to the
invariance conclusion: the graph of the Banach fixed-point section `M_ε` of `G`, realized by the
coupled flow `F`, is forward-invariant under the iterate coupled semiflow. -/
theorem manifold_graphSet_isInvariant (G : GraphTransformData Y E)
    (F : CoupledFlowGraphTransform Y E)
    (hfix : F.op (G.manifold : Y → E) = (G.manifold : Y → E)) :
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (graphSet (G.manifold : Y → E)) :=
  (fenichel_persistence G F hfix).1

end Persistence

end ODE

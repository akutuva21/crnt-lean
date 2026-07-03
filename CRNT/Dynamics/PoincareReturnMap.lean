import CRNT.Dynamics.TransversalCrossingTime

/-!
# The Poincaré first-return map

The Poincaré (first-return) map of a planar flow sends a state on a transversal section back to
the section by following the flow until it next meets the section. Built on the transversal
first-crossing time `crossingTime` of `CRNT.Dynamics.TransversalCrossingTime`, the return map is
`P(x) = Φ x (τ x)`: flow the state `x` for its crossing time `τ x`. Its fixed point on the
section is a periodic orbit of the flow, the object the Hopf rotation-closure step needs.

## What this module establishes

* **Exact base crossing time** (`crossingTime_base`). The implicit function returned by the
  bivariate implicit function theorem hits the seed exactly: `τ base = time`. The
  `crossingTime_tendsto` of the underlying module gives this only as a limit; the
  equation-characterization of the implicit function pins it on the nose.
* **Strict positivity near the base** (`crossingTime_pos`). When the base crossing time is
  positive, continuity of `τ` makes the crossing time of every nearby state positive: the flow
  genuinely runs forward before returning to the section. This is positivity of the return time,
  not strict first-ness (no earlier crossing); strict first-ness is left as residue.
* **The return map** (`returnMap`), `P(x) = Φ x (τ x)`, with
  - **section landing** (`returnMap_mem_section`): for `x` near `base`, `P(x)` lies on the
    section `S = { y | ⟪y − point, normal⟫ = 0 }`, since `τ x` is by construction a crossing time;
  - **fixed-point compatibility** (`returnMap_base`): the base returns to the section's seed
    point, `P(base) = point`, because `τ base = time` and the base crosses at `point`;
  - **continuity** (`continuousAt_returnMap`): `P` is continuous at `base`, by joint continuity
    of the flow composed with the continuous crossing time;
  - **`C¹` dependence** (`hasFDerivAt_returnMap`): `P` has a Fréchet derivative at `base`, the
    joint flow derivative composed with the state-and-crossing-time pairing `(id, Dτ)` by the
    chain rule — the differentiable Poincaré map whose derivative spectrum and fixed point discharge
    the Hopf rotation-closure step.

The differentiable return map consumes the *joint* Fréchet derivative of the flow in state and time
at the crossing — the variational operator together with the field — which the section carries as
the datum `jointFlowDeriv`.

(Poincaré, *Les méthodes nouvelles de la mécanique céleste*, vol. I, on the section map;
Hartman, *Ordinary Differential Equations*, IX.10, on the differentiable first-return map.)

Depends on: `CRNT.Dynamics.TransversalCrossingTime`.
-/

namespace CRNT

open Filter Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace TransversalSection

variable (S : TransversalSection (E := E))

/-- **The base crossing time is hit exactly.** The implicit function `τ` returned by the
bivariate implicit function theorem solves the section equation at the seed exactly, so
`τ base = time`. The equation-characterization of the implicit function — near the seed,
`sectionCoord x t = sectionCoord base time ↔ τ x = t` — read at the seed itself, where the left
side is reflexively true, forces `τ base = time`. -/
theorem crossingTime_base : S.crossingTime S.base = S.time := by
  have h := eventually_apply_eq_iff_implicitFunctionOfBivariate
    (u := (S.base, S.time)) (f := S.sectionCoord)
    (f₁ := fun x t => S.spaceCoordDeriv x t)
    (f₂ := fun x t => ContinuousLinearMap.toSpanSingleton ℝ ⟪S.field (S.flow x t), S.normal⟫)
    S.hasFDeriv_space_coord S.hasFDeriv_time
    S.continuousAt_spaceCoordDeriv S.continuousAt_timeDeriv
    (by simpa [S.isCrossing] using toSpanSingleton_isInvertible S.transversal)
  have h0 := h.self_of_nhds
  simpa [crossingTime] using (h0.mp rfl)

/-- **Strict positivity of the crossing time near the base.** When the base crossing time is
positive, continuity of the crossing time at the base (and `τ base = time`) makes `τ x` positive
for every state `x` near `base`: the flow genuinely runs forward before returning to the section.
This is positivity of the return time; that no earlier crossing exists (strict first-ness) is not
asserted. -/
theorem crossingTime_pos (htime : 0 < S.time) :
    ∀ᶠ x in 𝓝 S.base, 0 < S.crossingTime x := by
  have hcont : ContinuousAt S.crossingTime S.base := S.crossingTime_continuousAt
  have hbase : S.crossingTime S.base = S.time := S.crossingTime_base
  have : ∀ᶠ x in 𝓝 S.base, S.crossingTime x ∈ Set.Ioi (0 : ℝ) :=
    hcont (by simpa [hbase] using isOpen_Ioi.mem_nhds htime)
  simpa [Set.mem_Ioi] using this

/-! ## The first-return map -/

/-- **The Poincaré first-return map.** `returnMap x = Φ x (τ x)`: flow the state `x` for its
transversal crossing time `τ x`, landing back on the section. Its fixed point on the section is a
periodic orbit of the flow. -/
noncomputable def returnMap (x : E) : E := S.flow x (S.crossingTime x)

/-- **The signed section coordinate of the return map is the crossing coordinate.** The return
map evaluated at `x` is the flow of `x` at its crossing time, so its signed distance to the
section is `sectionCoord x (τ x)`. -/
theorem sectionCoord_returnMap (x : E) :
    ⟪S.returnMap x - S.point, S.normal⟫ = S.sectionCoord x (S.crossingTime x) := rfl

/-- **The return map lands on the section.** For every state `x` near `base`, the return map
`returnMap x = Φ x (τ x)` lies on the section `S = { y | ⟪y − point, normal⟫ = 0 }`, because
`τ x` is by construction a crossing time of the flow line of `x`. -/
theorem returnMap_mem_section :
    ∀ᶠ x in 𝓝 S.base, ⟪S.returnMap x - S.point, S.normal⟫ = 0 := by
  filter_upwards [S.crossingTime_isCrossing] with x hx
  rw [S.sectionCoord_returnMap, hx]

/-- **The base returns to the section seed.** The return map fixes the seed crossing point:
`returnMap base = point`. Since `τ base = time` and the base crosses the section at `point`
(`flow base time = point`), the base flows for exactly its base crossing time and lands on
`point`. This is the fixed-point compatibility at the known crossing. -/
@[simp] theorem returnMap_base : S.returnMap S.base = S.point := by
  rw [returnMap, S.crossingTime_base, S.isCrossing]

/-- **Continuity of the return map at the base.** The return map `x ↦ Φ x (τ x)` is continuous
at the base state, by joint continuity of the flow composed with the continuous crossing time
`x ↦ (x, τ x)`. This is the continuous dependence of the first return on the initial state — the
regularity a Poincaré fixed-point search consumes. -/
theorem continuousAt_returnMap : ContinuousAt S.returnMap S.base := by
  have hpair : ContinuousAt (fun x => (x, S.crossingTime x)) S.base :=
    continuousAt_id.prodMk S.crossingTime_continuousAt
  have hflow : ContinuousAt (Function.uncurry S.flow) (S.base, S.crossingTime S.base) :=
    S.cont_flow.continuousAt
  exact ContinuousAt.comp (x := S.base)
    (f := fun x => (x, S.crossingTime x)) (g := Function.uncurry S.flow) hflow hpair

/-! ## The differentiable first-return map -/

/-- **`C¹` dependence of the first-return map on the initial state.** The return map
`returnMap x = Φ x (τ x)` is the composition of `x ↦ (x, τ x)` with the flow `(x, t) ↦ Φ x t`. By
the chain rule its Fréchet derivative at the base is the joint flow derivative composed with the
state-and-crossing-time pairing `(id, Dτ)`, where `Dτ` is the strict derivative of the crossing
time. This upgrades the mere continuity of `continuousAt_returnMap` to genuine `C¹` dependence —
the differentiable Poincaré map whose derivative spectrum and fixed point discharge the Hopf
rotation-closure step. -/
theorem hasFDerivAt_returnMap :
    HasFDerivAt S.returnMap
      ((S.jointFlowDeriv S.base S.time).comp
        ((ContinuousLinearMap.id ℝ E).prod
          (-(ContinuousLinearMap.toSpanSingleton ℝ ⟪S.field S.point, S.normal⟫).inverse ∘L
            S.spaceCoordDeriv S.base S.time)))
      S.base := by
  have hpair :
      HasFDerivAt (fun x => (x, S.crossingTime x))
        ((ContinuousLinearMap.id ℝ E).prod
          (-(ContinuousLinearMap.toSpanSingleton ℝ ⟪S.field S.point, S.normal⟫).inverse ∘L
            S.spaceCoordDeriv S.base S.time))
        S.base :=
    (hasFDerivAt_id S.base).prodMk S.hasStrictFDerivAt_crossingTime.hasFDerivAt
  have hflow :
      HasFDerivAt (fun p : E × ℝ => S.flow p.1 p.2) (S.jointFlowDeriv S.base S.time)
        (S.base, S.crossingTime S.base) := by
    rw [S.crossingTime_base]; exact S.hasFDeriv_flow_joint
  exact hflow.comp S.base hpair

end TransversalSection

end CRNT

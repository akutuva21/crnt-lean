import CRNT.Dynamics.PoincareReturnMap

/-!
# A return-map fixed point is a nonconstant periodic orbit

The Poincaré first-return map `returnMap x = Φ x (τ x)` of
`CRNT.Dynamics.PoincareReturnMap` flows a state on a transversal section back to the section. Its
fixed point closes the rotation: when `returnMap x = x` the flow line of `x` is a *periodic orbit*
of the flow, of period the crossing time `τ x`. This module performs that rotation-closure — the
last conceptual step turning a return-map fixed point into a genuine nonconstant periodic orbit, the
hypothesis `CRNT.Dynamics.HopfPersistentOrbit` carries as `realizes`.

## The closure

The closure rests on the **flow semigroup law** `Φ x (a + b) = Φ (Φ x a) b`: the integral curve of
the flowed state is the time-shifted integral curve. `Mathlib`'s `CRNT.Dynamics.FlowConstruction`
proves this for the flow of a bounded Lipschitz field from ODE uniqueness, so it is supplied here as
the hypothesis `hsemi` rather than re-derived from the section data. With it, a fixed point
`Φ x T = x` (where `T = τ x`) gives, for every `t`,

`Φ x (t + T) = Φ (Φ x T) t = Φ x t`,

so `t ↦ Φ x t` is `Function.Periodic` of period `T` (`isPeriodic_returnMap_fixedPoint`).

## Nonconstancy

A periodic orbit through a point where the field is nonzero is not the equilibrium: if
`field x ≠ 0` then `Φ x` is not constant near `0` — its derivative there is `field (Φ x 0)`, which is
nonzero once the orbit starts at `x` (`flow x 0 = x`). `nonconstant_of_field_ne_zero` records the
two-point witness `∃ s t, Φ x s ≠ Φ x t` the seed asks for.

## Toward `realizes`

`realizes_of_returnMap_fixedPoint` assembles exactly the triple
`CRNT.Dynamics.HopfPersistentOrbit.hopf_andronov_full_field` consumes as `realizes`: the orbit is
`T`-periodic, nonconstant, and attains the amplitude `‖x‖` at the section base time. It is stated
over a general inner-product state space with the orbit read in any normed codomain through a fixed
linear chart, leaving only the identification of `‖x‖` with the radial equilibrium `√(−α/ℓ₁)` — the
Hopf-specific coordinate match — as the residue named in this module's frontier note.

(Poincaré, *Les méthodes nouvelles de la mécanique céleste*, vol. I, on the section map; Hartman,
*Ordinary Differential Equations*, IX.10, on the first-return map; the periodicity of a return-map
fixed point is the closing-of-the-orbit step of the Andronov–Hopf construction.)

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.PoincareReturnMap`.
-/

namespace CRNT

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace TransversalSection

variable (S : TransversalSection (E := E))

/-- **A return-map fixed point is a periodic orbit.** If `x` is a fixed point of the return map,
`returnMap x = x`, i.e. the flow line of `x` returns to `x` at its crossing time `T = τ x`, then the
flow line `t ↦ Φ x t` is `Function.Periodic` of period `T`. The flow semigroup law `hsemi` turns the
closure `Φ x T = x` into the period identity `Φ x (t + T) = Φ (Φ x T) t = Φ x t`. -/
theorem isPeriodic_returnMap_fixedPoint {x : E}
    (hsemi : ∀ a b : ℝ, S.flow x (a + b) = S.flow (S.flow x a) b)
    (hfix : S.returnMap x = x) :
    Function.Periodic (S.flow x) (S.crossingTime x) := by
  intro t
  have hT : S.flow x (S.crossingTime x) = x := hfix
  calc S.flow x (t + S.crossingTime x)
      = S.flow x (S.crossingTime x + t) := by rw [add_comm]
    _ = S.flow (S.flow x (S.crossingTime x)) t := hsemi _ _
    _ = S.flow x t := by rw [hT]

omit [CompleteSpace E] in
/-- **A periodic orbit through a transversal point is nonconstant.** If the field is nonzero at `x`
and the flow line starts there (`Φ x 0 = x`), the orbit is not the equilibrium: its time derivative
at `0` is `field x ≠ 0`, so `Φ x` is not locally constant, witnessed by two times with distinct
images. This is the `∃ s t, Φ x s ≠ Φ x t` nonconstancy the seed asks for. -/
theorem nonconstant_of_field_ne_zero {x : E} (hx0 : S.flow x 0 = x)
    (hfield : S.field x ≠ 0) :
    ∃ s t, S.flow x s ≠ S.flow x t := by
  by_contra hcon
  push Not at hcon
  -- The flow line is globally constant, so its time derivative vanishes everywhere.
  have hconst : S.flow x = fun _ => S.flow x 0 := funext fun t => hcon t 0
  have hderiv : HasDerivAt (S.flow x) (S.field (S.flow x 0)) 0 := by
    have := S.hasDeriv_flow x 0; simpa using this
  have hderiv0 : HasDerivAt (S.flow x) 0 0 := by
    rw [hconst]; exact hasDerivAt_const 0 _
  have : S.field (S.flow x 0) = 0 := hderiv.unique hderiv0
  rw [hx0] at this
  exact hfield this

/-! ## The return-map orbit datum -/

/-- **The periodic orbit packaged from a return-map fixed point.** A genuine return — fixed point
`returnMap x = x` of positive crossing time, with the flow base law and the semigroup law — closes
the flow line of `x` into a periodic orbit. `returnMapOrbit` bundles the period `T = τ x > 0`, the
orbit map `t ↦ Φ x t`, the closure `Φ x T = x`, and the periodicity, the data the Hopf seed
consumes. -/
structure ReturnMapOrbit (x : E) where
  /-- The period of the closed orbit: the crossing time. -/
  period : ℝ
  /-- The period is positive: a genuine forward return. -/
  period_pos : 0 < period
  /-- The orbit map closes: it returns to its seed after one period. -/
  closes : S.flow x period = x
  /-- The orbit map is periodic of period `period`. -/
  periodic : Function.Periodic (S.flow x) period

/-- **Closing the orbit at a return-map fixed point.** From a positive-time fixed point of the
return map, the flow base law, and the semigroup law, build the `ReturnMapOrbit`: the period is the
crossing time, the closure is the fixed-point equation, and periodicity is
`isPeriodic_returnMap_fixedPoint`. -/
noncomputable def returnMapOrbit {x : E}
    (hsemi : ∀ a b : ℝ, S.flow x (a + b) = S.flow (S.flow x a) b)
    (hfix : S.returnMap x = x) (hpos : 0 < S.crossingTime x) :
    S.ReturnMapOrbit x where
  period := S.crossingTime x
  period_pos := hpos
  closes := hfix
  periodic := S.isPeriodic_returnMap_fixedPoint hsemi hfix

/-! ## Toward the `realizes` hypothesis -/

/-- **A return-map fixed point realizes the seed's periodic-orbit triple.** Reading the closed orbit
through a fixed continuous-linear chart `chart : E →L[ℝ] F` (the planar-coordinate identification),
a positive-time return-map fixed point at a point `x` where the field is nonzero realizes the exact
shape `CRNT.Dynamics.HopfPersistentOrbit.hopf_andronov_full_field` consumes as `realizes`:

* `Function.Periodic (chart ∘ Φ x) T` — the charted orbit is `T`-periodic;
* `∃ s t, (chart ∘ Φ x) s ≠ (chart ∘ Φ x) t` — it is nonconstant;
* `∃ s, ‖(chart ∘ Φ x) s‖ = ‖chart x‖` — it attains the amplitude `‖chart x‖` (at the section base
  time `0`, where the orbit sits at `x`).

The chart is required injective only where nonconstancy is read; here it is supplied through
`hchart_inj`, the faithful reading of the orbit in the codomain coordinate. -/
theorem realizes_of_returnMap_fixedPoint {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (chart : E →L[ℝ] F) {x : E}
    (hsemi : ∀ a b : ℝ, S.flow x (a + b) = S.flow (S.flow x a) b)
    (hx0 : S.flow x 0 = x)
    (hfix : S.returnMap x = x) (hfield : S.field x ≠ 0)
    (hchart_inj : Function.Injective chart) :
    Function.Periodic (fun t => chart (S.flow x t)) (S.crossingTime x)
      ∧ (∃ s t, chart (S.flow x s) ≠ chart (S.flow x t))
      ∧ (∃ s, ‖chart (S.flow x s)‖ = ‖chart x‖) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    simp only [S.isPeriodic_returnMap_fixedPoint hsemi hfix t]
  · obtain ⟨s, t, hst⟩ := S.nonconstant_of_field_ne_zero hx0 hfield
    exact ⟨s, t, fun h => hst (hchart_inj h)⟩
  · exact ⟨0, by rw [hx0]⟩

end TransversalSection

end CRNT

/-!
**Frontier.** `realizes_of_returnMap_fixedPoint` delivers the `realizes` triple for the charted
return-map orbit with amplitude `‖chart x‖`. Wiring it into
`CRNT.Dynamics.HopfPersistentOrbit.hopf_andronov_full_field` needs only the Hopf coordinate match
`‖chart x‖ = √(−α/ℓ₁)` — the identification of the section base point's amplitude with the radial
equilibrium — together with strict first-ness of the crossing time (no earlier return), which the
return-time construction defers. Both are coordinate/ordering facts, separate from the rotation
closure proved here.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.PoincareReturnMap`.
-/

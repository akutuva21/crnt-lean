import CRNT.Dynamics.MichaelisMentenReduced

/-!
# Monotone depletion of the constructed Michaelis–Menten substrate

This module records the qualitative dynamics of the constructed Michaelis–Menten reduced flow
`mmSubstrate` of `CRNT.Dynamics.MichaelisMentenReduced`: the substrate is **monotonically depleted**.
The reduced scalar field `mmReducedField Km Vmax` is nonpositive everywhere (`mmReducedField_nonpos`),
so the constructed substrate curve has nonpositive derivative at every time and is therefore globally
antitone (`mmSubstrate_antitone`). From a nonnegative initial substrate it stays in `[0, s₀]` for all
forward time (`mmSubstrate_le_init`), and being antitone and bounded below it **settles to a limit**
(`mmSubstrate_tendsto_atTop`) — the substrate concentration relaxes monotonically toward a steady
value, the expected behaviour of an enzyme reaction consuming its substrate.

## Main results

* `mmSubstrate_antitone` — the constructed substrate curve is antitone.
* `mmSubstrate_le_init` — from a nonnegative start it stays at or below `s₀` on the forward ray.
* `mmSubstrate_tendsto_atTop` — the substrate curve converges as `t → ∞`.

Depends on: `CRNT.Dynamics.MichaelisMentenReduced`.
-/

open Filter Set
open scoped Topology

namespace CRNT.MichaelisMenten

/-- **Global antitonicity.** The constructed Michaelis–Menten substrate curve is antitone: its
derivative is the everywhere-nonpositive reduced field, so the substrate never increases. -/
theorem mmSubstrate_antitone (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) (s₀ : ℝ) :
    Antitone (mmSubstrate Km Vmax hKm hV s₀) := by
  have hd := mmSubstrate_hasDerivAt Km Vmax hKm hV s₀
  refine antitone_of_deriv_nonpos (fun t => (hd t).differentiableAt) (fun t => ?_)
  rw [(hd t).deriv]
  exact mmReducedField_nonpos Km Vmax hKm hV _

/-- **Forward depletion bound.** From a nonnegative initial substrate the constructed curve stays at
or below its initial value on the forward ray. -/
theorem mmSubstrate_le_init (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) (s₀ : ℝ)
    {t : ℝ} (ht : 0 ≤ t) : mmSubstrate Km Vmax hKm hV s₀ t ≤ s₀ := by
  have := mmSubstrate_antitone Km Vmax hKm hV s₀ ht
  rwa [mmSubstrate_init Km Vmax hKm hV s₀] at this

/-- The constructed substrate curve is nonnegative at every time, given a nonnegative start: forward
times are handled by `mmSubstrate_nonneg`, and backward times dominate the start by antitonicity. -/
theorem mmSubstrate_nonneg_all (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ} (hs0 : 0 ≤ s₀)
    (t : ℝ) : 0 ≤ mmSubstrate Km Vmax hKm hV s₀ t := by
  rcases le_or_gt 0 t with ht | ht
  · exact mmSubstrate_nonneg Km Vmax hKm hV hs0 ht
  · have := mmSubstrate_antitone Km Vmax hKm hV s₀ ht.le
    rw [mmSubstrate_init Km Vmax hKm hV s₀] at this
    linarith

/-- **The substrate settles to a limit.** Being antitone and bounded below by `0`, the constructed
Michaelis–Menten substrate curve converges as `t → ∞`: the substrate concentration relaxes
monotonically toward a steady value. -/
theorem mmSubstrate_tendsto_atTop (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ}
    (hs0 : 0 ≤ s₀) :
    ∃ L : ℝ, Tendsto (mmSubstrate Km Vmax hKm hV s₀) atTop (𝓝 L) := by
  refine ⟨_, tendsto_atTop_ciInf (mmSubstrate_antitone Km Vmax hKm hV s₀) ?_⟩
  exact ⟨0, fun y hy => by obtain ⟨t, rfl⟩ := hy; exact mmSubstrate_nonneg_all Km Vmax hKm hV hs0 t⟩

end CRNT.MichaelisMenten

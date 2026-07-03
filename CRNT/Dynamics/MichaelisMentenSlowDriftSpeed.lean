import CRNT.Dynamics.MichaelisMentenSlowDrift
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The substrate-path speed bound of the ε-coupled Michaelis–Menten flow, derived from its drift

This module removes the speed-bound hypothesis from the `O(ε)` slaved-velocity estimate of
`CRNT.Dynamics.MichaelisMentenSlowDrift`. There the slaved complex velocity is bounded by
`(L / rate)·(ε·G)` only *after* assuming the substrate path satisfies the Lipschitz speed bound
`dist (s t) (s t') ≤ (ε·G)·|t - t'|`. Here that speed bound is itself *derived* from the pointwise
defining law of the coupled flow — the substrate solves `ṡ = ε·g(s, z)` (`mmRegSlowDrift`) with the
uniform drift bound `‖g‖ ≤ G` — by the one-dimensional mean-value inequality
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`. The resulting velocity bound therefore rests
only on the drift bound `‖g‖ ≤ G`, not on an assumed Lipschitz substrate path.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations",
and Tikhonov: on an attracting slow manifold the slaved fast variable tracks the slow flow at speed
`O(ε)`. The substrate of `ṡ = ε·g(s, z)` moves at speed `O(ε)` because its derivative is everywhere
`ε·g`, whose norm is at most `ε·G`; the mean-value inequality converts that pointwise derivative
bound into the displacement bound `dist (s t) (s t') ≤ (ε·G)·|t - t'|`.

**The derived speed bound** (`mmRegSubstrate_speed_le`). For a substrate path `s : ℝ → ℝ` solving the
coupled slow law `HasDerivAt s (mmRegSlowDrift ε g (s τ) (z τ)) τ` at every time `τ`, under the
uniform drift bound `‖g a b‖ ≤ G` and `0 ≤ ε`, the substrate is `(ε·G)`-Lipschitz in time:
`dist (s t) (s t') ≤ (ε·G)·|t - t'|`.

**The hypothesis-reduced velocity bound** (`mmRegSlavedVelocity_le_of_drift`). Feeding the derived
speed bound into `mmRegSlavedVelocity_le` gives the `O(ε)` slaved complex velocity bound
`‖mmRegSlavedVelocity …‖ ≤ (L / rate)·(ε·G)` with `hspeed` discharged: the only kinetic hypotheses
left are the fast-field substrate Lipschitz constant `L` and the slow drift bound `‖g‖ ≤ G`. This is
the certified `O(ε)` Michaelis–Menten slaving velocity resting on the drift bound alone, valid over
the whole substrate line.

Depends on: CRNT.Dynamics.MichaelisMentenSlowDrift,
Mathlib.Analysis.Calculus.MeanValue.
-/

open scoped RealInnerProductSpace

namespace CRNT.MichaelisMenten

/-- **The substrate path of the ε-coupled flow is `(ε·G)`-Lipschitz in time, derived from its drift.**
A substrate path `s` solving the coupled slow law `ṡ = ε·g(s, z)` (`HasDerivAt s (mmRegSlowDrift ε g
(s τ) (z τ)) τ` at every `τ`) has time derivative `ε·g(s τ)(z τ)` of norm at most `ε·G` under the
uniform drift bound `‖g‖ ≤ G`. The one-dimensional mean-value inequality converts this pointwise
derivative bound into the displacement bound `dist (s t) (s t') ≤ (ε·G)·|t - t'|`. This is the speed
bound assumed as `hspeed` in `mmRegSlavedVelocity_le`, here derived from the defining drift law. -/
theorem mmRegSubstrate_speed_le {ε G : ℝ} (hε : 0 ≤ ε) {g : ℝ → E → ℝ}
    (hg : ∀ a b, ‖g a b‖ ≤ G) {s : ℝ → ℝ} {z : ℝ → E}
    (hs : ∀ τ, HasDerivAt s (mmRegSlowDrift ε g (s τ) (z τ)) τ) :
    ∀ t t', dist (s t) (s t') ≤ (ε * G) * |t - t'| := by
  intro t t'
  have hbound : ∀ τ ∈ (Set.univ : Set ℝ),
      ‖mmRegSlowDrift ε g (s τ) (z τ)‖ ≤ ε * G := by
    intro τ _
    rw [mmRegSlowDrift_apply, norm_mul, Real.norm_eq_abs, abs_of_nonneg hε]
    exact mul_le_mul_of_nonneg_left (hg (s τ) (z τ)) hε
  have hmv := (convex_univ (𝕜 := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := s) (f' := fun τ => mmRegSlowDrift ε g (s τ) (z τ))
    (fun τ _ => (hs τ).hasDerivWithinAt) hbound (Set.mem_univ t') (Set.mem_univ t)
  rw [Real.dist_eq]
  calc |s t - s t'| = ‖s t - s t'‖ := (Real.norm_eq_abs _).symm
    _ ≤ (ε * G) * ‖t - t'‖ := hmv
    _ = (ε * G) * |t - t'| := by rw [Real.norm_eq_abs]

/-- **The certified `O(ε)` slaved velocity resting on the drift bound alone.** With the regularized
fast field uniformly `L`-Lipschitz in the substrate and the substrate path solving the coupled slow
law `ṡ = ε·g(s, z)` under the uniform drift bound `‖g‖ ≤ G`, the slaved complex curve's velocity is
bounded by `(L / rate)·(ε·G)`. This is `mmRegSlavedVelocity_le` with its speed hypothesis discharged
by `mmRegSubstrate_speed_le`: the bound is `O(ε)` and the only remaining kinetic inputs are the
fast-field substrate Lipschitz constant `L` and the slow drift bound `‖g‖ ≤ G`, valid over the whole
substrate line. -/
theorem mmRegSlavedVelocity_le_of_drift (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km)
    {L ε G : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hlip : ∀ s s' z, ‖mmRegFastField rate Km Vmax s z - mmRegFastField rate Km Vmax s' z‖
      ≤ L * dist s s')
    {g : ℝ → E → ℝ} (hg : ∀ a b, ‖g a b‖ ≤ G) {s : ℝ → ℝ} {z : ℝ → E}
    (hs : ∀ τ, HasDerivAt s (mmRegSlowDrift ε g (s τ) (z τ)) τ) {t₀ : ℝ} :
    ‖mmRegSlavedVelocity rate hrate Km Vmax hKm (s t₀)
        (mmRegSlowDrift ε g (s t₀) (z t₀))‖ ≤ (L / rate) * (ε * G) :=
  mmRegSlavedVelocity_le rate hrate Km Vmax hKm hL hε hG hlip
    (mmRegSubstrate_speed_le hε hg hs)
    (s' := fun τ => mmRegSlowDrift ε g (s τ) (z τ)) (hs t₀)

end CRNT.MichaelisMenten

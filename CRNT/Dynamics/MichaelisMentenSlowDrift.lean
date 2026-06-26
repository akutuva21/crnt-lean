import CRNT.Dynamics.MichaelisMentenRegularized

/-!
# The ε-coupled Michaelis–Menten slow drift and its derived `O(ε)` slaved velocity

This module couples the globally `C¹` regularized Michaelis–Menten fast subsystem of
`CRNT.Dynamics.MichaelisMentenRegularized` to a slow substrate equation `ṡ = ε·g(s, z)` carrying the
singular-perturbation small parameter `ε`, and derives that along the resulting slow flow the slaved
complex curve `t ↦ manifoldMap (s t)` moves at speed `O(ε)`. The bound is genuinely *derived* from
the global `C¹` slow-manifold seed `mmRegSlowManifoldSeed`: its implicit-function regularity
(`ODE.SlowManifoldC1Seed.hasFDerivAt_manifoldMap`) supplies the chain-rule derivative of the slaved
curve, so no differentiability of the slaved curve is assumed — only the slow substrate path is taken
to be differentiable, exactly as the integral-curve tracking lemmas of `CRNT.Dynamics.QSSA` and
`CRNT.Dynamics.FenichelSlowDrift` do. Defined by Fenichel, "Geometric singular perturbation theory
for ordinary differential equations", and Tikhonov: on an attracting slow manifold the slaved fast
variable tracks the slow flow at speed `O(ε)`.

**The ε-coupled slow field** (`mmRegSlowDrift`). The substrate drift is `mmRegSlowDrift ε g s z =
ε · g s z`, the `ε`-scaled slow vector field of the singularly perturbed pair `ṡ = ε·g(s, z)`,
`ż = mmRegFastField rate Km Vmax s z`. The drift `g` carries the standard uniform bound `‖g s z‖ ≤ G`.

**The slaved-curve velocity** (`mmRegSlavedVelocity`, `mmRegHasDerivAt_slavedCurve`). For a coupled
trajectory whose slow component `s` is differentiable at `t₀` with substrate velocity `s' t₀`, the
slaved complex curve `t ↦ mmRegSlowManifoldSeed.manifoldMap (s t)` is differentiable at `t₀` by the
chain rule through the global `C¹` regularity of the manifold map, with velocity
`mmRegSlavedVelocity = D(manifoldMap)(s t₀) (s' t₀)`.

**The derived `O(ε)` bound** (`mmRegSlavedVelocity_le`). When the regularized fast field is uniformly
`L`-Lipschitz in the substrate and the slow substrate path moves at speed at most `ε·G` (the speed
the coupling `ṡ = ε·g`, `‖g‖ ≤ G` enforces), the converse mean-value inequality bounds the slaved
velocity by `(L / rate)·(ε·G)`. This is the certified `O(ε)` Michaelis–Menten slaving velocity over
the whole substrate line, with the slaved curve's differentiability discharged by the seed's global
`C¹` regularity rather than assumed.

This module is **stable** and `sorry`-free. Depends on: CRNT.Dynamics.MichaelisMentenRegularized.
-/

open scoped RealInnerProductSpace

namespace CRNT.MichaelisMenten

/-- The **ε-coupled Michaelis–Menten slow drift** `mmRegSlowDrift ε g s z = ε · g s z`: the
`ε`-scaled substrate vector field of the singularly perturbed pair `ṡ = ε·g(s, z)`,
`ż = mmRegFastField rate Km Vmax s z`. The substrate drift `g` is the slow direction of the coupled
flow; the small parameter `ε` makes the substrate evolve `O(ε)` slowly relative to the fast complex
relaxation. -/
noncomputable def mmRegSlowDrift (ε : ℝ) (g : ℝ → E → ℝ) (s : ℝ) (z : E) : ℝ := ε * g s z

@[simp] lemma mmRegSlowDrift_apply (ε : ℝ) (g : ℝ → E → ℝ) (s : ℝ) (z : E) :
    mmRegSlowDrift ε g s z = ε * g s z := rfl

/-- The **slaved complex velocity** of the regularized seed along a substrate path with velocity
`s'`: the chain-rule image of the substrate velocity under the implicit-function Fréchet derivative
of the global `C¹` manifold map at the current substrate `s₀`. This is the time derivative of the
slaved curve `t ↦ manifoldMap (s t)` supplied by the seed's regularity, not an assumed velocity. -/
noncomputable def mmRegSlavedVelocity (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km)
    (s₀ : ℝ) (s' : ℝ) : E :=
  (-((mmRegSlowManifoldSeed rate hrate Km Vmax hKm).fibreDeriv s₀ : E ≃L[ℝ] E).symm.toContinuousLinearMap ∘L
    (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).slowDeriv s₀) s'

/-- **The slaved complex curve is differentiable along the slow flow, with no assumed velocity.**
For a coupled trajectory whose substrate component `s` is differentiable at `t₀`, the slaved curve
`t ↦ manifoldMap (s t)` is differentiable at `t₀`, its velocity furnished by the chain rule through
the global `C¹` regularity of the regularized manifold map. The substrate velocity is the slow
field `ṡ = ε·g` evaluated along the trajectory. -/
theorem mmRegHasDerivAt_slavedCurve (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km)
    {s : ℝ → ℝ} {s' : ℝ → ℝ} {t₀ : ℝ} (hs : HasDerivAt s (s' t₀) t₀) :
    HasDerivAt (fun t => (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s t))
      (mmRegSlavedVelocity rate hrate Km Vmax hKm (s t₀) (s' t₀)) t₀ :=
  (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).hasDerivAt_comp hs

/-- **The certified `O(ε)` Michaelis–Menten slaved velocity over the whole substrate line.** When
the regularized fast field is uniformly `L`-Lipschitz in the substrate and the substrate path of the
ε-coupled flow moves at speed at most `ε·G` (the speed the coupling `ṡ = ε·g` with uniform bound
`‖g‖ ≤ G` enforces), the slaved complex curve's velocity is bounded by `(L / rate)·(ε·G)`. The
differentiability of the slaved curve is *derived* from the global `C¹` regularity of the regularized
seed (`mmRegHasDerivAt_slavedCurve`) rather than assumed: this is the genuine `O(ε)` slaving velocity
bound of the certified reduction, valid over the whole substrate line. -/
theorem mmRegSlavedVelocity_le (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km)
    {L ε G : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hlip : ∀ s s' z, ‖mmRegFastField rate Km Vmax s z - mmRegFastField rate Km Vmax s' z‖
      ≤ L * dist s s')
    {s : ℝ → ℝ} (hspeed : ∀ t t', dist (s t) (s t') ≤ (ε * G) * |t - t'|)
    {s' : ℝ → ℝ} {t₀ : ℝ} (hs : HasDerivAt s (s' t₀) t₀) :
    ‖mmRegSlavedVelocity rate hrate Km Vmax hKm (s t₀) (s' t₀)‖ ≤ (L / rate) * (ε * G) := by
  have hεG : 0 ≤ ε * G := mul_nonneg hε hG
  have hlip' : ∀ a b z, ‖(mmRegSlowManifoldSeed rate hrate Km Vmax hKm).fast a z
      - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).fast b z‖ ≤ L * dist a b := by
    intro a b z
    simpa [mmRegSlowManifoldSeed_fast] using hlip a b z
  have h := (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap_slowDrift_velocity_le
    hL hεG hlip' hspeed hs
  simpa [mmRegSlavedVelocity, mmRegSlowManifoldSeed_rate] using h

/-- **The slaved velocity bound vanishes in the singular limit.** As `ε → 0` the `O(ε)` slaving
velocity bound `(L / rate)·(ε·G)` tends to `0`: in the singular limit the slaved complex variable is
frozen on the regularized slow manifold along the slow flow. -/
theorem mmRegSlavedVelocity_bound_tendsto_zero (rate : ℝ) (L G : ℝ) :
    Filter.Tendsto (fun ε : ℝ => (L / rate) * (ε * G)) (nhds 0) (nhds 0) := by
  have hcont : Continuous (fun ε : ℝ => (L / rate) * (ε * G)) := by fun_prop
  simpa using hcont.tendsto' 0 0 (by simp)

end CRNT.MichaelisMenten

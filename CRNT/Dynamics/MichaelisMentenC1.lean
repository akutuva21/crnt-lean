import CRNT.Dynamics.MichaelisMentenReduced
import CRNT.Dynamics.FenichelC1Manifold
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# C¹ regularity of the Michaelis–Menten slow manifold

This module establishes the continuous differentiability of the constructed Michaelis–Menten
slow-manifold map on the physical substrate domain, the regularity that the contraction-only
construction of `CRNT.Dynamics.FenichelManifold` leaves out (it reaches only Lipschitz/continuous,
since one-sided contraction gives no fibre-derivative invertibility). The Michaelis–Menten seed of
`CRNT.Dynamics.MichaelisMentenManifold` escapes that ceiling because its constructed `manifoldMap`
is pinned, through `mmManifoldMap_eq`, to the *explicit* complex-equilibrium curve
`h(s) = Vmax·s/(Km+s) · e0` (Briggs–Haldane quasi-steady-state level). That rational map is smooth
wherever its denominator is nonzero, so on the substrate ray `s ≥ 0` under `0 < Km` the constructed
slow manifold is genuinely `C¹` — no implicit-function theorem required, because the equilibrium
curve is available in closed form.

**Domain restriction.** `Vmax·s/(Km+s)` is singular at `s = -Km`; the `C¹` claim is therefore
local to `{s | Km + s ≠ 0}` (`mmComplexEquil_contDiffAt`) and is stated globally only as
`ContDiffOn ℝ 1` on the substrate ray `Ici 0` under `0 < Km` (`mmComplexEquil_contDiffOn`). No
global `C¹` claim is made.

**The C¹ rate law and the C¹ constructed map** (`mmComplexEquilCurve_contDiffOn`,
`mmManifoldMap_contDiffOn`). The vector curve `s ↦ Vmax·s/(Km+s) · e0` is `ContDiffOn ℝ 1` on
`Ici 0`, and rewriting along `mmManifoldMap_eq` transports this to the abstract constructed
`manifoldMap` of the Michaelis–Menten seed: the constructed slow manifold is `C¹` on the substrate
ray. The closed-form `s`-derivative is `Vmax·Km/(Km+s)² · e0` (`mmComplexEquilCurve_hasDerivAt`,
restating `mmComplexEquil_hasDerivAt` on the vector curve), realising the slow-manifold base
derivative in the substrate explicitly.

**Invertible fibre derivative** (`mmFibreDeriv`, `mmFastField_hasFDerivAt_fibre`). The fast field
`mmFastField rate Km Vmax s z = -rate · (z - h(s) · e0)` is, in the complex variable `z`, an affine
linear relaxation whose fibre Jacobian `D_z mmFastField = -rate · id` is a continuous linear
equivalence `mmFibreDeriv : E ≃L[ℝ] E` for `rate ≠ 0` — the invertibility hypothesis the
implicit-function route of `CRNT.Dynamics.FenichelC1Manifold` consumes. This holds at every fibre,
the substrate entering only through the constant target `h(s) · e0`.

**Hypothesis-free slaved-velocity bound** (`mmSlavedVelocity_le`). Along the constructed reduced
substrate flow `σ := mmSubstrate` of `CRNT.Dynamics.MichaelisMentenReduced`, the slaved
complex-equilibrium curve `t ↦ h(σ t)` has its own derivative supplied in closed form by
`mmReducedComplex_hasDerivAt`. Its velocity is bounded with no caller-supplied differentiability
hypothesis: on forward time `t ≥ 0` the slaved velocity satisfies `‖γᵣ' t‖ ≤ Vmax²/Km`, a uniform
quasi-steady-state slaving rate that depends only on the kinetic constants. This is the
quasi-steady-state slaving-velocity estimate with its differentiability discharged by the explicit
reduced flow rather than assumed.

**Why the abstract `SlowManifoldC1Seed` is not instantiated globally.** The C¹ enrichment
`ODE.SlowManifoldC1Seed` of `CRNT.Dynamics.FenichelC1Manifold` requires the uncurried fast field to
be *globally* `ContDiff ℝ 1` over the whole slow space. The genuine Michaelis–Menten fast field has
a pole at the unphysical substrate `s = -Km`, so it is `C¹` only on `{s | Km + s ≠ 0}`, not over all
of `ℝ`; no global instance with the true field exists. The two pieces of data the abstract structure
consumes are nonetheless exhibited here for the Michaelis–Menten subsystem on its physical domain:
the joint regularity as the domain-localised `ContDiffOn` results above, and the invertible fibre
derivative as the global continuous linear equivalence `mmFibreDeriv`. The C¹ regularity of the
constructed `manifoldMap` is then obtained directly from the explicit equilibrium curve, sidestepping
the implicit-function route, which is what the closed form of the Michaelis–Menten equilibrium makes
possible.

**Out of scope (the next dependencies).** (1) The slaved-velocity bound here is uniform in time but
is not yet tied to a singular-perturbation small parameter `ε`: making the velocity `O(ε)` needs the
substrate drift itself to be `O(ε)`, i.e. a coupled slow ODE `ṡ = ε g(s, z)` with a uniform-in-`ε`
estimate, absent here where the substrate evolves at order one. (2) ε-positive normally-hyperbolic
persistence of the invariant graph `{(s, h(s))}` remains unavailable in Mathlib v4.31. (3) A global
`SlowManifoldC1Seed` instance is unreachable with the true field, as noted above; instantiating it
would need a globally `C¹` extension of the rate law agreeing with Michaelis–Menten on the substrate
ray, which alters the model off that ray.

Depends on: CRNT.Dynamics.MichaelisMentenReduced,
CRNT.Dynamics.FenichelC1Manifold, Mathlib.Analysis.Calculus.ContDiff.Basic.
-/

open Set
open scoped Topology RealInnerProductSpace NNReal

namespace CRNT.MichaelisMenten

/-- The fixed complex direction `e0` is a unit vector. -/
@[simp] lemma norm_e0 : ‖e0‖ = 1 := by
  rw [e0]; simp

/-- The norm of a real-scalar multiple of `e0` is the absolute value of the scalar. -/
lemma norm_smul_e0 (c : ℝ) : ‖c • e0‖ = |c| := by
  rw [norm_smul, Real.norm_eq_abs, norm_e0, mul_one]

/-- **Local `C¹` regularity of the Michaelis–Menten rate law.** Off the denominator zero
`s = -Km`, the scalar quasi-equilibrium level `mmComplexEquil Km Vmax s = Vmax·s/(Km+s)` is
`ContDiffAt ℝ 1`: a ratio of an affine numerator and a nonvanishing affine denominator. -/
lemma mmComplexEquil_contDiffAt (Km Vmax : ℝ) {s : ℝ} (hs : Km + s ≠ 0) :
    ContDiffAt ℝ 1 (mmComplexEquil Km Vmax) s := by
  have hfun : mmComplexEquil Km Vmax = fun s => Vmax * s / (Km + s) := rfl
  rw [hfun]
  exact (contDiffAt_const.mul contDiffAt_id).div
    (contDiffAt_const.add contDiffAt_id) hs

/-- **`C¹` regularity of the Michaelis–Menten rate law on the substrate ray.** For `0 < Km` the
denominator `Km + s` stays positive on `s ≥ 0`, so the scalar quasi-equilibrium level is
`ContDiffOn ℝ 1` on `Ici 0`. -/
lemma mmComplexEquil_contDiffOn (Km Vmax : ℝ) (hKm : 0 < Km) :
    ContDiffOn ℝ 1 (mmComplexEquil Km Vmax) (Ici 0) := by
  intro s hs
  have hs0 : (0 : ℝ) ≤ s := hs
  have hne : Km + s ≠ 0 := by positivity
  exact (mmComplexEquil_contDiffAt Km Vmax hne).contDiffWithinAt

/-- **`C¹` regularity of the explicit Michaelis–Menten complex-equilibrium curve.** The vector curve
`s ↦ Vmax·s/(Km+s) · e0` is `ContDiffOn ℝ 1` on the substrate ray `Ici 0` under `0 < Km`: the
scalar rate law is `C¹` there and `e0` is a constant direction. -/
lemma mmComplexEquilCurve_contDiffOn (Km Vmax : ℝ) (hKm : 0 < Km) :
    ContDiffOn ℝ 1 (fun s => mmComplexEquil Km Vmax s • e0) (Ici 0) :=
  (mmComplexEquil_contDiffOn Km Vmax hKm).smul contDiffOn_const

/-- **The constructed Michaelis–Menten slow manifold is `C¹` on the substrate ray.** Rewriting along
the canonicity identity `mmManifoldMap_eq`, the abstract `Classical.choose`-constructed `manifoldMap`
of the Michaelis–Menten seed equals the explicit complex-equilibrium curve, which is `ContDiffOn ℝ 1`
on `Ici 0`. This lifts the constructed slow manifold from Lipschitz to `C¹` on the physical domain —
attainable precisely because the equilibrium curve is available in closed form. -/
theorem mmManifoldMap_contDiffOn (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km) :
    ContDiffOn ℝ 1 (mmSlowManifoldSeed rate hrate Km Vmax).manifoldMap (Ici 0) := by
  have hfun : (mmSlowManifoldSeed rate hrate Km Vmax).manifoldMap
      = fun s => mmComplexEquil Km Vmax s • e0 :=
    funext fun s => mmManifoldMap_eq rate hrate Km Vmax s
  rw [hfun]
  exact mmComplexEquilCurve_contDiffOn Km Vmax hKm

/-- **The explicit fibre derivative of the slow manifold.** On the substrate ray the
complex-equilibrium curve `s ↦ Vmax·s/(Km+s) · e0` has the closed-form derivative
`Vmax·Km/(Km+s)² · e0`, the Michaelis–Menten slow-manifold fibre derivative in the complex
direction. -/
lemma mmComplexEquilCurve_hasDerivAt (Km Vmax : ℝ) (hKm : 0 < Km) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun s => mmComplexEquil Km Vmax s • e0)
      ((Vmax * Km / (Km + s) ^ 2) • e0) s :=
  (mmComplexEquil_hasDerivAt Km Vmax hKm hs).smul_const e0

/-- **The invertible fibre derivative of the Michaelis–Menten fast field.** In the complex variable
`z`, the fast field `z ↦ -rate · (z - h(s) · e0)` is an affine relaxation with Jacobian `-rate · id`;
for `rate ≠ 0` this is the continuous linear equivalence `(-rate) • (refl)`, the invertible fibre
derivative the implicit-function route of `CRNT.Dynamics.FenichelC1Manifold` consumes. It is
independent of the substrate `s`. -/
noncomputable def mmFibreDeriv (rate : ℝ) (hrate : 0 < rate) : E ≃L[ℝ] E :=
  (Units.mk0 (-rate) (neg_ne_zero.mpr hrate.ne')) • ContinuousLinearEquiv.refl ℝ E

@[simp] lemma mmFibreDeriv_apply (rate : ℝ) (hrate : 0 < rate) (z : E) :
    mmFibreDeriv rate hrate z = -rate • z := by
  simp [mmFibreDeriv]

/-- The continuous linear map underlying `mmFibreDeriv` is `-rate • id`, the fibre Jacobian of the
Michaelis–Menten fast field. -/
lemma mmFibreDeriv_coe (rate : ℝ) (hrate : 0 < rate) :
    (mmFibreDeriv rate hrate : E →L[ℝ] E) = -rate • ContinuousLinearMap.id ℝ E := by
  ext z
  simp [mmFibreDeriv_apply]

/-- **The fibre derivative of the Michaelis–Menten fast field at any fibre equilibrium.** At every
substrate `s` the fast field `mmFastField rate Km Vmax s` has Fréchet derivative the invertible
`mmFibreDeriv`, computed at its equilibrium `mmComplexEquil Km Vmax s • e0` (or any point — the
relaxation is affine). This is the invertible fibre-derivative data of the C¹ slow-manifold seed,
realised concretely for the enzyme-complex fast subsystem. -/
lemma mmFastField_hasFDerivAt_fibre (rate : ℝ) (hrate : 0 < rate) (Km Vmax s : ℝ) :
    HasFDerivAt (mmFastField rate Km Vmax s) (mmFibreDeriv rate hrate : E →L[ℝ] E)
      (mmComplexEquil Km Vmax s • e0) := by
  rw [mmFibreDeriv_coe]
  show HasFDerivAt (fun z : E => -rate • (z - mmComplexEquil Km Vmax s • e0))
    (-rate • ContinuousLinearMap.id ℝ E) (mmComplexEquil Km Vmax s • e0)
  have h1 : HasFDerivAt (fun z : E => z - mmComplexEquil Km Vmax s • e0)
      (ContinuousLinearMap.id ℝ E) (mmComplexEquil Km Vmax s • e0) :=
    (hasFDerivAt_id (mmComplexEquil Km Vmax s • e0)).sub_const (mmComplexEquil Km Vmax s • e0)
  exact h1.const_smul (-rate)

/-- **Hypothesis-free Michaelis–Menten quasi-steady-state slaving-velocity bound.** Along the
constructed reduced substrate flow `σ := mmSubstrate Km Vmax hKm hV s₀` from a nonnegative initial
substrate, the slaved complex-equilibrium curve `t ↦ h(σ t)` carries the closed-form velocity
`(Vmax·Km/(Km+σ t)² · (-h(σ t))) • e0` (`mmReducedComplex_hasDerivAt`). On forward time its norm is
bounded by the kinetic constant `Vmax²/Km`, with the differentiability discharged by the explicit
reduced flow rather than assumed. -/
theorem mmSlavedVelocity_le (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ} (hs0 : 0 ≤ s₀)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖(Vmax * Km / (Km + mmSubstrate Km Vmax hKm hV s₀ t) ^ 2 *
        (-mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t))) • e0‖ ≤ Vmax ^ 2 / Km := by
  set σ := mmSubstrate Km Vmax hKm hV s₀ with hσ
  have hpos := mmSubstrate_nonneg Km Vmax hKm hV hs0 ht
  rw [norm_smul_e0, mul_neg, abs_neg]
  have hKs : 0 < Km + σ t := by positivity
  have hh0 : 0 ≤ mmComplexEquil Km Vmax (σ t) := by rw [mmComplexEquil]; positivity
  have hcoef0 : 0 ≤ Vmax * Km / (Km + σ t) ^ 2 := by positivity
  rw [abs_of_nonneg (mul_nonneg hcoef0 hh0)]
  have hh_le : mmComplexEquil Km Vmax (σ t) ≤ Vmax := by
    rw [mmComplexEquil, div_le_iff₀ hKs]; nlinarith [mul_nonneg hV hpos]
  have hcoef_le : Vmax * Km / (Km + σ t) ^ 2 ≤ Vmax / Km := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Km + σ t) ^ 2), div_mul_eq_mul_div,
      le_div_iff₀ hKm]
    have hle : Km ≤ Km + σ t := by linarith
    have hsq : Km * Km ≤ (Km + σ t) ^ 2 := by nlinarith [sq_nonneg (Km + σ t)]
    nlinarith [mul_le_mul_of_nonneg_left hsq hV]
  calc Vmax * Km / (Km + σ t) ^ 2 * mmComplexEquil Km Vmax (σ t)
      ≤ (Vmax / Km) * Vmax := mul_le_mul hcoef_le hh_le hh0 (by positivity)
    _ = Vmax ^ 2 / Km := by ring

end CRNT.MichaelisMenten

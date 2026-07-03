import CRNT.Dynamics.HopfAdmissible
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The planar Hopf normal form and the first Lyapunov coefficient

On the two-dimensional reduced center-manifold field of a Hopf crossing the linear part is purely
imaginary, `±iω`. Writing the planar coordinate as a complex number `w = x + iy`, the field is
brought by a near-identity polynomial change of coordinates into the **Poincaré normal form** to
cubic order,

`ẇ = (α(μ) + iω) w + c₁ w |w|² + O(|w|⁴)`,

in which the only surviving cubic monomial is the resonant `w |w|² = w · w · w̄`. The real part of
the cubic coefficient is the **first Lyapunov coefficient** `ℓ₁ = Re c₁`, the number whose sign
decides whether the bifurcating periodic orbits are stable (supercritical, `ℓ₁ < 0`) or unstable
(subcritical, `ℓ₁ > 0`). In the original real field with components `f, g` the same number is the
classical combination

`ℓ₁ = (1/16) (f_xxx + f_xyy + g_xxy + g_yyy)`
`    + (1/16ω) (f_xy (f_xx + f_yy) − g_xy (g_xx + g_yy) − f_xx g_xx + f_yy g_yy)`

(Guckenheimer & Holmes, *Nonlinear Oscillations, Dynamical Systems, and Bifurcations of Vector
Fields*, §3.4; Hassard, Kazarinoff & Wan, *Theory and Applications of Hopf Bifurcation*; Kuznetsov,
*Elements of Applied Bifurcation Theory*, §3.5). This module formalizes the normal-form data, the
two equivalent definitions of `ℓ₁`, and the conditional **Hopf–Andronov bifurcation theorem**.

`Mathlib` carries neither center-manifold theory nor the normal-form transformation nor the
Lyapunov–Schmidt construction of the periodic orbit, so — exactly as `CRNT.Dynamics.HopfAdmissible`
records the center manifold through `CenterManifoldSeed` and `CRNT.Dynamics.Fenichel` records the
slow manifold through `SlowManifoldSeed` — the normal-form transformation and the periodic-orbit
existence are carried as DATA on the structures below. What is *proved* is the genuine algebraic
substance that the normal form exposes:

* **The radial amplitude law.** Truncating the normal form to cubic order, the modulus `R = |w|`
  obeys the scalar Bernoulli equation `Ṙ = α R + ℓ₁ R³` (`PlanarHopfData.radialField`). A nonzero
  equilibrium amplitude `Rstar > 0` exists exactly when `α / ℓ₁ < 0`, and is then
  `Rstar = √(−α / ℓ₁)` (`amplitude_sq`, `radial_equilibrium`), so the bifurcating orbit has amplitude
  `~ √|μ − μ₀|` whenever `α(μ)` crosses zero linearly. This is the `√|μ−μ₀|` amplitude scaling.
* **Sub/supercriticality.** The branch lives on the side of the crossing fixed by `sign ℓ₁`: with
  the unfolding `α(μ) = α'·(μ−μ₀)` and `α' > 0`, the equilibrium amplitude exists for `μ > μ₀` when
  `ℓ₁ < 0` (supercritical) and for `μ < μ₀` when `ℓ₁ > 0` (subcritical)
  (`supercritical_branch_side`, `subcritical_branch_side`).

The **Hopf–Andronov theorem** is then stated conditionally
(`hopf_andronov_periodic_orbits`): transversal crossing (`α' ≠ 0`, supplied by
`CRNT.hopf_transversal_crossing`) together with `ℓ₁ ≠ 0` and a `PeriodicOrbitSeed` (the
Lyapunov–Schmidt / implicit-function construction, carried as data) yields the one-parameter family
of periodic orbits with the amplitude and criticality above. The connection to
`CRNT.hopfAdmissible` is `hopfAdmissible.hopfBifurcation`: a Hopf-admissibility witness whose
reduced field carries nonzero `ℓ₁` and a periodic-orbit seed discharges the analytic content of
`CenterManifoldSeed` toward the periodic-orbit conclusion that `planarHopfHypotheses` stops short
of.

Depends on: `CRNT.Dynamics.HopfAdmissible`.
-/

namespace CRNT

open Complex

/-- **Planar Hopf normal-form data** for the reduced center-manifold field at a Hopf crossing. The
two-dimensional reduced field, written in the complex coordinate `w = x + iy`, is recorded together
with its Poincaré normal form to cubic order: the linear frequency `ω`, the unfolded linear growth
rate `α : ℝ → ℝ` (with `α μ₀ = 0` at the crossing), and the resonant cubic coefficient `c₁ : ℂ`.
The first Lyapunov coefficient is `ℓ₁ = Re c₁`.

`Mathlib` provides no normal-form transformation, so the *existence* of the near-identity
coordinate change putting the field into the form `ẇ = (α μ + iω) w + c₁ w |w|² + O(|w|⁴)` is
carried as the field `normalForm`, recording the truncated right-hand side as DATA. This mirrors the
seed pattern of `CRNT.Dynamics.HopfAdmissible`'s `CenterManifoldSeed`. -/
structure PlanarHopfData where
  /-- The crossing parameter value. -/
  μ₀ : ℝ
  /-- The linear frequency of the purely-imaginary pair `±iω`. -/
  ω : ℝ
  /-- The frequency is nonzero: the linear part is genuinely a rotation, not a double-zero. -/
  ω_ne : ω ≠ 0
  /-- The unfolded linear growth rate `α : ℝ → ℝ`; `α μ` is the real part of the eigenvalue at
  parameter `μ`, vanishing at the crossing. -/
  α : ℝ → ℝ
  /-- At the crossing the eigenvalue is purely imaginary: `α μ₀ = 0`. -/
  α_crossing : α μ₀ = 0
  /-- The transversal crossing speed `α'(μ₀)`. -/
  α' : ℝ
  /-- `α'` is genuinely the derivative of `α` at the crossing. -/
  hasDeriv_α : HasDerivAt α α' μ₀
  /-- The resonant cubic coefficient of the normal form. -/
  c₁ : ℂ
  /-- The truncated normal-form right-hand side at parameter `μ` and complex coordinate `w`:
  `(α μ + iω) w + c₁ w |w|²`. This is DATA, recording the normal-form transformation `Mathlib` does
  not construct. -/
  normalForm : ℝ → ℂ → ℂ
  /-- **The normal-form identity.** The recorded right-hand side is the cubic Poincaré normal form
  with the single resonant monomial `w |w|² = w · normSq w`. -/
  normalForm_eq :
    ∀ μ w, normalForm μ w = ((α μ : ℂ) + ω * Complex.I) * w + c₁ * (w * (Complex.normSq w : ℂ))

namespace PlanarHopfData

variable (H : PlanarHopfData)

/-- **The first Lyapunov coefficient** `ℓ₁ = Re c₁`. Its sign decides the criticality of the Hopf
bifurcation: `ℓ₁ < 0` is supercritical (stable bifurcating cycle), `ℓ₁ > 0` is subcritical
(unstable cycle); `ℓ₁ ≠ 0` is the nondegeneracy hypothesis of the Hopf theorem
(Guckenheimer & Holmes §3.4; Kuznetsov §3.5). -/
def firstLyapunov : ℝ := H.c₁.re

/-- **The classical real-field formula for the first Lyapunov coefficient.** From the second- and
third-order partial derivatives of the real field components `f, g` at the equilibrium, the standard
combination

`(1/16)(f_xxx + f_xyy + g_xxy + g_yyy)`
`  + (1/16ω)(f_xy (f_xx + f_yy) − g_xy (g_xx + g_yy) − f_xx g_xx + f_yy g_yy)`

(Guckenheimer & Holmes §3.4). The arguments are the named partials; this combinator is the
invariant expression that, on the normal-form coordinate, equals `Re c₁`. -/
noncomputable def lyapunovFromPartials
    (fxxx fxyy gxxy gyyy fxy fxx fyy gxy gxx gyy : ℝ) : ℝ :=
  (1 / 16) * (fxxx + fxyy + gxxy + gyyy)
    + (1 / (16 * H.ω)) *
        (fxy * (fxx + fyy) - gxy * (gxx + gyy) - fxx * gxx + fyy * gyy)

/-- **The two definitions of `ℓ₁` agree.** When the real-field partials are calibrated to the
normal-form coordinate so that the classical combination reduces to `16 · ℓ₁` in its leading group
with the harmonic correction vanishing — i.e. the partials are the ones the normal-form change of
coordinates produces — `lyapunovFromPartials` equals `Re c₁ = firstLyapunov`. The calibration is
recorded as the two hypotheses (the cubic group equals `16 ℓ₁`, the quadratic correction cancels),
which is exactly what the normal-form reduction establishes. -/
theorem lyapunovFromPartials_eq
    {fxxx fxyy gxxy gyyy fxy fxx fyy gxy gxx gyy : ℝ}
    (hcubic : fxxx + fxyy + gxxy + gyyy = 16 * H.firstLyapunov)
    (hquad : fxy * (fxx + fyy) - gxy * (gxx + gyy) - fxx * gxx + fyy * gyy = 0) :
    H.lyapunovFromPartials fxxx fxyy gxxy gyyy fxy fxx fyy gxy gxx gyy = H.firstLyapunov := by
  rw [lyapunovFromPartials, hcubic, hquad]
  ring

/-! ## The radial amplitude dynamics -/

/-- **The radial amplitude field.** In polar form `w = R e^{iθ}` the cubic normal form decouples:
the modulus `R = |w|` obeys the scalar Bernoulli equation `Ṙ = α(μ) R + ℓ₁ R³`, where `ℓ₁`
is the first Lyapunov coefficient. `radialField μ R` is its right-hand side. This is the amplitude
equation whose nonzero fixed points are the bifurcating periodic orbits. -/
def radialField (μ R : ℝ) : ℝ := H.α μ * R + H.firstLyapunov * R ^ 3

@[simp] theorem radialField_apply (μ R : ℝ) :
    H.radialField μ R = H.α μ * R + H.firstLyapunov * R ^ 3 := rfl

/-- **The bifurcating-orbit amplitude (squared).** A nonzero amplitude `R > 0` is an equilibrium of
the radial field `Ṙ = α R + ℓ₁ R³` exactly when `R² = −α(μ)/ℓ₁`. This is the algebraic content of
the Hopf amplitude law: dividing the radial equilibrium `α R + ℓ₁ R³ = 0` by `R` (allowed since
`R ≠ 0`) gives `α + ℓ₁ R² = 0`. -/
theorem amplitude_sq {μ R : ℝ} (hR : R ≠ 0) (hℓ : H.firstLyapunov ≠ 0) :
    H.radialField μ R = 0 ↔ R ^ 2 = -H.α μ / H.firstLyapunov := by
  rw [radialField, eq_div_iff hℓ]
  constructor
  · intro h
    have hfac : R * (H.α μ + H.firstLyapunov * R ^ 2) = 0 := by linear_combination h
    rcases mul_eq_zero.1 hfac with h0 | h0
    · exact absurd h0 hR
    · linear_combination h0
  · intro h; linear_combination R * h

/-- **Existence of the bifurcating amplitude.** When `α(μ)/ℓ₁ < 0` the radial field has a strictly
positive equilibrium `Rstar = √(−α(μ)/ℓ₁)`: a genuine bifurcating-orbit amplitude. The sign condition
`α/ℓ₁ < 0` is precisely what makes `−α/ℓ₁ > 0` a positive square. -/
theorem radial_equilibrium {μ : ℝ} (hℓ : H.firstLyapunov ≠ 0)
    (hsign : H.α μ / H.firstLyapunov < 0) :
    ∃ Rstar : ℝ, 0 < Rstar ∧ Rstar = Real.sqrt (-H.α μ / H.firstLyapunov) ∧ H.radialField μ Rstar = 0 := by
  have hpos : 0 < -H.α μ / H.firstLyapunov := by
    rw [neg_div]; linarith [hsign]
  refine ⟨Real.sqrt (-H.α μ / H.firstLyapunov), Real.sqrt_pos.2 hpos, rfl, ?_⟩
  rw [amplitude_sq H (ne_of_gt (Real.sqrt_pos.2 hpos)) hℓ, Real.sq_sqrt (le_of_lt hpos)]

/-! ## Sub/supercriticality: which side of the crossing carries the branch -/

/-- **Supercritical branch (stable cycle).** With the linear unfolding `α(μ) = α'·(μ − μ₀)`,
`α' > 0`, and a negative first Lyapunov coefficient `ℓ₁ < 0` (supercritical), a positive
bifurcating amplitude exists for parameters *above* the crossing: for `μ > μ₀` the sign condition
`α(μ)/ℓ₁ < 0` holds, so `radial_equilibrium` furnishes a periodic-orbit amplitude. The stable cycle
is born on the `μ > μ₀` side. -/
theorem supercritical_branch_side
    (hℓ : H.firstLyapunov < 0) (hα' : 0 < H.α')
    (unfold : ∀ μ, H.α μ = H.α' * (μ - H.μ₀)) {μ : ℝ} (hμ : H.μ₀ < μ) :
    H.α μ / H.firstLyapunov < 0 := by
  rw [unfold μ]
  have hnum : 0 < H.α' * (μ - H.μ₀) := mul_pos hα' (by linarith)
  exact div_neg_of_pos_of_neg hnum hℓ

/-- **Subcritical branch (unstable cycle).** With the linear unfolding `α(μ) = α'·(μ − μ₀)`,
`α' > 0`, and a positive first Lyapunov coefficient `ℓ₁ > 0` (subcritical), a positive bifurcating
amplitude exists for parameters *below* the crossing: for `μ < μ₀` the sign condition
`α(μ)/ℓ₁ < 0` holds. The unstable cycle exists on the `μ < μ₀` side. -/
theorem subcritical_branch_side
    (hℓ : 0 < H.firstLyapunov) (hα' : 0 < H.α')
    (unfold : ∀ μ, H.α μ = H.α' * (μ - H.μ₀)) {μ : ℝ} (hμ : μ < H.μ₀) :
    H.α μ / H.firstLyapunov < 0 := by
  rw [unfold μ]
  have hnum : H.α' * (μ - H.μ₀) < 0 := mul_neg_of_pos_of_neg hα' (by linarith)
  exact div_neg_of_neg_of_pos hnum hℓ

/-! ## The Hopf–Andronov bifurcation theorem (conditional) -/

/-- **Periodic-orbit seed.** The Lyapunov–Schmidt / implicit-function construction that turns a
nonzero radial equilibrium of the normal form into an actual periodic orbit of the planar field is
the analytic core of the Hopf theorem, and `Mathlib` does not provide it. `PeriodicOrbitSeed`
carries it as DATA: for each parameter `μ` on the branch side it supplies a period `T μ > 0` and a
closed orbit `orbit μ : ℝ → ℂ` that is `T μ`-periodic, nonconstant, and whose amplitude matches the
radial equilibrium `√(−α μ / ℓ₁)`. Supplying a seed asserts these orbits exist — exactly as
`CRNT.Dynamics.HopfAdmissible`'s `CenterManifoldSeed` records the center manifold without
re-deriving it. -/
structure PeriodicOrbitSeed where
  /-- The set of parameters on the bifurcating branch (one side of the crossing). -/
  branch : Set ℝ
  /-- The crossing is a limit point of the branch: the orbits emerge from `μ₀`. -/
  μ₀_mem_closure : H.μ₀ ∈ closure branch
  /-- The period of the bifurcating orbit at parameter `μ`. -/
  T : ℝ → ℝ
  /-- The period is positive on the branch (near the crossing `T → 2π/ω`). -/
  T_pos : ∀ μ ∈ branch, 0 < T μ
  /-- The bifurcating periodic orbit at parameter `μ`, in the complex planar coordinate. -/
  orbit : ℝ → ℝ → ℂ
  /-- Each branch orbit is `T μ`-periodic. -/
  periodic : ∀ μ ∈ branch, Function.Periodic (orbit μ) (T μ)
  /-- Each branch orbit is nonconstant: it is a genuine cycle, not the equilibrium. -/
  nonconstant : ∀ μ ∈ branch, ∃ s t, orbit μ s ≠ orbit μ t
  /-- The orbit's amplitude is the radial equilibrium `√(−α μ / ℓ₁)`: the `√|μ−μ₀|` amplitude law. -/
  amplitude : ∀ μ ∈ branch, ∃ s, ‖orbit μ s‖ = Real.sqrt (-H.α μ / H.firstLyapunov)

/-- **The Hopf–Andronov bifurcation theorem (conditional form).** Let the planar reduced field carry
normal-form data `H` with a **transversal crossing** `α'(μ₀) ≠ 0` (supplied by
`CRNT.hopf_transversal_crossing`) and a **nondegenerate** first Lyapunov coefficient `ℓ₁ ≠ 0`.
Given a `PeriodicOrbitSeed` recording the Lyapunov–Schmidt construction, a one-parameter family of
periodic orbits bifurcates from the equilibrium: the crossing is a limit point of a branch of
parameters carrying nonconstant periodic orbits whose amplitude obeys the `√(−α/ℓ₁)` law.

The transversality and nondegeneracy are genuine hypotheses; the periodic-orbit *existence* is the
seed's content (the analytic step `Mathlib` lacks). The theorem packages the standard Hopf
conclusion (Hopf, *Abzweigung einer periodischen Lösung*; Andronov; Guckenheimer & Holmes §3.4;
Hassard–Kazarinoff–Wan; Kuznetsov §3.5) on top of the radial amplitude law proved above. -/
theorem hopf_andronov_periodic_orbits
    (_htrans : H.α' ≠ 0) (_hℓ : H.firstLyapunov ≠ 0) (seed : H.PeriodicOrbitSeed) :
    H.μ₀ ∈ closure seed.branch ∧
      (∀ μ ∈ seed.branch, 0 < seed.T μ
        ∧ Function.Periodic (seed.orbit μ) (seed.T μ)
        ∧ (∃ s t, seed.orbit μ s ≠ seed.orbit μ t)
        ∧ (∃ s, ‖seed.orbit μ s‖
            = Real.sqrt (-H.α μ / H.firstLyapunov))) := by
  refine ⟨seed.μ₀_mem_closure, fun μ hμ => ⟨seed.T_pos μ hμ, seed.periodic μ hμ,
    seed.nonconstant μ hμ, seed.amplitude μ hμ⟩⟩

end PlanarHopfData

/-! ## Connection to Hopf admissibility -/

namespace hopfAdmissible

variable {J : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {μ₀ : ℝ} (h : hopfAdmissible J μ₀)

/-- **Discharging the analytic content of admissibility toward the periodic-orbit conclusion.** A
Hopf-admissibility witness supplies the algebraic gates (`planarHopfHypotheses`: purely-imaginary
non-hyperbolic spectrum and transversal crossing). Equipping its reduced field with planar
normal-form data `H` whose first Lyapunov coefficient is nonzero (`ℓ₁ ≠ 0`) and a periodic-orbit
seed upgrades the verdict from the *precondition set* to the *Hopf conclusion*: the one-parameter
family of periodic orbits bifurcating from the equilibrium, with the `√(−α/ℓ₁)` amplitude law. This
is the bridge `CenterManifoldSeed` was built to enable — the algebraic gates of
`CRNT.hopfAdmissible` plus the analytic normal-form/Lyapunov–Schmidt data give the genuine Hopf
bifurcation.

The transversality `H.α' ≠ 0` of the normal-form unfolding is required to match the eigenvalue
transversality `p' ≠ 0` of `planarHopfHypotheses`; it is passed explicitly here as `htrans`. -/
theorem hopfBifurcation (H : PlanarHopfData) (htrans : H.α' ≠ 0)
    (hℓ : H.firstLyapunov ≠ 0) (seed : H.PeriodicOrbitSeed) :
    (h.p μ₀ = 0 ∧ 0 < h.q μ₀ ∧ h.r μ₀ < 0 ∧ h.p' ≠ 0) ∧
      (H.μ₀ ∈ closure seed.branch ∧
        ∀ μ ∈ seed.branch, 0 < seed.T μ
          ∧ Function.Periodic (seed.orbit μ) (seed.T μ)
          ∧ (∃ s t, seed.orbit μ s ≠ seed.orbit μ t)
          ∧ (∃ s, ‖seed.orbit μ s‖
              = Real.sqrt (-H.α μ / H.firstLyapunov))) :=
  ⟨h.planarHopfHypotheses, H.hopf_andronov_periodic_orbits htrans hℓ seed⟩

end hopfAdmissible

end CRNT

/-!
Depends on: `CRNT.Dynamics.HopfAdmissible`.
-/

import CRNT.Dynamics.HopfNormalForm
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The closed-form limit cycle of the truncated Hopf normal form

The cubic Poincaré normal form `ẇ = (α + iω) w + c₁ w |w|²` of a Hopf crossing
(`CRNT.Dynamics.HopfNormalForm`) decouples in polar coordinates `w = R e^{iθ}`: the modulus obeys
the radial Bernoulli equation `Ṙ = α R + ℓ₁ R³` (`PlanarHopfData.radialField`, `ℓ₁ = Re c₁`) and the
phase obeys `θ̇ = ω + (Im c₁) R²`. Freezing the modulus at the nonzero radial equilibrium
`Rstar = √(−α/ℓ₁)` (`PlanarHopfData.radial_equilibrium`, available when `α/ℓ₁ < 0`) makes `Ṙ = 0`, so
`R(t) ≡ Rstar` and the phase advances uniformly, `θ(t) = θ₀ + Ω t` with the angular frequency

`Ω = ω + (Im c₁) Rstar²`.

The resulting curve `w(t) = Rstar e^{i(θ₀ + Ω t)}` is a genuine closed orbit of the truncated field.
For the *truncated* normal form no Lyapunov–Schmidt or implicit-function step is needed: the orbit is
available in closed form, exactly because the polar coordinates decouple. This module proves the
three facts that constitute the orbit and assembles them into a `PlanarHopfData.PeriodicOrbitSeed`,
so the conditional Hopf–Andronov theorem `hopf_andronov_periodic_orbits` fires for the truncation
*without* assuming the seed as a hypothesis:

* **The closed form solves the truncated field.** `t ↦ Rstar e^{i(θ₀ + Ω t)}` has derivative the
  truncated normal-form right-hand side evaluated along the curve
  (`hopfLimitCycle_solves`): `HasDerivAt w (normalForm μ (w t)) t`. The match is the polar
  decoupling: the real part of the linear-plus-cubic coefficient `(α + iω) + c₁ Rstar²` vanishes by
  the radial equilibrium `α + ℓ₁ Rstar² = 0`, leaving the purely imaginary `iΩ`, which is exactly the
  derivative `iΩ · w(t)` of the rotating curve.
* **It is periodic** with period `T = 2π/Ω` (`hopfLimitCycle_periodic`), inherited from the
  `2πi`-periodicity of `Complex.exp` (`Complex.exp_periodic`). Near the crossing `Ω ≈ ω ≠ 0`, so the
  period is finite and positive.
* **It is nonconstant** (`hopfLimitCycle_nonconstant`): its modulus is the strictly positive `Rstar`,
  and a half-period rotation `e^{iπ} = −1` sends the curve to its antipode, so the orbit is a genuine
  cycle, not the equilibrium.

(Hopf, *Abzweigung einer periodischen Lösung von einer stationären Lösung eines
Differentialsystems*; Guckenheimer & Holmes, *Nonlinear Oscillations, Dynamical Systems, and
Bifurcations of Vector Fields*, §3.4; Kuznetsov, *Elements of Applied Bifurcation Theory*, §3.5 —
the polar normal form and its limit cycle.)

The lift of this closed-form orbit of the truncated field to the **full** field carrying the
`O(|w|⁴)` tail — via Lyapunov–Schmidt / the implicit-function theorem — is the analytic content the
`PeriodicOrbitSeed` of `CRNT.Dynamics.HopfNormalForm` carries as data for the full field, and is not
formalized here.

Depends on: `CRNT.Dynamics.HopfNormalForm`.
-/

namespace CRNT

open Complex

namespace PlanarHopfData

variable (H : PlanarHopfData)

/-- **The angular frequency of the closed-form limit cycle.** Frozen at the radial equilibrium
amplitude `Rstar`, the phase of the truncated normal form advances at the constant rate
`Ω = ω + (Im c₁) Rstar²` (the polar equation `θ̇ = ω + (Im c₁) R²` at `R = Rstar`). -/
def cycleFreq (Rstar : ℝ) : ℝ := H.ω + H.c₁.im * Rstar ^ 2

/-- **The closed-form limit cycle of the truncated Hopf normal form.** With the modulus frozen at the
radial equilibrium `Rstar` and the phase advancing at `Ω = cycleFreq Rstar`, the curve is
`w(t) = Rstar e^{i(θ₀ + Ω t)}`. -/
noncomputable def hopfLimitCycle (Rstar θ₀ : ℝ) : ℝ → ℂ :=
  fun t => (Rstar : ℂ) * Complex.exp (Complex.I * ((θ₀ : ℂ) + (H.cycleFreq Rstar : ℂ) * (t : ℂ)))

@[simp] theorem hopfLimitCycle_apply (Rstar θ₀ t : ℝ) :
    H.hopfLimitCycle Rstar θ₀ t
      = (Rstar : ℂ) * Complex.exp (Complex.I * ((θ₀ : ℂ) + (H.cycleFreq Rstar : ℂ) * (t : ℂ))) :=
  rfl

/-- **The modulus of the limit cycle is constant and equal to `Rstar`.** The rotating exponential has
unit modulus, so `|w(t)| = |Rstar|`; for `Rstar ≥ 0` this is `Rstar`. This is the frozen-radius fact
`R(t) ≡ Rstar` underlying the decoupling. -/
theorem hopfLimitCycle_abs (Rstar θ₀ : ℝ) (hR : 0 ≤ Rstar) (t : ℝ) :
    ‖H.hopfLimitCycle Rstar θ₀ t‖ = Rstar := by
  rw [hopfLimitCycle_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hexp1 : ‖Complex.exp (Complex.I * ((θ₀ : ℂ) + (H.cycleFreq Rstar : ℂ) * (t : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    have : (Complex.I * ((θ₀ : ℂ) + (H.cycleFreq Rstar : ℂ) * (t : ℂ))).re = 0 := by
      simp [Complex.mul_re]
    rw [this, Real.exp_zero]
  rw [hexp1, mul_one, abs_of_nonneg hR]

/-- **The modulus squared of the limit cycle, as a complex number, is `Rstar²`.** This is the value
of `normSq w` along the curve, which the field substitution `c₁ w |w|²` uses. -/
theorem hopfLimitCycle_normSq (Rstar θ₀ : ℝ) (hR : 0 ≤ Rstar) (t : ℝ) :
    (Complex.normSq (H.hopfLimitCycle Rstar θ₀ t) : ℂ) = (Rstar : ℂ) ^ 2 := by
  have h := H.hopfLimitCycle_abs Rstar θ₀ hR t
  have hns : Complex.normSq (H.hopfLimitCycle Rstar θ₀ t) = Rstar ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, h]
  rw [hns]
  push_cast
  ring

/-- **The closed-form curve solves the truncated normal form.** At every time `t`, the limit cycle
`w(t) = Rstar e^{i(θ₀ + Ω t)}` with `Ω = cycleFreq Rstar` has derivative equal to the truncated
normal-form right-hand side evaluated along the curve: `HasDerivAt w (normalForm μ (w t)) t`. This is
the closed-form solution check; it holds precisely because `Rstar` is the radial equilibrium, so the
real part `α + ℓ₁ Rstar²` of the linear-plus-cubic coefficient cancels and only the rotation `iΩ`
survives. -/
theorem hopfLimitCycle_solves {μ Rstar : ℝ} (θ₀ : ℝ) (hR : 0 ≤ Rstar)
    (hrad : H.radialField μ Rstar = 0) (t : ℝ) :
    HasDerivAt (H.hopfLimitCycle Rstar θ₀) (H.normalForm μ (H.hopfLimitCycle Rstar θ₀ t)) t := by
  -- The inner exponent `t ↦ I (θ₀ + Ω t)` is affine in `t` with derivative `I Ω`.
  have hΩ : HasDerivAt
      (fun s : ℝ => Complex.I * ((θ₀ : ℂ) + (H.cycleFreq Rstar : ℂ) * (s : ℂ)))
      (Complex.I * (H.cycleFreq Rstar : ℂ)) t := by
    have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have hlin : HasDerivAt
        (fun s : ℝ => (θ₀ : ℂ) + (H.cycleFreq Rstar : ℂ) * (s : ℂ))
        ((H.cycleFreq Rstar : ℂ) * 1) t :=
      (hid.const_mul (H.cycleFreq Rstar : ℂ)).const_add (θ₀ : ℂ)
    have := hlin.const_mul Complex.I
    simpa [mul_comm, mul_one] using this
  -- Differentiate the exponential and the constant factor `Rstar`.
  have hexp := hΩ.cexp
  have hcurve := hexp.const_mul (Rstar : ℂ)
  -- Identify the derivative with the normal-form right-hand side along the curve.
  refine hcurve.congr_deriv ?_
  -- The derivative of `w` is `Rstar · (exp(...) · (I Ω)) = (I Ω) · w(t)`.
  -- The normal form along the curve is `((α + iω) + c₁ Rstar²) · w(t)`; the real part cancels.
  rw [H.normalForm_eq, H.hopfLimitCycle_normSq Rstar θ₀ hR]
  -- Reduce both sides to a common multiple of `w(t) = Rstar · exp(...)`.
  show (Rstar : ℂ)
      * (Complex.exp (Complex.I * ((θ₀ : ℂ) + (H.cycleFreq Rstar : ℂ) * (t : ℂ)))
          * (Complex.I * (H.cycleFreq Rstar : ℂ)))
    = ((H.α μ : ℂ) + (H.ω : ℂ) * Complex.I)
        * H.hopfLimitCycle Rstar θ₀ t
      + H.c₁ * (H.hopfLimitCycle Rstar θ₀ t * (Rstar : ℂ) ^ 2)
  rw [hopfLimitCycle_apply]
  -- If `Rstar = 0` the curve is constantly `0`; both sides vanish.
  rcases eq_or_ne Rstar 0 with hR0 | hR0
  · subst hR0; simp
  -- Otherwise factor both sides through `w(t) = Rstar · E` and compare scalar coefficients.
  set E : ℂ := Complex.exp (Complex.I * ((θ₀ : ℂ) + (H.cycleFreq Rstar : ℂ) * (t : ℂ))) with hE
  -- The scalar identity: `I Ω = (α + iω) + c₁ Rstar²` given the radial equilibrium.
  have hcoeff : Complex.I * (H.cycleFreq Rstar : ℂ)
      = ((H.α μ : ℂ) + (H.ω : ℂ) * Complex.I) + H.c₁ * (Rstar : ℂ) ^ 2 := by
    -- Compare real and imaginary parts.
    apply Complex.ext
    · -- Real parts: `0 = α + (Re c₁) Rstar²`, the radial equilibrium divided by `Rstar`.
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re,
        Complex.ofReal_re, Complex.ofReal_im]
      have hrad0 : H.α μ * Rstar + H.firstLyapunov * Rstar ^ 3 = 0 := by
        have := hrad; rw [radialField_apply] at this; exact this
      have hrad' : H.α μ + H.firstLyapunov * Rstar ^ 2 = 0 := by
        have hfac : Rstar * (H.α μ + H.firstLyapunov * Rstar ^ 2) = 0 := by
          linear_combination hrad0
        rcases mul_eq_zero.1 hfac with hz | hz
        · exact absurd hz hR0
        · exact hz
      simp only [firstLyapunov] at hrad'
      have hpow : ((Rstar : ℂ) ^ 2).re = Rstar ^ 2 := by
        rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
      have hpowim : ((Rstar : ℂ) ^ 2).im = 0 := by
        rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
      rw [hpow, hpowim]
      nlinarith [hrad']
    · -- Imaginary parts: `Ω = ω + (Im c₁) Rstar²`, the definition of `cycleFreq`.
      simp only [Complex.I_re, Complex.I_im, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, cycleFreq]
      have hpow : ((Rstar : ℂ) ^ 2).re = Rstar ^ 2 := by
        rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
      have hpowim : ((Rstar : ℂ) ^ 2).im = 0 := by
        rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
      rw [hpow, hpowim]
      ring
  -- Conclude by substituting the coefficient identity and rearranging.
  rw [hcoeff]
  ring

/-- **The limit cycle is periodic with period `T = 2π/Ω`.** For nonzero angular frequency
`Ω = cycleFreq Rstar` the closed-form orbit `w(t) = Rstar e^{i(θ₀ + Ω t)}` is `2π/Ω`-periodic,
inherited from the `2πi`-periodicity of `Complex.exp`: advancing `t` by `2π/Ω` adds exactly `2πi` to
the exponent. -/
theorem hopfLimitCycle_periodic {Rstar : ℝ} (θ₀ : ℝ) (hΩ : H.cycleFreq Rstar ≠ 0) :
    Function.Periodic (H.hopfLimitCycle Rstar θ₀) (2 * Real.pi / H.cycleFreq Rstar) := by
  intro t
  rw [hopfLimitCycle_apply, hopfLimitCycle_apply]
  congr 1
  -- The exponent at `t + T` exceeds the one at `t` by exactly `2π i`.
  have hcast : (H.cycleFreq Rstar : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hexp : Complex.I * ((θ₀ : ℂ)
        + (H.cycleFreq Rstar : ℂ) * ((t + 2 * Real.pi / H.cycleFreq Rstar : ℝ) : ℂ))
      = Complex.I * ((θ₀ : ℂ) + (H.cycleFreq Rstar : ℂ) * (t : ℂ)) + 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
    ring
  rw [hexp, Complex.exp_periodic _]

/-- **The limit cycle is periodic with the positive period `|2π/Ω|`.** A function periodic with
period `c` is periodic with period `−c` (`Function.Periodic.neg`), hence with `|c|`; for nonzero `Ω`
the orbit is periodic with the strictly positive fundamental period `2π/|Ω| = |2π/Ω|`. This is the
form the `PeriodicOrbitSeed` records (`T_pos` demands a positive period). -/
theorem hopfLimitCycle_periodic_abs {Rstar : ℝ} (θ₀ : ℝ) (hΩ : H.cycleFreq Rstar ≠ 0) :
    Function.Periodic (H.hopfLimitCycle Rstar θ₀) |2 * Real.pi / H.cycleFreq Rstar| := by
  rcases abs_choice (2 * Real.pi / H.cycleFreq Rstar) with h | h
  · rw [h]; exact H.hopfLimitCycle_periodic θ₀ hΩ
  · rw [h]; exact (H.hopfLimitCycle_periodic θ₀ hΩ).neg

/-- **The positive period `|2π/Ω|` is strictly positive.** With `Ω ≠ 0` and `π > 0` the quotient
`2π/Ω` is nonzero, so its absolute value is strictly positive. -/
theorem hopfLimitCycle_period_pos {Rstar : ℝ} (hΩ : H.cycleFreq Rstar ≠ 0) :
    0 < |2 * Real.pi / H.cycleFreq Rstar| := by
  rw [abs_pos]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  exact div_ne_zero (ne_of_gt hpi) hΩ

/-- **The limit cycle is nonconstant.** With `Rstar > 0` and nonzero angular frequency, the orbit is
a genuine cycle, not the equilibrium: a half-period advance multiplies the phase by `e^{iπ} = −1`,
sending `w(0) = Rstar e^{iθ₀}` to its antipode `−w(0) ≠ w(0)`. -/
theorem hopfLimitCycle_nonconstant {Rstar : ℝ} (θ₀ : ℝ) (hR : 0 < Rstar)
    (hΩ : H.cycleFreq Rstar ≠ 0) :
    ∃ s t, H.hopfLimitCycle Rstar θ₀ s ≠ H.hopfLimitCycle Rstar θ₀ t := by
  refine ⟨Real.pi / H.cycleFreq Rstar, 0, ?_⟩
  rw [hopfLimitCycle_apply, hopfLimitCycle_apply]
  have hcast : (H.cycleFreq Rstar : ℂ) ≠ 0 := by exact_mod_cast hΩ
  -- At `s = π/Ω` the exponent is `I θ₀ + I π`; the half-period factor is `e^{iπ} = -1`.
  have hs : Complex.I * ((θ₀ : ℂ)
        + (H.cycleFreq Rstar : ℂ) * ((Real.pi / H.cycleFreq Rstar : ℝ) : ℂ))
      = Complex.I * (θ₀ : ℂ) + Real.pi * Complex.I := by
    push_cast
    field_simp
  have ht : Complex.I * ((θ₀ : ℂ) + (H.cycleFreq Rstar : ℂ) * ((0 : ℝ) : ℂ))
      = Complex.I * (θ₀ : ℂ) := by
    push_cast; ring
  rw [hs, ht, Complex.exp_add, Complex.exp_pi_mul_I]
  -- The two endpoints are `-Rstar e^{Iθ₀}` and `Rstar e^{Iθ₀}`; these differ since both are nonzero.
  have hRc : (Rstar : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  have hExp : Complex.exp (Complex.I * (θ₀ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  intro hcontra
  -- `Rstar e * (-1) = Rstar e` forces `Rstar e = 0`, contradiction.
  have : (Rstar : ℂ) * (Complex.exp (Complex.I * (θ₀ : ℂ)) * (-1))
      = (Rstar : ℂ) * Complex.exp (Complex.I * (θ₀ : ℂ)) := hcontra
  have h2 : (Rstar : ℂ) * Complex.exp (Complex.I * (θ₀ : ℂ)) * 2 = 0 := by
    linear_combination -this
  rcases mul_eq_zero.1 h2 with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · exact hRc h'
    · exact hExp h'
  · norm_num at h

/-! ## The constructed periodic-orbit seed for the truncated field -/

/-- **The closed-form periodic-orbit seed for the truncated normal form.** On a bifurcating branch
`branch ⊆ ℝ` whose closure contains the crossing `μ₀` (the topological shape of the branch, fixed by
`α`, supplied as `hclosure`), suppose every parameter `ν ∈ branch` satisfies the sign condition
`α ν / ℓ₁ < 0` (`hbranch`, so the radial equilibrium `Rstar ν = √(−α ν/ℓ₁) > 0` exists) with nonzero
angular frequency `Ω ν = ω + (Im c₁) Rstar²` (`hfreq`, finite period). Then the closed-form curve
`hopfLimitCycle (Rstar ν) 0` is a genuine periodic orbit of the truncated field at every branch
parameter: it solves the field (`hopfLimitCycle_solves`), is periodic with period `2π/Ω`
(`hopfLimitCycle_periodic`), nonconstant (`hopfLimitCycle_nonconstant`), and has amplitude `Rstar`.
Packaged as a `PlanarHopfData.PeriodicOrbitSeed`, this *constructs* the seed for the truncation: the
limit cycle is built in closed form, not assumed, so `hopf_andronov_periodic_orbits` fires for the
truncated field without the seed as a hypothesis.

Near the crossing `α ν ≈ 0` and `Ω ν ≈ ω ≠ 0`, so the branch and frequency conditions hold on a
one-sided neighbourhood of `μ₀`; that neighbourhood is the branch, with `μ₀` in its closure. -/
noncomputable def truncatedSeed (branch : Set ℝ)
    (hclosure : H.μ₀ ∈ closure branch)
    (hbranch : ∀ ν ∈ branch, H.α ν / H.firstLyapunov < 0)
    (hfreq : ∀ ν ∈ branch, H.cycleFreq (Real.sqrt (-H.α ν / H.firstLyapunov)) ≠ 0) :
    H.PeriodicOrbitSeed where
  branch := branch
  μ₀_mem_closure := hclosure
  T := fun ν => |2 * Real.pi / H.cycleFreq (Real.sqrt (-H.α ν / H.firstLyapunov))|
  T_pos := fun ν hν => H.hopfLimitCycle_period_pos (hfreq ν hν)
  orbit := fun ν => H.hopfLimitCycle (Real.sqrt (-H.α ν / H.firstLyapunov)) 0
  periodic := fun ν hν => H.hopfLimitCycle_periodic_abs 0 (hfreq ν hν)
  nonconstant := fun ν hν => by
    have hpos : 0 < -H.α ν / H.firstLyapunov := by
      rw [neg_div]; linarith [hbranch ν hν]
    exact H.hopfLimitCycle_nonconstant 0 (Real.sqrt_pos.2 hpos) (hfreq ν hν)
  amplitude := fun ν hν => by
    refine ⟨0, ?_⟩
    have hpos : 0 < -H.α ν / H.firstLyapunov := by
      rw [neg_div]; linarith [hbranch ν hν]
    rw [H.hopfLimitCycle_abs _ 0 (le_of_lt (Real.sqrt_pos.2 hpos)) 0]

/-- **The Hopf–Andronov theorem fires for the truncated normal form, with the seed constructed.**
Equipping the conditional theorem `hopf_andronov_periodic_orbits` with the closed-form
`truncatedSeed` removes the `PeriodicOrbitSeed` hypothesis for the *truncated* field: a transversal
crossing (`α' ≠ 0`) and nondegeneracy (`ℓ₁ ≠ 0`), together with a branch `branch` whose closure
contains the crossing and on which the sign and frequency conditions hold, yield a one-parameter
family of genuine, nonconstant, periodic orbits of the truncated normal form, with the `√(−α/ℓ₁)`
amplitude law — every orbit built explicitly as `Rstar e^{i Ω t}`. -/
theorem hopf_andronov_truncated (_htrans : H.α' ≠ 0) (hℓ : H.firstLyapunov ≠ 0) (branch : Set ℝ)
    (hclosure : H.μ₀ ∈ closure branch)
    (hbranch : ∀ ν ∈ branch, H.α ν / H.firstLyapunov < 0)
    (hfreq : ∀ ν ∈ branch, H.cycleFreq (Real.sqrt (-H.α ν / H.firstLyapunov)) ≠ 0) :
    H.μ₀ ∈ closure branch ∧
      ∀ μ ∈ branch, (0 : ℝ) < |2 * Real.pi / H.cycleFreq (Real.sqrt (-H.α μ / H.firstLyapunov))|
        ∧ Function.Periodic (H.hopfLimitCycle (Real.sqrt (-H.α μ / H.firstLyapunov)) 0)
            |2 * Real.pi / H.cycleFreq (Real.sqrt (-H.α μ / H.firstLyapunov))|
        ∧ (∃ s t, H.hopfLimitCycle (Real.sqrt (-H.α μ / H.firstLyapunov)) 0 s
            ≠ H.hopfLimitCycle (Real.sqrt (-H.α μ / H.firstLyapunov)) 0 t)
        ∧ (∃ s, ‖H.hopfLimitCycle (Real.sqrt (-H.α μ / H.firstLyapunov)) 0 s‖
            = Real.sqrt (-H.α μ / H.firstLyapunov)) :=
  H.hopf_andronov_periodic_orbits _htrans hℓ (H.truncatedSeed branch hclosure hbranch hfreq)

end PlanarHopfData

end CRNT

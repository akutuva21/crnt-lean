import CRNT.Examples.HopfNetwork3
import CRNT.Dynamics.HopfTransversality3
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

/-!
# C¹ eigenvalue branches of the network Jacobian and eigenvalue-real-part transversality

The genuine three-species autocatalytic network `CRNT.Examples.HopfNetwork3.N` has mass-action
Jacobian `J μ` at the equilibrium `(1,1,1)`, with characteristic cubic
`X³ − (trace J μ) X² + (c₂Fin3 J μ) X − (det J μ)` over `ℂ`. The cubic does not factor rationally in
the autocatalytic rate `μ`, so the conjugate-pair real part `p(μ)`, squared imaginary part `q(μ)`,
and real eigenvalue `r(μ)` cannot be written in closed form. This module constructs them as `C¹`
implicit branches near the crossing rate `μ₀ = 6` and upgrades the network's boundary-velocity
transversality (`CRNT.Examples.HopfNetwork3.boundary_crossing_transversal`) to the
eigenvalue-real-part form `p'(μ₀) ≠ 0`.

The real eigenvalue branch `r` is the implicit function of

`charCubic μ x = x³ + (μ + 3) x² + (μ² + 3μ − 42) x + (10 μ² − 42 μ)`,

the complexified characteristic polynomial written with `−trace = μ + 3`, `c₂Fin3 = μ² + 3μ − 42`,
`−det = 10 μ² − 42 μ`. At `(μ₀, x₀) = (6, −9)` the cubic vanishes and its `x`-partial derivative
`3x² + 2(μ + 3)x + (μ² + 3μ − 42)` equals `93 ≠ 0`, so the root `x₀ = −9` is simple. Mathlib's
implicit function theorem (`implicitFunctionOfBivariate`, the curried bivariate form used by
`CRNT.Dynamics.FenichelC1Manifold`) produces a branch `r` with `HasDerivAt r r' μ₀`, `r μ₀ = −9`,
and `charCubic μ (r μ) = 0` for all `μ` near `μ₀`.

The conjugate-pair data follow from `r` by the real Vieta identities, made into genuine functions:
`p μ = (trace (J μ) − r μ) / 2` and `q μ = c₂Fin3 (J μ) − 2 (r μ) (p μ) − (p μ)²`. By construction
`r μ + 2 p μ = trace (J μ)` and `2 (r μ) (p μ) + ((p μ)² + q μ) = c₂Fin3 (J μ)`; the third Vieta
relation `r μ ((p μ)² + q μ) = det (J μ)` holds wherever `r μ` is a root. Consequently the Vieta
boundary function `hopfBoundaryFn (r μ) (p μ) (q μ)` agrees with the network's penultimate Hurwitz
determinant `boundaryFn μ` on a neighbourhood of `μ₀`, so their derivatives at `μ₀` coincide. The
network already has `boundaryFn' μ₀ = 69 ≠ 0`, so `CRNT.hopf_transversal_crossing` yields the
eigenvalue-real-part crossing speed `p'(μ₀) ≠ 0`: the conjugate eigenvalue pair of a genuine
mass-action network crosses the imaginary axis transversally.

* `CRNT.Examples.HopfNetwork3Branches.r` — the `C¹` real-eigenvalue branch (implicit function).
* `CRNT.Examples.HopfNetwork3Branches.hasDerivAt_r` — `HasDerivAt r r' μ₀` with `r μ₀ = −9`.
* `CRNT.Examples.HopfNetwork3Branches.p`, `q` — the conjugate-pair real part and squared imaginary
  part as `C¹` functions of `r`, with `p μ₀ = 0`, `q μ₀ = 12`.
* `CRNT.Examples.HopfNetwork3Branches.hopfBoundaryFn_eventuallyEq` — `hopfBoundaryFn (r ·) (p ·)
  (q ·)` agrees with `boundaryFn` near `μ₀`.
* `CRNT.Examples.HopfNetwork3Branches.eigenvalue_real_part_transversal` — the headline: the
  conjugate-pair real-part crossing speed is nonzero, `p'(μ₀) ≠ 0`.

The limit-cycle existence conclusion of the Hopf theorem — turning this transversal crossing into a
one-parameter family of periodic orbits — is the analytic center-manifold reduction of Guckenheimer
& Holmes, "Nonlinear Oscillations, Dynamical Systems, and Bifurcations of Vector Fields", §3.4,
which needs center-manifold theory absent from `Mathlib` and stays out of scope.

Depends on: CRNT.Examples.HopfNetwork3,
CRNT.Dynamics.HopfTransversality3, Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate.
-/

namespace CRNT.Examples.HopfNetwork3Branches

open CRNT CRNT.Examples.HopfNetwork3 Filter Topology

/-- The complexified characteristic cubic of `J μ` as a curried bivariate real function of the rate
`μ` and the root `x`: `x³ + (μ + 3) x² + (μ² + 3μ − 42) x + (10 μ² − 42 μ)`, the polynomial
`X³ − (trace J μ) X² + (c₂Fin3 J μ) X − (det J μ)` with the network's invariants substituted. -/
def charCubic (μ x : ℝ) : ℝ :=
  x ^ 3 + (μ + 3) * x ^ 2 + (μ ^ 2 + 3 * μ - 42) * x + (10 * μ ^ 2 - 42 * μ)

/-- The crossing rate and the simple real root there: `(μ₀, x₀) = (6, −9)`. -/
def x₀ : ℝ := -9

/-- The cubic vanishes at `(μ₀, x₀) = (6, −9)`: `x₀ = −9` is a genuine root of the network
characteristic polynomial at the crossing rate. -/
theorem charCubic_pt : charCubic μ₀ x₀ = 0 := by
  simp only [charCubic, μ₀, x₀]; norm_num

/-- The `x`-partial derivative of the cubic is `3x² + 2(μ + 3)x + (μ² + 3μ − 42)`. -/
theorem hasDerivAt_charCubic_snd (μ x : ℝ) :
    HasDerivAt (charCubic μ ·) (3 * x ^ 2 + 2 * (μ + 3) * x + (μ ^ 2 + 3 * μ - 42)) x := by
  have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  have hx2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x ^ 1) x := by simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt (fun x : ℝ => (μ + 3) * x ^ 2) ((μ + 3) * (2 * x ^ 1)) x :=
    hx2.const_mul (μ + 3)
  have h1 : HasDerivAt (fun x : ℝ => (μ ^ 2 + 3 * μ - 42) * x) (μ ^ 2 + 3 * μ - 42) x := by
    simpa using (hasDerivAt_id x).const_mul (μ ^ 2 + 3 * μ - 42)
  have hsum := ((h3.add h2).add h1).add_const (10 * μ ^ 2 - 42 * μ)
  have heq : 3 * x ^ 2 + (μ + 3) * (2 * x ^ 1) + (μ ^ 2 + 3 * μ - 42)
      = 3 * x ^ 2 + 2 * (μ + 3) * x + (μ ^ 2 + 3 * μ - 42) := by ring
  rw [← heq]
  exact hsum

/-- The `μ`-partial derivative of the cubic is `x² + (2μ + 3)x + (20μ − 42)`. -/
theorem hasDerivAt_charCubic_fst (μ x : ℝ) :
    HasDerivAt (charCubic · x) (x ^ 2 + (2 * μ + 3) * x + (20 * μ - 42)) μ := by
  have hc3 : HasDerivAt (fun _ : ℝ => x ^ 3) 0 μ := hasDerivAt_const μ (x ^ 3)
  have ha : HasDerivAt (fun μ : ℝ => (μ + 3) * x ^ 2) (x ^ 2) μ := by
    simpa using ((hasDerivAt_id μ).add_const (3 : ℝ)).mul_const (x ^ 2)
  have hb : HasDerivAt (fun μ : ℝ => (μ ^ 2 + 3 * μ - 42) * x) ((2 * μ + 3) * x) μ := by
    have hpoly : HasDerivAt (fun μ : ℝ => μ ^ 2 + 3 * μ - 42) (2 * μ + 3) μ := by
      have hp2 : HasDerivAt (fun μ : ℝ => μ ^ 2) (2 * μ ^ 1) μ := by simpa using hasDerivAt_pow 2 μ
      have hp1 : HasDerivAt (fun μ : ℝ => 3 * μ) 3 μ := by
        simpa using (hasDerivAt_id μ).const_mul (3 : ℝ)
      have := (hp2.add hp1).sub_const (42 : ℝ)
      have heq : 2 * μ ^ 1 + 3 = 2 * μ + 3 := by ring
      rwa [heq] at this
    simpa using hpoly.mul_const x
  have hd : HasDerivAt (fun μ : ℝ => 10 * μ ^ 2 - 42 * μ) (20 * μ - 42) μ := by
    have hm2 : HasDerivAt (fun μ : ℝ => μ ^ 2) (2 * μ ^ 1) μ := by simpa using hasDerivAt_pow 2 μ
    have hp2 : HasDerivAt (fun μ : ℝ => 10 * μ ^ 2) (10 * (2 * μ ^ 1)) μ :=
      hm2.const_mul (10 : ℝ)
    have hp1 : HasDerivAt (fun μ : ℝ => 42 * μ) 42 μ := by
      simpa using (hasDerivAt_id μ).const_mul (42 : ℝ)
    have := hp2.sub hp1
    have heq : 10 * (2 * μ ^ 1) - 42 = 20 * μ - 42 := by ring
    rwa [heq] at this
  have hsum := ((hc3.add ha).add hb).add hd
  have hfun : (charCubic · x) = fun μ : ℝ =>
      x ^ 3 + (μ + 3) * x ^ 2 + (μ ^ 2 + 3 * μ - 42) * x + (10 * μ ^ 2 - 42 * μ) := by
    funext μ; rfl
  rw [hfun]
  have heq : 0 + x ^ 2 + (2 * μ + 3) * x + (20 * μ - 42)
      = x ^ 2 + (2 * μ + 3) * x + (20 * μ - 42) := by ring
  rw [← heq]
  exact hsum

/-- The `x`-partial derivative of the cubic at the crossing point is `93 ≠ 0`: the real root
`x₀ = −9` of the network characteristic polynomial at `μ₀ = 6` is simple, the nondegeneracy the
implicit function theorem consumes. -/
theorem charCubic_snd_deriv_pt :
    (3 * x₀ ^ 2 + 2 * (μ₀ + 3) * x₀ + (μ₀ ^ 2 + 3 * μ₀ - 42)) = 93 := by
  simp only [μ₀, x₀]; norm_num

/-- The `x`-partial derivative of the cubic as a continuous linear map `ℝ →L[ℝ] ℝ`, the scalar
multiplication by `3x² + 2(μ + 3)x + (μ² + 3μ − 42)`. -/
def fst₂ (μ x : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (3 * x ^ 2 + 2 * (μ + 3) * x + (μ ^ 2 + 3 * μ - 42))

/-- The `μ`-partial derivative of the cubic as a continuous linear map `ℝ →L[ℝ] ℝ`, the scalar
multiplication by `x² + (2μ + 3)x + (20μ − 42)`. -/
def fst₁ (μ x : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (x ^ 2 + (2 * μ + 3) * x + (20 * μ - 42))

/-- The cubic's first-variable Fréchet derivative is `fst₁`, everywhere. -/
theorem hasFDerivAt_fst₁ (μ x : ℝ) : HasFDerivAt (charCubic · x) (fst₁ μ x) μ :=
  (hasDerivAt_charCubic_fst μ x).hasFDerivAt

/-- The cubic's second-variable Fréchet derivative is `fst₂`, everywhere. -/
theorem hasFDerivAt_fst₂ (μ x : ℝ) : HasFDerivAt (charCubic μ ·) (fst₂ μ x) x :=
  (hasDerivAt_charCubic_snd μ x).hasFDerivAt

/-- The uncurried second-partial-derivative map is continuous: it is scalar multiplication by a
polynomial in `(μ, x)`, the polynomial composed with the continuous linear `smulRightL`. -/
theorem continuous_fst₂ : Continuous (↿fst₂) := by
  have hfun : (↿fst₂) = fun p : ℝ × ℝ =>
      ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)
        (3 * p.2 ^ 2 + 2 * (p.1 + 3) * p.2 + (p.1 ^ 2 + 3 * p.1 - 42)) := rfl
  rw [hfun]
  exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.comp (by fun_prop)

/-- The uncurried first-partial-derivative map is continuous. -/
theorem continuous_fst₁ : Continuous (↿fst₁) := by
  have hfun : (↿fst₁) = fun p : ℝ × ℝ =>
      ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)
        (p.2 ^ 2 + (2 * p.1 + 3) * p.2 + (20 * p.1 - 42)) := rfl
  rw [hfun]
  exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.comp (by fun_prop)

/-- The second-partial-derivative continuous linear map at the crossing point is invertible: it is
scalar multiplication by `93 ≠ 0`, the forward direction of the continuous linear automorphism
`x ↦ x · 93`. -/
theorem isInvertible_fst₂_pt : (fst₂ μ₀ x₀).IsInvertible := by
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (93 : ℝ) (by norm_num)), ?_⟩
  apply ContinuousLinearMap.ext
  intro y
  rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquivAut_apply]
  simp only [fst₂, ContinuousLinearMap.smulRight_apply, smul_eq_mul, Units.val_mk0,
    charCubic_snd_deriv_pt]
  show y * 93 = y * 93
  rfl

/-! ## The implicit real-eigenvalue branch -/

/-- The cubic's first-variable Fréchet derivative is `fst₁` on a neighbourhood of `(μ₀, x₀)`. -/
theorem eventually_hasFDerivAt_fst₁ :
    ∀ᶠ v in 𝓝 ((μ₀, x₀) : ℝ × ℝ), HasFDerivAt (charCubic · v.2) (fst₁ v.1 v.2) v.1 :=
  Eventually.of_forall fun v => hasFDerivAt_fst₁ v.1 v.2

/-- The cubic's second-variable Fréchet derivative is `fst₂` on a neighbourhood of `(μ₀, x₀)`. -/
theorem eventually_hasFDerivAt_fst₂ :
    ∀ᶠ v in 𝓝 ((μ₀, x₀) : ℝ × ℝ), HasFDerivAt (charCubic v.1 ·) (fst₂ v.1 v.2) v.2 :=
  Eventually.of_forall fun v => hasFDerivAt_fst₂ v.1 v.2

/-- **The C¹ real-eigenvalue branch.** Mathlib's curried bivariate implicit function theorem,
applied to the characteristic cubic `charCubic` at the simple root `(μ₀, x₀) = (6, −9)`, yields the
real-eigenvalue branch `r : ℝ → ℝ`. It is the implicit function of `charCubic μ x = 0` near `μ₀`. -/
noncomputable def r : ℝ → ℝ :=
  implicitFunctionOfBivariate eventually_hasFDerivAt_fst₁ eventually_hasFDerivAt_fst₂
    continuous_fst₁.continuousAt continuous_fst₂.continuousAt isInvertible_fst₂_pt

/-- The branch solves the characteristic equation near `μ₀`: `charCubic μ (r μ) = charCubic μ₀ x₀
= 0` for all `μ` near `μ₀`. -/
theorem eventually_charCubic_r :
    ∀ᶠ μ in 𝓝 μ₀, charCubic μ (r μ) = charCubic μ₀ x₀ :=
  eventually_apply_implicitFunctionOfBivariate eventually_hasFDerivAt_fst₁
    eventually_hasFDerivAt_fst₂ continuous_fst₁.continuousAt continuous_fst₂.continuousAt
    isInvertible_fst₂_pt

/-- The branch passes through the simple root: `r μ₀ = x₀ = −9`. -/
theorem r_μ₀ : r μ₀ = x₀ := by
  have h := eventually_apply_eq_iff_implicitFunctionOfBivariate eventually_hasFDerivAt_fst₁
    eventually_hasFDerivAt_fst₂ continuous_fst₁.continuousAt continuous_fst₂.continuousAt
    isInvertible_fst₂_pt
  have h0 := h.self_of_nhds
  exact h0.1 rfl

/-- The branch is differentiable at `μ₀`: the implicit function theorem gives it the strict
derivative `−(fst₂ μ₀ x₀)⁻¹ ∘ fst₁ μ₀ x₀`, hence a `HasDerivAt` with the scalar derivative its
value at `1`. -/
theorem hasDerivAt_r :
    HasDerivAt r ((-(fst₂ μ₀ x₀).inverse ∘L fst₁ μ₀ x₀) 1) μ₀ := by
  have hsd := hasStrictFDerivAt_implicitFunctionOfBivariate eventually_hasFDerivAt_fst₁
    eventually_hasFDerivAt_fst₂ continuous_fst₁.continuousAt continuous_fst₂.continuousAt
    isInvertible_fst₂_pt
  exact hsd.hasFDerivAt.hasDerivAt

/-! ## The conjugate-pair branches from Vieta -/

/-- The conjugate-pair real part as a function of the rate, from the trace Vieta identity
`r + 2 p = trace`: `p μ = (trace (J μ) − r μ) / 2 = (−(μ + 3) − r μ) / 2`. -/
noncomputable def p (μ : ℝ) : ℝ := ((J μ).trace - r μ) / 2

/-- The squared imaginary part as a function of the rate, from the `c₂Fin3` Vieta identity
`2 r p + (p² + q) = c₂Fin3`: `q μ = c₂Fin3 (J μ) − 2 (r μ) (p μ) − (p μ)²`. -/
noncomputable def q (μ : ℝ) : ℝ := (J μ).c₂Fin3 - 2 * r μ * p μ - p μ ^ 2

/-- The trace Vieta identity holds for the branch data, by construction: `r μ + 2 p μ
= trace (J μ)`. -/
theorem vieta_trace (μ : ℝ) : r μ + 2 * p μ = (J μ).trace := by
  rw [p]; ring

/-- The `c₂Fin3` Vieta identity holds for the branch data, by construction:
`2 (r μ) (p μ) + ((p μ)² + q μ) = c₂Fin3 (J μ)`. -/
theorem vieta_c₂ (μ : ℝ) : 2 * r μ * p μ + (p μ ^ 2 + q μ) = (J μ).c₂Fin3 := by
  rw [q]; ring

/-- At the crossing rate the conjugate-pair real part vanishes: `p μ₀ = 0`. -/
theorem p_μ₀ : p μ₀ = 0 := by
  rw [p, trace_J, r_μ₀, x₀, μ₀]; norm_num

/-- At the crossing rate the squared imaginary part is `q μ₀ = c₂Fin3 (J μ₀) = 12 > 0`. -/
theorem q_μ₀ : q μ₀ = 12 := by
  rw [q, c₂Fin3_J, p_μ₀, r_μ₀, x₀, μ₀]; norm_num

/-- The scalar derivative of `r` at `μ₀` supplied by the implicit function theorem. -/
noncomputable def r' : ℝ := (-(fst₂ μ₀ x₀).inverse ∘L fst₁ μ₀ x₀) 1

theorem hasDerivAt_r' : HasDerivAt r r' μ₀ := hasDerivAt_r

/-- The trace of `J` is differentiable in the rate with derivative `−1` at `μ₀`. -/
theorem hasDerivAt_trace_J : HasDerivAt (fun μ : ℝ => (J μ).trace) (-1) μ₀ := by
  have hfun : (fun μ : ℝ => (J μ).trace) = fun μ : ℝ => -(μ + 3) := by funext μ; rw [trace_J]
  rw [hfun]
  have h := ((hasDerivAt_id μ₀).add_const (3 : ℝ)).neg
  have heq : -(1 : ℝ) = -1 := by ring
  rw [heq] at h
  exact h

/-- The `c₂Fin3` invariant of `J` is differentiable in the rate with derivative `2μ₀ + 3` at `μ₀`. -/
theorem hasDerivAt_c₂_J : HasDerivAt (fun μ : ℝ => (J μ).c₂Fin3) (2 * μ₀ + 3) μ₀ := by
  have hfun : (fun μ : ℝ => (J μ).c₂Fin3) = fun μ : ℝ => μ ^ 2 + 3 * μ - 42 := by
    funext μ; rw [c₂Fin3_J]
  rw [hfun]
  have hp2 : HasDerivAt (fun μ : ℝ => μ ^ 2) (2 * μ₀ ^ 1) μ₀ := by simpa using hasDerivAt_pow 2 μ₀
  have hp1 : HasDerivAt (fun μ : ℝ => 3 * μ) 3 μ₀ := by
    simpa using (hasDerivAt_id μ₀).const_mul (3 : ℝ)
  have hsum := (hp2.add hp1).sub_const (42 : ℝ)
  have heq : 2 * μ₀ ^ 1 + 3 = 2 * μ₀ + 3 := by ring
  rwa [heq] at hsum

/-- `p` is differentiable at `μ₀`, with derivative `(−1 − r') / 2`. -/
theorem hasDerivAt_p : HasDerivAt p ((-1 - r') / 2) μ₀ :=
  (hasDerivAt_trace_J.sub hasDerivAt_r').div_const 2

/-- `q` is differentiable at `μ₀`: it is the polynomial combination of the `C¹` data `r` and `p`
through the product and power rules. -/
theorem hasDerivAt_q : ∃ q', HasDerivAt q q' μ₀ := by
  have hfun : q = fun μ : ℝ => (J μ).c₂Fin3 - 2 * (r μ * p μ) - p μ ^ 2 := by
    funext μ; rw [q]; ring
  rw [hfun]
  exact ⟨_, ((hasDerivAt_c₂_J.sub ((hasDerivAt_r'.mul hasDerivAt_p).const_mul 2)).sub
    (hasDerivAt_p.pow 2))⟩

/-! ## Agreement with the network boundary function and transversality -/

/-- **The third Vieta identity from the root equation.** Wherever the branch solves the
characteristic cubic — `charCubic μ (r μ) = 0` — the determinant Vieta relation holds:
`r μ ((p μ)² + q μ) = det (J μ)`. The branch values genuinely parametrize the three eigenvalues. -/
theorem vieta_det {μ : ℝ} (hroot : charCubic μ (r μ) = 0) :
    r μ * (p μ ^ 2 + q μ) = (J μ).det := by
  have ht := vieta_trace μ
  have hc := vieta_c₂ μ
  rw [trace_J] at ht
  rw [c₂Fin3_J] at hc
  rw [det_J]
  rw [charCubic] at hroot
  -- From `hc`, `p² + q = (μ² + 3μ − 42) − 2 r p`; from `ht`, `2 r p = −(μ+3) r − r²`.
  have hpq : p μ ^ 2 + q μ = (μ ^ 2 + 3 * μ - 42) - 2 * r μ * p μ := by linear_combination hc
  have h2rp : 2 * r μ * p μ = -(μ + 3) * r μ - r μ ^ 2 := by linear_combination r μ * ht
  rw [hpq, h2rp]
  -- The remaining equation is the root equation `hroot` rearranged.
  linear_combination hroot

/-- **Agreement with the network boundary function near `μ₀`.** On the neighbourhood of `μ₀` where
the branch solves the characteristic cubic, the Vieta boundary function
`hopfBoundaryFn (r μ) (p μ) (q μ)` equals the network's penultimate Hurwitz determinant
`boundaryFn μ = det (J μ) − trace (J μ)·c₂Fin3 (J μ)`. -/
theorem hopfBoundaryFn_eventuallyEq :
    (fun μ => hopfBoundaryFn (r μ) (p μ) (q μ)) =ᶠ[𝓝 μ₀] boundaryFn := by
  have hev := eventually_charCubic_r
  rw [charCubic_pt] at hev
  filter_upwards [hev] with μ hroot
  have hdet := vieta_det hroot
  have ht := vieta_trace μ
  have hc := vieta_c₂ μ
  rw [boundaryFn, ← hopfBoundary_eq (r μ) (p μ) (q μ), ht, hc, hdet]
  ring

/-- **Eigenvalue-real-part transversal crossing (headline).** The conjugate eigenvalue pair of the
genuine three-species autocatalytic network `N` crosses the imaginary axis with nonzero speed at the
crossing rate `μ₀ = 6`: the `C¹` real-part branch satisfies `p'(μ₀) ≠ 0`.

The `C¹` eigenvalue branches `r, p, q` of `J μ` are constructed near `μ₀` by the implicit function
theorem; their Vieta boundary function agrees with the network's penultimate Hurwitz determinant
`boundaryFn` near `μ₀`, whose nonzero crossing velocity `boundaryFn'(μ₀) = 69 ≠ 0`
(`CRNT.Examples.HopfNetwork3.boundary_crossing_transversal`) therefore forces the eigenvalue
real-part crossing speed to be nonzero, via `CRNT.hopf_transversal_crossing`.

The limit-cycle existence conclusion (a one-parameter family of periodic orbits from this crossing)
is the analytic center-manifold reduction of Guckenheimer & Holmes, "Nonlinear Oscillations,
Dynamical Systems, and Bifurcations of Vector Fields", §3.4, absent from `Mathlib` and out of scope. -/
theorem eigenvalue_real_part_transversal : ((-1 - r') / 2 : ℝ) ≠ 0 := by
  obtain ⟨q', hq'⟩ := hasDerivAt_q
  -- The boundary velocity of the Vieta data is nonzero, transported from the network's `boundaryFn`.
  have hg : deriv (fun μ => hopfBoundaryFn (r μ) (p μ) (q μ)) μ₀ ≠ 0 := by
    rw [hopfBoundaryFn_eventuallyEq.deriv_eq]
    exact boundary_crossing_transversal.2
  -- Positivity of the constant coefficient `a₀ μ₀ = -(r μ₀ (p μ₀² + q μ₀)) = 108 > 0`.
  have hpos : 0 < -(r μ₀ * (p μ₀ ^ 2 + q μ₀)) := by
    rw [r_μ₀, p_μ₀, q_μ₀, x₀]; norm_num
  exact hopf_transversal_crossing hasDerivAt_r' hasDerivAt_p hq' p_μ₀
    (by rw [q_μ₀]; norm_num) hpos hg

end CRNT.Examples.HopfNetwork3Branches

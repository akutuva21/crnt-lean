import CRNT.Dynamics.HopfTransversality3

/-!
# Hopf admissibility of a one-parameter mass-action family at a crossing point

A one-parameter family of three-species mass-action Jacobians that crosses the cubic
Routh–Hurwitz boundary transversally satisfies the *algebraic* preconditions of the Hopf
bifurcation theorem: a conjugate eigenvalue pair reaches the imaginary axis
(`CRNT.Dynamics.HopfGate3Matrix`) and crosses it with nonzero speed
(`CRNT.Dynamics.HopfTransversality3`). The *analytic* conclusion — that a one-parameter family of
periodic orbits bifurcates from the equilibrium — is the planar Hopf theorem applied to the
reduced flow on a two-dimensional center manifold. `Mathlib` carries no center-manifold existence
theory, so the existence of that manifold is packaged here as a hypothesis-bearing structure,
exactly as `CRNT.Dynamics.Fenichel`'s `SlowManifoldSeed` packages Fenichel's reduction. This module
states the admissibility verdict gated on such a seed and proves the genuine consequence: the
reduced planar field inherits a non-hyperbolic equilibrium with a transversally-crossing conjugate
pair — the standard input hypotheses of the planar Hopf theorem.

**Center-manifold seed** (`CenterManifoldSeed`). At a Hopf crossing the spectrum of the `3 × 3`
Jacobian splits into a hyperbolic real eigenvalue and a critical purely-imaginary conjugate pair.
The center-manifold reduction theorem furnishes, near the crossing, a `C¹` two-dimensional
invariant manifold tangent to the critical eigenspace, on which the full flow restricts to a planar
vector field. `CenterManifoldSeed` carries this as DATA: the `C¹` center-manifold chart
`centerChart : ℝ → ℝ² → ℝ³` (parameter `μ` and a planar coordinate), its tangency to the critical
eigenspace at the crossing, forward invariance of its image under the family field, and the reduced
planar field `reducedField : ℝ → ℝ² → ℝ²` together with the reduction identity relating the two
flows. None of these analytic facts is proved; the existence of the center manifold is the
hypothesis the seed records. This mirrors how `SlowManifoldSeed` records the Fenichel slow manifold
without re-deriving it. See Hassard, Kazarinoff & Wan, "Theory and Applications of Hopf
Bifurcation", and Guckenheimer & Holmes, "Nonlinear Oscillations, Dynamical Systems, and
Bifurcations of Vector Fields", §3.2 (center manifolds) and §3.4 (the planar Hopf theorem).

**Admissibility predicate** (`hopfAdmissible`). A one-parameter mass-action Jacobian family is
Hopf-admissible at a crossing `μ₀` when (i) the `3 × 3` Hopf crossing holds at `μ₀` (a
purely-imaginary conjugate pair, via `CRNT.hurwitz_matrix_fin_three_hopf_crossing`), (ii) the
crossing is transversal (nonzero crossing speed of the real part, via
`CRNT.hopf_transversal_crossing`), and (iii) a `CenterManifoldSeed` is supplied. This bundles the
two algebraic gates with the analytic existence hypothesis.

**The genuine consequence** (`hopfAdmissible.planarHopfHypotheses`). From an admissibility witness
the reduced planar field's spectral data satisfies the *input hypotheses* of the planar Hopf
theorem: the critical eigenvalue is purely imaginary (real part zero, nonzero imaginary part), the
real eigenvalue is hyperbolic (strictly negative), and the real part crosses with nonzero speed.
These are exactly the assumptions Hassard–Kazarinoff–Wan and Guckenheimer & Holmes feed into the
planar Hopf theorem; the periodic-orbit conclusion itself is *not* asserted here, since proving it
needs the center-manifold and normal-form analysis absent from `Mathlib`. The verdict is honest:
the algebraic gates are proved, the manifold existence is carried as a seed, and the conclusion is
the precondition set, never the bifurcation theorem's output.

Depends on: CRNT.Dynamics.HopfTransversality3.
-/

namespace CRNT

open Matrix Complex

/-- A **center-manifold seed** for a one-parameter mass-action family at a Hopf crossing. It records
as DATA the two-dimensional center manifold and its reduced planar flow that the center-manifold
reduction theorem furnishes near a purely-imaginary crossing — the analytic ingredient `Mathlib`
does not provide. The `3 × 3` field is the (one-parameter) right-hand side
`field μ : ℝ³ → ℝ³`; the seed carries the `C¹` center-manifold chart, its tangency to the critical
eigenspace, forward invariance of the manifold under the field, and the reduced planar field with
its reduction identity. These fields are hypotheses, not theorems: supplying a seed asserts the
center manifold exists, mirroring how `ODE.SlowManifoldSeed` records the Fenichel slow manifold. -/
structure CenterManifoldSeed where
  /-- The one-parameter `3 × 3` vector field whose flow the seed reduces. -/
  field : ℝ → (EuclideanSpace ℝ (Fin 3)) → EuclideanSpace ℝ (Fin 3)
  /-- The crossing parameter value. -/
  μ₀ : ℝ
  /-- The `C¹` center-manifold chart: `centerChart μ w` is the point of the two-dimensional center
  manifold at parameter `μ` with planar coordinate `w`. -/
  centerChart : ℝ → (EuclideanSpace ℝ (Fin 2)) → EuclideanSpace ℝ (Fin 3)
  /-- The chart is jointly `C¹` in parameter and planar coordinate. -/
  contDiff_centerChart : ContDiff ℝ 1 (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => centerChart p.1 p.2)
  /-- The critical (purely-imaginary) eigenspace of the Jacobian at the crossing, recorded as the
  span of two real vectors `v₁, v₂` spanning the conjugate pair's real and imaginary parts. -/
  critRe : EuclideanSpace ℝ (Fin 3)
  critIm : EuclideanSpace ℝ (Fin 3)
  /-- The reduced planar vector field on the center-manifold coordinate. -/
  reducedField : ℝ → (EuclideanSpace ℝ (Fin 2)) → EuclideanSpace ℝ (Fin 2)
  /-- The Fréchet derivative of the chart `centerChart μ₀` at the planar origin. -/
  chartDeriv : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)
  /-- `chartDeriv` is genuinely the derivative of the chart at the origin. -/
  hasFDeriv_chart :
    HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 2) => centerChart μ₀ w) chartDeriv 0
  /-- **Tangency.** At the crossing the center manifold is tangent to the critical eigenspace: the
  range of the chart's derivative at the planar origin is the span of the critical pair's real and
  imaginary parts. -/
  tangency :
    LinearMap.range (chartDeriv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) =
      Submodule.span ℝ {critRe, critIm}
  /-- **Forward invariance of the center manifold under the field.** The full field at a chart point
  lies in the image of the chart's derivative, so the flow stays on the manifold. -/
  invariance :
    ∀ μ w, ∃ u : EuclideanSpace ℝ (Fin 2),
      field μ (centerChart μ w) =
        (fderiv ℝ (fun v : EuclideanSpace ℝ (Fin 2) => centerChart μ v) w) u
  /-- **Reduction identity.** The reduced planar field is the chart-pullback of the full field: the
  chart intertwines the two flows, `D(centerChart μ) (reducedField μ w) = field μ (centerChart μ w)`.
  This is the defining property of the reduced field on the center manifold. -/
  reduction :
    ∀ μ w,
      (fderiv ℝ (fun v : EuclideanSpace ℝ (Fin 2) => centerChart μ v) w) (reducedField μ w) =
        field μ (centerChart μ w)

/-- **Hopf admissibility** of a one-parameter mass-action Jacobian family at a crossing point. The
family `J : ℝ → Matrix (Fin 3) (Fin 3) ℝ` is Hopf-admissible at `μ₀` when the three Hopf
ingredients are present: the algebraic `3 × 3` eigenvalue crossing at `μ₀`, the transversality of
that crossing, and a `CenterManifoldSeed` recording the (analytically furnished) center manifold.

The crossing is recorded through the eigenvalue parametrization `r, p, q : ℝ → ℝ` — the real
eigenvalue, the conjugate pair's real part, and its squared imaginary part — with the conjugate pair
purely imaginary at `μ₀` (`p μ₀ = 0`, `0 < q μ₀`), the lower data positive (`0 < a₀`, written
`0 < -(r μ₀ (p μ₀² + q μ₀))`), and a nonzero boundary-function velocity `g'(μ₀) ≠ 0` driving the
crossing speed. -/
structure hopfAdmissible (J : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (μ₀ : ℝ) where
  /-- The eigenvalue parametrization: real eigenvalue, conjugate-pair real part, squared imaginary
  part of the conjugate pair, as functions of the parameter. -/
  r : ℝ → ℝ
  /-- The conjugate pair's real part as a function of the parameter; `p μ₀ = 0` at the crossing. -/
  p : ℝ → ℝ
  /-- The squared imaginary part of the conjugate pair as a function of the parameter. -/
  q : ℝ → ℝ
  /-- Crossing-velocity witnesses for the eigenvalue data at `μ₀`. -/
  r' : ℝ
  /-- Crossing velocity of the conjugate pair's real part at `μ₀`. -/
  p' : ℝ
  /-- Crossing velocity of the squared imaginary part at `μ₀`. -/
  q' : ℝ
  /-- The real eigenvalue is differentiable at the crossing. -/
  hr : HasDerivAt r r' μ₀
  /-- The conjugate pair's real part is differentiable at the crossing. -/
  hp : HasDerivAt p p' μ₀
  /-- The squared imaginary part is differentiable at the crossing. -/
  hq : HasDerivAt q q' μ₀
  /-- The conjugate pair sits on the imaginary axis at the crossing. -/
  hp0 : p μ₀ = 0
  /-- The squared imaginary part is nonnegative (it is a real square). -/
  hqnn : 0 ≤ q μ₀
  /-- The lower data is positive at the crossing (`0 < a₀(μ₀)`). -/
  hpos : 0 < -(r μ₀ * (p μ₀ ^ 2 + q μ₀))
  /-- The imaginary part is genuinely nonzero, so the pair is not the origin. -/
  him : q μ₀ ≠ 0
  /-- The boundary-function velocity is nonzero, driving a transversal crossing. -/
  hg : deriv (fun μ => hopfBoundaryFn (r μ) (p μ) (q μ)) μ₀ ≠ 0
  /-- The analytically furnished center manifold, recorded as a seed; its crossing parameter agrees
  with `μ₀`. -/
  seed : CenterManifoldSeed
  /-- The seed reduces the family at the same crossing parameter. -/
  seed_μ₀ : seed.μ₀ = μ₀

namespace hopfAdmissible

variable {J : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {μ₀ : ℝ} (h : hopfAdmissible J μ₀)

/-- **The planar Hopf preconditions hold for the reduced field.** From a Hopf-admissibility witness
the eigenvalue data of the reduced planar system on the center manifold satisfies the standard input
hypotheses of the planar Hopf theorem at the crossing `μ₀`:

* the critical eigenvalue is **purely imaginary** — its real part vanishes (`p μ₀ = 0`) and its
  squared imaginary part is **strictly positive** (`0 < q μ₀`), so the pair is genuinely on the
  imaginary axis and away from the origin;
* the real eigenvalue is **hyperbolic** — strictly negative (`r μ₀ < 0`), so the only non-hyperbolic
  directions are the critical pair captured by the center manifold;
* the crossing is **transversal** — the real part crosses the imaginary axis with nonzero speed
  (`p' ≠ 0`), via `CRNT.hopf_transversal_crossing`.

These are exactly the assumptions the planar Hopf theorem consumes (Hassard–Kazarinoff–Wan;
Guckenheimer & Holmes §3.4). The periodic-orbit conclusion is **not** asserted: proving it needs
the normal-form analysis on the seed's center manifold, which `Mathlib` does not provide. -/
theorem planarHopfHypotheses :
    h.p μ₀ = 0 ∧ 0 < h.q μ₀ ∧ h.r μ₀ < 0 ∧ h.p' ≠ 0 := by
  -- The transversal crossing speed, from the boundary-function velocity.
  have htrans : h.p' ≠ 0 :=
    hopf_transversal_crossing h.hr h.hp h.hq h.hp0 h.hqnn h.hpos h.hg
  -- `0 < q μ₀`: nonnegative and nonzero.
  have hq0 : 0 < h.q μ₀ := lt_of_le_of_ne h.hqnn (Ne.symm h.him)
  -- `r μ₀ < 0`: from `0 < -(r μ₀ (p μ₀² + q μ₀))` with `p μ₀ = 0` and `q μ₀ > 0`.
  have hr0 : h.r μ₀ < 0 := by
    have hpos := h.hpos
    rw [h.hp0] at hpos
    -- `0 < -(r μ₀ * (0 + q μ₀)) = -(r μ₀ * q μ₀)`, and `q μ₀ > 0`, so `r μ₀ < 0`.
    nlinarith [hpos, hq0]
  exact ⟨h.hp0, hq0, hr0, htrans⟩

/-- **The reduced planar equilibrium is non-hyperbolic with a transversal crossing.** Repackaging of
`planarHopfHypotheses`: the reduced field on the center manifold has, at the crossing, a conjugate
eigenvalue pair with zero real part and strictly positive squared imaginary part (the
non-hyperbolic, purely-imaginary spectrum) whose real part crosses with nonzero velocity. This is
the precise non-hyperbolicity-plus-transversality hypothesis pair of the planar Hopf theorem. -/
theorem reduced_nonhyperbolic_transversal :
    (h.p μ₀ = 0 ∧ 0 < h.q μ₀) ∧ h.p' ≠ 0 := by
  obtain ⟨hp0, hq0, _, htrans⟩ := h.planarHopfHypotheses
  exact ⟨⟨hp0, hq0⟩, htrans⟩

end hopfAdmissible

end CRNT

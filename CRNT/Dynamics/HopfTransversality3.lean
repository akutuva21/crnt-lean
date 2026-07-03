import CRNT.Dynamics.HopfGate3Matrix
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The transversality (eigenvalue-crossing-velocity) condition for the 3×3 Hopf boundary

A one-parameter real `3 × 3` matrix family crossing the cubic Routh–Hurwitz boundary supplies a
Hopf bifurcation only if the conjugate eigenvalue pair crosses the imaginary axis with nonzero
speed. This module proves that algebraic transversality condition purely from the cubic's
coefficients, with no center-manifold machinery.

Write the monic real cubic `X³ + a₂(μ)X² + a₁(μ)X + a₀(μ)` with `a₂ = -trace`, `a₁ = c₂Fin3`,
`a₀ = -det` (`CRNT.Dynamics.Hurwitz3Matrix`), and let the conjugate eigenvalue pair carry real
part `p(μ)`, real eigenvalue `r(μ)`, and squared imaginary part `q(μ)` through the Vieta
identities. The Hopf boundary is the vanishing of the penultimate Hurwitz determinant,
`g(μ) := a₂(μ) · a₁(μ) - a₀(μ)`. On the boundary the factorization `g = -2 p ((r + p)² + q)` of
`CRNT.hopf_crossing_core` is exact, so at a crossing `μ₀` where `p(μ₀) = 0` the derivative is

`g'(μ₀) = -2 · p'(μ₀) · (r(μ₀)² + q(μ₀))`.

With `r(μ₀)² + q(μ₀) > 0` (automatic when `a₀(μ₀) > 0`, since `a₀ = -r(r²+q)` forces `r < 0` and
`r²+q > 0`), the crossing speed of the real part `p'(μ₀)` is a nonzero multiple of `g'(μ₀)`, so
`g'(μ₀) ≠ 0` is equivalent to transversal crossing `p'(μ₀) ≠ 0`.

* `CRNT.hopf_boundary_deriv` — the boundary-function derivative identity: with `r, p, q`
  differentiable at `μ₀` and `p(μ₀) = 0`, the boundary function `g = a₂ a₁ - a₀` has derivative
  `-2 · p' · (r(μ₀)² + q(μ₀))` at `μ₀`.
* `CRNT.hopf_transversality_iff` — the transversality equivalence: under positivity of the lower
  data at `μ₀`, `g'(μ₀) ≠ 0 ↔ p'(μ₀) ≠ 0` (nonzero crossing velocity of the eigenvalue real part).
* `CRNT.hopf_transversal_crossing` — the headline implication: `g'(μ₀) ≠ 0` forces transversal
  crossing of the imaginary axis by the conjugate pair, `p'(μ₀) ≠ 0`.

The center-manifold reduction itself —
turning the transversal crossing into a one-parameter family of limit cycles — is the analytic Hopf
bifurcation theorem (Guckenheimer & Holmes, "Nonlinear Oscillations, Dynamical Systems, and
Bifurcations of Vector Fields", §3.4), which needs center-manifold theory absent from `Mathlib` and
stays out of scope.

Depends on: CRNT.Dynamics.HopfGate3Matrix.
-/

namespace CRNT

/-- The cubic's penultimate Hurwitz determinant as a function of the parameter, expressed through
the real Vieta parametrization `(r, p, q)` of the eigenvalues. With `a₂ = -(r + 2p)`,
`a₁ = 2 r p + (p² + q)`, `a₀ = -(r (p² + q))`, the boundary function `a₂ a₁ - a₀` equals
`-2 p ((r + p)² + q)`; this is the parametrized form of the factorization in
`CRNT.hopf_crossing_core`. -/
def hopfBoundaryFn (r p q : ℝ) : ℝ := -2 * p * ((r + p) ^ 2 + q)

/-- **The boundary-function factorization.** With the real Vieta parametrization `a₂ = -(r + 2p)`,
`a₁ = 2 r p + (p² + q)`, `a₀ = -(r (p² + q))`, the penultimate Hurwitz determinant
`a₂ a₁ - a₀` equals `hopfBoundaryFn r p q = -2 p ((r + p)² + q)`. -/
theorem hopfBoundary_eq (r p q : ℝ) :
    (-(r + 2 * p)) * (2 * r * p + (p ^ 2 + q)) - (-(r * (p ^ 2 + q)))
      = hopfBoundaryFn r p q := by
  rw [hopfBoundaryFn]; ring

/-- **The Hopf boundary-function derivative at a crossing.** Let `r, p, q : ℝ → ℝ` parametrize the
real eigenvalue, the conjugate-pair real part, and its squared imaginary part, each differentiable
at `μ₀` with derivatives `r', p', q'`. On the Hopf boundary the parameter `p(μ₀) = 0`, so the
boundary function `g μ = hopfBoundaryFn (r μ) (p μ) (q μ)` has derivative

`g'(μ₀) = -2 · p' · (r(μ₀)² + q(μ₀))`

at `μ₀`: the only surviving term is the one carrying `p'`, because every other term is multiplied
by the vanishing factor `p(μ₀)`. -/
theorem hopf_boundary_deriv {r p q : ℝ → ℝ} {μ₀ r' p' q' : ℝ}
    (hr : HasDerivAt r r' μ₀) (hp : HasDerivAt p p' μ₀) (hq : HasDerivAt q q' μ₀)
    (hp0 : p μ₀ = 0) :
    HasDerivAt (fun μ => hopfBoundaryFn (r μ) (p μ) (q μ))
      (-2 * p' * (r μ₀ ^ 2 + q μ₀)) μ₀ := by
  -- `g = (-2 * p) * ((r + p)² + q)`. Differentiate as a product, then specialize at `p μ₀ = 0`.
  have hrp : HasDerivAt (fun μ => r μ + p μ) (r' + p') μ₀ := hr.add hp
  have hsq : HasDerivAt (fun μ => (r μ + p μ) ^ 2)
      (2 * (r μ₀ + p μ₀) ^ 1 * (r' + p')) μ₀ := hrp.pow 2
  have hbase : HasDerivAt (fun μ => (r μ + p μ) ^ 2 + q μ)
      (2 * (r μ₀ + p μ₀) ^ 1 * (r' + p') + q') μ₀ := hsq.add hq
  have hlead : HasDerivAt (fun μ => -2 * p μ) (-2 * p') μ₀ := by
    simpa using hp.const_mul (-2 : ℝ)
  have hprod := hlead.mul hbase
  -- The product derivative, before simplification, with the `hopfBoundaryFn` function form.
  have hpre : HasDerivAt (fun μ => hopfBoundaryFn (r μ) (p μ) (q μ))
      (-2 * p' * ((r μ₀ + p μ₀) ^ 2 + q μ₀)
        + -2 * p μ₀ * (2 * (r μ₀ + p μ₀) ^ 1 * (r' + p') + q')) μ₀ := by
    have hfun : (fun μ => hopfBoundaryFn (r μ) (p μ) (q μ))
        = fun μ => -2 * p μ * ((r μ + p μ) ^ 2 + q μ) := by
      funext μ; rw [hopfBoundaryFn]
    rw [hfun]; exact hprod
  -- At `p μ₀ = 0` the second product term vanishes, leaving `-2 p' (r² + q)`.
  have hval : -2 * p' * ((r μ₀ + p μ₀) ^ 2 + q μ₀)
      + -2 * p μ₀ * (2 * (r μ₀ + p μ₀) ^ 1 * (r' + p') + q')
      = -2 * p' * (r μ₀ ^ 2 + q μ₀) := by rw [hp0]; ring
  rwa [hval] at hpre

/-- **Positivity of the crossing modulus.** At a crossing `μ₀` with `p(μ₀) = 0` and the lower data
positive in the form `0 < -(r(μ₀) (p(μ₀)² + q(μ₀)))` — i.e. `0 < a₀(μ₀)` — the modulus
`r(μ₀)² + q(μ₀)` is strictly positive. (It is the squared distance of the conjugate pair from the
origin; `q ≥ 0` as a squared imaginary part, and `a₀ > 0` forbids the degenerate `r = q = 0`.) -/
theorem hopf_crossing_modulus_pos {r q : ℝ} (hq : 0 ≤ q)
    (H₀ : 0 < -(r * (0 ^ 2 + q))) : 0 < r ^ 2 + q := by
  -- `0 < -(r q)` forces `q ≠ 0`, hence `q > 0`, hence `r² + q > 0`.
  rcases lt_or_eq_of_le hq with h | h
  · positivity
  · exfalso; rw [← h] at H₀; simp at H₀

/-- **Hopf transversality, equivalence form.** Let `r, p, q : ℝ → ℝ` parametrize the eigenvalue
data of the one-parameter cubic, differentiable at the crossing `μ₀` with derivatives `r', p', q'`,
on the Hopf boundary `p(μ₀) = 0` and `q(μ₀) ≥ 0`. Suppose the constant coefficient stays positive,
`0 < a₀(μ₀)` written as `0 < -(r(μ₀) (p(μ₀)² + q(μ₀)))`. Then the boundary function
`g = a₂ a₁ - a₀ = hopfBoundaryFn (r ·) (p ·) (q ·)` has a nonzero derivative at `μ₀` **iff** the
conjugate pair's real part crosses with nonzero speed:

`g'(μ₀) ≠ 0 ↔ p'(μ₀) ≠ 0`.

The crossing speed is the explicit nonzero multiple `g'(μ₀) = -2 (r(μ₀)² + q(μ₀)) · p'(μ₀)`. -/
theorem hopf_transversality_iff {r p q : ℝ → ℝ} {μ₀ r' p' q' : ℝ}
    (hr : HasDerivAt r r' μ₀) (hp : HasDerivAt p p' μ₀) (hq : HasDerivAt q q' μ₀)
    (hp0 : p μ₀ = 0) (hqnn : 0 ≤ q μ₀)
    (H₀ : 0 < -(r μ₀ * (p μ₀ ^ 2 + q μ₀))) :
    deriv (fun μ => hopfBoundaryFn (r μ) (p μ) (q μ)) μ₀ ≠ 0 ↔ p' ≠ 0 := by
  have hderiv := hopf_boundary_deriv hr hp hq hp0
  rw [hderiv.deriv]
  have hmod : 0 < r μ₀ ^ 2 + q μ₀ := by
    have H₀' : 0 < -(r μ₀ * (0 ^ 2 + q μ₀)) := by rw [hp0] at H₀; exact H₀
    exact hopf_crossing_modulus_pos hqnn H₀'
  have hne : (r μ₀ ^ 2 + q μ₀) ≠ 0 := ne_of_gt hmod
  constructor
  · intro h hp'
    apply h; rw [hp']; ring
  · intro hp' h
    apply hp'
    have hfac : -2 * (r μ₀ ^ 2 + q μ₀) * p' = 0 := by linear_combination h
    rcases mul_eq_zero.1 hfac with h2 | h2
    · rcases mul_eq_zero.1 h2 with h3 | h3
      · norm_num at h3
      · exact absurd h3 hne
    · exact h2

/-- **Hopf transversal crossing (headline).** On the cubic Hopf boundary, with eigenvalue data
`r, p, q : ℝ → ℝ` differentiable at the crossing `μ₀`, `p(μ₀) = 0`, `q(μ₀) ≥ 0`, and the constant
coefficient positive (`0 < a₀(μ₀)`, written `0 < -(r(μ₀) (p(μ₀)² + q(μ₀)))`), a nonzero boundary
velocity `g'(μ₀) ≠ 0` forces the conjugate eigenvalue pair to cross the imaginary axis
**transversally**: its real-part crossing speed `p'(μ₀)` is nonzero.

This is the eigenvalue-crossing-velocity precondition of the Hopf bifurcation theorem; the analytic
center-manifold reduction producing the limit cycle is out of scope (Guckenheimer & Holmes,
"Nonlinear Oscillations, Dynamical Systems, and Bifurcations of Vector Fields", §3.4). -/
theorem hopf_transversal_crossing {r p q : ℝ → ℝ} {μ₀ r' p' q' : ℝ}
    (hr : HasDerivAt r r' μ₀) (hp : HasDerivAt p p' μ₀) (hq : HasDerivAt q q' μ₀)
    (hp0 : p μ₀ = 0) (hqnn : 0 ≤ q μ₀)
    (H₀ : 0 < -(r μ₀ * (p μ₀ ^ 2 + q μ₀)))
    (hg : deriv (fun μ => hopfBoundaryFn (r μ) (p μ) (q μ)) μ₀ ≠ 0) :
    p' ≠ 0 :=
  (hopf_transversality_iff hr hp hq hp0 hqnn H₀).1 hg

end CRNT

import CRNT.Dynamics.HopfAdmissible
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# A concrete Hopf-admissible three-dimensional family

A worked instance proving the algebraic Hopf-admissibility fields of `CRNT.hopfAdmissible` are
simultaneously satisfiable on a real object, so the admissibility verdict is non-vacuous. The
family is the explicit block-diagonal one-parameter `3 × 3` matrix

```text
J μ = [ -1   0    0 ]
      [  0   μ   -1 ]
      [  0   1    μ ]
```

a hyperbolic real eigenvalue `-1` in the first coordinate together with a planar rotation-scaling
block `[[μ, -1], [1, μ]]` in the last two coordinates, whose eigenvalues are the conjugate pair
`μ ± i`. At the crossing `μ₀ = 0` the pair sits on the imaginary axis (`±i`), so the four cubic
Routh–Hurwitz boundary data hold simultaneously:

* `c₂Fin3 (J 0) = 1 > 0`, `−trace (J 0) = 1 > 0`, `−det (J 0) = 1 > 0`;
* the Hopf boundary `−det = (−trace)·c₂Fin3` is `1 = 1·1` at `μ₀`.

So `CRNT.hurwitz_matrix_fin_three_hopf_crossing` applies and the conjugate pair is genuinely purely
imaginary. The Vieta parametrization `r μ = -1`, `p μ = μ`, `q μ = 1` (real eigenvalue, conjugate
real part, squared imaginary part) drives the boundary velocity `g'(0) = -4 ≠ 0`, so
`CRNT.hopf_transversal_crossing` gives a transversal crossing `p'(0) = 1 ≠ 0`.

The last two coordinates span a genuine invariant plane of `J μ` for every `μ` — the rotation-scaling
block leaves `span{e₁, e₂}` invariant — so the `CenterManifoldSeed` is realized honestly: its field
*is* the linear flow of `J μ`, its center manifold *is* the invariant coordinate plane, and its
reduced planar field *is* the `2 × 2` block. The full `CRNT.hopfAdmissible` witness is assembled,
establishing non-vacuity of every field — the eigenvalue-side algebraic gates and the
center-manifold seed together — on one concrete object.

The periodic-orbit conclusion of the Hopf theorem is *not* asserted here; only the simultaneous
satisfiability of the admissibility hypotheses is. See Guckenheimer & Holmes, "Nonlinear
Oscillations, Dynamical Systems, and Bifurcations of Vector Fields", §3.4 (the planar Hopf theorem).

Depends on: CRNT.Dynamics.HopfAdmissible.
-/

namespace CRNT.Examples.HopfOscillator3

open CRNT Matrix Complex

/-- The explicit one-parameter `3 × 3` family: a hyperbolic real eigenvalue `-1` and a planar
rotation-scaling block `[[μ, -1], [1, μ]]` with eigenvalues `μ ± i`. -/
def J (μ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(-1 : ℝ), 0, 0; 0, μ, -1; 0, 1, μ]

/-- The crossing parameter: the conjugate pair `μ ± i` sits on the imaginary axis at `μ₀ = 0`. -/
def μ₀ : ℝ := 0

@[simp] theorem trace_J (μ : ℝ) : (J μ).trace = -1 + 2 * μ := by
  simp [J, Matrix.trace_fin_three]; ring

@[simp] theorem det_J (μ : ℝ) : (J μ).det = -(μ ^ 2 + 1) := by
  simp [J, Matrix.det_fin_three]; ring

@[simp] theorem c₂Fin3_J (μ : ℝ) : (J μ).c₂Fin3 = (μ - 1) ^ 2 := by
  simp [J, Matrix.c₂Fin3]; ring

/-- At `μ₀ = 0` the lower Routh–Hurwitz data are all positive and the Hopf boundary holds:
`−trace = 1 > 0`, `c₂Fin3 = 1 > 0`, `−det = 1 > 0`, and `−det = (−trace)·c₂Fin3`. -/
theorem hurwitz_boundary_data_at_μ₀ :
    0 < -(J μ₀).trace ∧ 0 < (J μ₀).c₂Fin3 ∧ 0 < -(J μ₀).det ∧
      (-(J μ₀).det) = (-(J μ₀).trace) * (J μ₀).c₂Fin3 := by
  refine ⟨by simp [μ₀], by simp [μ₀], by simp [μ₀], by simp [μ₀]⟩

/-- The Vieta eigenvalue parametrization of the conjugate pair: real part `p μ = μ`. -/
def p (μ : ℝ) : ℝ := μ

/-- The squared imaginary part of the conjugate pair: constant `q μ = 1`. -/
def q (_ : ℝ) : ℝ := 1

/-- The hyperbolic real eigenvalue: constant `r μ = -1`. -/
def r (_ : ℝ) : ℝ := -1

/-- **The purely-imaginary conjugate pair at the crossing.** Feeding the Vieta identities for the
eigenvalues `z₁ = -1` and `z₂ = i` into the matrix Hopf gate gives a genuine purely-imaginary
conjugate pair (`z₂.re = 0`, `z₂.im ≠ 0`, `z₂.im² = c₂Fin3 (J 0) = 1`) with a strictly negative
real eigenvalue. -/
theorem hopf_crossing_at_μ₀ :
    (((-1 : ℂ)).re < 0) ∧ ((Complex.I).re = 0) ∧ ((Complex.I).im ≠ 0) ∧
      (Complex.I).im ^ 2 = (J μ₀).c₂Fin3 := by
  have h :=
    hurwitz_matrix_fin_three_hopf_crossing (J μ₀) (-1 : ℂ) Complex.I
      (by simp)
      (by simp [μ₀])
      (by simp [μ₀])
      (by simp [μ₀])
      (by simp [μ₀]) (by simp [μ₀]) (by simp [μ₀])
  exact h

theorem hasDerivAt_r : HasDerivAt r 0 μ₀ := by
  unfold r; exact hasDerivAt_const μ₀ (-1 : ℝ)

theorem hasDerivAt_p : HasDerivAt p 1 μ₀ := by
  unfold p; exact hasDerivAt_id μ₀

theorem hasDerivAt_q : HasDerivAt q 0 μ₀ := by
  unfold q; exact hasDerivAt_const μ₀ (1 : ℝ)

/-- The boundary velocity is nonzero: `g'(0) = -2·p'·(r² + q) = -2·1·(1 + 1) = -4 ≠ 0`. -/
theorem boundary_velocity_ne_zero :
    deriv (fun μ => hopfBoundaryFn (r μ) (p μ) (q μ)) μ₀ ≠ 0 := by
  have hderiv := hopf_boundary_deriv hasDerivAt_r hasDerivAt_p hasDerivAt_q (by simp [p, μ₀])
  rw [hderiv.deriv]
  simp [r, q]

/-- **Transversal crossing.** The conjugate pair's real part crosses with nonzero speed:
`p'(0) = 1 ≠ 0`, via `CRNT.hopf_transversal_crossing`. -/
theorem transversal_crossing : (1 : ℝ) ≠ 0 :=
  hopf_transversal_crossing hasDerivAt_r hasDerivAt_p hasDerivAt_q
    (by simp [p, μ₀]) (by simp [q]) (by simp [r, p, q, μ₀]) boundary_velocity_ne_zero

/-! ## The center-manifold seed, realized on the invariant coordinate plane

The last two coordinates span a genuine `J μ`-invariant plane for every `μ`, so the seed's analytic
hypotheses are met honestly: the field is the linear flow of `J μ`, the center manifold is the
embedded plane `{0} × ℝ²`, and the reduced planar field is the `2 × 2` rotation-scaling block. -/

/-- The chart embedding `ℝ² → ℝ³`, `w ↦ (0, w 0, w 1)`, as a continuous linear map onto the
invariant coordinate plane. -/
noncomputable def chartCLM : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => (EuclideanSpace.equiv (Fin 3) ℝ).symm ![0, w 0, w 1]
      map_add' := fun w₁ w₂ => by ext i; fin_cases i <;> simp
      map_smul' := fun c w => by ext i; fin_cases i <;> simp }

@[simp] theorem chartCLM_apply (w : EuclideanSpace ℝ (Fin 2)) :
    chartCLM w = (EuclideanSpace.equiv (Fin 3) ℝ).symm ![0, w 0, w 1] := rfl

/-- The full `3 × 3` linear field `x ↦ J μ ·ᵥ x` on `ℝ³`, as a continuous linear map. -/
noncomputable def fieldCLM (μ : ℝ) : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => (EuclideanSpace.equiv (Fin 3) ℝ).symm ((J μ).mulVec x)
      map_add' := fun x₁ x₂ => by ext i; simp [Matrix.mulVec_add]
      map_smul' := fun c x => by ext i; simp [Matrix.mulVec_smul] }

@[simp] theorem fieldCLM_apply (μ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    fieldCLM μ x = (EuclideanSpace.equiv (Fin 3) ℝ).symm ((J μ).mulVec x) := rfl

/-- The reduced planar field `ℝ² → ℝ²`, the `2 × 2` block `w ↦ (μ w0 - w1, w0 + μ w1)`. -/
noncomputable def reducedCLM (μ : ℝ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![μ * w 0 - w 1, w 0 + μ * w 1]
      map_add' := fun w₁ w₂ => by ext i; fin_cases i <;> simp <;> ring
      map_smul' := fun c w => by ext i; fin_cases i <;> simp <;> ring }

@[simp] theorem reducedCLM_apply (μ : ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    reducedCLM μ w = (EuclideanSpace.equiv (Fin 2) ℝ).symm ![μ * w 0 - w 1, w 0 + μ * w 1] := rfl

/-- The chart intertwines the reduced and full fields: `chartCLM (reducedCLM μ w) = fieldCLM μ
(chartCLM w)`. The defining property of the reduced field on the invariant plane. -/
theorem chart_reduction (μ : ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    chartCLM (reducedCLM μ w) = fieldCLM μ (chartCLM w) := by
  ext i
  fin_cases i <;>
    simp [J, Matrix.mulVec_eq_sum, Fin.sum_univ_three, EuclideanSpace.equiv] <;> ring

/-- The center-manifold seed, with field, chart, and reduced field genuinely realized. -/
noncomputable def seed : CenterManifoldSeed where
  field := fun μ => fieldCLM μ
  μ₀ := μ₀
  centerChart := fun _ => chartCLM
  contDiff_centerChart := by
    have : (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => (fun _ => ⇑chartCLM) p.1 p.2)
        = fun p : ℝ × EuclideanSpace ℝ (Fin 2) => chartCLM p.2 := rfl
    rw [this]
    exact chartCLM.contDiff.comp contDiff_snd
  critRe := chartCLM (EuclideanSpace.single 0 1)
  critIm := chartCLM (EuclideanSpace.single 1 1)
  reducedField := fun μ => reducedCLM μ
  chartDeriv := chartCLM
  hasFDeriv_chart := chartCLM.hasFDerivAt
  tangency := by
    -- The range of the chart is the span of the images of the two basis vectors `single 0 1`,
    -- `single 1 1`, which span all of `ℝ²`.
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      -- Write `w = w 0 • single 0 1 + w 1 • single 1 1`, push the chart through, land in the span.
      have hw : w = w 0 • EuclideanSpace.single 0 1 + w 1 • EuclideanSpace.single 1 1 := by
        ext i; fin_cases i <;> simp
      rw [hw, map_add, map_smul, map_smul]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl rfl)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl)))
    · rw [Submodule.span_le]
      rintro x hx
      rcases hx with hx | hx <;> subst hx <;>
        [exact ⟨EuclideanSpace.single 0 1, rfl⟩;
         exact ⟨EuclideanSpace.single 1 1, rfl⟩]
  invariance := by
    intro μ w
    refine ⟨reducedCLM μ w, ?_⟩
    have hfd : fderiv ℝ (fun v : EuclideanSpace ℝ (Fin 2) => chartCLM v) w = chartCLM :=
      chartCLM.fderiv
    rw [hfd]
    exact (chart_reduction μ w).symm
  reduction := by
    intro μ w
    have hfd : fderiv ℝ (fun v : EuclideanSpace ℝ (Fin 2) => chartCLM v) w = chartCLM :=
      chartCLM.fderiv
    rw [hfd]
    exact chart_reduction μ w

/-- **Full Hopf-admissibility witness.** The concrete family `J` is Hopf-admissible at `μ₀ = 0`:
every field of `CRNT.hopfAdmissible` is satisfied simultaneously — the eigenvalue-side algebraic
gates (purely-imaginary conjugate pair, positivity, transversality) *and* the center-manifold seed —
so the admissibility verdict is non-vacuous on a real object. -/
noncomputable def admissible : hopfAdmissible J μ₀ where
  r := r
  p := p
  q := q
  r' := 0
  p' := 1
  q' := 0
  hr := hasDerivAt_r
  hp := hasDerivAt_p
  hq := hasDerivAt_q
  hp0 := by simp [p, μ₀]
  hqnn := by simp [q]
  hpos := by simp [r, p, q, μ₀]
  him := by simp [q]
  hg := boundary_velocity_ne_zero
  seed := seed
  seed_μ₀ := rfl

end CRNT.Examples.HopfOscillator3

import CRNT.Multistationarity.ReducedJacobian
import CRNT.Decision.StoichBasisQ

/-!
# Mass-action injectivity through a pivot-row coordinate chart

The reduced-Jacobian injectivity route of `ReducedJacobian`/`SRInjectivityClass` carries the
box Gale–Nikaido theorem to compatibility-class injectivity through the noncomputable basis chart
`stoichChart`/`stoichProj` of `StoichChart`, whose chart is `Module.finBasis`. Its reduced Jacobian
`stoichProj ∘ J ∘ stoichChart` is an oblique Schur-style compression of the full Jacobian, not a
principal submatrix, so the principal-submatrix P-matrix inheritance does not apply to it and the
coordinate-selection identity `reducedJacobian κ x₀ y = (massActionJacobian κ x).submatrix f f` is
unsatisfiable for that chart.

This module replaces the basis chart by a **pivot-row coordinate chart**, the chart that the
rational pivot minor of `CRNT.Decision.StoichBasisQ` realizes. Fix an injective pivot-row selection
`ρ : Fin (stoichRank N) → S` (the rows of a maximal nonsingular minor of the stoichiometric matrix)
and a continuous-linear section `B : (Fin s → ℝ) →L[ℝ] (S → ℝ)` of the stoichiometric subspace with
the pivot-recovery laws

* `pivotSel ρ (B y) = y` — selecting the pivot rows of `B y` recovers the coordinate, and
* `B (pivotSel ρ w) = w` for `w ∈ S(N)` — `B` is a two-sided inverse of the pivot-row selection on
  the subspace,

so `B` is a linear isomorphism of `Fin s → ℝ` onto `S(N)` whose inverse is the pivot-row selection.
The compatibility class is parameterized by the pivot coordinates `x ↦ (x - x₀) ∘ ρ`.

The reduced field on `Fin s → ℝ` is `G y = (F (x₀ + B y)) ∘ ρ`, the mass-action vector field on the
slice read in pivot coordinates. Its derivative is, by the chain rule, the compression
`pivotSel ρ ∘ J(x₀ + B y) ∘ B`, whose `s × s` matrix is the **pivot-reduced Jacobian**
`pivotReducedJacobian`. With that matrix a P-matrix on an enclosing box of pivot coordinates, the box
Gale–Nikaido theorem (`injOn_of_pmatrix_fderiv`) makes `G` injective on the box; pulled back through
the injective affine pivot chart, mass-action kinetics is injective on the class, so the class carries
at most one positive steady state (Craciun–Feinberg monostationarity).

The pivot-reduced Jacobian `pivotSel ρ ∘ J ∘ B` is a genuine compression of the full Jacobian and is
in general not a principal submatrix of it (the inverse-section columns of `B` are not standard basis
vectors), so the point-free full-Jacobian P-matrix verdict of `SRCoverPointIndependence` does not
transport to it by principal-submatrix selection; the P-matrix property of the pivot-reduced Jacobian
is carried here as a hypothesis on the chart, which is the satisfiable replacement for the
unsatisfiable coordinate-selection identity of the basis chart.

For the explicit chart `B = concretePivotChart ρ γ` built from a nonsingular maximal minor of the
rational stoichiometric matrix (the real cast of `chartSectionQ = chartBasisQ · pivotBlockInvQ` of
`CRNT.Decision.StoichBasisQ`, read through `Matrix.mulVecLin`), the section law `hBsec` is **not** an
assumption but a theorem: `concretePivotChart_section` discharges `B (w ∘ ρ) = w` for every
`w ∈ S(N)`, from the rational chart identity `selRow · (B · C⁻¹) = 1` (`chartSectionR_mulVec_pivotSel`)
extended by linearity across the section columns, which span `S(N)`. The consequence
`massActionInjectiveOnClass_of_concretePivotChart` is a concrete, no-section-hypothesis injectivity
verdict whose only remaining input is the pivot-reduced-Jacobian P-matrix property on the box.

That P-matrix property is genuinely a consumer input: the pivot-reduced Jacobian `pivotSel ρ ∘ J ∘ B`
is an oblique compression of the full Jacobian, not a principal submatrix of it, so the decidable
point-free full-Jacobian P-matrix verdict of `SRCoverPointIndependence`/`PointIndepDecidable` does not
transport to it by submatrix selection. A fully structural, `decide`-driven `InjectiveOnClass` verdict
is therefore not available from the point-free certificate alone; the box-membership and reduced
P-matrix hypotheses remain consumer inputs.

This is the species–reaction-graph injectivity route of Craciun and Feinberg ("Multiple equilibria in
complex chemical reaction networks: I. The injectivity property" and "II. The species–reaction
graph"), whose injectivity conclusion feeds the global-univalence theorem of Gale and Nikaido ("The
Jacobian matrix and global univalence of mappings"). The pivot chart is the rational pivot minor of
`CRNT.Decision.StoichBasisQ`.

Depends on:
`CRNT.Multistationarity.ReducedJacobian`, `CRNT.Decision.StoichBasisQ`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Matrix
open CRNT.GaussianRank

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The pivot-row selection -/

/-- **Pivot-row selection as a continuous linear map.** Selecting the entries `ρ i` of a vector,
`v ↦ fun i => v (ρ i)`, the projection of `S → ℝ` onto the pivot coordinates `Fin s → ℝ`. -/
noncomputable def pivotSel {s : ℕ} (ρ : Fin s → S) : (S → ℝ) →L[ℝ] (Fin s → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (ρ i))

omit [DecidableEq S] [Fintype S] in
@[simp] theorem pivotSel_apply {s : ℕ} (ρ : Fin s → S) (v : S → ℝ) (i : Fin s) :
    pivotSel ρ v i = v (ρ i) := by
  simp [pivotSel, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]

/-! ## The affine pivot chart -/

/-- The affine pivot chart of the compatibility class through `x₀`: `y ↦ x₀ + B y`, with `B` a
continuous-linear section of the stoichiometric subspace. -/
noncomputable def pivotAffineChart (x₀ : Concentration S) {s : ℕ}
    (B : (Fin s → ℝ) →L[ℝ] (S → ℝ)) : (Fin s → ℝ) → (S → ℝ) :=
  fun y => x₀ + B y

/-- The pivot coordinate of a concentration relative to `x₀`: the pivot rows of the displacement,
`(x - x₀) ∘ ρ`. -/
noncomputable def pivotChartCoord (_N : Network S) (x₀ : Concentration S) {s : ℕ} (ρ : Fin s → S)
    (x : Concentration S) : Fin s → ℝ :=
  fun i => (x - x₀) (ρ i)

omit [DecidableEq S] in
/-- **The affine pivot chart is `C¹` with derivative `B`.** -/
theorem pivotAffineChart_hasFDerivAt (x₀ : Concentration S) {s : ℕ}
    (B : (Fin s → ℝ) →L[ℝ] (S → ℝ)) (y : Fin s → ℝ) :
    HasFDerivAt (pivotAffineChart x₀ B) B y :=
  (B.hasFDerivAt).const_add x₀

/-- **The affine pivot chart recovers a class point from its pivot coordinate.** If `x` is
stoichiometrically compatible with `x₀` (so `x - x₀ ∈ S(N)`) and `B` is a section recovering subspace
elements from their pivot rows (`hBsec`), then `pivotAffineChart x₀ B (pivotChartCoord x₀ ρ x) = x`. -/
theorem pivotAffineChart_pivotChartCoord (N : Network S) {x₀ x : Concentration S} {s : ℕ}
    (ρ : Fin s → S) (B : (Fin s → ℝ) →L[ℝ] (S → ℝ))
    (hBsec : ∀ w ∈ N.stoichSubspace, B (fun i => w (ρ i)) = w)
    (h : N.StoichCompatible x₀ x) :
    pivotAffineChart x₀ B (N.pivotChartCoord x₀ ρ x) = x := by
  have hB : B (N.pivotChartCoord x₀ ρ x) = x - x₀ := by
    show B (fun i => (x - x₀) (ρ i)) = x - x₀
    exact hBsec _ h
  rw [pivotAffineChart, hB]; abel

/-! ## The pivot-reduced field and its Jacobian -/

/-- The pivot-reduced field on `Fin s → ℝ`: the mass-action vector field on the affine slice through
`x₀`, read in pivot coordinates `G y = (F (x₀ + B y)) ∘ ρ`. -/
noncomputable def pivotReducedField (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    {s : ℕ} (ρ : Fin s → S) (B : (Fin s → ℝ) →L[ℝ] (S → ℝ)) :
    (Fin s → ℝ) → (Fin s → ℝ) :=
  fun y => pivotSel ρ (N.massActionVectorField κ (pivotAffineChart x₀ B y))

/-- The pivot-reduced Jacobian operator at pivot coordinate `y`: the compression
`pivotSel ρ ∘ J(x₀ + B y) ∘ B` of the full mass-action Jacobian. -/
noncomputable def pivotReducedJacobianCLM (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    {s : ℕ} (ρ : Fin s → S) (B : (Fin s → ℝ) →L[ℝ] (S → ℝ)) (y : Fin s → ℝ) :
    (Fin s → ℝ) →L[ℝ] (Fin s → ℝ) :=
  (pivotSel ρ).comp ((N.massActionJacobianCLM κ (pivotAffineChart x₀ B y)).comp B)

/-- The pivot-reduced Jacobian matrix at pivot coordinate `y`: the `s × s` matrix of the compressed
operator `pivotSel ρ ∘ J ∘ B`. -/
noncomputable def pivotReducedJacobian (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    {s : ℕ} (ρ : Fin s → S) (B : (Fin s → ℝ) →L[ℝ] (S → ℝ)) (y : Fin s → ℝ) :
    Matrix (Fin s) (Fin s) ℝ :=
  jacobianMatrix (N.pivotReducedJacobianCLM κ x₀ ρ B y)

/-- **The pivot-reduced field is `C¹`, with the pivot-reduced Jacobian operator as derivative.** By
the chain rule on `pivotSel ρ ∘ F ∘ pivotAffineChart`. -/
theorem pivotReducedField_hasFDerivAt (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    {s : ℕ} (ρ : Fin s → S) (B : (Fin s → ℝ) →L[ℝ] (S → ℝ)) (y : Fin s → ℝ) :
    HasFDerivAt (N.pivotReducedField κ x₀ ρ B) (N.pivotReducedJacobianCLM κ x₀ ρ B y) y := by
  have h1 : HasFDerivAt (pivotAffineChart x₀ B) B y := pivotAffineChart_hasFDerivAt x₀ B y
  have h2 : HasFDerivAt (fun x => N.massActionVectorField κ x)
      (N.massActionJacobianCLM κ (pivotAffineChart x₀ B y)) (pivotAffineChart x₀ B y) :=
    N.massActionVectorField_hasFDerivAt κ (pivotAffineChart x₀ B y)
  have h3 : HasFDerivAt (fun y => N.massActionVectorField κ (pivotAffineChart x₀ B y))
      ((N.massActionJacobianCLM κ (pivotAffineChart x₀ B y)).comp B) y :=
    h2.comp y h1
  exact (pivotSel ρ).hasFDerivAt.comp y h3

/-! ## Mass-action injectivity through the pivot chart -/

/-- **Mass-action injectivity on a class from a P-matrix pivot-reduced Jacobian.** Fix an injective
pivot-row selection `ρ : Fin (stoichRank N) → S` and a continuous-linear section
`B : (Fin s → ℝ) →L[ℝ] (S → ℝ)` of the stoichiometric subspace with the pivot-recovery law `hBsec`
(`B` recovers each subspace element from its pivot rows). Suppose the pivot coordinates of every
point of the positive compatibility class of `x₀` lie in a box `Icc lo hi`, and the pivot-reduced
(`s × s`) Jacobian `pivotSel ρ ∘ J ∘ B` is a P-matrix at every coordinate of that box. Then the box
Gale–Nikaido theorem makes the pivot-reduced field injective on the box; pulled back through the
injective affine pivot chart, mass-action kinetics is injective on the class.

The pivot-reduced Jacobian is a genuine, satisfiable object — the chart-transported compression
`pivotSel ρ ∘ J ∘ B` — so the verdict is non-vacuous, unlike the basis-chart coordinate-selection
identity. This is the Craciun–Feinberg species–reaction-graph injectivity verdict carried through the
Gale–Nikaido box theorem in pivot coordinates. -/
theorem massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix (N : Network S)
    (κ : N.RateConstants) (x₀ : Concentration S) {s : ℕ} (ρ : Fin s → S)
    (B : (Fin s → ℝ) →L[ℝ] (S → ℝ))
    (hBsec : ∀ w ∈ N.stoichSubspace, B (fun i => w (ρ i)) = w)
    {lo hi : Fin s → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.pivotChartCoord x₀ ρ x ∈ Set.Icc lo hi)
    (hpm : ∀ y ∈ Set.Icc lo hi, (N.pivotReducedJacobian κ x₀ ρ B y).IsPMatrix) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ := by
  -- The box Gale–Nikaido theorem makes the pivot-reduced field injective on the box.
  have hGinj : Set.InjOn (N.pivotReducedField κ x₀ ρ B) (Set.Icc lo hi) :=
    injOn_of_pmatrix_fderiv
      (fun y _ => N.pivotReducedField_hasFDerivAt κ x₀ ρ B y)
      (fun y hy => hpm y hy)
  show Set.InjOn (N.massActionVectorField κ) (N.positiveCompatibilityClass x₀)
  intro x hx x' hx' hFxx'
  -- Pivot coordinates of the two class points lie in the box.
  have hyx : N.pivotChartCoord x₀ ρ x ∈ Set.Icc lo hi := hbox x hx
  have hyx' : N.pivotChartCoord x₀ ρ x' ∈ Set.Icc lo hi := hbox x' hx'
  -- The affine pivot chart recovers each point from its coordinate.
  have hax : pivotAffineChart x₀ B (N.pivotChartCoord x₀ ρ x) = x :=
    N.pivotAffineChart_pivotChartCoord ρ B hBsec hx.1
  have hax' : pivotAffineChart x₀ B (N.pivotChartCoord x₀ ρ x') = x' :=
    N.pivotAffineChart_pivotChartCoord ρ B hBsec hx'.1
  -- The pivot-reduced field agrees at the two coordinates.
  have hGeq : N.pivotReducedField κ x₀ ρ B (N.pivotChartCoord x₀ ρ x)
      = N.pivotReducedField κ x₀ ρ B (N.pivotChartCoord x₀ ρ x') := by
    unfold pivotReducedField
    rw [hax, hax', hFxx']
  -- Injectivity of the pivot-reduced field pins the coordinates, hence the points.
  have hyeq : N.pivotChartCoord x₀ ρ x = N.pivotChartCoord x₀ ρ x' := hGinj hyx hyx' hGeq
  calc x = pivotAffineChart x₀ B (N.pivotChartCoord x₀ ρ x) := hax.symm
    _ = pivotAffineChart x₀ B (N.pivotChartCoord x₀ ρ x') := by rw [hyeq]
    _ = x' := hax'

/-- **Monostationarity from a P-matrix pivot-reduced Jacobian.** Under the hypotheses of
`massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix`, the positive compatibility class of
`x₀` carries at most one positive mass-action steady state — the Craciun–Feinberg monostationarity
verdict carried through the pivot chart. -/
theorem subsingleton_steadyState_of_pivotReducedJacobian_pmatrix (N : Network S)
    (κ : N.RateConstants) (x₀ : Concentration S) {s : ℕ} (ρ : Fin s → S)
    (B : (Fin s → ℝ) →L[ℝ] (S → ℝ))
    (hBsec : ∀ w ∈ N.stoichSubspace, B (fun i => w (ρ i)) = w)
    {lo hi : Fin s → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.pivotChartCoord x₀ ρ x ∈ Set.Icc lo hi)
    (hpm : ∀ y ∈ Set.Icc lo hi, (N.pivotReducedJacobian κ x₀ ρ B y).IsPMatrix)
    {x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsMassActionSteadyState κ x) (hsy : N.IsMassActionSteadyState κ y) : x = y :=
  (N.massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix κ x₀ ρ B hBsec hbox hpm).subsingleton_steadyState
    hx hy ((N.isMassActionSteadyState_iff_kinetic κ x).mp hsx)
    ((N.isMassActionSteadyState_iff_kinetic κ y).mp hsy)

/-! ## The concrete pivot chart, with the section identity discharged -/

/-- **The concrete pivot chart `B` as a continuous linear map.** The real section chart
`chartSectionR ρ γ = (B · C⁻¹) ⊗ ℝ` of `CRNT.Decision.StoichBasisQ`, read as a continuous linear map
`(Fin k → ℝ) →L[ℝ] (S → ℝ)` through `Matrix.mulVecLin` (continuous because the spaces are
finite-dimensional). This is the explicit, rational-pivot-minor chart of the stoichiometric subspace;
unlike a generic section it satisfies the pivot-row section law with the pivot-row selection itself,
with no change of coordinates. -/
noncomputable def concretePivotChart (N : Network S) {k : ℕ} (ρ : Fin k → S) (γ : Fin k → N.R) :
    (Fin k → ℝ) →L[ℝ] (S → ℝ) :=
  LinearMap.toContinuousLinearMap (N.chartSectionR ρ γ).mulVecLin

@[simp] theorem concretePivotChart_apply (N : Network S) {k : ℕ} (ρ : Fin k → S) (γ : Fin k → N.R)
    (c : Fin k → ℝ) : N.concretePivotChart ρ γ c = (N.chartSectionR ρ γ).mulVec c := by
  rfl

/-- **The concrete pivot chart discharges the section identity `hBsec`.** For the explicit chart
`concretePivotChart ρ γ` built from a nonsingular maximal minor, the pivot-row section law
`B (w ∘ ρ) = w` holds for every `w` in the stoichiometric subspace — it is exactly the pivot-row
section identity `chartSectionR_mulVec_pivotSel` of the rational chart. The hypothesis `hBsec` of
`massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix` is therefore not an assumption for this
chart but a theorem. -/
theorem concretePivotChart_section (N : Network S)
    (ρ : Fin (computeRank N.stoichMatrixQ) → S) (γ : Fin (computeRank N.stoichMatrixQ) → N.R)
    (hdet : (N.stoichMatrixQ.submatrix ρ γ).det ≠ 0)
    {w : S → ℝ} (hw : w ∈ N.stoichSubspace) :
    N.concretePivotChart ρ γ (fun i => w (ρ i)) = w := by
  rw [concretePivotChart_apply]
  exact N.chartSectionR_mulVec_pivotSel ρ γ hdet hw

/-- **Concrete-chart mass-action injectivity, with no section hypothesis.** Fix a nonsingular maximal
minor of the rational stoichiometric matrix (pivot rows `ρ`, pivot columns `γ`,
`(A.submatrix ρ γ).det ≠ 0`; `CRNT.Decision.StoichBasisQ.exists_pivotSelection` supplies one,
`MinorSearch.findMinorWitness` computably). Build the concrete pivot chart `B = concretePivotChart ρ γ`.
Then the section hypothesis `hBsec` is discharged automatically (`concretePivotChart_section`), and
mass-action kinetics is injective on the positive compatibility class of `x₀` provided only that the
pivot coordinates of the class lie in a box and the pivot-reduced Jacobian `pivotSel ρ ∘ J ∘ B` is a
P-matrix throughout that box.

The chart index is `Fin (computeRank A) = Fin (stoichRank N)` (`stoichRank_eq_computeRank`), the true
dimension of the class. This is the Craciun–Feinberg species–reaction-graph monostationarity verdict
through the explicit rational pivot chart, fed to the Gale–Nikaido box univalence theorem; the only
remaining input is the pivot-reduced-Jacobian P-matrix property on the box, which — the pivot-reduced
Jacobian being an oblique compression `P · J · B` rather than a principal submatrix of `J` — is
genuinely basis-dependent and does not follow from the full Jacobian being a P-matrix. -/
theorem massActionInjectiveOnClass_of_concretePivotChart (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S)
    (ρ : Fin (computeRank N.stoichMatrixQ) → S) (γ : Fin (computeRank N.stoichMatrixQ) → N.R)
    (hdet : (N.stoichMatrixQ.submatrix ρ γ).det ≠ 0)
    {lo hi : Fin (computeRank N.stoichMatrixQ) → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀,
      N.pivotChartCoord x₀ ρ x ∈ Set.Icc lo hi)
    (hpm : ∀ y ∈ Set.Icc lo hi,
      (N.pivotReducedJacobian κ x₀ ρ (N.concretePivotChart ρ γ) y).IsPMatrix) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ := by
  refine N.massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix κ x₀ ρ
    (N.concretePivotChart ρ γ) ?_ (lo := lo) (hi := hi) ?_ ?_
  · intro w hw
    exact N.concretePivotChart_section ρ γ hdet hw
  · intro x hx
    exact hbox x hx
  · intro y hy
    exact hpm y hy

end Network

end CRNT

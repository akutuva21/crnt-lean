import CRNT.Multistationarity.SRCoverPointIndependence

/-!
# Mass-action injectivity from point-free network data through a coordinate-selection chart

The point-independence keystone of `SRCoverPointIndependence` makes the *full* mass-action
Jacobian a P-matrix at every positive concentration from data read off the signed
species–reaction graph alone: the cover-weight nonnegativity `SignCoverWeightNonneg` and the
positive-diagonal-drive condition `PositiveDiagonalDrive`. Neither mentions a concentration, so a
single check of the incidence data discharges the box-quantified P-matrix verdict
(`isPMatrix_massActionJacobian_box_of_pointIndep`).

Carrying that full-Jacobian verdict to injectivity of the mass-action vector field on a
compatibility class needs the *reduced* `s × s` Jacobian (`s = stoichRank N`) to be a P-matrix on
the chart box, because `massActionInjectiveOnClass_of_jacobian_pmatrix` consumes the reduced
Jacobian, not the full one. The reduced Jacobian is in general a Schur-style compression of the
full Jacobian and not a principal submatrix of it, so the two verdicts do not connect for an
arbitrary chart.

They connect exactly when the chart is a **coordinate selection**: a maximal nonsingular minor of
the stoichiometric matrix selects pivot rows `f : Fin s → S`, and on the pivot rows the chart reads
the full Jacobian through the bare coordinate inclusion. For such a chart the reduced Jacobian *is*
the principal submatrix of the full Jacobian on the pivot rows, and a principal submatrix of a
P-matrix is a P-matrix (`Matrix.IsPMatrix.submatrix_isPMatrix`). This is the shape the pivot chart
`chartBasisQ`/`chartProjQ` of `CRNT.Decision.StoichBasisQ` realizes: its projection `P =
C⁻¹ · selRow` selects the pivot rows `ρ`, so the chart-transported reduced matrix on the pivot rows
is the principal submatrix of the Jacobian.

This module chains the three steps with the *coordinate-selection* identity carried as a hypothesis
(the chart-is-coordinate-selection property of a maximal pivot minor), so no per-point and no
per-chart-cover assumption enters:

* `reducedJacobian_isPMatrix_box_of_pointIndep` — on a box of chart coordinates whose chart points
  are positive and over which the reduced Jacobian equals the principal submatrix on a fixed
  pivot-row selection, the point-free conditions make the reduced Jacobian a P-matrix at every box
  coordinate.
* `massActionInjectiveOnClass_of_pointIndep` — chaining the box P-matrix verdict through the box
  Gale–Nikaido univalence theorem, mass-action kinetics is injective on the positive compatibility
  class. The only network-specific inputs are the coordinate-selection identity of the chart, the
  box covering the class, and the two point-free signed-incidence conditions — no per-point or
  per-chart-cover hypothesis.
* `subsingleton_steadyState_of_pointIndep` — equivalently, the class carries at most one positive
  mass-action steady state (Craciun–Feinberg monostationarity).

This is the species–reaction-graph injectivity route of Craciun and Feinberg ("Multiple equilibria
in complex chemical reaction networks: I. The injectivity property" and "II. The species–reaction
graph"), whose injectivity conclusion feeds the global-univalence theorem of Gale and Nikaido ("The
Jacobian matrix and global univalence of mappings"). The coordinate-selection chart is the rational
pivot minor of `CRNT.Decision.StoichBasisQ`.

Depends on:
`CRNT.Multistationarity.SRCoverPointIndependence`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The reduced Jacobian is a P-matrix over the box from point-free data -/

/-- **On a coordinate-selection chart the reduced Jacobian is a P-matrix over the box from
point-free data.** Fix a pivot-row selection `f : Fin (stoichRank N) → S` (the rows of a maximal
nonsingular minor of the stoichiometric matrix, injective) and suppose that over a box of chart
coordinates the reduced Jacobian equals the principal submatrix of the full Jacobian on those pivot
rows (`hsub`). If the chart points of the box are positive (`hpos`), the point-free
signed-incidence weight `SignCoverWeightNonneg` and the diagonal-drive condition
`PositiveDiagonalDrive` make the *full* mass-action Jacobian a P-matrix at every chart point
(`isPMatrix_massActionJacobian_box_of_pointIndep`), and a principal submatrix of a P-matrix is a
P-matrix (`Matrix.IsPMatrix.submatrix_isPMatrix`), so the reduced Jacobian is a P-matrix at every
box coordinate. No per-point and no per-chart-cover hypothesis enters: the verdict is read off the
signed species–reaction graph once. -/
theorem reducedJacobian_isPMatrix_box_of_pointIndep (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    {f : Fin N.stoichRank → S} (hf : Function.Injective f)
    (hpos : ∀ y ∈ Set.Icc lo hi, Concentration.Positive (N.affineChart x₀ y))
    (hsub : ∀ y ∈ Set.Icc lo hi, N.reducedJacobian κ x₀ y
      = (N.massActionJacobian κ (N.affineChart x₀ y)).submatrix f f)
    (hweight : N.SignCoverWeightNonneg) (hdrive : N.PositiveDiagonalDrive) :
    ∀ y ∈ Set.Icc lo hi, (N.reducedJacobian κ x₀ y).IsPMatrix := by
  intro y hy
  -- The point-free conditions make the full Jacobian a P-matrix at this chart point.
  have hP : (N.massActionJacobian κ (N.affineChart x₀ y)).IsPMatrix :=
    N.isPMatrix_massActionJacobian_of_pointIndep κ (hpos y hy) hweight hdrive
  -- The reduced Jacobian is the principal submatrix on the pivot rows, hence a P-matrix.
  exact N.reducedJacobian_isPMatrix_of_submatrix κ x₀ y hf hP (hsub y hy)

/-! ## Mass-action injectivity from point-free network data -/

/-- **Mass-action injectivity on a class from point-free network data through a coordinate-selection
chart.** Suppose the chart coordinates of every point of the positive compatibility class of `x₀`
lie in a box `Icc lo hi`, the chart points of the box are positive, and over the box the reduced
Jacobian equals the principal submatrix of the full Jacobian on a fixed injective pivot-row
selection `f`. Then the point-free signed-incidence weight `SignCoverWeightNonneg` and the
diagonal-drive condition `PositiveDiagonalDrive` make the reduced Jacobian a P-matrix at every box
coordinate, the box Gale–Nikaido theorem makes the reduced field injective on the box, and pulled
back through the injective affine chart mass-action kinetics is injective on the class. This is the
sound general injectivity verdict from point-free network data: the only network-specific inputs are
the coordinate-selection identity of the chart, the box covering the class, and the two point-free
conditions — no per-point or per-chart-cover assumption. -/
theorem massActionInjectiveOnClass_of_pointIndep (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    {f : Fin N.stoichRank → S} (hf : Function.Injective f)
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hpos : ∀ y ∈ Set.Icc lo hi, Concentration.Positive (N.affineChart x₀ y))
    (hsub : ∀ y ∈ Set.Icc lo hi, N.reducedJacobian κ x₀ y
      = (N.massActionJacobian κ (N.affineChart x₀ y)).submatrix f f)
    (hweight : N.SignCoverWeightNonneg) (hdrive : N.PositiveDiagonalDrive) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ :=
  N.massActionInjectiveOnClass_of_jacobian_pmatrix κ x₀ hbox
    (N.reducedJacobian_isPMatrix_box_of_pointIndep κ x₀ hf hpos hsub hweight hdrive)

/-- **Monostationarity from point-free network data through a coordinate-selection chart.** Under
the hypotheses of `massActionInjectiveOnClass_of_pointIndep`, the positive compatibility class of
`x₀` carries at most one positive mass-action steady state — the point-free signed-incidence data,
checked once, certifies Craciun–Feinberg monostationarity. -/
theorem subsingleton_steadyState_of_pointIndep (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    {f : Fin N.stoichRank → S} (hf : Function.Injective f)
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hpos : ∀ y ∈ Set.Icc lo hi, Concentration.Positive (N.affineChart x₀ y))
    (hsub : ∀ y ∈ Set.Icc lo hi, N.reducedJacobian κ x₀ y
      = (N.massActionJacobian κ (N.affineChart x₀ y)).submatrix f f)
    (hweight : N.SignCoverWeightNonneg) (hdrive : N.PositiveDiagonalDrive)
    {x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsMassActionSteadyState κ x) (hsy : N.IsMassActionSteadyState κ y) : x = y :=
  N.subsingleton_steadyState_of_jacobian_pmatrix κ x₀ hbox
    (N.reducedJacobian_isPMatrix_box_of_pointIndep κ x₀ hf hpos hsub hweight hdrive)
    hx hy hsx hsy

end Network

end CRNT

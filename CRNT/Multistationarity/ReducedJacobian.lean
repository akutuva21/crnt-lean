import CRNT.Multistationarity.StoichChart
import CRNT.Multistationarity.GaleNikaidoUniv
import CRNT.Kinetics.MassActionJacobian

/-!
# The reduced Jacobian and mass-action injectivity from a P-matrix reduced Jacobian

Coordinate reduction binds the box Gale–Nikaido theorem to chemical-reaction-network
class-injectivity. The mass-action vector field `F` confined to the affine slice `x₀ + S(N)` is
pushed through the linear chart of `StoichChart` to a full-dimensional reduced field on `Fin s → ℝ`
(`s = stoichRank N`):

```
G y = stoichProj (F (affineChart x₀ y)) = stoichProj (F (x₀ + stoichChart y)).
```

The chain rule (`reducedField_hasFDerivAt`) gives `G' y = stoichProj ∘ J(x₀ + stoichChart y) ∘
stoichChart`, whose `s × s` matrix is the **reduced Jacobian** `reducedJacobian`. With the reduced
Jacobian a P-matrix on an enclosing box covering the chart coordinates of the positive compatibility
class, the box Gale–Nikaido theorem (`injOn_of_pmatrix_fderiv`) makes `G` injective on the box; pulled
back through the injective affine chart, the mass-action vector field is injective on the class, so
the class carries at most one positive steady state (Craciun–Feinberg monostationarity).

This module is **stable** and `sorry`-free. Depends on: `CRNT.Multistationarity.StoichChart`,
`CRNT.Multistationarity.GaleNikaidoUniv`, `CRNT.Kinetics.MassActionJacobian`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Matrix
open Module

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The reduced field on `Fin s → ℝ`: the mass-action vector field on the affine slice through `x₀`,
read in chart coordinates. -/
noncomputable def reducedField (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) :
    (Fin N.stoichRank → ℝ) → (Fin N.stoichRank → ℝ) :=
  fun y => N.stoichProj (N.massActionVectorField κ (N.affineChart x₀ y))

/-- The reduced Jacobian operator at chart coordinate `y`: the compression
`stoichProj ∘ J(x₀ + stoichChart y) ∘ stoichChart` of the full mass-action Jacobian. -/
noncomputable def reducedJacobianCLM (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) : (Fin N.stoichRank → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ) :=
  N.stoichProj.comp ((N.massActionJacobianCLM κ (N.affineChart x₀ y)).comp N.stoichChart)

/-- The reduced Jacobian matrix at chart coordinate `y`: the `s × s` matrix of the compressed
operator `stoichProj ∘ J ∘ stoichChart`. -/
noncomputable def reducedJacobian (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) : Matrix (Fin N.stoichRank) (Fin N.stoichRank) ℝ :=
  jacobianMatrix (N.reducedJacobianCLM κ x₀ y)

/-- **The affine chart is `C¹` with derivative `stoichChart`.** -/
theorem affineChart_hasFDerivAt (N : Network S) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) :
    HasFDerivAt (N.affineChart x₀) N.stoichChart y :=
  (N.stoichChart.hasFDerivAt).const_add x₀

/-- **The reduced field is `C¹`, with the reduced Jacobian operator as derivative.** By the chain
rule on `stoichProj ∘ F ∘ affineChart`. -/
theorem reducedField_hasFDerivAt (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) :
    HasFDerivAt (N.reducedField κ x₀) (N.reducedJacobianCLM κ x₀ y) y := by
  have h1 : HasFDerivAt (N.affineChart x₀) N.stoichChart y := N.affineChart_hasFDerivAt x₀ y
  have h2 : HasFDerivAt (fun x => N.massActionVectorField κ x)
      (N.massActionJacobianCLM κ (N.affineChart x₀ y)) (N.affineChart x₀ y) :=
    N.massActionVectorField_hasFDerivAt κ (N.affineChart x₀ y)
  have h3 : HasFDerivAt (fun y => N.massActionVectorField κ (N.affineChart x₀ y))
      ((N.massActionJacobianCLM κ (N.affineChart x₀ y)).comp N.stoichChart) y :=
    h2.comp y h1
  exact N.stoichProj.hasFDerivAt.comp y h3

/-- **The reduced Jacobian matrix is the matrix of the reduced field's derivative.** -/
theorem jacobianMatrix_reducedField (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) :
    jacobianMatrix (N.reducedJacobianCLM κ x₀ y) = N.reducedJacobian κ x₀ y :=
  rfl

/-- **Mass-action injectivity from a P-matrix reduced Jacobian on a class.** Suppose the chart
coordinates of every point of the positive compatibility class of `x₀` lie in a box `Icc lo hi`, and
that the reduced (`s × s`) Jacobian is a P-matrix at every coordinate of that box. Then the box
Gale–Nikaido theorem makes the reduced field injective on the box; pulled back through the injective
affine chart, mass-action kinetics is injective on the class. -/
theorem massActionInjectiveOnClass_of_jacobian_pmatrix (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hpm : ∀ y ∈ Set.Icc lo hi, (N.reducedJacobian κ x₀ y).IsPMatrix) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ := by
  -- The box Gale–Nikaido theorem makes the reduced field injective on the box.
  have hGinj : Set.InjOn (N.reducedField κ x₀) (Set.Icc lo hi) :=
    injOn_of_pmatrix_fderiv
      (fun y _ => N.reducedField_hasFDerivAt κ x₀ y)
      (fun y hy => hpm y hy)
  show Set.InjOn (N.massActionVectorField κ) (N.positiveCompatibilityClass x₀)
  intro x hx x' hx' hFxx'
  -- Chart coordinates of the two class points lie in the box.
  have hyx : N.chartCoord x₀ x ∈ Set.Icc lo hi := hbox x hx
  have hyx' : N.chartCoord x₀ x' ∈ Set.Icc lo hi := hbox x' hx'
  -- The affine chart recovers each point from its coordinate.
  have hax : N.affineChart x₀ (N.chartCoord x₀ x) = x := N.affineChart_chartCoord hx.1
  have hax' : N.affineChart x₀ (N.chartCoord x₀ x') = x' := N.affineChart_chartCoord hx'.1
  -- The reduced field agrees at the two coordinates.
  have hGeq : N.reducedField κ x₀ (N.chartCoord x₀ x)
      = N.reducedField κ x₀ (N.chartCoord x₀ x') := by
    simp only [reducedField, hax, hax', hFxx']
  -- Injectivity of the reduced field pins the coordinates, hence the points.
  have hyeq : N.chartCoord x₀ x = N.chartCoord x₀ x' := hGinj hyx hyx' hGeq
  calc x = N.affineChart x₀ (N.chartCoord x₀ x) := hax.symm
    _ = N.affineChart x₀ (N.chartCoord x₀ x') := by rw [hyeq]
    _ = x' := hax'

/-- **Monostationarity from a P-matrix reduced Jacobian.** Under the hypotheses of
`massActionInjectiveOnClass_of_jacobian_pmatrix`, the positive compatibility class of `x₀` carries at
most one positive mass-action steady state. -/
theorem subsingleton_steadyState_of_jacobian_pmatrix (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hpm : ∀ y ∈ Set.Icc lo hi, (N.reducedJacobian κ x₀ y).IsPMatrix)
    {x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsMassActionSteadyState κ x) (hsy : N.IsMassActionSteadyState κ y) : x = y :=
  (N.massActionInjectiveOnClass_of_jacobian_pmatrix κ x₀ hbox hpm).subsingleton_steadyState
    hx hy ((N.isMassActionSteadyState_iff_kinetic κ x).mp hsx)
    ((N.isMassActionSteadyState_iff_kinetic κ y).mp hsy)

end Network

end CRNT

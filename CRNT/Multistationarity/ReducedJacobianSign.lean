import CRNT.Multistationarity.SRCycleInjectivity
import CRNT.LinearAlgebra.CauchyBinet

/-!
# The reduced Jacobian as an oblique compression of the full mass-action Jacobian

For a general stoichiometric chart the reduced (`s × s`) Jacobian
`stoichProj ∘ J(x₀ + stoichChart y) ∘ stoichChart` is a Schur-style oblique compression of the
full mass-action Jacobian, not a principal submatrix. This module supplies the matrix-level
foundation for analysing that compression's principal minors with the Cauchy–Binet formula.

Writing the chart and its dual projection as matrices `B = stoichChartMatrix` (`S × Fin s`) and
`P = stoichProjMatrix` (`Fin s × S`), the duality `stoichProj ∘ stoichChart = id` becomes the
matrix identity `P · B = 1` (`stoichProjMatrix_mul_stoichChartMatrix`), and the reduced Jacobian
is the matrix product

```
reducedJacobian κ x₀ y = P · M · B,   M = massActionJacobian κ (affineChart x₀ y)
```

(`reducedJacobian_eq_mul`). A principal minor of `P · M · B` over an index subset therefore splits
as `(P · M · B).submatrix incl incl = (P.submatrix incl id) · M · (B.submatrix id incl)`, on which
the Cauchy–Binet formula (`Matrix.det_mul_eq_sum_powersetCard`) expands the minor into a sum over
species subsets of products of minors of `P`, `M`, and `B`.

This is the matrix scaffolding for the general-chart species–reaction graph injectivity verdict of
Craciun and Feinberg ("Multiple equilibria in complex chemical reaction networks: I. The injectivity
property" and "II. The species–reaction graph"), which feeds the global-univalence theorem of Gale
and Nikaido ("The Jacobian matrix and global univalence of mappings"); the determinant expansion
rests on the formula of Augustin-Louis Cauchy and Jacques Philippe Marie Binet.

* `stoichChartMatrix`, `stoichProjMatrix` — the chart and dual-projection matrices `B`, `P`.
* `stoichProjMatrix_mul_stoichChartMatrix` — the duality `P · B = 1`.
* `toMatrix'_massActionJacobianCLM` — the mass-action Jacobian matrix is the standard matrix of the
  Jacobian operator.
* `reducedJacobian_eq_mul` — the reduced Jacobian is the oblique compression `P · M · B`.

Turning this product form into the P-matrix verdict for a general chart — replacing the
coordinate-selection hypothesis `hsub` of `massActionInjectiveOnClass_of_consistentSRSign` — needs
the principal minors of `P · M · B` to be positive. Their Cauchy–Binet expansion pairs a minor of
the sign-definite Jacobian `M` (controlled by the signed SR-cover condition through
`coverProductSingle_eq_magnitude_mul_sign`) with minors of `P` and `B`, whose signs the signed
SR-cover condition does not by itself govern; establishing the cancellation that makes each
principal minor positive is the remaining step and is not developed here.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Multistationarity.SRCycleInjectivity`, `CRNT.LinearAlgebra.CauchyBinet`.
-/

namespace CRNT

namespace Network

open scoped Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The matrix of the chart `stoichChart : (Fin s → ℝ) → (S → ℝ)`, an `S × Fin s` matrix `B`
with columns the chosen stoichiometric basis vectors. -/
noncomputable def stoichChartMatrix (N : Network S) :
    Matrix S (Fin N.stoichRank) ℝ :=
  LinearMap.toMatrix' N.stoichChartLM

/-- The matrix of the projection `stoichProj : (S → ℝ) → (Fin s → ℝ)`, a `Fin s × S` matrix `P`. -/
noncomputable def stoichProjMatrix (N : Network S) :
    Matrix (Fin N.stoichRank) S ℝ :=
  LinearMap.toMatrix' N.stoichProjLM

/-- **The projection-times-chart matrix is the identity.** `P · B = 1`. -/
theorem stoichProjMatrix_mul_stoichChartMatrix (N : Network S) :
    N.stoichProjMatrix * N.stoichChartMatrix = 1 := by
  rw [stoichProjMatrix, stoichChartMatrix, ← LinearMap.toMatrix'_comp]
  have : N.stoichProjLM ∘ₗ N.stoichChartLM = LinearMap.id :=
    LinearMap.ext fun y => N.stoichProjLM_stoichChartLM y
  rw [this, LinearMap.toMatrix'_id]

/-- **The mass-action Jacobian matrix is the matrix of the Jacobian operator.** -/
theorem toMatrix'_massActionJacobianCLM (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) :
    LinearMap.toMatrix' (N.massActionJacobianCLM κ x : (S → ℝ) →ₗ[ℝ] (S → ℝ))
      = N.massActionJacobian κ x := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply]
  exact N.massActionJacobianCLM_apply κ x v

/-- **The reduced Jacobian is the oblique compression `P · M · B`.** With `M` the full mass-action
Jacobian, `B = stoichChartMatrix`, `P = stoichProjMatrix`, the reduced (`s × s`) Jacobian equals
the matrix product `P · M · B`. -/
theorem reducedJacobian_eq_mul (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) :
    N.reducedJacobian κ x₀ y
      = N.stoichProjMatrix * N.massActionJacobian κ (N.affineChart x₀ y)
          * N.stoichChartMatrix := by
  rw [reducedJacobian, jacobianMatrix, reducedJacobianCLM]
  show LinearMap.toMatrix'
      (N.stoichProjLM ∘ₗ ((N.massActionJacobianCLM κ (N.affineChart x₀ y) :
        (S → ℝ) →ₗ[ℝ] (S → ℝ)) ∘ₗ N.stoichChartLM)) = _
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
    toMatrix'_massActionJacobianCLM, ← stoichProjMatrix, ← stoichChartMatrix, Matrix.mul_assoc]

end Network

end CRNT

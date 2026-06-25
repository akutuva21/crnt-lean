import CRNT.Multistationarity.PMatrix
import CRNT.Multistationarity.JacobianInjectivity
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Gale–Nikaido: P-matrix Jacobian ⇒ injectivity (foundational rungs)

The degree-free route to the Gale–Nikaido theorem (a `C¹` map whose Jacobian is a P-matrix
everywhere is injective). This module establishes the two foundational rungs:

* `isLocalHomeomorph_of_pmatrix_fderiv` — a map with an everywhere-strict derivative whose Jacobian
  matrix is a P-matrix at every point is a **local homeomorphism**. A P-matrix has nonzero
  determinant (`IsPMatrix.det_ne_zero`), so each derivative is an invertible continuous linear map,
  and the inverse function theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`) makes `f` a local
  homeomorphism at every point. This is the local (inverse-function) half of injectivity and is
  independently useful.
* `injOn_of_pmatrix_fderiv_dim_one` — the **one-dimensional base case** of the inductive Gale–Nikaido
  theorem: a differentiable map on a one-dimensional box with a P-matrix Jacobian is injective. A
  `1 × 1` P-matrix is a positive scalar (`IsPMatrix.diag_pos`), so the quadratic form is positive
  definite and the existing positive-definite injectivity result applies.

The `jacobianMatrix` helper converts a continuous linear self-map of `ι → ℝ` to its standard matrix,
with `jacobianMatrix_mulVec` and `jacobianMatrix_det` relating it back to the map.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Multistationarity.PMatrix`,
`CRNT.Multistationarity.JacobianInjectivity`, Mathlib finite-dimensional and inverse-function theory.
-/

namespace CRNT

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard matrix of a continuous linear self-map of `ι → ℝ` — the Jacobian matrix of a
derivative `f' x`. -/
noncomputable def jacobianMatrix (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) : Matrix ι ι ℝ :=
  LinearMap.toMatrix' (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

/-- The Jacobian matrix acts as the map: `jacobianMatrix L *ᵥ v = L v`. -/
theorem jacobianMatrix_mulVec (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) (v : ι → ℝ) :
    (jacobianMatrix L) *ᵥ v = L v := by
  rw [jacobianMatrix, LinearMap.toMatrix'_mulVec]
  rfl

/-- The determinant of the Jacobian matrix is the determinant of the map. -/
theorem jacobianMatrix_det (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    (jacobianMatrix L).det = L.det := by
  rw [jacobianMatrix, LinearMap.det_toMatrix']

/-! ### Rung 1: local homeomorphism from a P-matrix Jacobian -/

/-- **Local injectivity from a P-matrix Jacobian.** A map with an everywhere-strict derivative whose
Jacobian matrix is a P-matrix at every point is a local homeomorphism: each derivative is invertible
(a P-matrix has nonzero determinant), so the inverse function theorem applies pointwise. -/
theorem isLocalHomeomorph_of_pmatrix_fderiv {n : ℕ}
    {f : (Fin n → ℝ) → (Fin n → ℝ)} {f' : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))}
    (hf : ∀ x, HasStrictFDerivAt f (f' x) x)
    (hP : ∀ x, (jacobianMatrix (f' x)).IsPMatrix) : IsLocalHomeomorph f := by
  intro x
  have hdet : (f' x).det ≠ 0 := by
    rw [← jacobianMatrix_det]
    exact (hP x).det_ne_zero
  set cle := (f' x).toContinuousLinearEquivOfDetNeZero hdet with hcle
  have hcoe : (cle : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = f' x :=
    (f' x).coe_toContinuousLinearEquivOfDetNeZero hdet
  have hf' : HasStrictFDerivAt f (cle : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x := by
    rw [hcoe]; exact hf x
  exact ⟨hf'.toOpenPartialHomeomorph f, hf'.mem_toOpenPartialHomeomorph_source,
    (hf'.toOpenPartialHomeomorph_coe).symm⟩

/-! ### Rung 2: the one-dimensional base case -/

/-- **The one-dimensional Gale–Nikaido base case.** A differentiable map on a one-dimensional box
whose Jacobian is a P-matrix is injective there. A `1 × 1` P-matrix is a positive scalar, so the
quadratic form `v ↦ ∑ i, vᵢ (f' x v)ᵢ` is strictly positive, and the positive-definite injectivity
result applies. -/
theorem injOn_of_pmatrix_fderiv_dim_one
    {f : (Fin 1 → ℝ) → (Fin 1 → ℝ)} {f' : (Fin 1 → ℝ) → ((Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ))}
    {a b : Fin 1 → ℝ} (hf : ∀ x ∈ Set.Icc a b, HasFDerivAt f (f' x) x)
    (hP : ∀ x ∈ Set.Icc a b, (jacobianMatrix (f' x)).IsPMatrix) :
    Set.InjOn f (Set.Icc a b) := by
  refine injOn_of_hasFDerivAt_dotProduct_pos (convex_Icc a b) hf ?_
  intro x hx v hv
  have hM : 0 < (jacobianMatrix (f' x)) 0 0 := (hP x hx).diag_pos 0
  have hv0 : v 0 ≠ 0 := by
    intro h0
    exact hv (funext fun i => by fin_cases i; simpa using h0)
  have happ : (f' x v) 0 = (jacobianMatrix (f' x)) 0 0 * v 0 := by
    have hfun := jacobianMatrix_mulVec (f' x) v
    have h0 : ((jacobianMatrix (f' x)) *ᵥ v) 0 = (jacobianMatrix (f' x)) 0 0 * v 0 := by
      show (∑ j, (jacobianMatrix (f' x)) 0 j * v j) = _
      rw [Fin.sum_univ_one]
    rw [← congrFun hfun 0, h0]
  rw [Fin.sum_univ_one, happ]
  have hrw : v 0 * ((jacobianMatrix (f' x)) 0 0 * v 0)
      = (jacobianMatrix (f' x)) 0 0 * (v 0 * v 0) := by ring
  rw [hrw]
  exact mul_pos hM (mul_self_pos.mpr hv0)

end CRNT

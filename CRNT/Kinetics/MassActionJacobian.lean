import CRNT.Kinetics.MassAction
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Differentiability of the mass-action vector field

The mass-action vector field `x ↦ ∑ r, κ r · (∏ s, x_s ^ source_r s) · reactionVector r` is a
polynomial map of the concentrations, hence differentiable everywhere on `Concentration S = S → ℝ`
(no positivity needed). This module establishes that smoothness from the bottom up: the source
monomial, the per-reaction rate, and the assembled vector field are each `Differentiable ℝ`. It is
the analytic foundation for the mass-action Jacobian used in the Craciun–Feinberg injectivity theory.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Kinetics.MassAction`, Mathlib
`Analysis.Calculus.FDeriv`.
-/

namespace CRNT

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The mass-action monomial `x ↦ ∏ s, x_s ^ (y_s)` of a complex `y` is differentiable: a finite
product of coordinate powers. -/
theorem massActionMonomial_differentiable (y : Complex S) :
    Differentiable ℝ (fun x : Concentration S => y.massActionMonomial x) := by
  intro x
  simp only [Complex.massActionMonomial]
  exact (HasFDerivAt.finsetProd fun s _ =>
    ((differentiable_apply s).pow (y s)).differentiableAt.hasFDerivAt).differentiableAt

/-- The `j`-th partial derivative of the source monomial `∏ s, x_s ^ (y_s)`, in the polynomial form
`y_j · x_j ^ (y_j - 1) · ∏_{s ≠ j} x_s ^ (y_s)` valid at every point. -/
def massActionMonomialGrad (y : Complex S) (x : Concentration S) (j : S) : ℝ :=
  (y j : ℝ) * x j ^ (y j - 1) * ∏ s ∈ Finset.univ.erase j, x s ^ (y s)

/-- The Fréchet derivative of the source monomial is the dot product with its gradient:
`∑ j, (∂_j monomial) • proj_j`. -/
theorem massActionMonomial_hasFDerivAt (y : Complex S) (x : Concentration S) :
    HasFDerivAt (fun x : Concentration S => y.massActionMonomial x)
      (∑ j, massActionMonomialGrad y x j •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) j) x := by
  have hfac : ∀ s : S, HasFDerivAt (fun x : Concentration S => x s ^ (y s))
      ((y s • x s ^ (y s - 1)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s) x :=
    fun s => (hasFDerivAt_apply s x).pow (y s)
  have h := HasFDerivAt.finsetProd (u := (Finset.univ : Finset S)) (fun s _ => hfac s)
  simp only [Complex.massActionMonomial]
  refine h.congr_fderiv (Finset.sum_congr rfl fun s _ => ?_)
  rw [massActionMonomialGrad, smul_smul, nsmul_eq_mul]
  congr 1
  ring

namespace Network

/-- The mass-action rate of a reaction, `x ↦ κ r · monomial`, is differentiable. -/
theorem massActionRate_differentiable (N : Network S) (κ : N.RateConstants) (r : N.R) :
    Differentiable ℝ (fun x : Concentration S => N.massActionRate κ r x) := by
  simp only [Network.massActionRate]
  exact (massActionMonomial_differentiable _).const_mul (κ.k r)

/-- The mass-action vector field is differentiable everywhere: each component is a finite sum of
rates scaled by reaction-vector entries. -/
theorem massActionVectorField_differentiable (N : Network S) (κ : N.RateConstants) :
    Differentiable ℝ (fun x : Concentration S => N.massActionVectorField κ x) := by
  apply differentiable_pi''
  intro s
  simp only [Network.massActionVectorField]
  exact Differentiable.fun_sum fun r _ => (N.massActionRate_differentiable κ r).mul_const _

/-- The mass-action Jacobian as a continuous linear operator at `x`: the Fréchet derivative of the
vector field, in outer-product form `v ↦ ∑ r, κ_r · (∇monomial_r · v) · reactionVector r`. -/
noncomputable def massActionJacobianCLM (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : Concentration S →L[ℝ] Concentration S :=
  ∑ r : N.R, (κ.k r • (∑ j, massActionMonomialGrad (N.reaction r).source x j •
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) j)).smulRight (N.reactionVector r)

/-- **The mass-action Jacobian is the Fréchet derivative of the vector field.** Differentiating
`∑ r, κ_r · monomial_r · reactionVector r` term by term, each reaction contributes the rank-one
operator `(κ_r · ∇monomial_r) ⊗ reactionVector r`. -/
theorem massActionVectorField_hasFDerivAt (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) :
    HasFDerivAt (fun x => N.massActionVectorField κ x) (N.massActionJacobianCLM κ x) x := by
  have hfun : (fun x : Concentration S => N.massActionVectorField κ x)
      = ∑ r : N.R, (fun x => N.massActionRate κ r x • N.reactionVector r) := by
    funext x s
    simp only [Network.massActionVectorField, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hr : ∀ r : N.R,
      HasFDerivAt (fun x : Concentration S => N.massActionRate κ r x • N.reactionVector r)
        ((κ.k r • (∑ j, massActionMonomialGrad (N.reaction r).source x j •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) j)).smulRight
            (N.reactionVector r)) x := by
    intro r
    simp only [Network.massActionRate]
    exact ((massActionMonomial_hasFDerivAt (N.reaction r).source x).const_mul (κ.k r)).smul_const
      (N.reactionVector r)
  rw [hfun]
  exact HasFDerivAt.sum fun r _ => hr r

end Network

end CRNT

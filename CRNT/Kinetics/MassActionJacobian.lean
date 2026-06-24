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

end Network

end CRNT

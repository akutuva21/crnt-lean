import CRNT.Kinetics.MassAction
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Regularity and invariance of the mass-action vector field

The analytic prerequisites a mass-action ODE `ẋ = f(x)` must satisfy before any
existence/uniqueness theory (Picard–Lindelöf, integral curves) applies, and before the
nonnegative orthant can be shown forward-invariant:

* `massActionVectorField_contDiff`: `f` is `C^∞` — it is a polynomial map. This is the
  regularity hypothesis of the local existence/uniqueness theorems.
* `massActionVectorField_nonneg_of_zero`: at a nonnegative concentration with `x_s = 0`,
  the `s`-component of `f` is `≥ 0`. Geometrically the boundary face `{x_s = 0}` is
  non-attracting: every reaction that would decrease `x_s` consumes `x_s` (so its rate
  carries a positive power of `x_s`, which vanishes on the face). This is the algebraic
  core of forward-invariance of the positive orthant.

These are the CRN-specific inputs to a future construction of the mass-action forward
semiflow; the general ODE machinery (global existence from a priori bounds, continuous
dependence on initial conditions, packaging as a `Flow`) is separate.

This module is **stable** and `sorry`-free.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The mass-action vector field is `C^∞`.** It is a polynomial map of the concentration
vector, hence smooth — the regularity hypothesis required by the Picard–Lindelöf and
integral-curve existence theory. -/
theorem massActionVectorField_contDiff (N : Network S) (κ : RateConstants N)
    {n : WithTop ℕ∞} : ContDiff ℝ n (N.massActionVectorField κ) := by
  rw [contDiff_pi]
  intro s
  simp only [massActionVectorField_apply]
  refine ContDiff.sum fun r _ => ContDiff.mul ?_ contDiff_const
  show ContDiff ℝ n fun x : Concentration S => κ.k r * (N.reaction r).source.massActionMonomial x
  refine contDiff_const.mul ?_
  show ContDiff ℝ n fun x : Concentration S => ∏ s', x s' ^ (N.reaction r).source s'
  exact contDiff_prod fun s' _ => (contDiff_apply ℝ ℝ s').pow _

/-- **The nonnegative orthant is non-attracting on its boundary faces.** At a nonnegative
concentration with `x_s = 0`, the `s`-component of the vector field is nonnegative — the
algebraic heart of forward-invariance of the orthant. -/
theorem massActionVectorField_nonneg_of_zero (N : Network S) (κ : RateConstants N)
    {x : Concentration S} (hx : x.Nonnegative) {s : S} (hs : x s = 0) :
    0 ≤ N.massActionVectorField κ x s := by
  rw [massActionVectorField_apply]
  refine Finset.sum_nonneg fun r _ => ?_
  by_cases hle : (N.reaction r).source s ≤ (N.reaction r).target s
  · -- the reaction does not consume `s`, so its reaction-vector entry is `≥ 0`
    refine mul_nonneg (N.massActionRate_nonneg κ r hx) ?_
    rw [reactionVector_apply]
    have : ((N.reaction r).source s : ℝ) ≤ ((N.reaction r).target s : ℝ) := by exact_mod_cast hle
    linarith
  · -- the reaction consumes `s`, so its monomial carries the vanishing factor `x_s`
    have hsrc : (N.reaction r).source s ≠ 0 := by omega
    have hmon : (N.reaction r).source.massActionMonomial x = 0 := by
      show (∏ s', x s' ^ (N.reaction r).source s') = 0
      exact Finset.prod_eq_zero (Finset.mem_univ s) (by rw [hs, zero_pow hsrc])
    have hrate : N.massActionRate κ r x = 0 := by
      show κ.k r * (N.reaction r).source.massActionMonomial x = 0
      rw [hmon, mul_zero]
    rw [hrate, zero_mul]

/-- **Local existence of mass-action solutions.** From every starting concentration there
is a solution of `ẋ = f(x)` on an open time interval (Picard–Lindelöf, via the smoothness
of `f`). -/
theorem exists_local_solution (N : Network S) (κ : RateConstants N) (x₀ : Concentration S)
    (t₀ : ℝ) :
    ∃ γ : ℝ → Concentration S, γ t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), HasDerivAt γ (N.massActionVectorField κ (γ t)) t :=
  (massActionVectorField_contDiff N κ).contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

end Network

end CRNT

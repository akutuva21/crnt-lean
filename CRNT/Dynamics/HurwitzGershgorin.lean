import CRNT.Kinetics.MassActionJacobian
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.Complex.Basic

/-!
# A dimension-free Hurwitz test from Gershgorin's circle theorem

Gershgorin's circle theorem localizes every eigenvalue of a square matrix `A` inside one of the
discs centered at a diagonal entry `A k k` with radius the off-diagonal row norm-sum
`∑ j ≠ k, ‖A k j‖`. Pushing each disc strictly into the open left half-plane forces every
eigenvalue there too, giving a **diagonal-dominance** Hurwitz criterion that holds in any finite
dimension — no characteristic polynomial, no Routh–Hurwitz determinants.

This module records the criterion at three levels:

* `CRNT.hurwitz_of_strict_diag_dominance` — the complex core. If for every row `k` the diagonal
  real part plus the off-diagonal norm-sum is negative, `(A k k).re + ∑ j ≠ k, ‖A k j‖ < 0`, then
  every eigenvalue of `Matrix.toLin' A` has negative real part. Obtained from Mathlib's
  `eigenvalue_mem_ball`: an eigenvalue `μ` satisfies `‖A k k − μ‖ ≤ ∑ j ≠ k, ‖A k j‖` for some `k`,
  and `(A k k).re − μ.re ≤ ‖A k k − μ‖` puts `μ.re` below the negative bound.
* `CRNT.hurwitz_of_strict_diag_dominance_real` — the real-matrix version, applying the core to the
  complexification `A.map (algebraMap ℝ ℂ)` and rewriting the diagonal real parts to `A k k` and the
  off-diagonal norms to `|A k j|`.
* `CRNT.massActionJacobian_hurwitz_of_strict_diag_dominance` — the all-dimension no-oscillation gate
  for a strictly diagonally dominant mass-action Jacobian at a point `x`.

This is the classical **diagonal-dominance stability test** (Gershgorin's circle theorem applied to
stability). It is a one-directional **sufficient** condition for the Hurwitz property: it can fail
for matrices that are nonetheless stable, so it is not a full Routh–Hurwitz equivalence. The
dynamical Hopf-bifurcation theorem (that loss of stability through a purely imaginary eigenvalue pair
produces an oscillation) is a separate analytic statement and stays out of scope here.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Kinetics.MassActionJacobian`, Mathlib
`LinearAlgebra.Matrix.Gershgorin`, `Analysis.Complex.Norm`.
-/

namespace CRNT

open Matrix Complex

/-- **Gershgorin diagonal-dominance Hurwitz test.** If every diagonal entry has negative real part
strictly exceeding (in magnitude) the row's off-diagonal norm-sum, i.e.
`(A k k).re + ∑ j ≠ k, ‖A k j‖ < 0` for all `k`, then every eigenvalue of `Matrix.toLin' A` lies in
the open left half-plane. This is Gershgorin's circle theorem read as a stability criterion: each
Gershgorin disc is pushed strictly into the left half-plane. -/
theorem hurwitz_of_strict_diag_dominance {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (h : ∀ k, (A k k).re + ∑ j ∈ Finset.univ.erase k, ‖A k j‖ < 0) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ.re < 0 := by
  intro μ hμ
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ
  rw [mem_closedBall_iff_norm'] at hk
  -- `hk : ‖A k k - μ‖ ≤ ∑ j ≠ k, ‖A k j‖`
  have hre : μ.re - (A k k).re ≤ ∑ j ∈ Finset.univ.erase k, ‖A k j‖ :=
    calc μ.re - (A k k).re = (μ - A k k).re := by rw [Complex.sub_re]
      _ ≤ |(μ - A k k).re| := le_abs_self _
      _ ≤ ‖μ - A k k‖ := Complex.abs_re_le_norm _
      _ = ‖A k k - μ‖ := norm_sub_rev _ _
      _ ≤ ∑ j ∈ Finset.univ.erase k, ‖A k j‖ := hk
  have hk' := h k
  linarith

/-- **Real-matrix Gershgorin Hurwitz test.** If a real matrix is strictly row diagonally dominant
with negative diagonal, `A k k + ∑ j ≠ k, |A k j| < 0` for all `k`, then every eigenvalue of its
complexification `A.map (algebraMap ℝ ℂ)` lies in the open left half-plane. This is the core test
applied to the complexified matrix, with the diagonal real parts and off-diagonal moduli computed
back to the real entries. -/
theorem hurwitz_of_strict_diag_dominance_real {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ)
    (h : ∀ k, A k k + ∑ j ∈ Finset.univ.erase k, |A k j| < 0) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0 := by
  apply hurwitz_of_strict_diag_dominance
  intro k
  have hdiag : ((A.map (algebraMap ℝ ℂ)) k k).re = A k k := by
    rw [Matrix.map_apply, Complex.coe_algebraMap, Complex.ofReal_re]
  have hsum : (∑ j ∈ Finset.univ.erase k, ‖(A.map (algebraMap ℝ ℂ)) k j‖)
      = ∑ j ∈ Finset.univ.erase k, |A k j| := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.map_apply, Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs]
  rw [hdiag, hsum]
  exact h k

/-- **All-dimension no-oscillation gate for a strictly diagonally dominant mass-action Jacobian.**
If the mass-action Jacobian `N.massActionJacobian κ x` is strictly row diagonally dominant with
negative diagonal at the point `x`, then every eigenvalue of its complexification lies in the open
left half-plane: the linearization at `x` is Hurwitz. This is a one-directional sufficient stability
test valid in any number of species. -/
theorem massActionJacobian_hurwitz_of_strict_diag_dominance {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (x : Concentration S)
    (h : ∀ k, (N.massActionJacobian κ x) k k +
        ∑ j ∈ Finset.univ.erase k, |(N.massActionJacobian κ x) k j| < 0) :
    ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toLin' ((N.massActionJacobian κ x).map (algebraMap ℝ ℂ))) μ → μ.re < 0 :=
  hurwitz_of_strict_diag_dominance_real _ h

end CRNT

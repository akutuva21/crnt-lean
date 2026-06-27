import CRNT.Dynamics.ExponentialDichotomy
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponential decay on the stable subspace

For a real matrix `A : Matrix (Fin n) (Fin n) ℝ` that is Hurwitz on the stable subspace, the linear
flow `t ↦ exp (t • A)` contracts: there are constants `C ≥ 1` and `α > 0` with
`‖exp (t • A) x‖ ≤ C e^{-α t} ‖x‖` for every stable `x` and every `t ≥ 0`. This module proves that
decay from a Lyapunov certificate.

The argument is the classical Lyapunov-function proof of asymptotic stability (Hahn, *Stability of
Motion*; Coppel, *Dichotomies in Stability Theory*; Hirsch–Smale–Devaney, *Differential Equations,
Dynamical Systems, and an Introduction to Chaos*). A Hurwitz generator `B` admits a positive-definite
`P` solving the continuous Lyapunov equation `BᵀP + P B = -I`. Reading `P` through the inner product
gives a quadratic Lyapunov function `V (t) = ⟪u t, P (u t)⟫` along the trajectory
`u t = exp (t • B) x`. Differentiating, `V' (t) = ⟪B (u t), P (u t)⟫ + ⟪u t, P (B (u t))⟫`, which the
Lyapunov inequality bounds by `-‖u t‖²`. Since `V` is comparable to `‖u‖²` from both sides, this is a
linear differential inequality `V' ≤ -(1 / C₀) V`, and Grönwall's inequality yields the exponential
decay of `V`, hence of `‖u‖`.

The decay is stated for an arbitrary generator `B` together with a `LyapunovCertificate`: a
self-adjoint operator coercive between `c₀ ‖y‖²` and `C₀ ‖y‖²` whose associated Lyapunov derivative is
bounded above by `-‖y‖²`. Specialising `B` to the restriction of `A` to `E_sℝ` gives the stable-subspace
decay. The construction of the certificate for a Hurwitz `B` — equivalently, solvability of the
continuous Lyapunov equation — is the residual analytic input, recorded separately.
-/

open scoped RealInnerProductSpace Matrix.Norms.Operator
open NormedSpace Set Filter Topology

namespace CRNT.ExponentialDecay

variable {n : ℕ}

/-- Euclidean phase space of the linear flow. -/
abbrev Phase (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The Euclidean continuous-linear-map action of a matrix on `Phase n`. -/
noncomputable def act (A : Matrix (Fin n) (Fin n) ℝ) : Phase n →L[ℝ] Phase n :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) A

/-! ## A scalar Grönwall comparison -/

/-- Scalar Grönwall comparison: a real function with right derivative bounded by `K · V` decays no
faster than the corresponding exponential. If `V` is everywhere differentiable and
`V' t ≤ K · V t` on `[0, b]`, then `V t ≤ V 0 · e^{K t}` on `[0, b]`. -/
theorem le_mul_exp_of_deriv_le {V V' : ℝ → ℝ} {K b : ℝ}
    (hV : ∀ t, HasDerivAt V (V' t) t)
    (bound : ∀ t ∈ Ico (0 : ℝ) b, V' t ≤ K * V t) :
    ∀ t ∈ Icc (0 : ℝ) b, V t ≤ V 0 * Real.exp (K * t) := by
  intro t ht
  have key : V t ≤ gronwallBound (V 0) K 0 (t - 0) := by
    refine le_gronwallBound_of_liminf_deriv_right_le
      (f := V) (f' := V') (δ := V 0) (K := K) (ε := 0) (a := 0) (b := b)
      (Continuous.continuousOn ?_) ?_ le_rfl ?_ t ht
    · exact continuous_iff_continuousAt.2 fun x => (hV x).continuousAt
    · intro x _ r hr
      have hslope := ((hV x).hasDerivWithinAt (s := Ici x)).liminf_right_slope_le hr
      refine hslope.mono fun z hz => ?_
      simpa only [slope, smul_eq_mul, vsub_eq_sub] using hz
    · intro x hx
      simpa using bound x hx
  simpa only [sub_zero, gronwallBound_ε0] using key

/-! ## The Lyapunov certificate -/

/-- A Lyapunov certificate for a generator `B` on `Phase n`: a self-adjoint operator `P` that is
coercive between `c₀ ‖y‖²` and `C₀ ‖y‖²`, and whose Lyapunov derivative
`⟪B y, P y⟫ + ⟪y, P (B y)⟫` is bounded above by `-‖y‖²`. This packages a positive-definite solution
of the continuous Lyapunov equation `BᵀP + P B ≼ -I`. -/
structure LyapunovCertificate (B : Phase n →L[ℝ] Phase n) where
  /-- The Lyapunov operator, read as a continuous linear map. -/
  P : Phase n →L[ℝ] Phase n
  /-- `P` is self-adjoint. -/
  selfAdjoint : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫
  /-- Lower coercivity constant. -/
  c₀ : ℝ
  /-- Upper coercivity constant. -/
  C₀ : ℝ
  /-- The lower constant is positive. -/
  c₀_pos : 0 < c₀
  /-- The quadratic form dominates `c₀ ‖y‖²`. -/
  lower : ∀ y, c₀ * ‖y‖ ^ 2 ≤ ⟪y, P y⟫
  /-- The quadratic form is dominated by `C₀ ‖y‖²`. -/
  upper : ∀ y, ⟪y, P y⟫ ≤ C₀ * ‖y‖ ^ 2
  /-- The upper constant is at least the lower constant. For a genuine positive-definite `P` on a
  nontrivial space this follows from evaluating both bounds at a unit vector; it is recorded as a
  field so the certificate carries no nontriviality assumption. -/
  c₀_le_C₀ : c₀ ≤ C₀
  /-- The Lyapunov inequality `BᵀP + P B ≼ -I`. -/
  lyap : ∀ y, ⟪B y, P y⟫ + ⟪y, P (B y)⟫ ≤ -‖y‖ ^ 2

/-! ## The linear trajectory and its derivative -/

/-- Evaluation of the Euclidean action at a fixed vector, as a continuous linear map of the matrix.
The map `M ↦ act M x` is `ℝ`-linear because `Matrix.toEuclideanCLM` is an algebra equivalence, and
continuous because the matrix space is finite-dimensional. -/
noncomputable def evalCLM (x : Phase n) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Phase n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => act M x
      map_add' := fun M N => by
        simp only [act, map_add, add_apply]
      map_smul' := fun c M => by
        simp only [act, map_smul, smul_apply, RingHom.id_apply] }

@[simp] theorem evalCLM_apply (x : Phase n) (M : Matrix (Fin n) (Fin n) ℝ) :
    evalCLM x M = act M x := rfl

/-- The linear trajectory `t ↦ exp (t • A) x` of `ẋ = A x` through `x`, in Euclidean space. -/
noncomputable def traj (A : Matrix (Fin n) (Fin n) ℝ) (x : Phase n) (t : ℝ) : Phase n :=
  act (exp (t • A)) x

@[simp] theorem traj_zero (A : Matrix (Fin n) (Fin n) ℝ) (x : Phase n) : traj A x 0 = x := by
  simp [traj, act, zero_smul, exp_zero]

/-- The trajectory solves `ẋ = A x`: its derivative is `A` applied to the current state. The matrix
exponential `t ↦ exp (t • A)` has derivative `exp (t • A) * A`, and post-composing with the evaluation
map `evalCLM x` gives the stated derivative. -/
theorem hasDerivAt_traj (A : Matrix (Fin n) (Fin n) ℝ) (x : Phase n) (t : ℝ) :
    HasDerivAt (traj A x) (act A (traj A x t)) t := by
  have hM : HasDerivAt (fun u : ℝ => exp (u • A)) (A * exp (t • A)) t :=
    hasDerivAt_exp_smul_const' A t
  have hcomp : HasDerivAt (fun u : ℝ => evalCLM x (exp (u • A)))
      (evalCLM x (A * exp (t • A))) t :=
    (evalCLM x).hasFDerivAt.comp_hasDerivAt t hM
  have hmap : act (A * exp (t • A)) x = act A (traj A x t) := by
    apply WithLp.ofLp_injective 2
    simp only [act, traj, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_mulVec]
  rw [evalCLM_apply] at hcomp
  rw [hmap] at hcomp
  exact hcomp

/-! ## Exponential decay from a Lyapunov certificate -/

namespace LyapunovCertificate

variable {A : Matrix (Fin n) (Fin n) ℝ} (cert : LyapunovCertificate (act A))

/-- The quadratic Lyapunov function `V (t) = ⟪u t, P (u t)⟫` along the trajectory `u t = exp (t • A) x`.
-/
noncomputable def lyapFun (x : Phase n) (t : ℝ) : ℝ :=
  ⟪traj A x t, cert.P (traj A x t)⟫

/-- The Lyapunov function is differentiable, with derivative the symmetric Lyapunov form evaluated at
the velocity: `V' (t) = ⟪A (u t), P (u t)⟫ + ⟪u t, P (A (u t))⟫`. -/
theorem hasDerivAt_lyapFun (x : Phase n) (t : ℝ) :
    HasDerivAt (cert.lyapFun x)
      (⟪traj A x t, cert.P (act A (traj A x t))⟫ + ⟪act A (traj A x t), cert.P (traj A x t)⟫) t := by
  have hu : HasDerivAt (traj A x) (act A (traj A x t)) t := hasDerivAt_traj A x t
  have hPu : HasDerivAt (fun s => cert.P (traj A x s)) (cert.P (act A (traj A x t))) t :=
    cert.P.hasFDerivAt.comp_hasDerivAt t hu
  exact hu.inner ℝ hPu

/-- The Lyapunov inequality on the trajectory: `V' (t) ≤ -‖u t‖²`. -/
theorem lyapFun_deriv_le (x : Phase n) (t : ℝ) :
    ⟪traj A x t, cert.P (act A (traj A x t))⟫ + ⟪act A (traj A x t), cert.P (traj A x t)⟫
      ≤ -‖traj A x t‖ ^ 2 := by
  rw [add_comm]
  exact cert.lyap (traj A x t)

/-- The upper Lyapunov constant is positive. -/
theorem C₀_pos : 0 < cert.C₀ := lt_of_lt_of_le cert.c₀_pos cert.c₀_le_C₀

/-- The Lyapunov function decays exponentially: `V t ≤ V 0 · e^{-t / C₀}` for `t ≥ 0`. This is the
linear differential inequality `V' ≤ -(1 / C₀) V` integrated by Grönwall's inequality. -/
theorem lyapFun_le (x : Phase n) {t : ℝ} (ht : 0 ≤ t) :
    cert.lyapFun x t ≤ cert.lyapFun x 0 * Real.exp (-(1 / cert.C₀) * t) := by
  have hC₀ : 0 < cert.C₀ := cert.C₀_pos
  -- the differential inequality `V' ≤ -(1 / C₀) V` on `[0, t]`.
  have bound : ∀ s ∈ Ico (0 : ℝ) (t + 1),
      (⟪traj A x s, cert.P (act A (traj A x s))⟫ + ⟪act A (traj A x s), cert.P (traj A x s)⟫)
        ≤ -(1 / cert.C₀) * cert.lyapFun x s := by
    intro s _
    have hderiv := cert.lyapFun_deriv_le x s
    have hupper : cert.lyapFun x s ≤ cert.C₀ * ‖traj A x s‖ ^ 2 := cert.upper (traj A x s)
    have hsq : (1 / cert.C₀) * cert.lyapFun x s ≤ ‖traj A x s‖ ^ 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hC₀]
      linarith [hupper]
    calc _ ≤ -‖traj A x s‖ ^ 2 := hderiv
      _ ≤ -(1 / cert.C₀) * cert.lyapFun x s := by
          rw [neg_mul]; linarith [hsq]
  have hgron := le_mul_exp_of_deriv_le
    (V := cert.lyapFun x)
    (V' := fun s => ⟪traj A x s, cert.P (act A (traj A x s))⟫
      + ⟪act A (traj A x s), cert.P (traj A x s)⟫)
    (K := -(1 / cert.C₀)) (b := t + 1)
    (fun s => cert.hasDerivAt_lyapFun x s) bound t ⟨ht, by linarith⟩
  exact hgron

/-- **Exponential decay on the stable subspace.** If `A` admits a Lyapunov certificate (equivalently,
`A` is Hurwitz, so the continuous Lyapunov equation `AᵀP + P A = -I` has a positive-definite
solution), then its linear flow contracts at an exponential rate: with `C = √(C₀ / c₀) ≥ 1` and
`α = 1 / (2 C₀) > 0`,
`‖exp (t • A) x‖ ≤ C · e^{-α t} · ‖x‖` for every `x` and every `t ≥ 0`.

This is the quantitative half of the exponential dichotomy (Coppel, *Dichotomies in Stability
Theory*; Hahn, *Stability of Motion*): the stable directions of a Hurwitz generator contract
uniformly and exponentially along the flow. -/
theorem norm_traj_le (x : Phase n) {t : ℝ} (ht : 0 ≤ t) :
    ‖traj A x t‖ ≤ Real.sqrt (cert.C₀ / cert.c₀) * Real.exp (-(1 / (2 * cert.C₀)) * t) * ‖x‖ := by
  have hc₀ : 0 < cert.c₀ := cert.c₀_pos
  have hC₀ : 0 < cert.C₀ := cert.C₀_pos
  set u := traj A x t with hu
  -- lower bound `c₀ ‖u‖² ≤ V t` and the decayed upper bound on `V t`.
  have hlow : cert.c₀ * ‖u‖ ^ 2 ≤ cert.lyapFun x t := cert.lower (traj A x t)
  have hV0 : cert.lyapFun x 0 ≤ cert.C₀ * ‖x‖ ^ 2 := by
    have := cert.upper (traj A x 0)
    rw [traj_zero] at this
    rw [lyapFun, traj_zero]
    exact this
  have hdecay : cert.lyapFun x t ≤ cert.C₀ * ‖x‖ ^ 2 * Real.exp (-(1 / cert.C₀) * t) :=
    le_trans (cert.lyapFun_le x ht)
      (by
        have hexp : 0 < Real.exp (-(1 / cert.C₀) * t) := Real.exp_pos _
        nlinarith [hV0, hexp])
  -- assemble `‖u‖² ≤ (C₀ / c₀) ‖x‖² e^{-t/C₀}`.
  have hsq : ‖u‖ ^ 2 ≤ cert.C₀ / cert.c₀ * ‖x‖ ^ 2 * Real.exp (-(1 / cert.C₀) * t) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc₀]
    nlinarith [hlow, hdecay]
  -- the target right-hand side, squared, equals that bound.
  have hexp_half : Real.exp (-(1 / (2 * cert.C₀)) * t) ^ 2 = Real.exp (-(1 / cert.C₀) * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
    ring
  set M := Real.sqrt (cert.C₀ / cert.c₀) * Real.exp (-(1 / (2 * cert.C₀)) * t) * ‖x‖ with hM
  have hMnn : 0 ≤ M := by
    apply mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)) (norm_nonneg _)
  have hMsq : M ^ 2 = cert.C₀ / cert.c₀ * ‖x‖ ^ 2 * Real.exp (-(1 / cert.C₀) * t) := by
    rw [hM, mul_pow, mul_pow, Real.sq_sqrt (by positivity), hexp_half]
    ring
  have hfinal : ‖u‖ ^ 2 ≤ M ^ 2 := by rw [hMsq]; exact hsq
  exact le_of_sq_le_sq hfinal hMnn

/-- The exponential decay, stated with the matrix exponential made explicit:
`‖exp (t • A) x‖ ≤ C · e^{-α t} · ‖x‖` with `C = √(C₀ / c₀) ≥ 1` and `α = 1 / (2 C₀) > 0`. -/
theorem norm_exp_smul_le (x : Phase n) {t : ℝ} (ht : 0 ≤ t) :
    ‖(act (exp (t • A))) x‖
      ≤ Real.sqrt (cert.C₀ / cert.c₀) * Real.exp (-(1 / (2 * cert.C₀)) * t) * ‖x‖ :=
  cert.norm_traj_le x ht

/-- The leading constant `C = √(C₀ / c₀)` is at least one, as required of a dichotomy bound. -/
theorem one_le_sqrt_C₀_div_c₀ : 1 ≤ Real.sqrt (cert.C₀ / cert.c₀) := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ cert.c₀_pos, one_mul]
  exact cert.c₀_le_C₀

/-- The decay rate `α = 1 / (2 C₀)` is positive. -/
theorem decay_rate_pos : 0 < 1 / (2 * cert.C₀) := by
  have := cert.C₀_pos
  positivity

end LyapunovCertificate

end CRNT.ExponentialDecay

/-!
This module is **stable** and `sorry`-free. Depends on:
`CRNT.Dynamics.ExponentialDichotomy`, `Mathlib.Analysis.CStarAlgebra.Matrix`,
`Mathlib.Analysis.InnerProductSpace.Calculus`, `Mathlib.Analysis.ODE.Gronwall`,
`Mathlib.Analysis.SpecialFunctions.Exponential`.
-/

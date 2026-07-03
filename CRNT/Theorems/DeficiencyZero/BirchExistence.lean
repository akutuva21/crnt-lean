import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import CRNT.LinearAlgebra.OrthogonalComplement
import CRNT.Theorems.DeficiencyZero.Birch

/-!
# Birch's theorem: the dual objective and its lower bound

Birch existence — that every positive stoichiometric compatibility class contains a
positive point with `S`-orthogonal log-ratio — is proved by minimizing the **dual
objective**

```text
birchDual x* c w = ∑ᵢ (x*ᵢ exp(wᵢ) − cᵢ wᵢ)
```

over the subspace `Sᗮ`; a critical point `ŵ` yields the solution `x = x* ⊙ exp(ŵ)`
(positive, with `x − c ∈ S` and `log(x/x*) = ŵ ∈ Sᗮ`). The objective is the convex
conjugate (Legendre transform) of the relative entropy in `CRNT.relEntropy`.

This module establishes the analytic core of that minimization:

* the **Fenchel–Young inequality** `birchDualTerm_ge`, the per-coordinate sharp lower
  bound dual to Gibbs' inequality (`relEntropyTerm_nonneg`), hence that `birchDual` is
  **bounded below** (`birchDual_ge`), with its infimum attained at `wᵢ = log(cᵢ/x*ᵢ)`;
* **coercivity** `birchDual_coercive`: every sublevel set is bounded;
* the resulting **minimizer over any finite-dimensional subspace**
  `birchDual_exists_isMinOn` (continuity + coercivity + compactness);
* its **first-order optimality** `birchDual_firstOrder`: the gradient `x* ⊙ exp(ŵ) − c`
  is orthogonal to the minimization subspace (`IsLocalMin.hasDerivAt_eq_zero`).

Taking the subspace to be `Sᗮ` and using the finite-dimensional duality `(Sᗮ)ᗮ = S`
(`orthSum_orthSum`), this yields the **existence half of Birch's theorem**
(`birch_existence`): the point `x = x* ⊙ exp(ŵ)` is positive, lies in the compatibility
class `c + S`, and has `S`-orthogonal log-ratio. Combined with `birch_uniqueness`, the
full **Birch theorem** `birch` follows: each positive compatibility class contains a
unique such point — the complex-balanced equilibrium.

-/

namespace CRNT

open scoped BigOperators

/-- **Fenchel–Young inequality** (per coordinate), dual to Gibbs' inequality: for
`a, cc > 0`, the dual term `a·exp s − cc·s` is bounded below by `cc − cc·log(cc/a)`, its
value at the minimizer `s = log(cc/a)`. -/
theorem birchDualTerm_ge {a cc : ℝ} (ha : 0 < a) (hc : 0 < cc) (s : ℝ) :
    cc - cc * Real.log (cc / a) ≤ a * Real.exp s - cc * s := by
  set s₀ := Real.log (cc / a) with hs0
  have h1 : a * Real.exp s₀ = cc := by
    rw [hs0, Real.exp_log (div_pos hc ha)]; field_simp
  have h2 : (s - s₀) + 1 ≤ Real.exp (s - s₀) := Real.add_one_le_exp (s - s₀)
  have h3 : Real.exp s = Real.exp s₀ * Real.exp (s - s₀) := by
    rw [← Real.exp_add]; congr 1; ring
  have h5 : a * Real.exp s = cc * Real.exp (s - s₀) := by
    rw [h3, ← mul_assoc, h1]
  nlinarith [h5, mul_le_mul_of_nonneg_left h2 hc.le]

/-- The dual objective of Birch's theorem: the convex conjugate of the relative entropy,
minimized (over `Sᗮ`) to produce the complex-balanced equilibrium. -/
noncomputable def birchDual {ι : Type*} [Fintype ι] (xstar c w : ι → ℝ) : ℝ :=
  ∑ i, (xstar i * Real.exp (w i) - c i * w i)

/-- **The dual objective is bounded below**, by the sum of its per-coordinate minima.
This is the well-posedness anchor for the minimization underlying Birch existence. -/
theorem birchDual_ge {ι : Type*} [Fintype ι] {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) (w : ι → ℝ) :
    (∑ i, (c i - c i * Real.log (c i / xstar i))) ≤ birchDual xstar c w :=
  Finset.sum_le_sum fun i _ => birchDualTerm_ge (hxs i) (hc i) (w i)

/-- **Coercivity of the dual objective.** Every sublevel set `{w | birchDual x* c w ≤ M}`
is bounded: each coordinate is pinned, with a uniform bound `R`. The lower bound on `wᵢ`
comes from `x*ᵢ exp wᵢ ≥ 0`; the upper bound from Fenchel–Young applied with the halved
coefficient `x*ᵢ/2` together with `Real.add_one_le_exp`. Coercivity makes the
minimization underlying Birch existence well-posed (a minimizer exists). -/
theorem birchDual_coercive {ι : Type*} [Fintype ι] {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) (M : ℝ) :
    ∃ R : ℝ, ∀ w : ι → ℝ, birchDual xstar c w ≤ M → ∀ i, |w i| ≤ R := by
  classical
  let m : ι → ℝ := fun i => c i - c i * Real.log (c i / xstar i)
  let ell : ι → ℝ := fun i => c i - c i * Real.log (c i / (xstar i / 2))
  let Cc : ι → ℝ := fun i => M - (∑ j, m j) + m i
  let U : ι → ℝ := fun i => 2 * (Cc i - ell i) / xstar i - 1
  refine ⟨∑ i, (|Cc i / c i| + |U i|), fun w hw i => ?_⟩
  have hge : ∀ j, m j ≤ xstar j * Real.exp (w j) - c j * w j :=
    fun j => birchDualTerm_ge (hxs j) (hc j) (w j)
  -- φᵢ(wᵢ) ≤ Cc i, since the other coordinates are each ≥ their minimum.
  have hCi : xstar i * Real.exp (w i) - c i * w i ≤ Cc i := by
    have hsum : (∑ j, (xstar j * Real.exp (w j) - c j * w j - m j))
        = birchDual xstar c w - ∑ j, m j := by
      simp only [birchDual]; rw [Finset.sum_sub_distrib]
    have hsingle := Finset.single_le_sum
      (f := fun j => xstar j * Real.exp (w j) - c j * w j - m j)
      (fun j _ => by linarith [hge j]) (Finset.mem_univ i)
    rw [hsum] at hsingle
    show xstar i * Real.exp (w i) - c i * w i ≤ M - (∑ j, m j) + m i
    linarith [hsingle, hw]
  -- lower bound on `w i`
  have hlow : -(Cc i / c i) ≤ w i := by
    have hnn : (0 : ℝ) ≤ xstar i * Real.exp (w i) :=
      mul_nonneg (hxs i).le (Real.exp_pos (w i)).le
    rw [← neg_div, div_le_iff₀ (hc i)]
    nlinarith [hCi, hnn]
  -- upper bound on `w i`, via Fenchel–Young with the halved coefficient
  have hup : w i ≤ U i := by
    have hfy2 : ell i ≤ xstar i / 2 * Real.exp (w i) - c i * w i :=
      birchDualTerm_ge (half_pos (hxs i)) (hc i) (w i)
    have hexpge : w i + 1 ≤ Real.exp (w i) := Real.add_one_le_exp (w i)
    have h1 : xstar i / 2 * Real.exp (w i) ≤ Cc i - ell i := by nlinarith [hCi, hfy2]
    have h2 : xstar i / 2 * (w i + 1) ≤ Cc i - ell i := by
      nlinarith [h1, mul_le_mul_of_nonneg_left hexpge (half_pos (hxs i)).le]
    have h3 : w i + 1 ≤ 2 * (Cc i - ell i) / xstar i := by
      rw [le_div_iff₀ (hxs i)]; nlinarith [h2]
    show w i ≤ 2 * (Cc i - ell i) / xstar i - 1
    linarith [h3]
  -- assemble: |w i| ≤ Bᵢ ≤ ∑ Bⱼ
  have hBi : |w i| ≤ |Cc i / c i| + |U i| := by
    rw [abs_le]
    exact ⟨by nlinarith [hlow, le_abs_self (Cc i / c i), abs_nonneg (U i)],
      by nlinarith [hup, le_abs_self (U i), abs_nonneg (Cc i / c i)]⟩
  exact hBi.trans
    (Finset.single_le_sum (f := fun j => |Cc j / c j| + |U j|)
      (fun j _ => by positivity) (Finset.mem_univ i))

/-- The Birch dual objective is continuous. -/
theorem continuous_birchDual {ι : Type*} [Fintype ι] (xstar c : ι → ℝ) :
    Continuous (birchDual xstar c) := by
  unfold birchDual
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_const.mul (Real.continuous_exp.comp (continuous_apply i))).sub
    (continuous_const.mul (continuous_apply i))

/-- **A minimizer of the dual objective over a (finite-dimensional) subspace exists.**
This is the payoff of coercivity: the objective is continuous and coercive, and the
subspace is closed, so the minimization is attained. (Taking the subspace to be `Sᗮ`,
the minimizer's first-order conditions will give Birch existence.) -/
theorem birchDual_exists_isMinOn {ι : Type*} [Fintype ι] {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) (T : Submodule ℝ (ι → ℝ)) :
    ∃ ŵ ∈ T, ∀ w ∈ T, birchDual xstar c ŵ ≤ birchDual xstar c w := by
  classical
  have hcont := continuous_birchDual xstar c
  obtain ⟨R₀, hR₀⟩ := birchDual_coercive hxs hc (birchDual xstar c 0)
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : (0 : ℝ) ≤ R := le_max_right _ _
  have hconf : ∀ w, birchDual xstar c w ≤ birchDual xstar c 0 → ‖w‖ ≤ R := by
    intro w hw
    rw [pi_norm_le_iff_of_nonneg hR0]
    intro i
    rw [Real.norm_eq_abs]
    exact (hR₀ w hw i).trans (le_max_left _ _)
  have hKcomp : IsCompact ((T : Set (ι → ℝ)) ∩ Metric.closedBall 0 R) :=
    (isCompact_closedBall 0 R).inter_left T.closed_of_finiteDimensional
  have h0mem : (0 : ι → ℝ) ∈ (T : Set (ι → ℝ)) ∩ Metric.closedBall 0 R :=
    ⟨T.zero_mem, by simpa using hR0⟩
  obtain ⟨ŵ, hŵK, hŵmin⟩ := hKcomp.exists_isMinOn ⟨0, h0mem⟩ hcont.continuousOn
  refine ⟨ŵ, hŵK.1, fun w hw => ?_⟩
  by_cases hcase : birchDual xstar c w ≤ birchDual xstar c 0
  · have hwK : w ∈ (T : Set (ι → ℝ)) ∩ Metric.closedBall 0 R :=
      ⟨hw, by rw [Metric.mem_closedBall, dist_zero_right]; exact hconf w hcase⟩
    exact isMinOn_iff.mp hŵmin w hwK
  · have hmin0 := isMinOn_iff.mp hŵmin 0 h0mem
    linarith [not_le.mp hcase]

/-- **First-order optimality (stationarity) of the dual minimizer.** If `ŵ` minimizes
`birchDual x* c` over a subspace `T`, then for every direction `v ∈ T` the gradient is
orthogonal to `v`: writing the minimizing point as `x = x* ⊙ exp(ŵ)`,

```text
∑ᵢ (x*ᵢ exp(ŵᵢ) − cᵢ) · vᵢ = 0   for all v ∈ T,
```

i.e. `x − c ⊥ T`. The proof restricts to the line `t ↦ birchDual (ŵ + t·v)`, which has a
minimum at `t = 0`; `IsLocalMin.hasDerivAt_eq_zero` forces its derivative — the gradient
paired with `v` — to vanish. With `T = Sᗮ` this gives `x − c ∈ (Sᗮ)ᗮ = S`. -/
theorem birchDual_firstOrder {ι : Type*} [Fintype ι] {xstar c : ι → ℝ}
    (T : Submodule ℝ (ι → ℝ)) {ŵ : ι → ℝ} (hŵT : ŵ ∈ T)
    (hŵmin : ∀ w ∈ T, birchDual xstar c ŵ ≤ birchDual xstar c w) :
    ∀ v ∈ T, ∑ i, (xstar i * Real.exp (ŵ i) - c i) * v i = 0 := by
  intro v hv
  -- the line `t ↦ birchDual (ŵ + t·v)`, written coordinatewise
  have hγ : (fun t : ℝ => birchDual xstar c (ŵ + t • v))
      = fun t => ∑ i, (xstar i * Real.exp (ŵ i + t * v i) - c i * (ŵ i + t * v i)) := by
    funext t; simp only [birchDual, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  -- its derivative at `0` is the gradient paired with `v`
  have hterm : ∀ i ∈ Finset.univ,
      HasDerivAt (fun t => xstar i * Real.exp (ŵ i + t * v i) - c i * (ŵ i + t * v i))
        (xstar i * (Real.exp (ŵ i) * v i) - c i * v i) 0 := by
    intro i _
    have he : HasDerivAt (fun t : ℝ => ŵ i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id 0).mul_const (v i)).const_add (ŵ i)
    have h1 : HasDerivAt (fun t => xstar i * Real.exp (ŵ i + t * v i))
        (xstar i * (Real.exp (ŵ i) * v i)) 0 := by simpa using he.exp.const_mul (xstar i)
    exact h1.sub (he.const_mul (c i))
  have hfun :
      (∑ i, fun t : ℝ => xstar i * Real.exp (ŵ i + t * v i) - c i * (ŵ i + t * v i))
        = fun t => ∑ i, (xstar i * Real.exp (ŵ i + t * v i) - c i * (ŵ i + t * v i)) := by
    funext t; simp only [Finset.sum_apply]
  have hderiv : HasDerivAt (fun t : ℝ => birchDual xstar c (ŵ + t • v))
      (∑ i, (xstar i * (Real.exp (ŵ i) * v i) - c i * v i)) 0 := by
    rw [hγ, ← hfun]; exact HasDerivAt.sum hterm
  -- `0` is a (global, hence local) minimum of the line
  have hmin : IsLocalMin (fun t : ℝ => birchDual xstar c (ŵ + t • v)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    have hmem : ŵ + t • v ∈ T := T.add_mem hŵT (T.smul_mem t hv)
    simpa using hŵmin (ŵ + t • v) hmem
  have hzero := hmin.hasDerivAt_eq_zero hderiv
  rw [← hzero]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Existence half of Birch's theorem.** For positive `x*` and `c`, the positive
stoichiometric compatibility class `c + S` contains a point `x = x* ⊙ exp(ŵ)` with
`S`-orthogonal log-ratio: `x > 0`, `x − c ∈ S`, and `log(x/x*) ⊥ S`. Such an `x` is the
complex-balanced equilibrium in that class. Combined with `birch_uniqueness`, it gives
the full Birch theorem.

The point is built from the minimizer `ŵ` of the dual objective over `Sᗮ` (= `orthSum S`):
positivity and the log-ratio identity `log(x/x*) = ŵ ∈ Sᗮ` are immediate, while
`x − c ∈ S` is the first-order optimality `birchDual_firstOrder` placing `x − c` in
`(Sᗮ)ᗮ = S` (`orthSum_orthSum`). -/
theorem birch_existence {ι : Type*} [Fintype ι] (S : Submodule ℝ (ι → ℝ))
    {xstar c : ι → ℝ} (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ x - c ∈ S ∧
      ∀ s ∈ S, ∑ i, (Real.log (x i) - Real.log (xstar i)) * s i = 0 := by
  obtain ⟨ŵ, hŵT, hŵmin⟩ := birchDual_exists_isMinOn hxs hc (orthSum S)
  refine ⟨fun i => xstar i * Real.exp (ŵ i), fun i => mul_pos (hxs i) (Real.exp_pos _),
    ?_, ?_⟩
  · -- `x − c ∈ S`, via first-order optimality and `(Sᗮ)ᗮ = S`
    have hmem : (fun i => xstar i * Real.exp (ŵ i)) - c ∈ orthSum (orthSum S) := by
      rw [mem_orthSum]
      intro v hv
      simpa [Pi.sub_apply] using birchDual_firstOrder (orthSum S) hŵT hŵmin v hv
    rwa [orthSum_orthSum] at hmem
  · -- `log(x/x*) = ŵ ∈ Sᗮ`
    intro s hs
    have hlog : ∀ i, Real.log (xstar i * Real.exp (ŵ i)) - Real.log (xstar i) = ŵ i := by
      intro i
      rw [Real.log_mul (hxs i).ne' (Real.exp_ne_zero _), Real.log_exp]; ring
    calc ∑ i, (Real.log (xstar i * Real.exp (ŵ i)) - Real.log (xstar i)) * s i
        = ∑ i, ŵ i * s i := Finset.sum_congr rfl fun i _ => by rw [hlog i]
      _ = 0 := (mem_orthSum.mp hŵT) s hs

/-- **Birch's theorem.** Relative to a positive reference `x*`, every positive
stoichiometric compatibility class `c + S` contains a **unique** point `x` with
`S`-orthogonal log-ratio `log(x/x*)`. This is the existence and uniqueness of the
complex-balanced equilibrium in each positive class, combining `birch_existence` with
`birch_uniqueness`. -/
theorem birch {ι : Type*} [Fintype ι] (S : Submodule ℝ (ι → ℝ))
    {xstar c : ι → ℝ} (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ x - c ∈ S ∧
      (∀ s ∈ S, ∑ i, (Real.log (x i) - Real.log (xstar i)) * s i = 0) ∧
      ∀ y : ι → ℝ, (∀ i, 0 < y i) → y - c ∈ S →
        (∀ s ∈ S, ∑ i, (Real.log (y i) - Real.log (xstar i)) * s i = 0) → y = x := by
  obtain ⟨x, hxpos, hxc, hxorth⟩ := birch_existence S hxs hc
  refine ⟨x, hxpos, hxc, hxorth, fun y hypos hyc hyorth => ?_⟩
  refine birch_uniqueness S hypos hxpos ?_ ?_
  · rw [show y - x = (y - c) - (x - c) from (sub_sub_sub_cancel_right y x c).symm]
    exact S.sub_mem hyc hxc
  · intro s hs
    have hsplit : ∑ i, (Real.log (y i) - Real.log (x i)) * s i
        = (∑ i, (Real.log (y i) - Real.log (xstar i)) * s i)
          - ∑ i, (Real.log (x i) - Real.log (xstar i)) * s i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, hyorth s hs, hxorth s hs]; ring

end CRNT

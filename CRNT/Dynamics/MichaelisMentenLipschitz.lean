import CRNT.Dynamics.MichaelisMentenCoupledContraction
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The explicit substrate-Lipschitz constant of the regularized Michaelis–Menten fast field

This module discharges the substrate-Lipschitz hypothesis `hlip` of
`CRNT.Dynamics.MichaelisMentenCoupledContraction` as a theorem, with an explicit constant read off
the model parameters. The regularized fast field
`mmRegFastField rate Km Vmax s z = -rate · (z - mmRegEquil Km Vmax s · e0)` depends on the substrate
`s` only through the regularized quasi-equilibrium level `mmRegEquil Km Vmax s = Vmax·s/mmRegDen Km s`;
in any difference of two field values at a common complex state `z` the `z` term cancels, leaving
`rate · |mmRegEquil Km Vmax s − mmRegEquil Km Vmax s'|` times the unit direction `e0`. The Lipschitz
constant of the field is therefore `rate` times the Lipschitz constant of `mmRegEquil`.

The regularized denominator `mmRegDen Km` is globally `C¹` with `mmRegDen Km s ≥ Km/2 > 0`
(`mmRegDen_ge_half`), so `mmRegEquil Km Vmax = (Vmax·s)/mmRegDen Km s` is differentiable everywhere
with derivative `(Vmax·mmRegDen Km s − Vmax·s·mmRegDeriv Km s)/(mmRegDen Km s)²`. The numerator is
exactly `Vmax·Km` on the physical ray `s ≥ 0` and is bounded by `|Vmax|·(3Km/2)` on `s < 0` — there
the only growing term `|s|·exp(2s/Km)` stays below `Km/2` because `x ≤ exp x`. With the denominator
square at least `Km²/4`, the derivative is bounded in magnitude by `6·|Vmax|/Km` everywhere, so the
mean value theorem gives `|mmRegEquil Km Vmax s − mmRegEquil Km Vmax s'| ≤ (6·|Vmax|/Km)·|s − s'|`.

Feeding this explicit bound as the discharged `hlip` into the tracking ceiling of
`CRNT.Dynamics.MichaelisMentenCoupledContraction` yields an end-to-end certified, horizon-uniform
`O(ε)` Michaelis–Menten reduction whose only remaining inputs are the rate and saturation positivity
`0 < rate`, `0 < Km`, the non-negativity `0 ≤ ε`, and the physical drift bound `‖g‖ ≤ G`.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations":
the slaved fast variable tracks the slow flow at speed `O(ε)`, with the transverse attraction
supplied by the fibre contraction rate; the rate law `Vmax·s/(Km+s)` is the
Michaelis–Menten/Briggs–Haldane quasi-steady-state level.

**The substrate Lipschitz constant of the equilibrium level** (`mmRegEquilLipConst`,
`mmRegEquil_hasDerivAt`, `mmRegEquil_deriv_le`, `mmRegEquil_lipschitz`). The explicit constant
`mmRegEquilLipConst Km Vmax = 6·|Vmax|/Km`, the everywhere-`HasDerivAt` law for `mmRegEquil`, the
global derivative bound, and the resulting Lipschitz estimate
`|mmRegEquil Km Vmax s − mmRegEquil Km Vmax s'| ≤ mmRegEquilLipConst Km Vmax · |s − s'|`.

**The substrate Lipschitz bound of the fast field** (`mmRegFastFieldLipConst`,
`mmRegFastField_substrate_lipschitz`). With `mmRegFastFieldLipConst rate Km Vmax = rate·6·|Vmax|/Km`,
the field obeys `‖mmRegFastField rate Km Vmax s z − mmRegFastField rate Km Vmax s' z‖ ≤
mmRegFastFieldLipConst rate Km Vmax · dist s s'` — the exact shape of the `hlip` hypothesis.

**The end-to-end certified reduction** (`mmReg_coupled_tracking_ceiling_certified`,
`mmCertifiedUniformReduction_certified`). The horizon-uniform tracking ceiling and the full certified
reduction with the substrate-Lipschitz hypothesis discharged: the only remaining hypotheses are
`0 < rate`, `0 < Km`, `0 ≤ ε`, and the drift bound `‖g‖ ≤ G`.

Depends on:
`CRNT.Dynamics.MichaelisMentenCoupledContraction`, `Mathlib.Analysis.Calculus.MeanValue`.
-/

open Set
open scoped Topology RealInnerProductSpace NNReal

namespace CRNT.MichaelisMenten

/-- **The explicit substrate-Lipschitz constant of the regularized equilibrium level**
`mmRegEquilLipConst Km Vmax = 6·|Vmax|/Km`. It bounds the magnitude of the derivative of
`mmRegEquil Km Vmax` everywhere. -/
noncomputable def mmRegEquilLipConst (Km Vmax : ℝ) : ℝ := 6 * |Vmax| / Km

/-- **Everywhere `HasDerivAt` law for the regularized equilibrium level.** The level is the quotient
of the affine numerator `Vmax·s` and the globally-`C¹`, nonvanishing denominator `mmRegDen Km`, so its
derivative is the quotient rule value `(Vmax·mmRegDen Km s − Vmax·s·mmRegDeriv Km s)/(mmRegDen Km s)²`. -/
lemma mmRegEquil_hasDerivAt (Km Vmax : ℝ) (hKm : 0 < Km) (s : ℝ) :
    HasDerivAt (mmRegEquil Km Vmax)
      ((Vmax * mmRegDen Km s - Vmax * s * mmRegDeriv Km s) / (mmRegDen Km s) ^ 2) s := by
  have hnum : HasDerivAt (fun u => Vmax * u) Vmax s := by
    simpa using (hasDerivAt_id s).const_mul Vmax
  have hden : HasDerivAt (mmRegDen Km) (mmRegDeriv Km s) s := mmRegDen_hasDerivAt Km hKm s
  have h := hnum.fun_div hden (mmRegDen_ne_zero Km hKm s)
  have hfun : (fun y => Vmax * y / mmRegDen Km y) = mmRegEquil Km Vmax := rfl
  rw [hfun] at h
  exact h

/-- The candidate derivative `mmRegDeriv Km` lies in `(0, 1]` for `0 < Km`: it is `1` on `s ≥ 0` and
`exp(2s/Km) ≤ 1` on `s < 0`. -/
lemma mmRegDeriv_mem (Km : ℝ) (hKm : 0 < Km) (s : ℝ) :
    0 < mmRegDeriv Km s ∧ mmRegDeriv Km s ≤ 1 := by
  rw [mmRegDeriv]
  split_ifs with hs
  · exact ⟨one_pos, le_rfl⟩
  · refine ⟨Real.exp_pos _, ?_⟩
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    apply Real.exp_le_exp.mpr
    have : 2 * s / Km < 0 := by
      apply div_neg_of_neg_of_pos _ hKm
      linarith [not_le.mp hs]
    linarith

/-- On the negative substrate branch the growing factor `|s|·exp(2s/Km)` stays below `Km/2`, because
`x ≤ exp x` gives `(2|s|/Km)·exp(−2|s|/Km) ≤ 1`. -/
lemma mmRegDen_neg_growth_le (Km : ℝ) (hKm : 0 < Km) {s : ℝ} (hs : s < 0) :
    -s * Real.exp (2 * s / Km) ≤ Km / 2 := by
  set x : ℝ := -2 * s / Km with hx
  have hxpos : 0 < x := by
    rw [hx]
    apply div_pos _ hKm
    linarith
  have hxexp : x ≤ Real.exp x := by
    have := Real.add_one_le_exp x
    linarith
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  -- `x·exp(−x) ≤ 1`, i.e. `x ≤ exp x`.
  have hkey : x * Real.exp (-x) ≤ 1 := by
    rw [Real.exp_neg]
    rw [mul_inv_le_iff₀ hexp_pos, one_mul]
    exact hxexp
  -- Rewrite `-s·exp(2s/Km) = (Km/2)·x·exp(−x)`.
  have hrw : -s * Real.exp (2 * s / Km) = (Km / 2) * (x * Real.exp (-x)) := by
    rw [hx]
    have : -(-2 * s / Km) = 2 * s / Km := by ring
    rw [this]
    field_simp
  rw [hrw]
  calc (Km / 2) * (x * Real.exp (-x)) ≤ (Km / 2) * 1 :=
        mul_le_mul_of_nonneg_left hkey (by linarith)
    _ = Km / 2 := by ring

/-- **The global derivative bound of the regularized equilibrium level.** The derivative of
`mmRegEquil Km Vmax` is bounded in magnitude by `mmRegEquilLipConst Km Vmax = 6·|Vmax|/Km` everywhere:
the quotient-rule numerator `Vmax·(mmRegDen Km s − s·mmRegDeriv Km s)` has magnitude at most
`|Vmax|·(3Km/2)` (exactly `|Vmax|·Km` on `s ≥ 0`, and bounded on `s < 0` by the growth lemma), while
the squared denominator is at least `Km²/4`. -/
lemma mmRegEquil_deriv_le (Km Vmax : ℝ) (hKm : 0 < Km) (s : ℝ) :
    |(Vmax * mmRegDen Km s - Vmax * s * mmRegDeriv Km s) / (mmRegDen Km s) ^ 2|
      ≤ mmRegEquilLipConst Km Vmax := by
  have hDpos : 0 < mmRegDen Km s := mmRegDen_pos Km hKm s
  have hDhalf : Km / 2 ≤ mmRegDen Km s := mmRegDen_ge_half Km hKm s
  -- Numerator bound: `|mmRegDen Km s − s·mmRegDeriv Km s| ≤ 3·Km/2`.
  have hnum : |mmRegDen Km s - s * mmRegDeriv Km s| ≤ 3 * Km / 2 := by
    rcases le_or_gt 0 s with hs | hs
    · -- On `s ≥ 0`: `mmRegDen = Km + s`, `mmRegDeriv = 1`, difference is exactly `Km`.
      rw [mmRegDen_of_nonneg Km hs, mmRegDeriv, if_pos hs]
      have : Km + s - s * 1 = Km := by ring
      rw [this, abs_of_pos hKm]
      linarith
    · -- On `s < 0`: bound each piece.
      rw [mmRegDeriv, if_neg (not_le.mpr hs)]
      have hDle : mmRegDen Km s ≤ Km := by
        rw [mmRegDen_of_neg Km hs]
        have hexp : Real.exp (2 * s / Km) ≤ 1 := by
          rw [show (1 : ℝ) = Real.exp 0 by simp]
          apply Real.exp_le_exp.mpr
          have : 2 * s / Km < 0 := div_neg_of_neg_of_pos (by linarith) hKm
          linarith
        nlinarith [Real.exp_pos (2 * s / Km)]
      have hgrow : -s * Real.exp (2 * s / Km) ≤ Km / 2 := mmRegDen_neg_growth_le Km hKm hs
      have hgrow_pos : 0 ≤ -s * Real.exp (2 * s / Km) :=
        mul_nonneg (by linarith) (Real.exp_pos _).le
      -- `mmRegDen − s·exp = mmRegDen + (−s·exp)`, both terms nonnegative and bounded.
      have heq : mmRegDen Km s - s * Real.exp (2 * s / Km)
          = mmRegDen Km s + (-s * Real.exp (2 * s / Km)) := by ring
      rw [heq, abs_of_nonneg (by linarith)]
      linarith
  -- Denominator square bound: `(mmRegDen Km s)² ≥ Km²/4`.
  have hDsq : (Km / 2) ^ 2 ≤ (mmRegDen Km s) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hDhalf 2
  have hDsq_pos : 0 < (mmRegDen Km s) ^ 2 := by positivity
  -- Combine.
  rw [abs_div, abs_of_pos hDsq_pos]
  rw [div_le_iff₀ hDsq_pos]
  have hVnum : |Vmax * mmRegDen Km s - Vmax * s * mmRegDeriv Km s|
      ≤ |Vmax| * (3 * Km / 2) := by
    have hfac : Vmax * mmRegDen Km s - Vmax * s * mmRegDeriv Km s
        = Vmax * (mmRegDen Km s - s * mmRegDeriv Km s) := by ring
    rw [hfac, abs_mul]
    exact mul_le_mul_of_nonneg_left hnum (abs_nonneg _)
  -- `|Vmax|·(3Km/2) ≤ (6|Vmax|/Km)·(mmRegDen)²` using `(mmRegDen)² ≥ Km²/4`.
  calc |Vmax * mmRegDen Km s - Vmax * s * mmRegDeriv Km s|
      ≤ |Vmax| * (3 * Km / 2) := hVnum
    _ = mmRegEquilLipConst Km Vmax * ((Km / 2) ^ 2) := by
        rw [mmRegEquilLipConst]; field_simp; ring
    _ ≤ mmRegEquilLipConst Km Vmax * (mmRegDen Km s) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hDsq
        rw [mmRegEquilLipConst]; positivity

/-- **The substrate Lipschitz estimate of the regularized equilibrium level.** Differentiable
everywhere with derivative bounded by `mmRegEquilLipConst Km Vmax`, the equilibrium level satisfies
`|mmRegEquil Km Vmax s − mmRegEquil Km Vmax s'| ≤ mmRegEquilLipConst Km Vmax · |s − s'|` for every
pair of substrate values, by the mean value theorem on the segment between them. -/
lemma mmRegEquil_lipschitz (Km Vmax : ℝ) (hKm : 0 < Km) (s s' : ℝ) :
    |mmRegEquil Km Vmax s - mmRegEquil Km Vmax s'|
      ≤ mmRegEquilLipConst Km Vmax * |s - s'| := by
  have hLnonneg : 0 ≤ mmRegEquilLipConst Km Vmax := by rw [mmRegEquilLipConst]; positivity
  -- The mean value inequality from the global derivative bound, on `univ` (convex).
  have hbound : ∀ x ∈ univ, ‖deriv (mmRegEquil Km Vmax) x‖ ≤ mmRegEquilLipConst Km Vmax := by
    intro x _
    rw [Real.norm_eq_abs, (mmRegEquil_hasDerivAt Km Vmax hKm x).deriv]
    exact mmRegEquil_deriv_le Km Vmax hKm x
  have hdiff : ∀ x ∈ (univ : Set ℝ), DifferentiableAt ℝ (mmRegEquil Km Vmax) x :=
    fun x _ => (mmRegEquil_hasDerivAt Km Vmax hKm x).differentiableAt
  have hlip := Convex.norm_image_sub_le_of_norm_deriv_le (f := mmRegEquil Km Vmax)
    (s := (univ : Set ℝ)) hdiff hbound convex_univ (mem_univ s') (mem_univ s)
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at hlip

/-- **The explicit substrate-Lipschitz constant of the regularized fast field**
`mmRegFastFieldLipConst rate Km Vmax = rate·6·|Vmax|/Km`, i.e. `rate · mmRegEquilLipConst Km Vmax`. -/
noncomputable def mmRegFastFieldLipConst (rate Km Vmax : ℝ) : ℝ :=
  rate * mmRegEquilLipConst Km Vmax

/-- The explicit fast-field Lipschitz constant is non-negative for `0 ≤ rate` and `0 < Km`. -/
lemma mmRegFastFieldLipConst_nonneg (rate Km Vmax : ℝ) (hrate : 0 ≤ rate) (hKm : 0 < Km) :
    0 ≤ mmRegFastFieldLipConst rate Km Vmax := by
  rw [mmRegFastFieldLipConst, mmRegEquilLipConst]
  positivity

/-- **The discharged substrate-Lipschitz hypothesis of the regularized fast field.** Since the field
depends on the substrate only through the additive target `mmRegEquil Km Vmax s · e0`, the `z` term
cancels in any difference at a common state, leaving
`‖mmRegFastField rate Km Vmax s z − mmRegFastField rate Km Vmax s' z‖
  = rate · |mmRegEquil Km Vmax s − mmRegEquil Km Vmax s'|`, which the equilibrium Lipschitz estimate
bounds by `mmRegFastFieldLipConst rate Km Vmax · dist s s'`. This is the exact shape of the `hlip`
hypothesis of `CRNT.Dynamics.MichaelisMentenCoupledContraction`, now a theorem with an explicit
constant in the model parameters. -/
theorem mmRegFastField_substrate_lipschitz (rate Km Vmax : ℝ) (hrate : 0 ≤ rate) (hKm : 0 < Km)
    (s s' : ℝ) (z : E) :
    ‖mmRegFastField rate Km Vmax s z - mmRegFastField rate Km Vmax s' z‖
      ≤ mmRegFastFieldLipConst rate Km Vmax * dist s s' := by
  -- The complex state cancels: the difference is `rate · (mmRegEquil s − mmRegEquil s') • e0`.
  have hdiff : mmRegFastField rate Km Vmax s z - mmRegFastField rate Km Vmax s' z
      = (rate * (mmRegEquil Km Vmax s - mmRegEquil Km Vmax s')) • e0 := by
    simp only [mmRegFastField, smul_sub, smul_smul]
    module
  rw [hdiff, norm_smul_e0, mmRegFastFieldLipConst, Real.dist_eq]
  rw [abs_mul, abs_of_nonneg hrate, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mmRegEquil_lipschitz Km Vmax hKm s s') hrate

/-- **The end-to-end certified horizon-uniform Michaelis–Menten tracking ceiling.** Feeding the
explicit substrate-Lipschitz bound `mmRegFastField_substrate_lipschitz` as the discharged `hlip` into
`mmReg_coupled_tracking_ceiling_unconditional`, the transverse gap obeys the time-uniform `O(ε)`
ceiling `‖x t − m t‖ ≤ ‖x 0 − m 0‖ + (L/rate)·(ε·G)/rate` with
`L = mmRegFastFieldLipConst rate Km Vmax`, for all `t ≥ 0`. The only remaining hypotheses are
`0 < rate`, `0 < Km`, `0 ≤ ε`, and the physical drift bound `‖g‖ ≤ G`. -/
theorem mmReg_coupled_tracking_ceiling_certified (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ)
    (hKm : 0 < Km) {ε G : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G)
    {g : ℝ → E → ℝ} (hg : ∀ a b, ‖g a b‖ ≤ G) {x : ℝ → E} {s : ℝ → ℝ} {z : ℝ → E}
    (hx : ∀ t, HasDerivAt x (mmRegFastField rate Km Vmax (s t) (x t)) t)
    (hs : ∀ τ, HasDerivAt s (mmRegSlowDrift ε g (s τ) (z τ)) τ) :
    ∀ t, 0 ≤ t →
      ‖x t - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s t)‖
        ≤ ‖x 0 - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s 0)‖
          + (mmRegFastFieldLipConst rate Km Vmax / rate) * (ε * G) / rate :=
  mmReg_coupled_tracking_ceiling_unconditional rate hrate Km Vmax hKm
    (mmRegFastFieldLipConst_nonneg rate Km Vmax hrate.le hKm) hε hG
    (fun a b w => mmRegFastField_substrate_lipschitz rate Km Vmax hrate.le hKm a b w) hg hx hs

/-- **The end-to-end certified horizon-uniform Michaelis–Menten reduction.** Feeding the explicit
substrate-Lipschitz bound into `mmCertifiedUniformReduction_unconditional`, the all-time confinements
together with the horizon-uniform `O(ε)` tracking field for the genuine ε-coupled flow with the
substrate-Lipschitz hypothesis discharged. The tracking constant
`C = ‖x 0 − m 0‖ + (L/rate)·(ε·G)/rate` with `L = mmRegFastFieldLipConst rate Km Vmax` is `O(ε)` and
horizon-uniform. The only remaining hypotheses are `0 < rate`, `0 < Km`, `0 ≤ Vmax`, `0 ≤ s₀`,
`0 ≤ ε`, and the physical drift bound `‖g‖ ≤ G`. -/
theorem mmCertifiedUniformReduction_certified (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ)
    (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ} (hs0 : 0 ≤ s₀) {ε G : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G)
    {g : ℝ → E → ℝ} (hg : ∀ a b, ‖g a b‖ ≤ G) {x : ℝ → E} {z : ℝ → E}
    (hx : ∀ t, HasDerivAt x
      (mmRegFastField rate Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t) (x t)) t)
    (hs : ∀ τ, HasDerivAt (mmSubstrate Km Vmax hKm hV s₀)
      (mmRegSlowDrift ε g (mmSubstrate Km Vmax hKm hV s₀ τ) (z τ)) τ) :
    mmCertifiedUniformReduction rate hrate Km Vmax hKm hV s₀ ε G
      (mmRegFastFieldLipConst rate Km Vmax) x (mmSubstrate Km Vmax hKm hV s₀) :=
  mmCertifiedUniformReduction_unconditional rate hrate Km Vmax hKm hV hs0
    (mmRegFastFieldLipConst_nonneg rate Km Vmax hrate.le hKm) hε hG
    (fun a b w => mmRegFastField_substrate_lipschitz rate Km Vmax hrate.le hKm a b w) hg hx hs

end CRNT.MichaelisMenten

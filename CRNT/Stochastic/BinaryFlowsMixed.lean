import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CRNT.Equilibria.ComplexBalanced

/-!
# The mixed case of binary networks with flows: the two new ingredients

`docs/notes/binary-flows-mixed-complex-balanced.md` proves ergodicity of a binary weakly reversible
network with all flows when the union of its all-two-molecule linkage classes is complex balanced.
The proof needs two facts beyond `CRNT.Stochastic.BinaryFlowsEntropy`; this module proves them.

1. **The per-reaction bound** (`f_le_zero_of_nonneg`, `f_le_eps_sq`): for the quantity
   `f = λ L + κζ (1 − e^L)` with `0 ≤ λ ≤ κζ`,
   * `f ≤ 0` if `L ≥ 0`;
   * `f ≤ κζ ε²` if `L < 0` and `λ ≥ κζ (1 − ε)`, `0 ≤ ε < 1`.
   For a source `2Sᵢ` one has `ε = 1/xᵢ` and `ζ = xᵢ²`, so `f ≤ κ`, uniformly in `L`. The proof
   is the tangent line of `exp` at `−t₀ = log(1 − ε)` together with `−log(1 − ε) ≥ ε`.
2. **The complex-balance identity** (`sum_balance_eq_zero`): if the weights `w_y` balance the
   reaction graph at every complex (`∑_{y_r = y} κ_r w_y = ∑_{y'_r = y} κ_r w_{y_r}`), then
   `∑_r κ_r (w_{y_r} u_{y_r} − w_{y_r} u_{y'_r}) = 0` for every `u`. With `w_y = c^y` and
   `u_y = ζ_y / c^y` this is `∑_r κ_r (ζ_{y_r} − c^{y_r} u_{y'_r}) = 0`.
-/

namespace CRNT
namespace BinaryFlowsMixed

/-- **The per-reaction bound for an ascending reaction**: `λ L + κζ (1 − e^L) ≤ 0` when `L ≥ 0`,
`κζ ≥ 0` and `λ ≤ κζ`. -/
theorem f_le_zero_of_nonneg {κζ lam L : ℝ} (hκ : 0 ≤ κζ) (hlam : lam ≤ κζ) (hL : 0 ≤ L) :
    lam * L + κζ * (1 - Real.exp L) ≤ 0 := by
  have h1 : lam * L ≤ κζ * L := mul_le_mul_of_nonneg_right hlam hL
  have h2 : L + 1 ≤ Real.exp L := Real.add_one_le_exp L
  have h3 : κζ * (L + 1 - Real.exp L) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ (by linarith)
  nlinarith [h1, h3]

/-- **The per-reaction bound for a descending reaction**: if `L < 0`, `κζ ≥ 0`,
`κζ (1 − ε) ≤ λ` and `0 ≤ ε < 1`, then `λ L + κζ (1 − e^L) ≤ κζ ε²`. -/
theorem f_le_eps_sq {κζ lam L ε : ℝ} (hκζ : 0 ≤ κζ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hlam : κζ * (1 - ε) ≤ lam) (hL : L < 0) :
    lam * L + κζ * (1 - Real.exp L) ≤ κζ * ε ^ 2 := by
  have h1e : 0 < 1 - ε := by linarith
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, t₀ = -Real.log (1 - ε) := ⟨_, rfl⟩
  -- `t₀ ≥ ε`
  have hlog := Real.log_le_sub_one_of_pos h1e
  have ht₀ε : ε ≤ t₀ := by rw [ht₀]; linarith
  -- `e^{t₀} (1 − ε) = 1`
  have hmul : Real.exp t₀ * (1 - ε) = 1 := by
    rw [ht₀, Real.exp_neg, Real.exp_log h1e, inv_mul_cancel₀ h1e.ne']
  -- the tangent line at `−t₀`: `(L + t₀ + 1)(1 − ε) ≤ e^L`
  have htan : (L + t₀ + 1) * (1 - ε) ≤ Real.exp L := by
    have h := Real.add_one_le_exp (L + t₀)
    rw [Real.exp_add] at h
    have h' := mul_le_mul_of_nonneg_right h h1e.le
    have e : Real.exp L * Real.exp t₀ * (1 - ε) = Real.exp L := by
      rw [mul_assoc, hmul, mul_one]
    linarith
  have hin : (1 - ε) * L + 1 - Real.exp L ≤ ε ^ 2 := by
    nlinarith [htan, mul_nonneg h1e.le (sub_nonneg.mpr ht₀ε)]
  have h1 : lam * L ≤ κζ * (1 - ε) * L := mul_le_mul_of_nonpos_right hlam hL.le
  calc lam * L + κζ * (1 - Real.exp L) ≤ κζ * (1 - ε) * L + κζ * (1 - Real.exp L) := by linarith
    _ = κζ * ((1 - ε) * L + 1 - Real.exp L) := by ring
    _ ≤ κζ * ε ^ 2 := mul_le_mul_of_nonneg_left hin hκζ

/-- **The source `2Sᵢ`**: with `ζ = x²`, `λ = κ x (x − 1)` and `ε = 1/x` (`x ≥ 2`), the
descending bound is the constant `κ`. -/
theorem f_le_rate_of_double {κ x L : ℝ} (hκ : 0 ≤ κ) (hx : 2 ≤ x) (hL : L < 0) :
    κ * (x * (x - 1)) * L + κ * x ^ 2 * (1 - Real.exp L) ≤ κ := by
  have hx0 : 0 < x := by linarith
  have hxne : x ≠ 0 := hx0.ne'
  have hx1 : x * (1 / x) = 1 := mul_one_div_cancel hxne
  have hlam : κ * x ^ 2 * (1 - 1 / x) = κ * (x * (x - 1)) := by
    linear_combination (-(κ * x)) * hx1
  have h := f_le_eps_sq (κζ := κ * x ^ 2) (lam := κ * (x * (x - 1))) (L := L) (ε := 1 / x)
    (by positivity) (by positivity) (by rw [div_lt_one hx0]; linarith) (le_of_eq hlam) hL
  have e : κ * x ^ 2 * (1 / x) ^ 2 = κ := by
    linear_combination (κ * (x * (1 / x) + 1)) * hx1
  linarith

/-! ## The complex-balance identity -/

open Finset in
/-- **The complex-balance identity.**  Let `src, tgt : R → C` be the source and target of each
reaction, all lying in `Cs`.  If the weights `w` balance every complex,
`∑_{src r = y} κ r · w y = ∑_{tgt r = y} κ r · w (src r)`, then for every `u`,
`∑_r κ r (w (src r) u (src r) − w (src r) u (tgt r)) = 0`. -/
theorem sum_balance_eq_zero {R C : Type*} [Fintype R] [DecidableEq C] (src tgt : R → C)
    (κ : R → ℝ) (w u : C → ℝ) (Cs : Finset C) (hsrc : ∀ r, src r ∈ Cs) (htgt : ∀ r, tgt r ∈ Cs)
    (hbal : ∀ y ∈ Cs, ∑ r ∈ univ.filter (fun r => src r = y), κ r * w y =
      ∑ r ∈ univ.filter (fun r => tgt r = y), κ r * w (src r)) :
    ∑ r, κ r * (w (src r) * u (src r) - w (src r) * u (tgt r)) = 0 := by
  have e1 : ∑ r, κ r * (w (src r) * u (src r)) =
      ∑ y ∈ Cs, u y * ∑ r ∈ univ.filter (fun r => src r = y), κ r * w y := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := src) (t := Cs) (by intro r _; exact hsrc r)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [(Finset.mem_filter.mp hr).2]
    ring
  have e2 : ∑ r, κ r * (w (src r) * u (tgt r)) =
      ∑ y ∈ Cs, u y * ∑ r ∈ univ.filter (fun r => tgt r = y), κ r * w (src r) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := tgt) (t := Cs) (by intro r _; exact htgt r)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [(Finset.mem_filter.mp hr).2]
    ring
  have split : ∑ r, κ r * (w (src r) * u (src r) - w (src r) * u (tgt r)) =
      ∑ r, κ r * (w (src r) * u (src r)) - ∑ r, κ r * (w (src r) * u (tgt r)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [split, e1, e2, ← Finset.sum_sub_distrib]
  exact Finset.sum_eq_zero fun y hy => by rw [← mul_sub, hbal y hy, sub_self, mul_zero]

/-! ## The identity for a complex-balanced network -/

open Finset in
/-- **Complex balance as weight balance**: a complex-balanced concentration `x` makes the weights
`w y = x^y` balance the reaction graph at every complex. -/
theorem balance_of_isComplexBalanced {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : N.RateConstants) (x : Concentration S) (h : N.IsComplexBalanced κ x) :
    ∀ y ∈ N.complexes,
      ∑ r ∈ univ.filter (fun r => (N.reaction r).source = y), κ.k r * y.massActionMonomial x =
        ∑ r ∈ univ.filter (fun r => (N.reaction r).target = y),
          κ.k r * (N.reaction r).source.massActionMonomial x := by
  intro y hy
  have hb := h y hy
  unfold Network.inflow Network.outflow at hb
  rw [Finset.sum_filter, Finset.sum_filter]
  have hout : ∑ r, (if (N.reaction r).source = y then κ.k r * y.massActionMonomial x else 0) =
      ∑ r, (if (N.reaction r).source = y then N.massActionRate κ r x else 0) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : (N.reaction r).source = y
    · simp only [if_pos hr, Network.massActionRate, hr]
    · rw [if_neg hr, if_neg hr]
  have hin : ∑ r, (if (N.reaction r).target = y then
        κ.k r * (N.reaction r).source.massActionMonomial x else 0) =
      ∑ r, (if (N.reaction r).target = y then N.massActionRate κ r x else 0) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : (N.reaction r).target = y
    · simp only [if_pos hr, Network.massActionRate]
    · rw [if_neg hr, if_neg hr]
  rw [hout, hin]
  exact hb.symm

/-- **The complex-balance identity for a network**: at a complex-balanced `x`, for every function
`u` of the complexes,
`∑_r κ_r (x^{y_r} u_{y_r} − x^{y_r} u_{y'_r}) = 0`. -/
theorem sum_complexBalanced_eq_zero {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : N.RateConstants) (x : Concentration S) (h : N.IsComplexBalanced κ x)
    (u : Complex S → ℝ) :
    ∑ r, κ.k r * ((N.reaction r).source.massActionMonomial x * u (N.reaction r).source -
      (N.reaction r).source.massActionMonomial x * u (N.reaction r).target) = 0 :=
  sum_balance_eq_zero (fun r => (N.reaction r).source) (fun r => (N.reaction r).target) κ.k
    (fun y => y.massActionMonomial x) u N.complexes (N.source_mem_complexes)
    (N.target_mem_complexes) (balance_of_isComplexBalanced N κ x h)

end BinaryFlowsMixed
end CRNT

#print axioms CRNT.BinaryFlowsMixed.f_le_zero_of_nonneg
#print axioms CRNT.BinaryFlowsMixed.f_le_eps_sq
#print axioms CRNT.BinaryFlowsMixed.f_le_rate_of_double
#print axioms CRNT.BinaryFlowsMixed.sum_balance_eq_zero
#print axioms CRNT.BinaryFlowsMixed.sum_complexBalanced_eq_zero

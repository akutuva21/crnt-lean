import CRNT.Theorems.DeficiencyZero.Toric
import CRNT.Deficiency.KernelDimension

/-!
# The dissipation inequality

The relative entropy `relEntropy x* ·` is a **strict Lyapunov function** for mass-action
dynamics: along the vector field `f = Y A_k Ψ`, its directional derivative

```text
⟨∇relEntropy(x), f(x)⟩ = ∑_s (log x_s − log x*_s) · f(x)_s
```

is `≤ 0` (`Network.dissipation_nonpos`), and vanishes exactly at complex-balanced
concentrations (`Network.complexBalanced_of_dissipation_eq_zero` and its converse). This is
the energetic heart of Horn–Jackson; the chain rule (supplied with the dynamical theory)
turns it into `d/dt relEntropy(x(t)) ≤ 0`.

The proof factors through the complex space and is termwise over reactions, mirroring
`Toric.lean`: the only genuinely new ingredient is the scalar inequality
`a·(log b − log a) ≤ b − a` (with equality iff `a = b`), a form of Gibbs' inequality.

-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A scalar Gibbs inequality: `a·(log b − log a) ≤ b − a` for `a, b > 0`. -/
theorem mul_log_sub_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * (Real.log b - Real.log a) ≤ b - a := by
  rw [← Real.log_div hb.ne' ha.ne']
  have hcancel : a * (b / a) = b := by rw [mul_comm]; exact div_mul_cancel₀ b ha.ne'
  calc a * Real.log (b / a) ≤ a * (b / a - 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hb ha)) ha.le
    _ = b - a := by rw [mul_sub, mul_one, hcancel]

/-- The Gibbs inequality is strict off the diagonal: equality `a·(log b − log a) = b − a`
forces `a = b`. -/
theorem eq_of_mul_log_sub_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a * (Real.log b - Real.log a) = b - a) : a = b := by
  by_contra hne
  have hba : b / a ≠ 1 := by
    intro heq; rw [div_eq_one_iff_eq ha.ne'] at heq; exact hne heq.symm
  have hlt : Real.log (b / a) < b / a - 1 := Real.log_lt_sub_one_of_pos (div_pos hb ha) hba
  rw [← Real.log_div hb.ne' ha.ne'] at h
  have hcancel : a * (b / a) = b := by rw [mul_comm]; exact div_mul_cancel₀ b ha.ne'
  have heq2 : a * Real.log (b / a) = a * (b / a - 1) := by rw [h, mul_sub, mul_one, hcancel]
  have := mul_left_cancel₀ ha.ne' heq2
  linarith

/-- Pairing the mass-action vector field against a species covector factors through the
complex space: `∑_s μ_s f(x)_s = ∑_c (A_k Ψ x)_c · ⟨c, μ⟩`. -/
theorem massActionVectorField_pairing (N : Network S) (κ : RateConstants N)
    (x : Concentration S) (μ : S → ℝ) :
    (∑ s, μ s * N.massActionVectorField κ x s)
      = ∑ c, N.kineticMap κ (N.complexMonomialVector x) c * (∑ s, (c.val s : ℝ) * μ s) := by
  simp only [massActionVectorField_eq, complexMap_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun s _ => by ring

/-- Pairing a covector against the kinetic map factors over reactions:
`∑_c (A_k v)_c · g_c = ∑_r κ_r v_{src r} (g_{tgt r} − g_{src r})`. -/
theorem kineticMap_pairing (N : Network S) (κ : RateConstants N)
    (v g : N.ComplexIdx → ℝ) :
    (∑ c, N.kineticMap κ v c * g c)
      = ∑ r : N.R, κ.k r * v (N.sourceIdx r) * (g (N.targetIdx r) - g (N.sourceIdx r)) := by
  simp only [kineticMap_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hsplit : ∀ c : N.ComplexIdx,
      κ.k r * v (N.sourceIdx r) *
          ((if N.targetIdx r = c then (1 : ℝ) else 0) - (if N.sourceIdx r = c then 1 else 0)) * g c
        = κ.k r * v (N.sourceIdx r) *
            ((if N.targetIdx r = c then (1 : ℝ) else 0) * g c
              - (if N.sourceIdx r = c then (1 : ℝ) else 0) * g c) := fun c => by ring
  simp only [hsplit]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, N.sum_ite_one_mul, N.sum_ite_one_mul]

/-- The per-reaction dissipation term is bounded by the corresponding `A_k w`-term. -/
theorem kineticMap_logRatio_term_le (N : Network S) (κ : RateConstants N)
    {v w : N.ComplexIdx → ℝ} (hv : ∀ c, 0 < v c) (hw : ∀ c, 0 < w c) (r : N.R) :
    κ.k r * v (N.sourceIdx r) *
        (Real.log (v (N.targetIdx r)) - Real.log (w (N.targetIdx r))
          - (Real.log (v (N.sourceIdx r)) - Real.log (w (N.sourceIdx r))))
      ≤ κ.k r * w (N.sourceIdx r) *
        (v (N.targetIdx r) / w (N.targetIdx r) - v (N.sourceIdx r) / w (N.sourceIdx r)) := by
  have hcancel : w (N.sourceIdx r) * (v (N.sourceIdx r) / w (N.sourceIdx r)) = v (N.sourceIdx r) := by
    rw [mul_comm]; exact div_mul_cancel₀ _ (hw _).ne'
  have hbase := mul_log_sub_le (div_pos (hv (N.sourceIdx r)) (hw (N.sourceIdx r)))
    (div_pos (hv (N.targetIdx r)) (hw (N.targetIdx r)))
  have hmul := mul_le_mul_of_nonneg_left hbase (hw (N.sourceIdx r)).le
  have hlog : Real.log (v (N.targetIdx r)) - Real.log (w (N.targetIdx r))
      - (Real.log (v (N.sourceIdx r)) - Real.log (w (N.sourceIdx r)))
      = Real.log (v (N.targetIdx r) / w (N.targetIdx r))
        - Real.log (v (N.sourceIdx r) / w (N.sourceIdx r)) := by
    rw [Real.log_div (hv _).ne' (hw _).ne', Real.log_div (hv _).ne' (hw _).ne']
  rw [hlog]
  have hstep : v (N.sourceIdx r) *
        (Real.log (v (N.targetIdx r) / w (N.targetIdx r))
          - Real.log (v (N.sourceIdx r) / w (N.sourceIdx r)))
      ≤ w (N.sourceIdx r) *
        (v (N.targetIdx r) / w (N.targetIdx r) - v (N.sourceIdx r) / w (N.sourceIdx r)) := by
    have hrw : v (N.sourceIdx r) *
          (Real.log (v (N.targetIdx r) / w (N.targetIdx r))
            - Real.log (v (N.sourceIdx r) / w (N.sourceIdx r)))
        = w (N.sourceIdx r) * (v (N.sourceIdx r) / w (N.sourceIdx r) *
            (Real.log (v (N.targetIdx r) / w (N.targetIdx r))
              - Real.log (v (N.sourceIdx r) / w (N.sourceIdx r)))) := by
      rw [← mul_assoc, hcancel]
    rw [hrw]; exact hmul
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left hstep (κ.positive r).le

/-- Tightness of the per-reaction term forces the log-ratio to agree across the reaction. -/
theorem kineticMap_logRatio_term_eq (N : Network S) (κ : RateConstants N)
    {v w : N.ComplexIdx → ℝ} (hv : ∀ c, 0 < v c) (hw : ∀ c, 0 < w c) (r : N.R)
    (heq : κ.k r * v (N.sourceIdx r) *
        (Real.log (v (N.targetIdx r)) - Real.log (w (N.targetIdx r))
          - (Real.log (v (N.sourceIdx r)) - Real.log (w (N.sourceIdx r))))
      = κ.k r * w (N.sourceIdx r) *
        (v (N.targetIdx r) / w (N.targetIdx r) - v (N.sourceIdx r) / w (N.sourceIdx r))) :
    v (N.targetIdx r) / w (N.targetIdx r) = v (N.sourceIdx r) / w (N.sourceIdx r) := by
  have hlog : Real.log (v (N.targetIdx r)) - Real.log (w (N.targetIdx r))
      - (Real.log (v (N.sourceIdx r)) - Real.log (w (N.sourceIdx r)))
      = Real.log (v (N.targetIdx r) / w (N.targetIdx r))
        - Real.log (v (N.sourceIdx r) / w (N.sourceIdx r)) := by
    rw [Real.log_div (hv _).ne' (hw _).ne', Real.log_div (hv _).ne' (hw _).ne']
  rw [hlog, mul_assoc, mul_assoc] at heq
  have h1 := mul_left_cancel₀ (κ.positive r).ne' heq
  -- h1 : v_src * (log φ_t − log φ_s) = w_src * (φ_t − φ_s)
  have h2 : (v (N.sourceIdx r) / w (N.sourceIdx r)) *
      (Real.log (v (N.targetIdx r) / w (N.targetIdx r))
        - Real.log (v (N.sourceIdx r) / w (N.sourceIdx r)))
      = v (N.targetIdx r) / w (N.targetIdx r) - v (N.sourceIdx r) / w (N.sourceIdx r) := by
    rw [div_mul_eq_mul_div, h1, mul_comm (w _), mul_div_assoc, div_self (hw _).ne', mul_one]
  exact (eq_of_mul_log_sub_eq (div_pos (hv _) (hw _)) (div_pos (hv _) (hw _)) h2).symm

/-- **Core dissipation bound (complex space).** If `w` is a positive kernel vector of `A_k`
and `v` is any positive vector, then `∑_c (A_k v)_c (log v_c − log w_c) ≤ 0`. -/
theorem kineticMap_logRatio_nonpos (N : Network S) (κ : RateConstants N)
    {v w : N.ComplexIdx → ℝ} (hv : ∀ c, 0 < v c) (hw : ∀ c, 0 < w c)
    (hcb : N.kineticMap κ w = 0) :
    (∑ c, N.kineticMap κ v c * (Real.log (v c) - Real.log (w c))) ≤ 0 := by
  rw [kineticMap_pairing N κ v fun c => Real.log (v c) - Real.log (w c)]
  have hbound : (∑ r : N.R, κ.k r * w (N.sourceIdx r) *
      (v (N.targetIdx r) / w (N.targetIdx r) - v (N.sourceIdx r) / w (N.sourceIdx r))) = 0 := by
    rw [← kineticMap_pairing N κ w fun c => v c / w c, hcb]; simp
  rw [← hbound]
  exact Finset.sum_le_sum fun r _ => kineticMap_logRatio_term_le N κ hv hw r

/-- **Tightness ⟹ kernel (complex space).** If the dissipation sum vanishes, the log-ratio
is constant across every reaction. -/
theorem kineticMap_logRatio_ratio_eq (N : Network S) (κ : RateConstants N)
    {v w : N.ComplexIdx → ℝ} (hv : ∀ c, 0 < v c) (hw : ∀ c, 0 < w c)
    (hcb : N.kineticMap κ w = 0)
    (hzero : (∑ c, N.kineticMap κ v c * (Real.log (v c) - Real.log (w c))) = 0) :
    ∀ r : N.R, v (N.targetIdx r) / w (N.targetIdx r) = v (N.sourceIdx r) / w (N.sourceIdx r) := by
  have hbound : (∑ r : N.R, κ.k r * w (N.sourceIdx r) *
      (v (N.targetIdx r) / w (N.targetIdx r) - v (N.sourceIdx r) / w (N.sourceIdx r))) = 0 := by
    rw [← kineticMap_pairing N κ w fun c => v c / w c, hcb]; simp
  have hLHS : (∑ r : N.R, κ.k r * v (N.sourceIdx r) *
      (Real.log (v (N.targetIdx r)) - Real.log (w (N.targetIdx r))
        - (Real.log (v (N.sourceIdx r)) - Real.log (w (N.sourceIdx r))))) = 0 := by
    rw [← kineticMap_pairing N κ v fun c => Real.log (v c) - Real.log (w c)]; exact hzero
  -- the gap `bound − term` is nonnegative and sums to zero, so each gap is zero
  have hgap : ∀ r ∈ Finset.univ,
      (0 : ℝ) ≤ (κ.k r * w (N.sourceIdx r) *
          (v (N.targetIdx r) / w (N.targetIdx r) - v (N.sourceIdx r) / w (N.sourceIdx r)))
        - (κ.k r * v (N.sourceIdx r) *
          (Real.log (v (N.targetIdx r)) - Real.log (w (N.targetIdx r))
            - (Real.log (v (N.sourceIdx r)) - Real.log (w (N.sourceIdx r))))) :=
    fun r _ => sub_nonneg.mpr (kineticMap_logRatio_term_le N κ hv hw r)
  have hgapsum : (∑ r : N.R, ((κ.k r * w (N.sourceIdx r) *
          (v (N.targetIdx r) / w (N.targetIdx r) - v (N.sourceIdx r) / w (N.sourceIdx r)))
        - (κ.k r * v (N.sourceIdx r) *
          (Real.log (v (N.targetIdx r)) - Real.log (w (N.targetIdx r))
            - (Real.log (v (N.sourceIdx r)) - Real.log (w (N.sourceIdx r))))))) = 0 := by
    rw [Finset.sum_sub_distrib, hbound, hLHS, sub_zero]
  have heach := (Finset.sum_eq_zero_iff_of_nonneg hgap).mp hgapsum
  intro r
  have hr := heach r (Finset.mem_univ r)
  exact kineticMap_logRatio_term_eq N κ hv hw r (by linarith [hr])

/-- **The dissipation inequality.** `⟨∇relEntropy(x), f(x)⟩ ≤ 0` relative to a positive
complex-balanced reference `x*`. -/
theorem dissipation_nonpos (N : Network S) (κ : RateConstants N) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    (∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) ≤ 0 := by
  have hvpos : ∀ c, 0 < N.complexMonomialVector x c := fun c => by
    rw [complexMonomialVector_apply]; exact Complex.massActionMonomial_pos hx c.val
  have hwpos : ∀ c, 0 < N.complexMonomialVector xstar c := fun c => by
    rw [complexMonomialVector_apply]; exact Complex.massActionMonomial_pos hxs c.val
  have hwker : N.kineticMap κ (N.complexMonomialVector xstar) = 0 :=
    (N.isComplexBalanced_iff_kineticMap κ xstar).mp hcb
  rw [massActionVectorField_pairing]
  have hpair : ∀ c, (∑ s, (c.val s : ℝ) * (Real.log (x s) - Real.log (xstar s)))
      = Real.log (N.complexMonomialVector x c) - Real.log (N.complexMonomialVector xstar c) := by
    intro c
    rw [log_complexMonomialVector N hx, log_complexMonomialVector N hxs, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  simp only [hpair]
  exact kineticMap_logRatio_nonpos N κ hvpos hwpos hwker

/-- **Vanishing dissipation forces complex balance.** Relative to a positive
complex-balanced reference `x*`, if the directional derivative `⟨∇relEntropy(x), f(x)⟩`
vanishes then `x` is complex-balanced. -/
theorem complexBalanced_of_dissipation_eq_zero (N : Network S) (κ : RateConstants N)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hzero : (∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) = 0) :
    N.IsComplexBalanced κ x := by
  have hvpos : ∀ c, 0 < N.complexMonomialVector x c := fun c => by
    rw [complexMonomialVector_apply]; exact Complex.massActionMonomial_pos hx c.val
  have hwpos : ∀ c, 0 < N.complexMonomialVector xstar c := fun c => by
    rw [complexMonomialVector_apply]; exact Complex.massActionMonomial_pos hxs c.val
  have hwker : N.kineticMap κ (N.complexMonomialVector xstar) = 0 :=
    (N.isComplexBalanced_iff_kineticMap κ xstar).mp hcb
  have hpair : ∀ c, (∑ s, (c.val s : ℝ) * (Real.log (x s) - Real.log (xstar s)))
      = Real.log (N.complexMonomialVector x c) - Real.log (N.complexMonomialVector xstar c) := by
    intro c
    rw [log_complexMonomialVector N hx, log_complexMonomialVector N hxs, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  -- transport the vanishing to the complex space
  have hzero' : (∑ c, N.kineticMap κ (N.complexMonomialVector x) c
      * (Real.log (N.complexMonomialVector x c) - Real.log (N.complexMonomialVector xstar c))) = 0 := by
    rw [← hzero, massActionVectorField_pairing N κ x fun s => Real.log (x s) - Real.log (xstar s)]
    exact Finset.sum_congr rfl fun c _ => by rw [hpair]
  have hratio := kineticMap_logRatio_ratio_eq N κ hvpos hwpos hwker hzero'
  -- conclude `log(x/x*) ⊥ S`, then apply the toric inclusion
  refine complexBalanced_of_logRatio_orthogonal N κ hx hxs hcb ?_
  apply mem_orthSum_span
  rintro g ⟨r, rfl⟩
  -- the log-ratio pairing agrees across reaction `r`
  have hgeq : (∑ s, ((N.targetIdx r).val s : ℝ) * (Real.log (x s) - Real.log (xstar s)))
      = ∑ s, ((N.sourceIdx r).val s : ℝ) * (Real.log (x s) - Real.log (xstar s)) := by
    have hlogeq : Real.log (N.complexMonomialVector x (N.targetIdx r))
          - Real.log (N.complexMonomialVector xstar (N.targetIdx r))
        = Real.log (N.complexMonomialVector x (N.sourceIdx r))
          - Real.log (N.complexMonomialVector xstar (N.sourceIdx r)) := by
      have h := hratio r
      rw [← Real.log_div (hvpos _).ne' (hwpos _).ne', ← Real.log_div (hvpos _).ne' (hwpos _).ne']
      rw [h]
    rw [← hpair, ← hpair] at hlogeq; exact hlogeq
  simp only [reactionVector_apply, mul_sub]
  rw [Finset.sum_sub_distrib,
    show (∑ i, (Real.log (x i) - Real.log (xstar i)) * ((N.reaction r).target i : ℝ))
        = ∑ s, ((N.targetIdx r).val s : ℝ) * (Real.log (x s) - Real.log (xstar s)) from
      Finset.sum_congr rfl fun i _ => by simp only [Network.targetIdx]; ring,
    show (∑ i, (Real.log (x i) - Real.log (xstar i)) * ((N.reaction r).source i : ℝ))
        = ∑ s, ((N.sourceIdx r).val s : ℝ) * (Real.log (x s) - Real.log (xstar s)) from
      Finset.sum_congr rfl fun i _ => by simp only [Network.sourceIdx]; ring]
  rw [hgeq, sub_self]

/-- A complex-balanced concentration has vanishing dissipation (the directional derivative
of any relative entropy is zero, since the vector field itself vanishes). -/
theorem dissipation_eq_zero_of_complexBalanced (N : Network S) (κ : RateConstants N)
    {x xstar : Concentration S} (hcb : N.IsComplexBalanced κ x) :
    (∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) = 0 := by
  have hk : N.kineticMap κ (N.complexMonomialVector x) = 0 :=
    (N.isComplexBalanced_iff_kineticMap κ x).mp hcb
  have hf : ∀ s, N.massActionVectorField κ x s = 0 := by
    intro s; rw [massActionVectorField_eq, hk, map_zero]; rfl
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [hf s, mul_zero]

end Network

end CRNT

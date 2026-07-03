import CRNT.Equilibria.CompatibilityClass
import CRNT.Kinetics.Generalized
import CRNT.Stoich.Subspace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Constructing a candidate steady-state pair from a stoichiometric direction

The forward (verdict) direction of the Deficiency One Algorithm — `DOAAffirmsCapacity →
HasMultistationarityCapacity` — must turn a *signature* `(g, sp, μ)` into two distinct positive
steady states in one compatibility class. The signature's sign-compatibility supplies a
stoichiometric vector `w ∈ S(N)` with `SameSign w μ`. This module discharges the **positional half**
of that construction: from such a `w` it builds two distinct positive stoichiometrically-compatible
concentrations whose log-ratio is sign-compatible with `w` (hence with `μ`).

The construction is the additive perturbation `x ≡ 1`, `y = 1 + t·w` for a small `t > 0`: the
difference `t·w` lies in `S(N)` (compatibility), is nonzero (distinctness), and `log(1 + t·w_s)`
shares the sign of `w_s` (since `t > 0` and `log` crosses zero at `1`). It is the constructive
inverse of `signCompatible_logRatio`, which runs the same correspondence from steady states to the
sign-compatible log-ratio.

What remains for the full forward direction is the genuinely analytic core: choosing rate constants
`κ` for which this candidate pair are both mass-action steady states (Feinberg's deficiency-one
existence theorem, 1995).

* `exists_compatible_pair_sameSign_logRatio` — the candidate compatible positive pair.

-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A candidate compatible pair from a stoichiometric direction.** Given a nonzero stoichiometric
vector `w`, there are two distinct positive concentrations in one compatibility class whose log-ratio
is sign-compatible with `w`: take `x ≡ 1` and `y = 1 + t·w` for small `t > 0`. -/
theorem exists_compatible_pair_sameSign_logRatio (N : Network S) {w : S → ℝ}
    (hw : w ∈ N.stoichSubspace) (hw0 : w ≠ 0) :
    ∃ x y : Concentration S, x.Positive ∧ y.Positive ∧ N.StoichCompatible x y ∧ x ≠ y ∧
      SameSign w (fun s => Real.log (y s) - Real.log (x s)) := by
  set t : ℝ := (1 + ∑ s, |w s|)⁻¹ with ht_def
  have hden_pos : 0 < 1 + ∑ s, |w s| :=
    by have := Finset.sum_nonneg (fun s (_ : s ∈ Finset.univ) => abs_nonneg (w s)); linarith
  have ht_pos : 0 < t := by rw [ht_def]; exact inv_pos.mpr hden_pos
  have hbound : ∀ s, t * |w s| < 1 := by
    intro s
    have hle : |w s| ≤ ∑ s, |w s| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (w i)) (Finset.mem_univ s)
    rw [ht_def, inv_mul_eq_div, div_lt_one hden_pos]
    linarith
  have hypos : ∀ s, 0 < 1 + t * w s := by
    intro s
    have h1 : -(t * |w s|) ≤ t * w s := by
      have := neg_abs_le (w s)
      nlinarith [ht_pos.le, abs_nonneg (w s)]
    have h2 := hbound s
    linarith
  refine ⟨fun _ => 1, fun s => 1 + t * w s, fun _ => one_pos, hypos, ?_, ?_, ?_⟩
  · show (fun s => 1 + t * w s) - (fun _ => (1 : ℝ)) ∈ N.stoichSubspace
    have heq : (fun s => 1 + t * w s) - (fun _ => (1 : ℝ)) = t • w := by
      funext s; simp [Pi.smul_apply, smul_eq_mul]
    rw [heq]
    exact N.stoichSubspace.smul_mem t hw
  · intro hxy
    apply hw0
    funext s
    have : (1 : ℝ) = 1 + t * w s := congrFun hxy s
    have : t * w s = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (ne_of_gt ht_pos)
  · intro s
    have harg : (0 : ℝ) < 1 + t * w s := hypos s
    simp only [Real.log_one, sub_zero]
    refine ⟨?_, ?_⟩
    · rw [Real.log_pos_iff harg.le]
      constructor
      · intro hws; nlinarith [ht_pos]
      · intro h1; nlinarith [ht_pos]
    · rw [Real.log_neg_iff harg]
      constructor
      · intro hws; nlinarith [ht_pos]
      · intro h1; nlinarith [ht_pos]

end Network

end CRNT

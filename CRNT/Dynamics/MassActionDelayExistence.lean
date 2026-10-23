import CRNT.Dynamics.DelayMassActionInvariance
import Mathlib.Analysis.ODE.ExistUnique

/-! # Local existence for delayed mass-action systems

This file proves a first-step existence theorem for reaction-specific mass-action delays. It uses
only a positive lower bound on nonzero delays, so that all delayed production on the first interval
is a known forcing term. It makes no global-existence or continuation claim.
-/

namespace CRNT
namespace Network

open Set

set_option maxHeartbeats 2400000

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A continuous history for a finite mass-action delay network gives a solution on a sufficiently
short initial interval, provided every nonzero reaction delay is bounded below by `d`. Zero-delay
reactions are included in the instantaneous polynomial field; positive-delay production is the
known history forcing. The theorem asserts only a local solution, not global continuation. -/
theorem massActionDelay_local_exists_of_delayGap
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (d : ℝ) (hd : 0 < d)
    (hτ : ∀ r, 0 ≤ τ r) (hgap : ∀ r, 0 < τ r → d ≤ τ r)
    (φ : ℝ → Concentration S) (hφ : Continuous φ) (x₀ : Concentration S)
    (hφ₀ : φ 0 = x₀) :
    ∃ h : ℝ, 0 < h ∧ h ≤ d ∧ ∃ x : ℝ → Concentration S,
      (∀ t ≤ 0, x t = φ t) ∧ x 0 = x₀ ∧
      ∀ t ∈ Set.Icc 0 h,
        HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 h) t := by
  classical
  let f : ℝ → Concentration S → Concentration S := fun t u =>
    N.massActionDelayField κ u (fun r => if τ r = 0 then u else φ (t - τ r))
  let B := ‖x₀‖ + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let K := Real.toNNReal (massActionLipschitzConstant
    (N.instantaneousDelayNetwork τ) (N.instantaneousDelayRates τ κ) B)
  have hK : ∀ t, LipschitzOnWith K (f t) (Metric.closedBall x₀ 1) := by
    intro t u hu u' hu'
    have hu0 : u ∈ Metric.closedBall (0 : Concentration S) B := by
      rw [Metric.mem_closedBall, dist_zero_right] at *
      rw [dist_eq_norm] at hu
      have := norm_add_le (u - x₀) x₀
      have heq : u - x₀ + x₀ = u := sub_add_cancel _ _
      rw [heq] at this
      dsimp [B]
      linarith
    have hu'0 : u' ∈ Metric.closedBall (0 : Concentration S) B := by
      rw [Metric.mem_closedBall, dist_zero_right] at *
      rw [dist_eq_norm] at hu'
      have := norm_add_le (u' - x₀) x₀
      have heq : u' - x₀ + x₀ = u' := sub_add_cancel _ _
      rw [heq] at this
      dsimp [B]
      linarith
    have hL := N.massActionDelayField_lipschitzOnWith_zeroDelaySplit κ τ B
      (fun r => φ (t - τ r))
    change edist (N.massActionDelayField κ u
        (fun r => if τ r = 0 then u else φ (t - τ r)))
      (N.massActionDelayField κ u'
        (fun r => if τ r = 0 then u' else φ (t - τ r))) ≤ _
    exact hL hu0 hu'0
  have hcont : Continuous (Function.uncurry f) := by
    apply continuous_pi
    intro s
    change Continuous (fun p : ℝ × Concentration S =>
      ∑ r, κ.k r * ((N.reaction r).source.massActionMonomial
          (if τ r = 0 then p.2 else φ (p.1 - τ r)) *
            ((N.reaction r).target s : ℝ) -
        (N.reaction r).source.massActionMonomial p.2 *
            ((N.reaction r).source s : ℝ)))
    apply continuous_finsetSum
    intro r hr
    by_cases hzero : τ r = 0
    · simp [hzero]
      unfold Complex.massActionMonomial
      fun_prop
    · simp [hzero]
      unfold Complex.massActionMonomial
      fun_prop
  let C : Set (ℝ × Concentration S) := Set.Icc 0 d ×ˢ Metric.closedBall x₀ 1
  have hCcompact : IsCompact C := isCompact_Icc.prod (isCompact_closedBall x₀ 1)
  have hCbdd : BddAbove (Set.image (fun p : ℝ × Concentration S => ‖f p.1 p.2‖) C) := by
    exact hCcompact.bddAbove_image (by
      exact (continuous_norm.comp hcont).continuousOn)
  obtain ⟨M, hM⟩ := hCbdd
  have hM0 : 0 ≤ M := by
    have hmem : (0, x₀) ∈ C := by
      exact ⟨⟨le_rfl, hd.le⟩, Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1)⟩
    have hle := hM (Set.mem_image_of_mem _ hmem)
    exact le_trans (norm_nonneg _) hle
  let L := Real.toNNReal M
  let h := min d (1 / (M + 1))
  have hh : 0 < h := lt_min hd (one_div_pos.mpr (by linarith))
  have hhd : h ≤ d := min_le_left _ _
  have hhM : M * h ≤ 1 := by
    have hhr := min_le_right d (1 / (M + 1))
    have hmul := mul_le_mul_of_nonneg_left hhr hM0
    have hpos : 0 < M + 1 := by linarith
    have hfactor : M * (1 / (M + 1)) ≤ 1 := by
      have heq : M * (1 / (M + 1)) = M / (M + 1) := by ring
      rw [heq, div_le_one hpos]
      linarith
    exact le_trans hmul hfactor
  have hpl : IsPicardLindelof f (tmin := 0) (tmax := h)
      ⟨0, ⟨le_rfl, hh.le⟩⟩ x₀ 1 0 L K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      exact hK t
    · intro u hu
      exact (hcont.comp (continuous_id.prodMk continuous_const)).continuousOn
    · intro t ht u hu
      have hmem : (t, u) ∈ C := ⟨⟨ht.1, le_trans ht.2 hhd⟩, hu⟩
      have hmemb := hM (Set.mem_image_of_mem _ hmem)
      rw [Real.coe_toNNReal M hM0]
      exact hmemb
    · rw [sub_zero, sub_self, max_eq_left hh.le]
      simpa [L, Real.coe_toNNReal M hM0] using hhM
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  let x : ℝ → Concentration S := fun t => if t < 0 then φ t else α t
  have hx0 : x 0 = x₀ := by simp [x, hα0]
  refine ⟨h, hh, hhd, x, ?_, hx0, ?_⟩
  · intro t ht
    by_cases hneg : t < 0
    · simp [x, hneg]
    · have hzero : t = 0 := by linarith
      simp [x, hzero, hα0, hφ₀]
  · intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hxt : x t = α t := by simp [x, not_lt.mpr ht0]
    have hdel : ∀ r, x (t - τ r) = (if τ r = 0 then α t else φ (t - τ r)) := by
      intro r
      by_cases hzero : τ r = 0
      · simp [hzero, hxt]
      · have hpos : 0 < τ r := lt_of_le_of_ne (hτ r) (Ne.symm hzero)
        have harg : t - τ r ≤ 0 := by
          have := hgap r hpos
          linarith [ht.2, hhd]
        by_cases heq : t - τ r < 0
        · simp [hzero, x, heq]
        · have hz : t - τ r = 0 := le_antisymm harg (le_of_not_gt heq)
          simp [hzero, x, hz, hα0, hφ₀]
    have hfield : N.delayField κ τ x t = f t (α t) := by
      have : (fun r => x (t - τ r)) =
          (fun r => if τ r = 0 then α t else φ (t - τ r)) := funext hdel
      change N.massActionDelayField κ (x t) (fun r => x (t - τ r)) = _
      rw [hxt, this]
    have hcong : ∀ s ∈ Set.Icc 0 h, x s = α s := by
      intro s hs
      simp [x, not_lt.mpr hs.1]
    exact (hα t ht).congr_of_mem hcong ht |>.congr_deriv hfield.symm

/-- Every finite family of reaction delays has a positive lower bound for its positive members.
Take the least positive delay, capped by one; when there are no positive delays, any positive
length is allowed. -/
theorem massActionDelay_exists_positive_step (N : Network S) (τ : N.R → ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ r, 0 < τ r → d ≤ τ r := by
  classical
  by_cases hpos : ∃ r, 0 < τ r
  · let P : Finset N.R := Finset.univ.filter fun r => 0 < τ r
    have hP : P.Nonempty := by
      obtain ⟨r, hr⟩ := hpos
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩⟩
    obtain ⟨rmin, hrmin, hmin⟩ := P.exists_min_image τ hP
    refine ⟨min 1 (τ rmin), lt_min (by norm_num) ?_, ?_⟩
    · exact (Finset.mem_filter.mp hrmin).2
    · intro r hr
      have hrP : r ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩
      exact le_trans (min_le_right 1 (τ rmin)) (hmin r hrP)
  · refine ⟨1, by norm_num, ?_⟩
    intro r hr
    exact (hpos ⟨r, hr⟩).elim

/-- **Local existence for arbitrary finite nonnegative-delay mass-action networks.** Every
continuous history with an initial value extends to a solution on some nontrivial first interval.
The solution is asserted only through that first interval; no global existence is claimed. -/
theorem massActionDelay_local_exists
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    (hτ : ∀ r, 0 ≤ τ r) (φ : ℝ → Concentration S) (hφ : Continuous φ)
    (x₀ : Concentration S) (hφ₀ : φ 0 = x₀) :
    ∃ h : ℝ, 0 < h ∧ ∃ x : ℝ → Concentration S,
      (∀ t ≤ 0, x t = φ t) ∧ x 0 = x₀ ∧
      ∀ t ∈ Set.Icc 0 h,
        HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 h) t := by
  obtain ⟨d, hd, hgap⟩ := massActionDelay_exists_positive_step N τ
  obtain ⟨h, hh, hhd, x, hxφ, hx₀, hx⟩ :=
    massActionDelay_local_exists_of_delayGap N κ τ d hd hτ hgap φ hφ x₀ hφ₀
  exact ⟨h, hh, x, hxφ, hx₀, hx⟩

/-- Nonnegative continuous histories produce a locally existing solution that remains in the
nonnegative orthant on its first interval. This combines the first-step Picard–Lindelöf result
with the finite-interval invariance theorem; it does not assert global existence. -/
theorem massActionDelay_local_exists_nonneg_history
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    (hτ : ∀ r, 0 ≤ τ r) (φ : ℝ → Concentration S) (hφ : Continuous φ)
    (hφnonneg : ∀ t ≤ 0, ∀ s, 0 ≤ φ t s) :
    ∃ h : ℝ, 0 < h ∧ ∃ x : ℝ → Concentration S,
      (∀ t ≤ 0, x t = φ t) ∧
      ∀ t ∈ Set.Icc 0 h,
        HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 h) t ∧
        ∀ s, 0 ≤ x t s := by
  obtain ⟨h, hh, x, hxφ, hx₀, hx⟩ :=
    N.massActionDelay_local_exists κ τ hτ φ hφ (φ 0) rfl
  refine ⟨h, hh, x, hxφ, ?_⟩
  intro t ht
  have hhistory : ∀ (r : N.R) s q, q ∈ Set.Icc (0 - τ r) 0 → 0 ≤ x q s := by
    intro r s q hq
    rw [hxφ q hq.2]
    exact hφnonneg q hq.2 s
  have hstart : ∀ s, 0 ≤ x 0 s := by
    intro s
    rw [hxφ 0 le_rfl]
    exact hφnonneg 0 le_rfl s
  have hnonneg := N.delayField_nonneg_of_nonnegative_delays κ τ (le_of_lt hh) hτ hx
    hhistory hstart t ht
  exact ⟨hx t ht, hnonneg⟩

#print axioms CRNT.Network.massActionDelay_local_exists_of_delayGap
#print axioms CRNT.Network.massActionDelay_exists_positive_step
#print axioms CRNT.Network.massActionDelay_local_exists
#print axioms CRNT.Network.massActionDelay_local_exists_nonneg_history

end Network
end CRNT

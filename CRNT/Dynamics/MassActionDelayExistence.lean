import CRNT.Dynamics.DelayMassActionInvariance
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Order.Compact

/-! # Local existence and first-step uniqueness for delayed mass-action systems

This file proves a first-step existence theorem for reaction-specific mass-action delays. It uses
only a positive lower bound on nonzero delays, so that all delayed production on the first interval
is a known forcing term. It makes no global-existence or continuation claim.
-/

namespace CRNT
namespace Network

open Set Filter Topology

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

/-- Two delayed mass-action solutions with the same history and initial state agree throughout
their common first step. Positive-delay reactions sample only the prescribed history on this
interval, while zero-delay reactions form a locally Lipschitz ordinary vector field. No global
Lipschitz assumption or uniqueness premise is needed. -/
theorem massActionDelay_firstStep_unique
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (d T : ℝ)
    (hd : 0 < d) (hT : 0 < T)
    (hτ : ∀ r, 0 ≤ τ r) (hgap : ∀ r, 0 < τ r → d ≤ τ r)
    (φ : ℝ → Concentration S) (x₀ : Concentration S)
    {x y : ℝ → Concentration S}
    (hxhist : ∀ t ≤ 0, x t = φ t) (hyhist : ∀ t ≤ 0, y t = φ t)
    (hx₀ : x 0 = x₀) (hy₀ : y 0 = x₀)
    (hx : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt y (N.delayField κ τ y t) (Set.Icc 0 T) t) :
    ∀ t ∈ Set.Icc 0 (min d T), x t = y t := by
  classical
  let H := min d T
  have hH : 0 < H := lt_min hd hT
  have hHd : H ≤ d := min_le_left _ _
  have hHT : H ≤ T := min_le_right _ _
  let f : ℝ → Concentration S → Concentration S := fun t u =>
    N.massActionDelayField κ u (fun r => if τ r = 0 then u else φ (t - τ r))
  have hxcont : ContinuousOn x (Set.Icc 0 T) := fun t ht => (hx t ht).continuousWithinAt
  have hycont : ContinuousOn y (Set.Icc 0 T) := fun t ht => (hy t ht).continuousWithinAt
  obtain ⟨Bx, hBx⟩ := isCompact_Icc.bddAbove_image (f := fun t => ‖x t‖) hxcont.norm
  obtain ⟨By, hBy⟩ := isCompact_Icc.bddAbove_image (f := fun t => ‖y t‖) hycont.norm
  have hBx0 : 0 ≤ Bx := by
    have hmem : ‖x 0‖ ∈ Set.image (fun t => ‖x t‖) (Set.Icc (0 : ℝ) T) :=
      Set.mem_image_of_mem _ ⟨le_rfl, hT.le⟩
    exact le_trans (norm_nonneg _) (hBx hmem)
  have hBy0 : 0 ≤ By := by
    have hmem : ‖y 0‖ ∈ Set.image (fun t => ‖y t‖) (Set.Icc (0 : ℝ) T) :=
      Set.mem_image_of_mem _ ⟨le_rfl, hT.le⟩
    exact le_trans (norm_nonneg _) (hBy hmem)
  let B := max Bx By
  have hB0 : 0 ≤ B := le_max_of_le_left hBx0
  let K := Real.toNNReal
    (massActionLipschitzConstant (N.instantaneousDelayNetwork τ)
      (N.instantaneousDelayRates τ κ) B)
  have hv : ∀ t ∈ Set.Ico 0 H, LipschitzOnWith K (f t)
      (Metric.closedBall (0 : Concentration S) B) := by
    intro t ht u hu u' hu'
    have hL := N.massActionDelayField_lipschitzOnWith_zeroDelaySplit κ τ B
      (fun r => φ (t - τ r))
    change edist (N.massActionDelayField κ u
        (fun r => if τ r = 0 then u else φ (t - τ r)))
      (N.massActionDelayField κ u'
        (fun r => if τ r = 0 then u' else φ (t - τ r))) ≤ _
    exact hL hu hu'
  have hxBall : ∀ t ∈ Set.Icc 0 H, x t ∈ Metric.closedBall (0 : Concentration S) B := by
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans (hBx (Set.mem_image_of_mem _ ⟨ht.1, ht.2.trans hHT⟩)) (le_max_left _ _)
  have hyBall : ∀ t ∈ Set.Icc 0 H, y t ∈ Metric.closedBall (0 : Concentration S) B := by
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans (hBy (Set.mem_image_of_mem _ ⟨ht.1, ht.2.trans hHT⟩)) (le_max_right _ _)
  have hright : ∀ (g : ℝ → Concentration S)
      (hg : ∀ t ∈ Set.Icc 0 H,
        HasDerivWithinAt g (f t (g t)) (Set.Icc 0 H) t),
      ∀ t ∈ Set.Ico 0 H, HasDerivWithinAt g (f t (g t)) (Set.Ici t) t := by
    intro g hg t ht
    by_cases heq : t = 0
    · subst t
      refine (hg 0 ⟨le_rfl, hH.le⟩).mono_of_mem_nhdsWithin ?_
      refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1) H, isOpen_Ioo, ?_, ?_⟩
      · exact ⟨by norm_num, hH⟩
      · intro z hz
        exact ⟨hz.2, hz.1.2.le⟩
    · have ht' : t ∈ Set.Ioo 0 H := ⟨lt_of_le_of_ne ht.1 (Ne.symm heq), ht.2⟩
      have hnhds : Set.Icc 0 H ∈ 𝓝 t := Icc_mem_nhds ht'.1 ht'.2
      exact (hg t ⟨ht.1, ht.2.le⟩).hasDerivAt hnhds |>.hasDerivWithinAt
  have hfield (g : ℝ → Concentration S) (hhist : ∀ t ≤ 0, g t = φ t)
      (t : ℝ) (ht : t ∈ Set.Icc 0 H) :
      N.delayField κ τ g t = f t (g t) := by
    have hdel : ∀ r, g (t - τ r) = (if τ r = 0 then g t else φ (t - τ r)) := by
      intro r
      by_cases hzero : τ r = 0
      · simp [hzero]
      · have hpos : 0 < τ r := lt_of_le_of_ne (hτ r) (Ne.symm hzero)
        have harg : t - τ r ≤ 0 := by
          have := hgap r hpos
          linarith [ht.2, hHd]
        rw [hhist (t - τ r) harg]
        simp [hzero]
    have : (fun r => g (t - τ r)) =
        (fun r => if τ r = 0 then g t else φ (t - τ r)) := funext hdel
    change N.massActionDelayField κ (g t) (fun r => g (t - τ r)) = _
    rw [this]
  have hx' : ∀ t ∈ Set.Ico 0 H, HasDerivWithinAt x (f t (x t)) (Set.Ici t) t := by
    intro t ht
    have hderiv : ∀ s ∈ Set.Icc 0 H,
        HasDerivWithinAt x (f s (x s)) (Set.Icc 0 H) s := by
      intro s hs
      have hsource := hx s ⟨hs.1, hs.2.trans hHT⟩
      have hsource' := hsource.congr_deriv (hfield x hxhist s hs)
      exact hsource'.mono (by
        intro z hz
        exact ⟨hz.1, hz.2.trans hHT⟩)
    exact hright x hderiv t ht
  have hy' : ∀ t ∈ Set.Ico 0 H, HasDerivWithinAt y (f t (y t)) (Set.Ici t) t := by
    intro t ht
    have hderiv : ∀ s ∈ Set.Icc 0 H,
        HasDerivWithinAt y (f s (y s)) (Set.Icc 0 H) s := by
      intro s hs
      have hsource := hy s ⟨hs.1, hs.2.trans hHT⟩
      have hsource' := hsource.congr_deriv (hfield y hyhist s hs)
      exact hsource'.mono (by
        intro z hz
        exact ⟨hz.1, hz.2.trans hHT⟩)
    exact hright y hderiv t ht
  have hxcont' : ContinuousOn x (Set.Icc 0 H) := hxcont.mono (by
    intro t ht
    exact ⟨ht.1, ht.2.trans hHT⟩)
  have hycont' : ContinuousOn y (Set.Icc 0 H) := hycont.mono (by
    intro t ht
    exact ⟨ht.1, ht.2.trans hHT⟩)
  have heq := ODE_solution_unique_of_mem_Icc_right
    (v := f) (s := fun _ => Metric.closedBall (0 : Concentration S) B) (K := K)
    hv hxcont' hx' (fun t ht => hxBall t ⟨ht.1, ht.2.le⟩)
    hycont' hy' (fun t ht => hyBall t ⟨ht.1, ht.2.le⟩) (hx₀.trans hy₀.symm)
  exact fun t ht => heq ht

/-- **Finite-interval uniqueness for delayed mass-action solutions.** Two solutions with the same
history and initial state agree on every common finite interval. The proof derives the minimum
positive delay from the finite reaction family, then applies local ODE uniqueness successively;
compactness of the two paths supplies each local Lipschitz ball. -/
theorem massActionDelay_solution_unique
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) {T : ℝ}
    (hT : 0 ≤ T) (hτ : ∀ r, 0 ≤ τ r) (φ : ℝ → Concentration S)
    {x y : ℝ → Concentration S}
    (hxhist : ∀ t ≤ 0, x t = φ t) (hyhist : ∀ t ≤ 0, y t = φ t)
    (hx : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt y (N.delayField κ τ y t) (Set.Icc 0 T) t) :
    ∀ t ∈ Set.Icc 0 T, x t = y t := by
  obtain ⟨d, hd, hgap⟩ := massActionDelay_exists_positive_step N τ
  let n : ℕ := Nat.ceil (T / d)
  have hsteps : T ≤ (n : ℝ) * d := by
    have hceil : T / d ≤ (n : ℝ) := Nat.le_ceil _
    have hmul := (div_le_iff₀ hd).mp hceil
    simpa [n] using hmul
  have hall : ∀ k : ℕ, ∀ q ≤ min T ((k : ℝ) * d), x q = y q := by
    intro k
    induction k with
    | zero =>
        intro q hq
        have hmin : min T ((0 : ℕ) * d) = 0 := by simp [hT]
        rw [hmin] at hq
        rw [hxhist q hq, hyhist q hq]
    | succ k ih =>
        intro q hq
        let c : ℝ := min T ((k : ℝ) * d)
        let e : ℝ := min T (((k + 1 : ℕ) : ℝ) * d)
        have hstep : c ≤ e := by
          dsimp [c, e]
          exact min_le_min_left T (by push_cast; nlinarith [hd])
        by_cases hcT : T ≤ c
        · have heq : e = T := by
            apply min_eq_left
            have hTkd : T ≤ (k : ℝ) * d := le_trans hcT (min_le_right _ _)
            have hsucc : (k : ℝ) * d ≤ ((k + 1 : ℕ) : ℝ) * d := by
              push_cast
              nlinarith [hd]
            exact le_trans hTkd hsucc
          have hc_eq : c = T := le_antisymm (min_le_left _ _) hcT
          have hqprev : q ≤ c := by
            have hqT : q ≤ T := le_trans hq (by simpa [heq] using min_le_left T _)
            simpa [hc_eq] using hqT
          exact ih q (by simpa [c] using hqprev)
        · have hc_lt : c < T := lt_of_not_ge hcT
          have hkd : (k : ℝ) * d < T := by
            by_contra hnot
            have hTle : T ≤ (k : ℝ) * d := le_of_not_gt hnot
            have : c = T := min_eq_left hTle
            exact hc_lt.ne this
          have hc_eq : c = (k : ℝ) * d := min_eq_right hkd.le
          have hc0 : 0 ≤ c := by
            dsimp [c]
            positivity
          have he_upper : e ≤ c + d := by
            calc
              e ≤ ((k + 1 : ℕ) : ℝ) * d := min_le_right _ _
              _ = (k : ℝ) * d + d := by push_cast; ring
              _ = c + d := by rw [hc_eq]
          have hdelta : 0 < e - c := by
            rw [hc_eq] at *
            dsimp [e]
            have hsucc : (k : ℝ) * d < ((k + 1 : ℕ) : ℝ) * d := by
              push_cast
              nlinarith [hd]
            have := lt_min hkd hsucc
            linarith
          have hdelta_le : e - c ≤ d := by linarith
          have hprev : ∀ q ≤ c, x q = y q := by
            intro q hq'
            exact ih q (by simpa [c] using hq')
          let xs : ℝ → Concentration S := fun u => x (u + c)
          let ys : ℝ → Concentration S := fun u => y (u + c)
          let ψ : ℝ → Concentration S := xs
          have hψ : ∀ u ≤ 0, ys u = ψ u := by
            intro u hu
            dsimp [ys, ψ, xs]
            exact (hprev (u + c) (by linarith)).symm
          have hxs₀ : xs 0 = x c := by simp [xs]
          have hys₀ : ys 0 = x c := by
            simpa [ys] using (hprev c le_rfl).symm
          have hxs : ∀ u ∈ Set.Icc 0 (e - c),
              HasDerivWithinAt xs (N.delayField κ τ xs u) (Set.Icc 0 (e - c)) u := by
            intro u hu
            have huT : u + c ∈ Set.Icc 0 T := by
              constructor
              · exact add_nonneg hu.1 hc0
              · have : u + c ≤ e := by calc
                  u + c ≤ (e - c) + c := by nlinarith [hu.2]
                  _ = e := by ring
                exact le_trans this (min_le_left T _)
            have htrans : HasDerivWithinAt (fun v : ℝ => v + c) 1
                (Set.Icc 0 (e - c)) u := (hasDerivAt_id u).add_const c |>.hasDerivWithinAt
            have hmap : MapsTo (fun v : ℝ => v + c) (Set.Icc 0 (e - c)) (Set.Icc 0 T) := by
              intro v hv
              constructor
              · exact add_nonneg hv.1 hc0
              · have : v + c ≤ e := by calc
                  v + c ≤ (e - c) + c := by nlinarith [hv.2]
                  _ = e := by ring
                exact le_trans this (min_le_left T _)
            have hcomp := (hx (u + c) huT).scomp u htrans hmap
            have hdelay : N.delayField κ τ xs u = N.delayField κ τ x (u + c) := by
              simp [xs, Network.delayField, massActionDelayField_delayField]
              congr 1
              funext r
              ring
            simpa [xs, Function.comp_def, hdelay] using hcomp
          have hys : ∀ u ∈ Set.Icc 0 (e - c),
              HasDerivWithinAt ys (N.delayField κ τ ys u) (Set.Icc 0 (e - c)) u := by
            intro u hu
            have huT : u + c ∈ Set.Icc 0 T := by
              constructor
              · exact add_nonneg hu.1 hc0
              · have : u + c ≤ e := by calc
                  u + c ≤ (e - c) + c := by nlinarith [hu.2]
                  _ = e := by ring
                exact le_trans this (min_le_left T _)
            have htrans : HasDerivWithinAt (fun v : ℝ => v + c) 1
                (Set.Icc 0 (e - c)) u := (hasDerivAt_id u).add_const c |>.hasDerivWithinAt
            have hmap : MapsTo (fun v : ℝ => v + c) (Set.Icc 0 (e - c)) (Set.Icc 0 T) := by
              intro v hv
              constructor
              · exact add_nonneg hv.1 hc0
              · have : v + c ≤ e := by calc
                  v + c ≤ (e - c) + c := by nlinarith [hv.2]
                  _ = e := by ring
                exact le_trans this (min_le_left T _)
            have hcomp := (hy (u + c) huT).scomp u htrans hmap
            have hdelay : N.delayField κ τ ys u = N.delayField κ τ y (u + c) := by
              simp [ys, Network.delayField, massActionDelayField_delayField]
              congr 1
              funext r
              ring
            simpa [ys, Function.comp_def, hdelay] using hcomp
          have hsame := N.massActionDelay_firstStep_unique κ τ d (e - c)
            hd hdelta hτ hgap ψ (x c)
            (fun _ _ => rfl) hψ hxs₀ hys₀ hxs hys
          have hmin : min d (e - c) = e - c := min_eq_right hdelta_le
          by_cases hqc : q ≤ c
          · exact hprev q hqc
          · have hqge : c ≤ q := le_of_lt (lt_of_not_ge hqc)
            have hqshift : q - c ∈ Set.Icc (0 : ℝ) (e - c) := by
              constructor <;> linarith
            have hq' := hsame (q - c) (by simpa [hmin] using hqshift)
            have heq_q : (q - c) + c = q := sub_add_cancel _ _
            simpa [xs, ys, ψ, heq_q] using hq'
  intro t ht
  have hlast : min T ((n : ℝ) * d) = T := min_eq_left hsteps
  have ht' : t ≤ min T ((n : ℝ) * d) := by simpa [hlast] using ht.2
  exact hall n t ht'

#print axioms CRNT.Network.massActionDelay_local_exists_of_delayGap
#print axioms CRNT.Network.massActionDelay_exists_positive_step
#print axioms CRNT.Network.massActionDelay_local_exists
#print axioms CRNT.Network.massActionDelay_local_exists_nonneg_history
#print axioms CRNT.Network.massActionDelay_firstStep_unique
#print axioms CRNT.Network.massActionDelay_solution_unique

end Network
end CRNT

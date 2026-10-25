import CRNT.Geometry.EndotacticGlobal
import CRNT.Persistence.StronglyEndotacticConsequences
import CRNT.Stochastic.FosterRecurrence

/-!
# A strongly endotactic network without positive recurrence

This module formalizes, for leaf **P7** of `docs/field-map.md`, Example 3.1 of
Anderson–Cappelletti–Kim–Nguyen (*Tier structure of strongly endotactic reaction networks*,
Stoch. Proc. Appl. 130 (2020); arXiv:1808.05328):

`0 → 2A + B → 4A + 4B → A`   (reactions `0, 1, 2`).

* The network is **strongly endotactic** (`stronglyEndotacticStd`), hence deterministically
  permanent (`structurallyPermanent`, from the repository's GMS theorem).
* Its stochastic model is **not positive recurrent**, for every choice of rate constants.  From a
  count `(a, 0)` the embedded jump chain can run the cycle
  `(a, 0) → (a + 2, 1) → (a + 4, 4) → (a + 1, 0)` forever, each cycle adding one molecule of `A`.
  The cycle is followed with probability `1 − O(1/a²)`, so for `a` large the probability of
  following it for `k` cycles is at least `1/2` uniformly in `k` (`survival_three_mul_ge_half`).
  Hence, for every **finite** set of counts `K`, the chain started far enough out avoids `K`
  forever with probability at least `1/2` (`survival_not_tendsto_zero`), and no Foster drift
  certificate `PV ≤ V − ε` off `K` exists (`no_foster_certificate`).

So "every strongly endotactic stochastic mass-action system is positive recurrent" is false; the
field map's earlier P7 target is refuted by a formal proof rather than only by citation.

## The bound

Write `X(a) = (a + 1)(a + 2)`.  The three jump probabilities along the cycle are
`p₀ = 1` (at `(a, 0)` only `0 → 2A + B` is enabled),
`p₁ ≥ 1 − c₁ / X(a)` with `c₁ = κ₀/κ₁`, and `p₂ ≥ 1 − c₂ / X(a)` with
`c₂ = (κ₀ + 64 κ₁)/(12 κ₂)`.  With `D = c₁ + c₂` and `1/X(a) = 1/(a+1) − 1/(a+2)`, induction on
the number of cycles gives the telescoped bound

`survival(3k, (a, 0)) ≥ 1 − D (1/(a + 1) − 1/(a + 1 + k))`

for `a ≥ ⌈2D⌉`, and the right-hand side is at least `1/2`.
-/

namespace CRNT
namespace Examples
namespace ACKTransient

open Network Foster Filter Topology

/-! ## The network -/

/-- ACK's Example 3.1: `0 → 2A + B`, `2A + B → 4A + 4B`, `4A + 4B → A` (species `A = 0`,
`B = 1`). -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 3, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![0, 0], ![2, 1]⟩ else if r = 1 then ⟨![2, 1], ![4, 4]⟩
    else ⟨![4, 4], ![1, 0]⟩⟩

theorem src0 : (net.reaction 0).source = ![0, 0] := rfl
theorem src1 : (net.reaction 1).source = ![2, 1] := rfl
theorem src2 : (net.reaction 2).source = ![4, 4] := rfl

/-! ## Strong endotacticity -/

theorem endotactic : net.Endotactic := by
  intro w r hmax
  fin_cases r
  · have h1 := hmax 1
    simp [Network.wValue, Network.wRate, Network.dotProduct, Network.reactionVector_apply,
      exponentVector, Fin.sum_univ_two] at h1 ⊢ <;> linarith
  · have h2 := hmax 2
    simp [Network.wValue, Network.wRate, Network.dotProduct, Network.reactionVector_apply,
      exponentVector, Fin.sum_univ_two] at h2 ⊢ <;> linarith
  · have h0 := hmax 0
    have h1 := hmax 1
    simp [Network.wValue, Network.wRate, Network.dotProduct, Network.reactionVector_apply,
      exponentVector, Fin.sum_univ_two] at h0 h1 ⊢ <;> linarith

/-- If both weights vanish, every `w`-rate vanishes. -/
theorem wRate_eq_zero_of_zero {w : Fin 2 → ℝ} (h0 : w 0 = 0) (h1 : w 1 = 0) (r : net.R) :
    net.wRate w r = 0 := by
  fin_cases r <;>
    simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, Fin.sum_univ_two, h0, h1]

/-- **The network is strongly endotactic.**  With `v₁ = 2w₀ + w₁` and `v₂ = 4w₀ + 4w₁` the
`w`-values of the sources `2A + B` and `4A + 4B` (the source `0` has value `0`): if `4A + 4B` is
`w`-maximal its reaction descends strictly unless `w = 0`; otherwise, if `2A + B` is maximal it
is strictly above `4A + 4B` and its reaction descends strictly; otherwise `0` is the strict
maximum and `0 → 2A + B` descends strictly. -/
theorem stronglyEndotacticStd : net.StronglyEndotacticStd := by
  refine ⟨endotactic, ?_⟩
  intro w hactive
  by_cases hA : 0 ≤ 4 * w 0 + 4 * w 1 ∧ 2 * w 0 + w 1 ≤ 4 * w 0 + 4 * w 1
  · obtain ⟨hA1, hA2⟩ := hA
    refine ⟨2, ?_, ?_⟩
    · intro r'
      fin_cases r' <;>
        simp [Network.wValue, Network.dotProduct, exponentVector, Fin.sum_univ_two] <;> linarith
    · have hrate : net.wRate w 2 = -3 * w 0 - 4 * w 1 := by
        simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, Fin.sum_univ_two] <;>
          ring
      rw [hrate]
      by_contra hc
      have hc' : 0 ≤ -3 * w 0 - 4 * w 1 := le_of_not_gt hc
      have hw0 : w 0 = 0 := by linarith
      have hw1 : w 1 = 0 := by linarith
      obtain ⟨r, hr⟩ := hactive
      exact hr (wRate_eq_zero_of_zero hw0 hw1 r)
  · by_cases hB : 0 ≤ 2 * w 0 + w 1 ∧ 4 * w 0 + 4 * w 1 ≤ 2 * w 0 + w 1
    · obtain ⟨hB1, hB2⟩ := hB
      refine ⟨1, ?_, ?_⟩
      · intro r'
        fin_cases r' <;>
          simp [Network.wValue, Network.dotProduct, exponentVector, Fin.sum_univ_two] <;> linarith
      · have hrate : net.wRate w 1 = 2 * w 0 + 3 * w 1 := by
          simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, Fin.sum_univ_two] <;>
            ring
        rw [hrate]
        by_contra hc
        have hc' : 0 ≤ 2 * w 0 + 3 * w 1 := le_of_not_gt hc
        exact hA ⟨by linarith, by linarith⟩
    · have hv1 : 2 * w 0 + w 1 < 0 := by
        by_contra hc
        have hc' : 0 ≤ 2 * w 0 + w 1 := le_of_not_gt hc
        by_cases hle : 4 * w 0 + 4 * w 1 ≤ 2 * w 0 + w 1
        · exact hB ⟨hc', hle⟩
        · exact hA ⟨by linarith, by linarith⟩
      have hv2 : 4 * w 0 + 4 * w 1 < 0 := by
        by_contra hc
        have hc' : 0 ≤ 4 * w 0 + 4 * w 1 := le_of_not_gt hc
        exact hA ⟨hc', by linarith⟩
      refine ⟨0, ?_, ?_⟩
      · intro r'
        fin_cases r' <;>
          simp [Network.wValue, Network.dotProduct, exponentVector, Fin.sum_univ_two] <;> linarith
      · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, Fin.sum_univ_two] <;>
          linarith

/-- **The deterministic model is permanent** (Gopalkrishnan–Miller–Shiu, via the repository's
strongly endotactic permanence theorem). -/
theorem structurallyPermanent : net.StructurallyPermanent :=
  strongEndotacticStdPermanenceClaim net stronglyEndotacticStd

/-! ## Counts, propensities and the cycle -/

/-- The count `(a, b)`. -/
def mk2 (a b : ℕ) : Fin 2 → ℕ := ![a, b]

variable (κ : net.RateConstants)

theorem rate_eq (n : Fin 2 → ℕ) (r : net.R) :
    net.stochasticMassActionRate κ n r =
      κ.k r * (((n 0).descFactorial ((net.reaction r).source 0) : ℝ) *
        ((n 1).descFactorial ((net.reaction r).source 1) : ℝ)) := by
  unfold stochasticMassActionRate
  rw [Fin.prod_univ_two]

theorem rate0 (n : Fin 2 → ℕ) : net.stochasticMassActionRate κ n 0 = κ.k 0 := by
  rw [rate_eq, src0]
  simp

theorem rate1_X0 (a : ℕ) : net.stochasticMassActionRate κ (mk2 a 0) 1 = 0 := by
  rw [rate_eq, src1]
  simp [mk2]

theorem rate2_X0 (a : ℕ) : net.stochasticMassActionRate κ (mk2 a 0) 2 = 0 := by
  rw [rate_eq, src2]
  simp [mk2]

theorem rate2_X1 (a : ℕ) : net.stochasticMassActionRate κ (mk2 (a + 2) 1) 2 = 0 := by
  rw [rate_eq, src2]
  have h : (1 : ℕ).descFactorial 4 = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by norm_num)
  simp [mk2, h]

theorem desc2 (a : ℕ) : (a + 2).descFactorial 2 = (a + 2) * (a + 1) := by
  rw [Nat.descFactorial_succ, Nat.descFactorial_one, show a + 2 - 1 = a + 1 by omega]
  ring

theorem rate1_X1 (a : ℕ) :
    net.stochasticMassActionRate κ (mk2 (a + 2) 1) 1 = κ.k 1 * (((a : ℝ) + 2) * ((a : ℝ) + 1)) := by
  rw [rate_eq, src1]
  simp only [mk2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [desc2, Nat.descFactorial_one]
  push_cast <;> ring

theorem rate1_X2_le (a : ℕ) :
    net.stochasticMassActionRate κ (mk2 (a + 4) 4) 1 ≤ 4 * κ.k 1 * ((a : ℝ) + 4) ^ 2 := by
  rw [rate_eq, src1]
  simp only [mk2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [Nat.descFactorial_one]
  have h : (((a + 4).descFactorial 2 : ℕ) : ℝ) ≤ ((a : ℝ) + 4) ^ 2 := by
    exact_mod_cast Nat.descFactorial_le_pow (a + 4) 2
  have hk := κ.positive 1
  have := mul_le_mul_of_nonneg_left h hk.le
  have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  rw [h4]
  linarith [this]

theorem rate2_X2_ge (a : ℕ) :
    24 * κ.k 2 * ((a : ℝ) + 1) ^ 4 ≤ net.stochasticMassActionRate κ (mk2 (a + 4) 4) 2 := by
  rw [rate_eq, src2]
  simp only [mk2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have h44 : (4 : ℕ).descFactorial 4 = 24 := by decide
  rw [h44]
  have hlow : ((a : ℝ) + 1) ^ 4 ≤ (((a + 4).descFactorial 4 : ℕ) : ℝ) := by
    have h := Nat.pow_sub_le_descFactorial (a + 4) 4
    rw [show a + 4 + 1 - 4 = a + 1 by omega] at h
    exact_mod_cast h
  have hk := κ.positive 2
  have := mul_le_mul_of_nonneg_left hlow hk.le
  have h24 : ((24 : ℕ) : ℝ) = 24 := by norm_num
  rw [h24]
  linarith [this]

theorem exitRate_eq (x : Fin 2 → ℕ) :
    net.exitRate κ x = net.stochasticMassActionRate κ x 0 +
      net.stochasticMassActionRate κ x 1 + net.stochasticMassActionRate κ x 2 := by
  unfold Network.exitRate
  exact Fin.sum_univ_three _

theorem exitRate_pos (x : Fin 2 → ℕ) : 0 < net.exitRate κ x := by
  rw [exitRate_eq, rate0]
  have h1 := net.stochasticMassActionRate_nonneg κ x 1
  have h2 := net.stochasticMassActionRate_nonneg κ x 2
  linarith [κ.positive 0]

theorem not_hold (x : Fin 2 → ℕ) : ¬ (net.jumpChain κ).hold x :=
  fun h => (exitRate_pos κ x).ne' h

theorem nx0 (a : ℕ) : (net.jumpChain κ).next (mk2 a 0) 0 = mk2 (a + 2) 1 := by
  show net.jumpNextCount _ _ = _
  funext i; fin_cases i <;> simp [mk2, jumpNextCount]

theorem nx1 (a : ℕ) : (net.jumpChain κ).next (mk2 (a + 2) 1) 1 = mk2 (a + 4) 4 := by
  show net.jumpNextCount _ _ = _
  funext i; fin_cases i <;> simp [mk2, jumpNextCount]

theorem nx2 (a : ℕ) : (net.jumpChain κ).next (mk2 (a + 4) 4) 2 = mk2 (a + 1) 0 := by
  show net.jumpNextCount _ _ = _
  funext i; fin_cases i <;> simp [mk2, jumpNextCount]

/-! ## A lower bound for the survival function -/

/-- **One step of the survival recursion**: following a particular jump `r` out of `x` (with
`next x r ∉ C`) is one of the terms of `survival (k + 1) x`. -/
theorem survival_succ_ge {X R : Type*} [Fintype R] (M : FiniteBranchChain X R) (C : Set X)
    [DecidablePred M.hold] [DecidablePred (· ∈ C)] (k : ℕ) (x : X) (r : R)
    (hx : ¬ M.hold x) (hn : M.next x r ∉ C) :
    M.p x r * M.survival C k (M.next x r) ≤ M.survival C (k + 1) x := by
  show _ ≤ M.killed C (M.survival C k) x
  unfold FiniteBranchChain.killed
  rw [if_neg hx]
  have hle := Finset.single_le_sum (f := fun r' => M.p x r' *
      (if M.next x r' ∈ C then 0 else M.survival C k (M.next x r')))
    (fun r' _ => mul_nonneg (M.p_nonneg x r')
      (by split_ifs <;> [exact le_rfl; exact M.survival_nonneg C k _]))
    (Finset.mem_univ r)
  simp only [if_neg hn] at hle
  exact hle

/-- **The cycle bound**: `p₀ p₁ p₂ · survival(k, (a+1, 0)) ≤ survival(k + 3, (a, 0))`. -/
theorem cycle_ge (C : Set (Fin 2 → ℕ)) [DecidablePred (· ∈ C)] (a k : ℕ)
    (h1 : mk2 (a + 2) 1 ∉ C) (h2 : mk2 (a + 4) 4 ∉ C) (h3 : mk2 (a + 1) 0 ∉ C) :
    (net.jumpChain κ).p (mk2 a 0) 0 * ((net.jumpChain κ).p (mk2 (a + 2) 1) 1 *
      ((net.jumpChain κ).p (mk2 (a + 4) 4) 2 * (net.jumpChain κ).survival C k (mk2 (a + 1) 0))) ≤
      (net.jumpChain κ).survival C (k + 3) (mk2 a 0) := by
  have s3 := survival_succ_ge (net.jumpChain κ) C k (mk2 (a + 4) 4) 2 (not_hold κ _)
    (by rw [nx2]; exact h3)
  rw [nx2] at s3
  have s2 := survival_succ_ge (net.jumpChain κ) C (k + 1) (mk2 (a + 2) 1) 1 (not_hold κ _)
    (by rw [nx1]; exact h2)
  rw [nx1] at s2
  have s1 := survival_succ_ge (net.jumpChain κ) C (k + 1 + 1) (mk2 a 0) 0 (not_hold κ _)
    (by rw [nx0]; exact h1)
  rw [nx0] at s1
  have hp0 := (net.jumpChain κ).p_nonneg (mk2 a 0) 0
  have hp1 := (net.jumpChain κ).p_nonneg (mk2 (a + 2) 1) 1
  have t1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left s3 hp1) hp0
  have t2 := mul_le_mul_of_nonneg_left s2 hp0
  exact t1.trans (t2.trans s1)

/-! ## The jump probabilities along the cycle -/

/-- `1 − E/R ≤ R/(R + E)`. -/
theorem one_sub_div_le_div_add {R E : ℝ} (hR : 0 < R) (hE : 0 ≤ E) :
    1 - E / R ≤ R / (R + E) := by
  rw [le_div_iff₀ (by linarith)]
  have h1 : E / R * R = E := div_mul_cancel₀ E hR.ne'
  have h2 : 0 ≤ E / R * E := mul_nonneg (div_nonneg hE hR.le) hE
  linarith [h1, h2]

/-- A probability lower bound in the form used below: if `E X ≤ c R` then
`1 − c/X ≤ R/(R + E)`. -/
theorem prob_ge {R E c X : ℝ} (hR : 0 < R) (hE : 0 ≤ E) (hX : 0 < X) (h : E * X ≤ c * R) :
    1 - c / X ≤ R / (R + E) := by
  have h1 := one_sub_div_le_div_add hR hE
  have h2 : E / R ≤ c / X := by rw [div_le_div_iff₀ hR hX]; linarith [h]
  linarith

/-- `X(a) = (a + 1)(a + 2)`. -/
noncomputable def Xa (a : ℕ) : ℝ := ((a : ℝ) + 1) * ((a : ℝ) + 1 + 1)

theorem Xa_pos (a : ℕ) : 0 < Xa a := by unfold Xa; positivity

/-- `1/(a + 1) − 1/(a + 2) = 1/X(a)`. -/
theorem one_div_sub_one_div (a : ℕ) :
    1 / ((a : ℝ) + 1) - 1 / ((a : ℝ) + 1 + 1) = 1 / Xa a := by
  unfold Xa
  have h1 : (a : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (a : ℝ) + 1 + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- `c₁ = κ₀/κ₁`. -/
noncomputable def c₁ : ℝ := κ.k 0 / κ.k 1

/-- `c₂ = (κ₀ + 64 κ₁)/(12 κ₂)`. -/
noncomputable def c₂ : ℝ := (κ.k 0 + 64 * κ.k 1) / (12 * κ.k 2)

/-- `D = c₁ + c₂`. -/
noncomputable def D : ℝ := c₁ κ + c₂ κ

theorem c₁_nonneg : 0 ≤ c₁ κ := by
  have := κ.positive 0; have := κ.positive 1
  unfold c₁; positivity

theorem c₂_nonneg : 0 ≤ c₂ κ := by
  have := κ.positive 0; have := κ.positive 1; have := κ.positive 2
  unfold c₂; positivity

theorem D_nonneg : 0 ≤ D κ := by
  have := c₁_nonneg κ; have := c₂_nonneg κ
  unfold D; linarith

theorem p0_eq (a : ℕ) : (net.jumpChain κ).p (mk2 a 0) 0 = 1 := by
  show net.jumpProb κ (mk2 a 0) 0 = 1
  unfold jumpProb
  rw [exitRate_eq, rate0, rate1_X0, rate2_X0, add_zero, add_zero]
  exact div_self (κ.positive 0).ne'

theorem p1_ge (a : ℕ) : 1 - c₁ κ / Xa a ≤ (net.jumpChain κ).p (mk2 (a + 2) 1) 1 := by
  show _ ≤ net.jumpProb κ (mk2 (a + 2) 1) 1
  unfold jumpProb
  rw [exitRate_eq, rate0, rate1_X1, rate2_X1]
  have hk0 := κ.positive 0
  have hk1 := κ.positive 1
  have hR : 0 < κ.k 1 * (((a : ℝ) + 2) * ((a : ℝ) + 1)) := by positivity
  have e : κ.k 0 + κ.k 1 * (((a : ℝ) + 2) * ((a : ℝ) + 1)) + 0 =
      κ.k 1 * (((a : ℝ) + 2) * ((a : ℝ) + 1)) + κ.k 0 := by ring
  rw [e]
  refine prob_ge hR hk0.le (Xa_pos a) (le_of_eq ?_)
  have hc : κ.k 0 / κ.k 1 * κ.k 1 = κ.k 0 := div_mul_cancel₀ _ hk1.ne'
  unfold c₁ Xa
  linear_combination (-(((a : ℝ) + 2) * ((a : ℝ) + 1))) * hc

theorem p2_ge (a : ℕ) : 1 - c₂ κ / Xa a ≤ (net.jumpChain κ).p (mk2 (a + 4) 4) 2 := by
  show _ ≤ net.jumpProb κ (mk2 (a + 4) 4) 2
  unfold jumpProb
  rw [exitRate_eq, rate0]
  have hk0 := κ.positive 0
  have hk1 := κ.positive 1
  have hk2 := κ.positive 2
  obtain ⟨R1, hR1⟩ : ∃ R1, R1 = net.stochasticMassActionRate κ (mk2 (a + 4) 4) 1 := ⟨_, rfl⟩
  obtain ⟨R2, hR2⟩ : ∃ R2, R2 = net.stochasticMassActionRate κ (mk2 (a + 4) 4) 2 := ⟨_, rfl⟩
  rw [← hR1, ← hR2]
  have hR1le : R1 ≤ 4 * κ.k 1 * ((a : ℝ) + 4) ^ 2 := by rw [hR1]; exact rate1_X2_le κ a
  have hR1nn : 0 ≤ R1 := by rw [hR1]; exact net.stochasticMassActionRate_nonneg κ _ _
  have hR2ge : 24 * κ.k 2 * ((a : ℝ) + 1) ^ 4 ≤ R2 := by rw [hR2]; exact rate2_X2_ge κ a
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (a : ℝ) + 1 := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := by rw [hy]; linarith
  have hR2pos : 0 < R2 := by
    have : 0 < 24 * κ.k 2 * ((a : ℝ) + 1) ^ 4 := by positivity
    linarith
  have e : κ.k 0 + R1 + R2 = R2 + (κ.k 0 + R1) := by ring
  rw [e]
  refine prob_ge hR2pos (by linarith) (Xa_pos a) ?_
  -- `(κ₀ + R₁) X(a) ≤ c₂ R₂`
  have h2 : ((a : ℝ) + 4) ^ 2 ≤ 16 * y ^ 2 := by
    have h4y : (a : ℝ) + 4 ≤ 4 * y := by rw [hy]; linarith
    have h0 : (0 : ℝ) ≤ (a : ℝ) + 4 := by linarith
    have := pow_le_pow_left₀ h0 h4y 2
    nlinarith [this]
  have h2' : 4 * κ.k 1 * ((a : ℝ) + 4) ^ 2 ≤ 64 * κ.k 1 * y ^ 2 := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * κ.k 1)
    linarith
  have h3 : κ.k 0 ≤ κ.k 0 * y ^ 2 := by
    have hy2 : (1 : ℝ) ≤ y ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hy2 hk0.le
    linarith
  have hE1 : κ.k 0 + R1 ≤ (κ.k 0 + 64 * κ.k 1) * y ^ 2 := by linarith
  have hX : Xa a ≤ 2 * y ^ 2 := by unfold Xa; rw [← hy]; nlinarith
  have hX0 : 0 ≤ Xa a := (Xa_pos a).le
  have hEX : (κ.k 0 + R1) * Xa a ≤ (κ.k 0 + 64 * κ.k 1) * y ^ 2 * (2 * y ^ 2) :=
    mul_le_mul hE1 hX hX0 (by positivity)
  have hR2y : 24 * κ.k 2 * y ^ 4 ≤ R2 := by rw [hy]; exact hR2ge
  have hc2 := c₂_nonneg κ
  have hc2R : c₂ κ * (24 * κ.k 2 * y ^ 4) ≤ c₂ κ * R2 := mul_le_mul_of_nonneg_left hR2y hc2
  have hc2eq : c₂ κ * (24 * κ.k 2 * y ^ 4) = 2 * (κ.k 0 + 64 * κ.k 1) * y ^ 4 := by
    have h12 : (κ.k 0 + 64 * κ.k 1) / (12 * κ.k 2) * (12 * κ.k 2) = κ.k 0 + 64 * κ.k 1 :=
      div_mul_cancel₀ _ (by positivity)
    unfold c₂
    linear_combination (2 * y ^ 4) * h12
  linarith [hEX, hc2R, hc2eq]

/-! ## The survival bound and its consequences -/

/-- The starting level `a₀ = ⌈2D⌉`. -/
noncomputable def a₀ : ℕ := ⌈2 * D κ⌉₊

theorem two_D_le (a : ℕ) (ha : a₀ κ ≤ a) : 2 * D κ ≤ (a : ℝ) := by
  have h1 : 2 * D κ ≤ (⌈2 * D κ⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((a₀ κ : ℕ) : ℝ) ≤ a := by exact_mod_cast ha
  unfold a₀ at h2
  linarith

/-- **The telescoped survival bound.**  Let `C` be any set of counts disjoint from
`{x | n₀ ≤ x 0}`.  For `a ≥ max n₀ a₀` and every `k`,
`1 − D (1/(a + 1) − 1/(a + 1 + k)) ≤ survival(3k, (a, 0))`. -/
theorem survival_lower (C : Set (Fin 2 → ℕ)) [DecidablePred (· ∈ C)] (n₀ : ℕ)
    (hC : ∀ x : Fin 2 → ℕ, n₀ ≤ x 0 → x ∉ C) (k : ℕ) :
    ∀ a : ℕ, n₀ ≤ a → a₀ κ ≤ a →
      1 - D κ * (1 / ((a : ℝ) + 1) - 1 / ((a : ℝ) + 1 + k)) ≤
        (net.jumpChain κ).survival C (3 * k) (mk2 a 0) := by
  induction k with
  | zero =>
      intro a _ _
      show _ ≤ (1 : ℝ)
      simp
  | succ k ih =>
      intro a ha1 ha2
      have hcyc := cycle_ge κ C a (3 * k) (hC _ (by show n₀ ≤ a + 2; omega))
        (hC _ (by show n₀ ≤ a + 4; omega)) (hC _ (by show n₀ ≤ a + 1; omega))
      rw [p0_eq, one_mul] at hcyc
      have hIH := ih (a + 1) (by omega) (by omega)
      push_cast at hIH
      rw [show 3 * (k + 1) = 3 * k + 3 by ring]
      push_cast
      have e : (a : ℝ) + 1 + ((k : ℝ) + 1) = (a : ℝ) + 1 + 1 + (k : ℝ) := by ring
      rw [e]
      -- notation
      obtain ⟨S, hS⟩ : ∃ S, S = (net.jumpChain κ).survival C (3 * k) (mk2 (a + 1) 0) :=
        ⟨_, rfl⟩
      rw [← hS] at hIH hcyc
      have hS0 : 0 ≤ S := by rw [hS]; exact (net.jumpChain κ).survival_nonneg C _ _
      have hp1 := p1_ge κ a
      have hp2 := p2_ge κ a
      have hp2nn := (net.jumpChain κ).p_nonneg (mk2 (a + 4) 4) 2
      have hD := D_nonneg κ
      have h2D := two_D_le κ a ha2
      have hX := Xa_pos a
      have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      -- the atoms `A₁ = 1/(a+1)`, `A₂ = 1/(a+2)`, `A₃ = 1/(a+2+k)`
      have hA2le : 1 / ((a : ℝ) + 1 + 1) ≤ 1 / ((a : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have hA3le : 1 / ((a : ℝ) + 1 + 1 + k) ≤ 1 / ((a : ℝ) + 1 + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have hA3nn : 0 ≤ 1 / ((a : ℝ) + 1 + 1 + k) := by positivity
      have hDA1 : D κ * (1 / ((a : ℝ) + 1)) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        linarith
      have htd := one_div_sub_one_div a
      -- `u₁ + u₂ = D (A₁ − A₂)`
      have hu : c₁ κ / Xa a + c₂ κ / Xa a =
          D κ * (1 / ((a : ℝ) + 1) - 1 / ((a : ℝ) + 1 + 1)) := by
        rw [htd]; unfold D; ring
      have hu1 : 0 ≤ c₁ κ / Xa a := div_nonneg (c₁_nonneg κ) hX.le
      have hu2 : 0 ≤ c₂ κ / Xa a := div_nonneg (c₂_nonneg κ) hX.le
      have hDA2 : 0 ≤ D κ * (1 / ((a : ℝ) + 1 + 1)) :=
        mul_nonneg hD (by positivity)
      have huhalf : c₁ κ / Xa a + c₂ κ / Xa a ≤ 1 / 2 := by
        rw [hu]
        have : D κ * (1 / ((a : ℝ) + 1) - 1 / ((a : ℝ) + 1 + 1)) =
            D κ * (1 / ((a : ℝ) + 1)) - D κ * (1 / ((a : ℝ) + 1 + 1)) := by ring
        linarith
      -- `v = D (A₂ − A₃) ∈ [0, 1/2]`
      have hv0 : 0 ≤ D κ * (1 / ((a : ℝ) + 1 + 1) - 1 / ((a : ℝ) + 1 + 1 + k)) :=
        mul_nonneg hD (by linarith)
      have hvhalf : D κ * (1 / ((a : ℝ) + 1 + 1) - 1 / ((a : ℝ) + 1 + 1 + k)) ≤ 1 / 2 := by
        have h1 : D κ * (1 / ((a : ℝ) + 1 + 1) - 1 / ((a : ℝ) + 1 + 1 + k)) ≤
            D κ * (1 / ((a : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) hD
        linarith
      -- the products
      have hp1nn : 0 ≤ 1 - c₁ κ / Xa a := by linarith
      have hp2lb : 0 ≤ 1 - c₂ κ / Xa a := by linarith
      have hP1 : (1 - c₁ κ / Xa a) * (1 - c₂ κ / Xa a) ≤
          (net.jumpChain κ).p (mk2 (a + 2) 1) 1 * (net.jumpChain κ).p (mk2 (a + 4) 4) 2 :=
        mul_le_mul hp1 hp2 hp2lb (le_trans hp1nn hp1)
      have hP2 : 1 - (c₁ κ / Xa a + c₂ κ / Xa a) ≤ (1 - c₁ κ / Xa a) * (1 - c₂ κ / Xa a) := by
        nlinarith [mul_nonneg hu1 hu2]
      have hPnn : 0 ≤ 1 - (c₁ κ / Xa a + c₂ κ / Xa a) := by linarith
      have hSlb : 1 - D κ * (1 / ((a : ℝ) + 1 + 1) - 1 / ((a : ℝ) + 1 + 1 + k)) ≤ S := hIH
      have hP3 : (1 - (c₁ κ / Xa a + c₂ κ / Xa a)) *
            (1 - D κ * (1 / ((a : ℝ) + 1 + 1) - 1 / ((a : ℝ) + 1 + 1 + k))) ≤
          ((net.jumpChain κ).p (mk2 (a + 2) 1) 1 * (net.jumpChain κ).p (mk2 (a + 4) 4) 2) * S :=
        mul_le_mul (hP2.trans hP1) hSlb (by linarith)
          (mul_nonneg (le_trans hp1nn hp1) hp2nn)
      have hP4 : 1 - (c₁ κ / Xa a + c₂ κ / Xa a) -
            D κ * (1 / ((a : ℝ) + 1 + 1) - 1 / ((a : ℝ) + 1 + 1 + k)) ≤
          (1 - (c₁ κ / Xa a + c₂ κ / Xa a)) *
            (1 - D κ * (1 / ((a : ℝ) + 1 + 1) - 1 / ((a : ℝ) + 1 + 1 + k))) := by
        nlinarith [mul_nonneg (add_nonneg hu1 hu2) hv0]
      have hassoc : ((net.jumpChain κ).p (mk2 (a + 2) 1) 1 *
            (net.jumpChain κ).p (mk2 (a + 4) 4) 2) * S =
          (net.jumpChain κ).p (mk2 (a + 2) 1) 1 * ((net.jumpChain κ).p (mk2 (a + 4) 4) 2 * S) :=
        mul_assoc _ _ _
      have hgoal : 1 - D κ * (1 / ((a : ℝ) + 1) - 1 / ((a : ℝ) + 1 + 1 + k)) =
          1 - (c₁ κ / Xa a + c₂ κ / Xa a) -
            D κ * (1 / ((a : ℝ) + 1 + 1) - 1 / ((a : ℝ) + 1 + 1 + k)) := by
        rw [hu]; ring
      rw [hgoal]
      linarith [hP3, hP4, hassoc, hcyc]

/-- **At least one half.**  For `a ≥ max n₀ a₀`, `survival(3k, (a, 0)) ≥ 1/2` for every `k`. -/
theorem survival_three_mul_ge_half (C : Set (Fin 2 → ℕ)) [DecidablePred (· ∈ C)] (n₀ : ℕ)
    (hC : ∀ x : Fin 2 → ℕ, n₀ ≤ x 0 → x ∉ C) (a : ℕ) (ha1 : n₀ ≤ a) (ha2 : a₀ κ ≤ a)
    (k : ℕ) : (1 : ℝ) / 2 ≤ (net.jumpChain κ).survival C (3 * k) (mk2 a 0) := by
  have h := survival_lower κ C n₀ hC k a ha1 ha2
  have hD := D_nonneg κ
  have h2D := two_D_le κ a ha2
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hA3 : 0 ≤ 1 / ((a : ℝ) + 1 + k) := by positivity
  have hDA1 : D κ * (1 / ((a : ℝ) + 1)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have : D κ * (1 / ((a : ℝ) + 1) - 1 / ((a : ℝ) + 1 + k)) ≤ D κ * (1 / ((a : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hD
  linarith

/-- **The chain avoids every finite set with probability at least `1/2`.**  For every finite
set `K` of counts there is a starting count from which the probability of avoiding `K` for `m`
steps does not tend to `0`. -/
theorem survival_not_tendsto_zero (K : Finset (Fin 2 → ℕ)) [DecidablePred (· ∈ (K : Set (Fin 2 → ℕ)))] :
    ∃ x : Fin 2 → ℕ,
      ¬ Tendsto (fun m => (net.jumpChain κ).survival (K : Set (Fin 2 → ℕ)) m x) atTop (𝓝 0) := by
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = K.sup (fun x => x 0) + 1 := ⟨_, rfl⟩
  have hC : ∀ x : Fin 2 → ℕ, n₀ ≤ x 0 → x ∉ (K : Set (Fin 2 → ℕ)) := by
    intro x hx hmem
    have h := Finset.le_sup (f := fun x : Fin 2 → ℕ => x 0) (Finset.mem_coe.mp hmem)
    have h' : x 0 ≤ K.sup (fun x : Fin 2 → ℕ => x 0) := h
    omega
  refine ⟨mk2 (max n₀ (a₀ κ)) 0, fun hT => ?_⟩
  have hev := Filter.Tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2) hT
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have h1 := hN (3 * N) (by omega)
  have h2 := survival_three_mul_ge_half κ (K : Set (Fin 2 → ℕ)) n₀ hC (max n₀ (a₀ κ))
    (le_max_left _ _) (le_max_right _ _) N
  linarith

/-- **No Foster drift certificate off any finite set.**  For every finite set `K` there is no
nonnegative `V` and `ε > 0` with `PV ≤ V − ε` off `K` for the embedded jump chain (Foster's
criterion, which would force the survival probabilities to tend to `0`,
`CRNT.Foster.FiniteBranchChain.tendsto_survival_zero`). -/
theorem no_foster_certificate (K : Finset (Fin 2 → ℕ)) :
    ¬ ∃ (V : (Fin 2 → ℕ) → ℝ) (ε : ℝ), (∀ x, 0 ≤ V x) ∧ 0 < ε ∧
      ∀ y, y ∉ (K : Set (Fin 2 → ℕ)) → (net.jumpChain κ).expect V y ≤ V y - ε := by
  classical
  rintro ⟨V, ε, hV, hε, hdrift⟩
  obtain ⟨x, hx⟩ := survival_not_tendsto_zero κ K
  exact hx ((net.jumpChain κ).tendsto_survival_zero (K : Set (Fin 2 → ℕ)) hV hε hdrift x)

end ACKTransient
end Examples
end CRNT

#print axioms CRNT.Examples.ACKTransient.stronglyEndotacticStd
#print axioms CRNT.Examples.ACKTransient.structurallyPermanent
#print axioms CRNT.Examples.ACKTransient.survival_three_mul_ge_half
#print axioms CRNT.Examples.ACKTransient.survival_not_tendsto_zero
#print axioms CRNT.Examples.ACKTransient.no_foster_certificate

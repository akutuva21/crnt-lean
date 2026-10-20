import CRNT.Stochastic.KurtzPathwise

open MeasureTheory Set Filter
open scoped BigOperators

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

noncomputable def exitMass (K : Finset α) (c : α) (h : ℝ) : ℝ :=
  ∑' b, (if b ∈ K then (0 : ℝ) else (J.stopOutside K).Pmin h c b)

theorem exitMass_nonneg (K : Finset α) (c : α) {h : ℝ} (ht : 0 ≤ h) :
    0 ≤ J.exitMass K c h := by
  refine tsum_nonneg fun b => ?_
  by_cases hb : b ∈ K <;> simp [hb, (J.stopOutside K).Pmin_nonneg h ht c b]

theorem exitMass_le_one (K : Finset α) (c : α) {h : ℝ} (ht : 0 ≤ h) :
    J.exitMass K c h ≤ 1 := by
  have hPs : Summable fun b => (J.stopOutside K).Pmin h c b :=
    ((J.stopOutside K).hasSum_Pmin_one (Λ := ∑ x ∈ K, J.q x) (fun c' _ => J.stopOutside_q_le K c') ht).summable
  have hle : ∀ b, (if b ∈ K then (0 : ℝ) else (J.stopOutside K).Pmin h c b) ≤ (J.stopOutside K).Pmin h c b := by
    intro b
    by_cases hb : b ∈ K <;> simp [hb, (J.stopOutside K).Pmin_nonneg h ht c b]
  have hsum : Summable fun b => if b ∈ K then (0 : ℝ) else (J.stopOutside K).Pmin h c b :=
    Summable.of_nonneg_of_le (fun b => by by_cases hb : b ∈ K <;> simp [hb, (J.stopOutside K).Pmin_nonneg h ht c b]) hle hPs
  have htsum : ∑' b, (if b ∈ K then (0 : ℝ) else (J.stopOutside K).Pmin h c b) ≤ ∑' b, (J.stopOutside K).Pmin h c b :=
    hsum.tsum_le_tsum hle hPs
  have hone : ∑' b, (J.stopOutside K).Pmin h c b = 1 :=
    ((J.stopOutside K).hasSum_Pmin_one (Λ := ∑ x ∈ K, J.q x) (fun c' _ => J.stopOutside_q_le K c') ht).tsum_eq
  exact htsum.trans (le_of_eq hone)

theorem exitMass_zero_of_mem (K : Finset α) (c : α) (hc : c ∈ K) :
    J.exitMass K c 0 = 0 := by
  have hP0 : ∀ b, (J.stopOutside K).Pmin 0 c b = if c = b then 1 else 0 := fun b => (J.stopOutside K).Pmin_zero c b
  have heq : J.exitMass K c 0 = ∑' b, (if b ∈ K then (0 : ℝ) else (J.stopOutside K).Pmin 0 c b) := rfl
  rw [heq, funext hP0]
  have hzero : ∀ b, (if b ∈ K then (0 : ℝ) else if c = b then (1 : ℝ) else 0) = 0 := by
    intro b
    by_cases hb : b ∈ K
    · simp [hb]
    · by_cases hcb : c = b
      · subst hcb; exact (hb hc).elim
      · simp [hcb]
  rw [funext hzero, tsum_zero]

end JumpSystem

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

theorem three_halves_step (δ : ℝ) (hδ : 0 ≤ δ) {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (hu : ∑ i, u i ^ 2 ≤ δ ^ 2)
    (hv : ∑ i, v i ^ 2 ≤ δ ^ 2 / 4) :
    ∑ i, (u i + v i) ^ 2 ≤ (3 * δ / 2) ^ 2 := by
  have hcross : ∑ i, u i * v i ≤ Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι) u v
  have hsqrtu : Real.sqrt (∑ i, u i ^ 2) ≤ δ := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hδ
    · nlinarith [hu]
  have hsqrtv : Real.sqrt (∑ i, v i ^ 2) ≤ δ / 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith [hδ]
    · nlinarith [hv, hδ]
  have heq : ∑ i, (u i + v i) ^ 2 = ∑ i, u i ^ 2 + 2 * ∑ i, u i * v i + ∑ i, v i ^ 2 := by
    calc ∑ i, (u i + v i) ^ 2
        = ∑ i, (u i ^ 2 + 2 * (u i * v i) + v i ^ 2) := by refine Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, u i ^ 2 + 2 * ∑ i, u i * v i + ∑ i, v i ^ 2 := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hle : ∑ i, u i ^ 2 + 2 * ∑ i, u i * v i + ∑ i, v i ^ 2 ≤ δ ^ 2 + δ ^ 2 + δ ^ 2 / 4 := by
    nlinarith [hu, hv, hcross, hsqrtu, hsqrtv, mul_le_mul hsqrtu hsqrtv (Real.sqrt_nonneg (∑ i, v i ^ 2)) (le_trans (Real.sqrt_nonneg (∑ i, u i ^ 2)) hsqrtu)]
  rw [heq]
  exact hle.trans (le_of_eq (by ring))

end Network

end CRNT

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Perron–Frobenius for column-stochastic matrices

A self-contained Perron–Frobenius theorem sufficient for chemical reaction network
theory. It comes in two halves:

* **Existence** (`exists_nonneg_mulVec_fixed_of_colStochastic`): a column-stochastic
  nonnegative matrix has a nonnegative, nonzero fixed vector. Proved by the
  Cesàro/Markov–Kakutani argument — the affine map `x ↦ P x` preserves the compact
  convex simplex, the time-averages of an orbit stay in it, and a convergent subsequence
  has a limit that the averaging forces to be a fixed point. No Brouwer needed.
* **Positivity** (`pos_of_nonneg_mulVec_fixed_of_stronglyConnected`): if in addition the
  support digraph is strongly connected, that fixed vector is strictly positive. Purely
  combinatorial.

Combined (`exists_pos_mulVec_fixed_of_stronglyConnected`): a strongly connected
column-stochastic nonnegative matrix has a strictly positive fixed vector. In CRNT this
yields a strictly positive vector in the kernel of the (rescaled) kinetic matrix on a
linkage class, since weak reversibility makes each linkage class strongly connected.

This module is **stable**: it contains no `sorry`.
-/

namespace CRNT

open scoped BigOperators

/-- The reachability relation of the support digraph of a matrix: `i` reaches `j` along
edges `a → c` present whenever `P a c ≠ 0`. -/
def supportReaches {ι : Type*} (P : Matrix ι ι ℝ) : ι → ι → Prop :=
  Relation.ReflTransGen fun a c => P a c ≠ 0

/-- **Positivity spreads along the support digraph.** For a nonnegative fixed vector
`b`, if `i` reaches a coordinate `j` where `b` is positive, then `b` is positive at `i`. -/
theorem pos_of_supportReaches_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hfix : P.mulVec b = b)
    {i j : ι} (hij : supportReaches P i j) (hbj : 0 < b j) : 0 < b i := by
  induction hij using Relation.ReflTransGen.head_induction_on with
  | refl => exact hbj
  | @head a c e _ ih =>
    have hba : b a = ∑ k : ι, P a k * b k := by
      have hcong := congrFun hfix a
      rw [← hcong]
      simp [Matrix.mulVec, dotProduct]
    rw [hba]
    refine Finset.sum_pos' (fun k _ => mul_nonneg (hP a k) (hb k)) ⟨c, Finset.mem_univ c, ?_⟩
    exact mul_pos ((hP a c).lt_of_ne (Ne.symm e)) ih

/-- **Localized positivity spreading.** As `pos_of_supportReaches_pos`, but the fixed
vector `w` need only be nonnegative on a forward-closed set `D` (one with no support edges
leaving it) that contains the source `i`; the support path then stays inside `D`. This is
what lets the spreading argument run inside a single block of a block-diagonal matrix. -/
theorem pos_of_supportReaches_pos_on
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (D : ι → Prop) (hD : ∀ d, D d → ∀ k, P d k ≠ 0 → D k)
    (w : ι → ℝ) (hw : ∀ k, D k → 0 ≤ w k) (hfix : P.mulVec w = w)
    {i j : ι} (hi : D i) (hij : supportReaches P i j) (hwj : 0 < w j) : 0 < w i := by
  suffices h : D i → 0 < w i from h hi
  clear hi
  induction hij using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ => hwj
  | @head a c e _ ih =>
    intro hDa
    have hwc : 0 < w c := ih (hD a hDa c e)
    have hwa : w a = ∑ k : ι, P a k * w k := by
      have hcong := congrFun hfix a
      rw [← hcong]; simp [Matrix.mulVec, dotProduct]
    rw [hwa]
    refine Finset.sum_pos' (fun k _ => ?_)
      ⟨c, Finset.mem_univ c, mul_pos ((hP a c).lt_of_ne (Ne.symm e)) hwc⟩
    by_cases hPak : P a k = 0
    · rw [hPak, zero_mul]
    · exact mul_nonneg (hP a k) (hw k (hD a hDa k hPak))

/-- **Perron–Frobenius positivity.** If `P` is entrywise nonnegative, `b` is an
entrywise nonnegative, nonzero fixed vector (`P.mulVec b = b`), and the support digraph
of `P` is strongly connected (every vertex reaches every vertex), then `b` is strictly
positive. -/
theorem pos_of_nonneg_mulVec_fixed_of_stronglyConnected
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hb0 : b ≠ 0)
    (hfix : P.mulVec b = b)
    (hsc : ∀ i j, supportReaches P i j) :
    ∀ i, 0 < b i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hb0
  have hbj : 0 < b j := (hb j).lt_of_ne (Ne.symm hj)
  exact fun i => pos_of_supportReaches_pos P hP b hb hfix (hsc i j) hbj

open Filter Topology in
/-- **Perron–Frobenius existence with invariant masses.** A column-stochastic
nonnegative matrix has a nonnegative fixed vector `b` arising as a Cesàro limit of the
orbit of the uniform distribution; consequently, for every "invariant" set `T` (a `T`
whose total mass is preserved by `P`), the mass `∑_{i∈T} b i` equals its uniform value
`|T| / |ι|`. This refinement is what lets a reducible chain's fixed vector stay positive
on every closed class. -/
theorem exists_nonneg_mulVec_fixed_invariant
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hcol : ∀ j, ∑ i, P i j = 1) :
    ∃ b : ι → ℝ, (∀ i, 0 ≤ b i) ∧ P.mulVec b = b ∧
      ∀ T : Finset ι, (∀ v : ι → ℝ, ∑ i ∈ T, P.mulVec v i = ∑ i ∈ T, v i) →
        ∑ i ∈ T, b i = (T.card : ℝ) * (Fintype.card ι : ℝ)⁻¹ := by
  classical
  -- `x ↦ P x` is continuous and preserves the standard simplex.
  have hcont : Continuous (fun x : ι → ℝ => P.mulVec x) :=
    (Matrix.mulVecLin P).continuous_of_finiteDimensional.congr fun x =>
      Matrix.mulVecLin_apply P x
  have hmulApply : ∀ (x : ι → ℝ) (i), P.mulVec x i = ∑ j, P i j * x j := fun x i => rfl
  have hmap : ∀ x ∈ stdSimplex ℝ ι, P.mulVec x ∈ stdSimplex ℝ ι := by
    rintro x ⟨hx0, hx1⟩
    refine ⟨fun i => ?_, ?_⟩
    · rw [hmulApply]; exact Finset.sum_nonneg fun j _ => mul_nonneg (hP i j) (hx0 j)
    · simp_rw [hmulApply]
      rw [Finset.sum_comm]
      have : ∀ j, ∑ i, P i j * x j = x j := fun j => by rw [← Finset.sum_mul, hcol j, one_mul]
      simp_rw [this]; exact hx1
  -- the orbit `x k = Pᵏ x₀` from the uniform distribution, and its time-averages `c n`.
  let x₀ : ι → ℝ := fun _ => (Fintype.card ι : ℝ)⁻¹
  have hx₀ : x₀ ∈ stdSimplex ℝ ι := by
    refine ⟨fun i => by positivity, ?_⟩
    show ∑ _i : ι, (Fintype.card ι : ℝ)⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  let x : ℕ → (ι → ℝ) := fun k => Nat.rec x₀ (fun _ y => P.mulVec y) k
  have hx_succ : ∀ k, x (k + 1) = P.mulVec (x k) := fun _ => rfl
  have hx_mem : ∀ k, x k ∈ stdSimplex ℝ ι := by
    intro k
    induction k with
    | zero => exact hx₀
    | succ k ih => rw [hx_succ]; exact hmap _ ih
  have hxge : ∀ k i, 0 ≤ x k i := fun k i => (hx_mem k).1 i
  have hxle : ∀ k i, x k i ≤ 1 := fun k i =>
    (Finset.single_le_sum (fun j _ => hxge k j) (Finset.mem_univ i)).trans_eq (hx_mem k).2
  let c : ℕ → (ι → ℝ) := fun n => ∑ k ∈ Finset.range (n + 1), ((n : ℝ) + 1)⁻¹ • x k
  have hc_mem : ∀ n, c n ∈ stdSimplex ℝ ι := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine (convex_stdSimplex ℝ ι).sum_mem (fun k _ => by positivity) ?_ (fun k _ => hx_mem k)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
      mul_inv_cancel₀ hpos.ne']
  -- averaging kills `P x - x`: `P (c n) - c n = (n+1)⁻¹ • (x (n+1) - x 0)`.
  have hmulVec_c : ∀ n, P.mulVec (c n)
      = ∑ k ∈ Finset.range (n + 1), ((n : ℝ) + 1)⁻¹ • x (k + 1) := by
    intro n
    rw [show P.mulVec (c n) = Matrix.mulVecLin P (c n) from (Matrix.mulVecLin_apply P (c n)).symm]
    show Matrix.mulVecLin P (∑ k ∈ Finset.range (n + 1), ((n : ℝ) + 1)⁻¹ • x k) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Matrix.mulVecLin_apply, ← hx_succ k]
  have htele : ∀ n, (∑ k ∈ Finset.range (n + 1), x (k + 1)) - ∑ k ∈ Finset.range (n + 1), x k
      = x (n + 1) - x 0 := by
    intro n
    rw [Finset.sum_range_succ (fun k => x (k + 1)) n, Finset.sum_range_succ' x n]
    abel
  have htel : ∀ n, P.mulVec (c n) - c n = ((n : ℝ) + 1)⁻¹ • (x (n + 1) - x 0) := by
    intro n
    have hc_eq : c n = ((n : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (n + 1), x k := by
      show (∑ k ∈ Finset.range (n + 1), ((n : ℝ) + 1)⁻¹ • x k) = _
      rw [Finset.smul_sum]
    have hPc_eq : P.mulVec (c n) = ((n : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (n + 1), x (k + 1) := by
      rw [hmulVec_c, Finset.smul_sum]
    rw [hPc_eq, hc_eq, ← smul_sub, htele n]
  -- hence `P (c n) - c n → 0`, coordinatewise.
  have hto0 : Tendsto (fun n => P.mulVec (c n) - c n) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro i
    simp only [htel]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
    refine squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    have hdiff : |x (n + 1) i - x 0 i| ≤ 1 :=
      abs_le.mpr ⟨by have := hxge (n + 1) i; have := hxle 0 i; linarith,
        by have := hxge 0 i; have := hxle (n + 1) i; linarith⟩
    have hpos : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos, one_div]
    exact mul_le_of_le_one_right hpos hdiff
  -- extract a convergent subsequence of the averages and conclude it is a fixed point.
  obtain ⟨b, hb_mem, φ, hφ_mono, hφ_lim⟩ := (isCompact_stdSimplex ℝ ι).tendsto_subseq hc_mem
  have hfix : P.mulVec b = b := by
    have hcb : Tendsto (fun j => P.mulVec (c (φ j))) atTop (𝓝 (P.mulVec b)) :=
      (hcont.tendsto b).comp hφ_lim
    have hsub_b : Tendsto (fun j => P.mulVec (c (φ j)) - c (φ j)) atTop (𝓝 (P.mulVec b - b)) :=
      hcb.sub hφ_lim
    have hsub_0 : Tendsto (fun j => P.mulVec (c (φ j)) - c (φ j)) atTop (𝓝 0) :=
      hto0.comp hφ_mono.tendsto_atTop
    have h := tendsto_nhds_unique hsub_b hsub_0
    rwa [sub_eq_zero] at h
  refine ⟨b, hb_mem.1, hfix, ?_⟩
  intro T hT
  -- partial masses are preserved along the orbit, hence on the Cesàro limit.
  have hxT : ∀ k, ∑ i ∈ T, x k i = ∑ i ∈ T, x₀ i := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [hx_succ k, hT (x k), ih]
  have hcT : ∀ n, ∑ i ∈ T, c n i = ∑ i ∈ T, x₀ i := by
    intro n
    have hci : ∀ i, c n i = ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), x k i := by
      intro i
      show (∑ k ∈ Finset.range (n + 1), ((n : ℝ) + 1)⁻¹ • x k) i = _
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    simp_rw [hci]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [hxT]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
      ← mul_assoc, inv_mul_cancel₀ (by positivity : ((n : ℝ) + 1) ≠ 0), one_mul]
  have hlimT : Tendsto (fun j => ∑ i ∈ T, c (φ j) i) atTop (𝓝 (∑ i ∈ T, b i)) :=
    tendsto_finsetSum T fun i _ => (tendsto_pi_nhds.mp hφ_lim) i
  have hbT : ∑ i ∈ T, b i = ∑ i ∈ T, x₀ i := by
    refine tendsto_nhds_unique hlimT ?_
    simp only [hcT]
    exact tendsto_const_nhds
  rw [hbT]
  show ∑ _i ∈ T, (Fintype.card ι : ℝ)⁻¹ = (T.card : ℝ) * (Fintype.card ι : ℝ)⁻¹
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **Perron–Frobenius existence.** A column-stochastic nonnegative matrix has a
nonnegative, nonzero fixed vector (the total-mass invariance forces `∑ b = 1`). -/
theorem exists_nonneg_mulVec_fixed_of_colStochastic
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hcol : ∀ j, ∑ i, P i j = 1) :
    ∃ b : ι → ℝ, (∀ i, 0 ≤ b i) ∧ b ≠ 0 ∧ P.mulVec b = b := by
  obtain ⟨b, hb, hfix, hinv⟩ := exists_nonneg_mulVec_fixed_invariant P hP hcol
  refine ⟨b, hb, ?_, hfix⟩
  have hcolsum : ∀ v : ι → ℝ, ∑ i, P.mulVec v i = ∑ i, v i := by
    intro v
    have hmv : ∀ i, P.mulVec v i = ∑ j, P i j * v j := fun i => rfl
    simp_rw [hmv]
    rw [Finset.sum_comm]
    have h2 : ∀ j, ∑ i, P i j * v j = v j := fun j => by rw [← Finset.sum_mul, hcol j, one_mul]
    simp_rw [h2]
  have huniv : ∑ i, b i = (Finset.univ.card : ℝ) * (Fintype.card ι : ℝ)⁻¹ :=
    hinv Finset.univ hcolsum
  rw [Finset.card_univ, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)] at huniv
  intro hb0
  rw [hb0] at huniv
  simp at huniv

/-- **Perron–Frobenius for strongly connected column-stochastic matrices.** Combining
existence and positivity: a strongly connected column-stochastic nonnegative matrix has
a strictly positive fixed vector. -/
theorem exists_pos_mulVec_fixed_of_stronglyConnected
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hcol : ∀ j, ∑ i, P i j = 1)
    (hsc : ∀ i j, supportReaches P i j) :
    ∃ b : ι → ℝ, (∀ i, 0 < b i) ∧ P.mulVec b = b := by
  obtain ⟨b, hb, hb0, hfix⟩ := exists_nonneg_mulVec_fixed_of_colStochastic P hP hcol
  exact ⟨b, pos_of_nonneg_mulVec_fixed_of_stronglyConnected P hP b hb hb0 hfix hsc, hfix⟩

/-- **Perron–Frobenius uniqueness.** For a strongly connected nonnegative matrix, a
strictly positive fixed vector is unique up to scaling: every nonnegative fixed vector is
a scalar multiple of it. (Proof: the minimum of the ratio `v/a` is attained at some `c₀`;
`w := v − (v c₀/a c₀)·a` is a nonnegative fixed vector vanishing at `c₀`, so by positivity
spreading from `c₀` it must be identically zero.) -/
theorem mulVec_fixed_unique_of_stronglyConnected
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : Matrix ι ι ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (a v : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hfa : P.mulVec a = a) (hfv : P.mulVec v = v)
    (hsc : ∀ i j, supportReaches P i j) :
    ∃ t : ℝ, v = t • a := by
  classical
  obtain ⟨c₀, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun c => v c / a c)
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  refine ⟨v c₀ / a c₀, ?_⟩
  set t := v c₀ / a c₀ with ht
  set w := v - t • a with hw
  have hwnn : ∀ c, 0 ≤ w c := by
    intro c
    have hle : t ≤ v c / a c := hmin c (Finset.mem_univ c)
    rw [le_div_iff₀ (ha c)] at hle
    simp only [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; linarith
  have hwfix : P.mulVec w = w := by
    rw [hw, Matrix.mulVec_sub, Matrix.mulVec_smul, hfv, hfa]
  have hwc0 : w c₀ = 0 := by
    have hcancel : v c₀ / a c₀ * a c₀ = v c₀ := div_mul_cancel₀ (v c₀) (ha c₀).ne'
    simp only [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ht]
    rw [hcancel, sub_self]
  have hw0 : w = 0 := by
    by_contra hne
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    have hwj : 0 < w j := (hwnn j).lt_of_ne (Ne.symm hj)
    have hpos := pos_of_supportReaches_pos P hP w hwnn hwfix (hsc c₀ j) hwj
    rw [hwc0] at hpos; exact lt_irrefl 0 hpos
  rw [hw] at hw0
  exact sub_eq_zero.mp hw0

end CRNT

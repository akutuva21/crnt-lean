import CRNT.Stochastic.Ergodicity

/-!
# Convergence to the stationary law of the embedded jump chain on a finite region

On a finite closed enabled region the embedded jump chain is a finite-state Markov chain whose
restricted transition matrix `regionMatrix κ T` is column-stochastic
(`regionMatrix_colStochastic`). When that matrix is strictly positive — the strongest finite-state
aperiodicity condition, primitivity at the first step — the chain mixes geometrically: the
distribution after `n` jumps converges to the unique stationary law from every initial
distribution. This is the Doeblin/Dobrushin form of the finite-state Perron–Frobenius convergence
theorem (Meyn & Tweedie, "Markov Chains and Stochastic Stability"); the dominant eigenvalue `1` is
simple and every other eigenvalue lies strictly inside the unit disk, so the subdominant modes
decay.

The argument is a contraction estimate in the `ℓ¹` distance `l1Dist u v = ∑ i, |u i - v i|`.
A column-stochastic matrix is `ℓ¹`-nonexpansive on mass-balanced differences
(`colStochastic_l1_le`). A strictly positive column-stochastic matrix contracts by the Doeblin
factor `1 - card · δ`, where `δ` is a positive lower bound on the entries
(`colStochastic_l1_contraction`): subtracting the common floor `δ` from each entry leaves a
nonnegative weight whose column sums are `1 - card · δ`, and the difference of two probability
vectors sums to zero, so the floor contributes nothing. Iterating the contraction
(`pow_mulVec_l1_le_geometric`) drives `l1Dist (P^n x) b` to zero geometrically, where `b` is the
stationary probability vector supplied by Perron–Frobenius
(`exists_pos_mulVec_fixed_of_stronglyConnected`). Entrywise convergence follows from the `ℓ¹`
bound.

For the embedded jump chain this is `regionMatrix_pow_mulVec_tendsto_stationaryVec`: the singleton
masses of the `n`-step pushforward of any region-supported initial probability measure converge to
the singleton masses of the canonical stationary probability measure
(`stationaryProbabilityMeasure`).

## Main results

* `l1Dist` — the `ℓ¹` distance `∑ i, |u i - v i|` between vectors on a finite index type.
* `colStochastic_l1_le` — a column-stochastic nonnegative matrix is `ℓ¹`-nonexpansive on the
  difference of two probability vectors.
* `colStochastic_l1_contraction` — a strictly positive column-stochastic matrix contracts the
  `ℓ¹` distance of probability vectors by the Doeblin factor `1 - card · δ < 1`.
* `pow_mulVec_l1_le_geometric` — iterating the contraction bounds `l1Dist (P^n x) b` by a geometric
  sequence in the Doeblin factor.
* `colStochastic_pow_mulVec_tendsto` — the matrix powers of a strictly positive column-stochastic
  matrix carry every probability vector to the unique stationary vector, `ℓ¹` and entrywise.
* `regionMatrix_pow_mulVec_tendsto_stationaryVec` — the embedded jump chain on a finite, strongly
  connected closed enabled region with strictly positive restricted transition matrix: the
  `n`-step singleton masses converge to the stationary singleton masses.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Stochastic.Ergodicity`.
-/

open MeasureTheory ProbabilityTheory
open Filter Topology
open scoped ENNReal BigOperators

namespace CRNT

/-- The `ℓ¹` distance between two vectors on a finite index type: `∑ i, |u i - v i|`. -/
def l1Dist {ι : Type*} [Fintype ι] (u v : ι → ℝ) : ℝ := ∑ i, |u i - v i|

@[simp] theorem l1Dist_nonneg {ι : Type*} [Fintype ι] (u v : ι → ℝ) : 0 ≤ l1Dist u v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- A coordinate of the `ℓ¹` distance is dominated by the whole distance. -/
theorem abs_sub_le_l1Dist {ι : Type*} [Fintype ι] (u v : ι → ℝ) (i : ι) :
    |u i - v i| ≤ l1Dist u v := by
  classical
  exact Finset.single_le_sum (f := fun k => |u k - v k|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)

/-- **`ℓ¹`-nonexpansiveness of a column-stochastic matrix.** For a nonnegative matrix `P` whose
columns sum to one and any two vectors `u`, `v`, the `ℓ¹` distance does not grow under `P`:
`l1Dist (P u) (P v) ≤ l1Dist u v`. The estimate is the triangle inequality on each row followed by
column-stochasticity `∑ i, P i j = 1`. -/
theorem colStochastic_l1_le {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hcol : ∀ j, ∑ i, P i j = 1) (u v : ι → ℝ) :
    l1Dist (P.mulVec u) (P.mulVec v) ≤ l1Dist u v := by
  classical
  have hrow : ∀ i, |P.mulVec u i - P.mulVec v i| ≤ ∑ j, P i j * |u j - v j| := by
    intro i
    have hdiff : P.mulVec u i - P.mulVec v i = ∑ j, P i j * (u j - v j) := by
      simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← mul_sub]
    rw [hdiff]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (hP i j)]
  calc l1Dist (P.mulVec u) (P.mulVec v)
      ≤ ∑ i, ∑ j, P i j * |u j - v j| := Finset.sum_le_sum fun i _ => hrow i
    _ = ∑ j, (∑ i, P i j) * |u j - v j| := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
    _ = l1Dist u v := by
        refine Finset.sum_congr rfl fun j _ => ?_; rw [hcol j, one_mul]

/-- **Doeblin contraction of a strictly positive column-stochastic matrix.** If `P` is nonnegative
with column sums one and a uniform positive floor `δ ≤ P i j` on every entry, then `P` contracts
the `ℓ¹` distance of any two probability vectors by the factor `1 - (card ι) · δ`:
`l1Dist (P u) (P v) ≤ (1 - card · δ) · l1Dist u v`. Because the probability difference `u - v` sums
to zero, subtracting the common floor `δ` from each entry of `P` does not change `P (u - v)`; the
floored matrix `P i j - δ` has column sums `1 - card · δ`, and `colStochastic_l1_le` applies to it. -/
theorem colStochastic_l1_contraction {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ)
    (hcol : ∀ j, ∑ i, P i j = 1)
    {δ : ℝ} (hδ : ∀ i j, δ ≤ P i j)
    (u v : ι → ℝ) (hu : ∑ i, u i = 1) (hv : ∑ i, v i = 1) :
    l1Dist (P.mulVec u) (P.mulVec v) ≤ (1 - (Fintype.card ι : ℝ) * δ) * l1Dist u v := by
  classical
  -- the floored matrix `Q i j = P i j - δ` is nonnegative with column sums `1 - card · δ`.
  set Q : Matrix ι ι ℝ := fun i j => P i j - δ with hQ
  have hQnn : ∀ i j, 0 ≤ Q i j := fun i j => sub_nonneg.mpr (hδ i j)
  have hQcol : ∀ j, ∑ i, Q i j = 1 - (Fintype.card ι : ℝ) * δ := by
    intro j
    simp only [hQ, Finset.sum_sub_distrib, hcol j, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  -- the mass balance `∑ (u - v) = 0` makes the floor invisible: `P (u-v) = Q (u-v)`.
  have hbal : ∑ j, (u j - v j) = 0 := by rw [Finset.sum_sub_distrib, hu, hv, sub_self]
  have hPQ : ∀ i, P.mulVec u i - P.mulVec v i = Q.mulVec u i - Q.mulVec v i := by
    intro i
    have hP_eq : P.mulVec u i - P.mulVec v i = ∑ j, P i j * (u j - v j) := by
      simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← mul_sub]
    have hQ_eq : Q.mulVec u i - Q.mulVec v i = ∑ j, Q i j * (u j - v j) := by
      simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← mul_sub]
    rw [hP_eq, hQ_eq]
    have hsplit : ∀ j, P i j * (u j - v j) = Q i j * (u j - v j) + δ * (u j - v j) := by
      intro j; simp only [hQ]; ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hbal, mul_zero, add_zero]
  -- `l1Dist (P u) (P v) = l1Dist (Q u) (Q v)`, then nonexpansiveness of the floored matrix gives the
  -- contraction with factor equal to the (constant) column sum of `Q`.
  have heq : l1Dist (P.mulVec u) (P.mulVec v) = l1Dist (Q.mulVec u) (Q.mulVec v) := by
    simp only [l1Dist]; exact Finset.sum_congr rfl fun i _ => by rw [hPQ i]
  rw [heq]
  -- the column-`l1` bound for `Q` with constant column sum `s := 1 - card · δ`.
  set s : ℝ := 1 - (Fintype.card ι : ℝ) * δ with hs
  have hrow : ∀ i, |Q.mulVec u i - Q.mulVec v i| ≤ ∑ j, Q i j * |u j - v j| := by
    intro i
    have hdiff : Q.mulVec u i - Q.mulVec v i = ∑ j, Q i j * (u j - v j) := by
      simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← mul_sub]
    rw [hdiff]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (hQnn i j)]
  calc l1Dist (Q.mulVec u) (Q.mulVec v)
      ≤ ∑ i, ∑ j, Q i j * |u j - v j| := Finset.sum_le_sum fun i _ => hrow i
    _ = ∑ j, (∑ i, Q i j) * |u j - v j| := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
    _ = ∑ j, s * |u j - v j| := by
        refine Finset.sum_congr rfl fun j _ => ?_; rw [hQcol j]
    _ = s * l1Dist u v := by rw [← Finset.mul_sum]; rfl

/-- A column-stochastic matrix preserves the total sum of a vector. -/
theorem colStochastic_sum_mulVec {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ)
    (hcol : ∀ j, ∑ i, P i j = 1) (x : ι → ℝ) : ∑ i, P.mulVec x i = ∑ j, x j := by
  classical
  have hmv : ∀ i, P.mulVec x i = ∑ j, P i j * x j := fun _ => rfl
  simp_rw [hmv]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul, hcol j, one_mul]

/-- Powers of a column-stochastic matrix are column-stochastic: they preserve total sum, and a
probability vector stays a probability vector under any power. -/
theorem colStochastic_sum_pow_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℝ)
    (hcol : ∀ j, ∑ i, P i j = 1) (x : ι → ℝ) (n : ℕ) :
    ∑ i, (P ^ n).mulVec x i = ∑ j, x j := by
  induction n with
  | zero => simp [Matrix.one_mulVec]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, colStochastic_sum_mulVec P hcol, ih]

/-- **Geometric contraction of the matrix powers.** For a strictly positive column-stochastic
matrix `P` with entry floor `δ`, and any two probability vectors `x`, `y`, the `ℓ¹` distance of the
`n`-step images decays geometrically in the Doeblin factor `s = 1 - card · δ`:
`l1Dist (P^n x) (P^n y) ≤ s^n · l1Dist x y`. Proved by iterating `colStochastic_l1_contraction`, the
total-sum preservation `colStochastic_sum_pow_mulVec` keeping each intermediate image a probability
vector. -/
theorem pow_mulVec_l1_le_geometric {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : Matrix ι ι ℝ)
    (hcol : ∀ j, ∑ i, P i j = 1)
    {δ : ℝ} (hδ : ∀ i j, δ ≤ P i j)
    (x y : ι → ℝ) (hx : ∑ i, x i = 1) (hy : ∑ i, y i = 1) (n : ℕ) :
    l1Dist ((P ^ n).mulVec x) ((P ^ n).mulVec y)
      ≤ (1 - (Fintype.card ι : ℝ) * δ) ^ n * l1Dist x y := by
  set s : ℝ := 1 - (Fintype.card ι : ℝ) * δ with hs
  induction n with
  | zero => simp [Matrix.one_mulVec]
  | succ n ih =>
    have hsumx : ∑ i, (P ^ n).mulVec x i = 1 := by
      rw [colStochastic_sum_pow_mulVec P hcol, hx]
    have hsumy : ∑ i, (P ^ n).mulVec y i = 1 := by
      rw [colStochastic_sum_pow_mulVec P hcol, hy]
    have hstep : l1Dist (P.mulVec ((P ^ n).mulVec x)) (P.mulVec ((P ^ n).mulVec y))
        ≤ s * l1Dist ((P ^ n).mulVec x) ((P ^ n).mulVec y) :=
      colStochastic_l1_contraction P hcol hδ _ _ hsumx hsumy
    have hsnn : 0 ≤ s := by
      have hsumδ : (Fintype.card ι : ℝ) * δ ≤ 1 := by
        have := hcol (Classical.arbitrary ι)
        calc (Fintype.card ι : ℝ) * δ = ∑ _i : ι, δ := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ ≤ ∑ i, P i (Classical.arbitrary ι) := Finset.sum_le_sum fun i _ => hδ i _
          _ = 1 := this
      linarith
    calc l1Dist ((P ^ (n + 1)).mulVec x) ((P ^ (n + 1)).mulVec y)
        = l1Dist (P.mulVec ((P ^ n).mulVec x)) (P.mulVec ((P ^ n).mulVec y)) := by
          rw [pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ ≤ s * l1Dist ((P ^ n).mulVec x) ((P ^ n).mulVec y) := hstep
      _ ≤ s * (s ^ n * l1Dist x y) := by
          exact mul_le_mul_of_nonneg_left ih hsnn
      _ = s ^ (n + 1) * l1Dist x y := by rw [pow_succ']; ring

/-- A strictly positive matrix has a strongly connected support digraph: every entry is a support
edge, so each index reaches every index in one step. -/
theorem supportReaches_of_pos {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ)
    (hpos : ∀ i j, 0 < P i j) (i j : ι) : supportReaches P i j :=
  Relation.ReflTransGen.single (hpos i j).ne'

/-- A strictly positive column-stochastic matrix has a strictly positive fixed *probability*
vector: normalize the positive Perron–Frobenius fixed vector by its total mass. -/
theorem exists_pos_prob_mulVec_fixed_of_pos {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : Matrix ι ι ℝ) (hpos : ∀ i j, 0 < P i j) (hcol : ∀ j, ∑ i, P i j = 1) :
    ∃ b : ι → ℝ, (∀ i, 0 < b i) ∧ (∑ i, b i = 1) ∧ P.mulVec b = b := by
  obtain ⟨b₀, hb₀pos, hb₀fix⟩ :=
    exists_pos_mulVec_fixed_of_stronglyConnected P (fun i j => (hpos i j).le) hcol
      (supportReaches_of_pos P hpos)
  set Z : ℝ := ∑ i, b₀ i with hZ
  have hZpos : 0 < Z := Finset.sum_pos (fun i _ => hb₀pos i) ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  refine ⟨fun i => b₀ i / Z, fun i => div_pos (hb₀pos i) hZpos, ?_, ?_⟩
  · rw [← Finset.sum_div, ← hZ, div_self hZpos.ne']
  · funext i
    have : P.mulVec (fun i => b₀ i / Z) i = P.mulVec b₀ i / Z := by
      simp only [Matrix.mulVec, dotProduct, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_div_assoc]
    rw [this, hb₀fix]

/-- **Convergence of the matrix powers to the unique stationary vector.** A strictly positive
column-stochastic matrix `P` (the strongest finite-state aperiodicity, primitivity at the first
step) carries every probability vector `x` to the unique stationary probability vector `b`: as
`n → ∞`, `P^n x → b`, both in the `ℓ¹` distance and entrywise. The Doeblin factor
`s = 1 - card · δ` lies in `[0, 1)`, so `s^n → 0` and the geometric bound
`pow_mulVec_l1_le_geometric` forces `l1Dist (P^n x) b → 0`; each coordinate is dominated by the
`ℓ¹` distance. This is the finite-state Perron–Frobenius convergence theorem
(Meyn & Tweedie, "Markov Chains and Stochastic Stability"). -/
theorem colStochastic_pow_mulVec_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : Matrix ι ι ℝ) (hpos : ∀ i j, 0 < P i j) (hcol : ∀ j, ∑ i, P i j = 1)
    (x : ι → ℝ) (hx : ∑ i, x i = 1) :
    ∃ b : ι → ℝ, (∀ i, 0 < b i) ∧ (∑ i, b i = 1) ∧ P.mulVec b = b ∧
      Tendsto (fun n => l1Dist ((P ^ n).mulVec x) b) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun n => (P ^ n).mulVec x i) atTop (𝓝 (b i)) := by
  classical
  obtain ⟨b, hbpos, hbsum, hbfix⟩ := exists_pos_prob_mulVec_fixed_of_pos P hpos hcol
  -- a uniform positive floor `δ` on the entries.
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i j, δ ≤ P i j := by
    obtain ⟨ij, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (ι × ι))
      (fun p => P p.1 p.2) ⟨(Classical.arbitrary ι, Classical.arbitrary ι), Finset.mem_univ _⟩
    exact ⟨P ij.1 ij.2, hpos _ _, fun i j => hmin (i, j) (Finset.mem_univ _)⟩
  set s : ℝ := 1 - (Fintype.card ι : ℝ) * δ with hs
  -- the Doeblin factor lies in `[0, 1)`.
  have hsnn : 0 ≤ s := by
    have hsumδ : (Fintype.card ι : ℝ) * δ ≤ 1 := by
      have hc := hcol (Classical.arbitrary ι)
      calc (Fintype.card ι : ℝ) * δ = ∑ _i : ι, δ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ ∑ i, P i (Classical.arbitrary ι) := Finset.sum_le_sum fun i _ => hδ i _
        _ = 1 := hc
    linarith
  have hslt : s < 1 := by
    have hcardpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have : 0 < (Fintype.card ι : ℝ) * δ := mul_pos hcardpos hδpos
    linarith
  -- the fixed point is a fixed point of every power, so `b` is the constant comparison sequence.
  have hbpow : ∀ n, (P ^ n).mulVec b = b := by
    intro n
    induction n with
    | zero => simp [Matrix.one_mulVec]
    | succ n ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hbfix]
  -- the geometric bound on the `ℓ¹` distance.
  have hgeom : ∀ n, l1Dist ((P ^ n).mulVec x) b ≤ s ^ n * l1Dist x b := by
    intro n
    have := pow_mulVec_l1_le_geometric P hcol hδ x b hx hbsum n
    rwa [hbpow n] at this
  -- `s^n · l1Dist x b → 0`.
  have hs0 : Tendsto (fun n => s ^ n * l1Dist x b) atTop (𝓝 0) := by
    have hspow : Tendsto (fun n => s ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hsnn hslt
    simpa using hspow.mul_const (l1Dist x b)
  have hl1 : Tendsto (fun n => l1Dist ((P ^ n).mulVec x) b) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => l1Dist_nonneg _ _) hgeom hs0
  refine ⟨b, hbpos, hbsum, hbfix, hl1, fun i => ?_⟩
  -- entrywise: `|P^n x i - b i| ≤ l1Dist (P^n x) b → 0`.
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hl1
  rw [Real.dist_eq]
  exact abs_sub_le_l1Dist _ b i

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- **Strict positivity of the restricted transition matrix.** The embedded jump chain restricted
to the region `T` reaches every state from every state in a single step: `regionMatrix κ T` is
entrywise strictly positive. This is the strongest finite-state aperiodicity condition,
primitivity at the first step, and it both implies `regionStronglyConnected` and supplies the
Doeblin floor that drives geometric mixing. -/
def regionPositive (N : Network S) (κ : RateConstants N) (T : Set (S → ℕ)) [Fintype ↥T] : Prop :=
  ∀ i j : ↥T, 0 < N.regionMatrix κ T i j

/-- A strictly positive restricted transition matrix is strongly connected: every state reaches
every state in one step. -/
theorem regionStronglyConnected_of_regionPositive (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} [Fintype ↥T] (hpos : N.regionPositive κ T) :
    N.regionStronglyConnected κ T :=
  fun i j => supportReaches_of_pos (N.regionMatrix κ T) hpos i j

/-- **Convergence to the stationary law on a finite, aperiodic, irreducible region.** On a finite
closed enabled region `T` whose restricted transition matrix is strictly positive
(`regionPositive` — primitivity at the first step), the embedded jump chain mixes geometrically:
for every initial probability measure `μ` supported on `T`, the singleton-mass vector of the
`n`-step matrix evolution `(regionMatrix κ T)^n` applied to `μ`'s mass vector converges entrywise to
the singleton-mass vector of the canonical stationary probability measure
`stationaryProbabilityMeasure`. The matrix `regionMatrix κ T` is column-stochastic
(`regionMatrix_colStochastic`); `colStochastic_pow_mulVec_tendsto` produces a positive stationary
probability vector that the powers converge to, and Perron–Frobenius uniqueness
(`mulVec_fixed_unique_of_stronglyConnected`) identifies it with `stationaryVec` of the canonical
stationary measure, the two probability vectors being positive fixed points with unit total mass.
This is the finite-state Perron–Frobenius / Doeblin convergence theorem
(Meyn & Tweedie, "Markov Chains and Stochastic Stability"). -/
theorem regionMatrix_pow_mulVec_tendsto_stationaryVec (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c) {T : Set (S → ℕ)}
    [Fintype ↥T] (hT : N.ClosedEnabledRegion κ T) (hne : T.Nonempty)
    (hpos : N.regionPositive κ T)
    (μ : Measure (S → ℕ)) [IsProbabilityMeasure μ] (hμsupp : μ Tᶜ = 0) :
    ∀ i : ↥T, Tendsto
        (fun n => ((N.regionMatrix κ T) ^ n).mulVec (stationaryVec (T := T) μ) i) atTop
        (𝓝 (stationaryVec (T := T) (N.stationaryProbabilityMeasure κ c T) i)) := by
  classical
  haveI : Nonempty ↥T := hne.to_subtype
  set P : Matrix ↥T ↥T ℝ := N.regionMatrix κ T with hP
  set ρ := N.stationaryProbabilityMeasure κ c T with hρ
  have hPnn : ∀ i j, 0 ≤ P i j := N.regionMatrix_nonneg κ T
  have hPcol : ∀ j, ∑ i, P i j = 1 := N.regionMatrix_colStochastic κ hT
  have hPpos : ∀ i j, 0 < P i j := hpos
  -- the initial mass vector is a probability vector.
  have hxsum : ∑ i, stationaryVec (T := T) μ i = 1 := stationaryVec_sum_eq_one μ hμsupp
  -- the matrix powers converge to a positive stationary probability vector `b`.
  obtain ⟨b, hbpos, hbsum, hbfix, _hl1, hentry⟩ :=
    colStochastic_pow_mulVec_tendsto P hPpos hPcol (stationaryVec (T := T) μ) hxsum
  -- the canonical stationary mass vector is a positive fixed probability vector.
  have hρsupp : ρ Tᶜ = 0 := N.stationaryProbabilityMeasure_compl_eq_zero κ c T
  haveI hρprob : IsProbabilityMeasure ρ :=
    (N.stationaryProbabilityMeasure_isInvariant_isProbability κ c hc hcb hT (Set.toFinite T) hne).2
  have hρinv : Kernel.Invariant (N.jumpKernel κ) ρ :=
    (N.stationaryProbabilityMeasure_isInvariant_isProbability κ c hc hcb hT (Set.toFinite T) hne).1
  have hρfix : P.mulVec (stationaryVec (T := T) ρ) = stationaryVec (T := T) ρ :=
    N.stationaryVec_mulVec_fixed κ ρ hρsupp hρinv
  have hρpos : ∀ i, 0 < stationaryVec (T := T) ρ i :=
    N.stationaryVec_stationaryProbabilityMeasure_pos κ c hc hT hne
  have hρsum : ∑ i, stationaryVec (T := T) ρ i = 1 := stationaryVec_sum_eq_one ρ hρsupp
  -- Perron–Frobenius uniqueness identifies the two stationary probability vectors.
  obtain ⟨t, ht⟩ := mulVec_fixed_unique_of_stronglyConnected P hPnn
    (stationaryVec (T := T) ρ) b hρpos hρfix hbfix
    (N.regionStronglyConnected_of_regionPositive κ hpos)
  have ht1 : t = 1 := by
    have hsumeq : (∑ i, b i) = t * ∑ i, stationaryVec (T := T) ρ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [ht]; rfl
    rw [hbsum, hρsum, mul_one] at hsumeq
    exact hsumeq.symm
  have hbeq : b = stationaryVec (T := T) ρ := by
    funext i; rw [ht, ht1, one_smul]
  intro i
  rw [← hbeq]
  exact hentry i

end Network

end CRNT

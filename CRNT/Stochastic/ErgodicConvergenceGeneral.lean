import CRNT.Stochastic.ErgodicConvergence

/-!
# Geometric convergence under the general primitivity hypothesis

On a finite closed enabled region the embedded jump chain is a finite-state Markov chain whose
restricted transition matrix `regionMatrix κ T` is column-stochastic
(`regionMatrix_colStochastic`). `CRNT.Stochastic.ErgodicConvergence` proves geometric convergence to
the stationary law under the strongest aperiodicity condition, primitivity at the first step
(`regionPositive`: the matrix is entrywise strictly positive). This module relaxes the hypothesis to
the standard finite-state primitivity condition: some fixed power is strictly positive,
`∃ N > 0, ∀ i j, 0 < (P ^ N) i j`. This is the Perron–Frobenius characterisation of a primitive
(irreducible and aperiodic) nonnegative matrix (Meyn & Tweedie, "Markov Chains and Stochastic
Stability"); the dominant eigenvalue `1` is simple and every other eigenvalue lies strictly inside
the unit disk, so all subdominant modes decay and the chain mixes geometrically.

The argument lifts the one-step contraction of `ErgodicConvergence` to the `N`-step matrix.
The power `Q = P ^ N` is itself column-stochastic (`colStochastic_pow_colStochastic`) and strictly
positive, so `colStochastic_pow_mulVec_tendsto` supplies a strictly positive stationary probability
vector `b` with `Q b = b`. That `b` is in fact `P`-fixed: `P b` is another `Q`-stationary
probability vector, and Perron–Frobenius uniqueness on the strongly connected `Q`
(`mulVec_fixed_unique_of_stronglyConnected`) forces `P b = b`.

For the rate, write `n = N · (n / N) + n % N`, so `P ^ n = Q ^ (n / N) · P ^ (n % N)` and
`(P ^ n) x = Q ^ (n / N) (P ^ (n % N) x)`. The residual factor is `ℓ¹`-nonexpansive
(`colStochastic_pow_mulVec_l1_le`, iterating `colStochastic_l1_le`), and the `Q`-power factor
contracts geometrically by the Doeblin factor `c = 1 − card · δ` of `Q`
(`pow_mulVec_l1_le_geometric`). Hence
`l1Dist (P ^ n x) b ≤ c ^ (n / N) · l1Dist x b`. The exponent `n / N → ∞`, so `c ^ (n / N) → 0`
and `l1Dist (P ^ n x) b → 0`; each coordinate is dominated by the `ℓ¹` distance.

## Main results

* `colStochastic_pow_colStochastic` — a power of a column-stochastic matrix is column-stochastic.
* `colStochastic_pow_mulVec_l1_le` — a power of a column-stochastic nonnegative matrix is
  `ℓ¹`-nonexpansive on two vectors.
* `colStochastic_primitive_pow_mulVec_tendsto` — a primitive column-stochastic nonnegative matrix
  (`∃ N > 0, ∀ i j, 0 < (P ^ N) i j`) carries every probability vector to the unique stationary
  vector, `ℓ¹` and entrywise.
* `regionPrimitive` — the region-level primitivity hypothesis: some power of `regionMatrix κ T` is
  entrywise strictly positive.
* `regionMatrix_primitive_pow_mulVec_tendsto_stationaryVec` — the embedded jump chain on a finite,
  primitive closed enabled region: the `n`-step singleton masses converge to the stationary
  singleton masses.

Depends on: `CRNT.Stochastic.ErgodicConvergence`.
-/

open MeasureTheory ProbabilityTheory
open Filter Topology
open scoped ENNReal BigOperators

namespace CRNT

/-- A power of a column-stochastic matrix is column-stochastic: applying the power to the `j`-th
standard basis vector reads off column `j`, and `colStochastic_sum_pow_mulVec` preserves the total
sum, which is one for a basis vector. -/
theorem colStochastic_pow_colStochastic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hcol : ∀ j, ∑ i, P i j = 1) (N : ℕ) :
    ∀ j, ∑ i, (P ^ N) i j = 1 := by
  classical
  intro j
  -- column `j` is the image of the `j`-th standard basis vector.
  have hcolvec : ∀ i, (P ^ N) i j = (P ^ N).mulVec (fun k => if k = j then (1 : ℝ) else 0) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl, mul_one]
    · intro k _ hk; rw [if_neg hk, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  simp_rw [hcolvec]
  rw [colStochastic_sum_pow_mulVec P hcol]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro k _ hk; rw [if_neg hk]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- **`ℓ¹`-nonexpansiveness of the powers.** A power of a column-stochastic nonnegative matrix does
not grow the `ℓ¹` distance of two vectors: iterate the one-step nonexpansiveness
`colStochastic_l1_le`. -/
theorem colStochastic_pow_mulVec_l1_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : ∀ i j, 0 ≤ P i j) (hcol : ∀ j, ∑ i, P i j = 1)
    (u v : ι → ℝ) (r : ℕ) :
    l1Dist ((P ^ r).mulVec u) ((P ^ r).mulVec v) ≤ l1Dist u v := by
  induction r with
  | zero => simp [Matrix.one_mulVec]
  | succ r ih =>
    calc l1Dist ((P ^ (r + 1)).mulVec u) ((P ^ (r + 1)).mulVec v)
        = l1Dist (P.mulVec ((P ^ r).mulVec u)) (P.mulVec ((P ^ r).mulVec v)) := by
          rw [pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ ≤ l1Dist ((P ^ r).mulVec u) ((P ^ r).mulVec v) := colStochastic_l1_le P hP hcol _ _
      _ ≤ l1Dist u v := ih

/-- A power of an entrywise nonnegative matrix is entrywise nonnegative. -/
theorem matrix_pow_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (k : ℕ) : ∀ i j, 0 ≤ (P ^ k) i j := by
  induction k with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    by_cases hij : i = j
    · rw [if_pos hij]; exact zero_le_one
    · rw [if_neg hij]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun m _ => mul_nonneg (ih i m) (hP m j)

/-- **A positive power entry yields a support walk.** If a power `(P ^ k) i j` of a nonnegative
matrix is strictly positive, then `i` reaches `j` in the support digraph of `P`: a positive
`k`-step weight forces a length-`k` walk along strictly positive single-step entries. -/
theorem supportReaches_of_pow_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : ∀ i j, 0 ≤ P i j) (k : ℕ) :
    ∀ {i j : ι}, 0 < (P ^ k) i j → supportReaches P i j := by
  induction k with
  | zero =>
    intro i j hpos
    rw [pow_zero, Matrix.one_apply] at hpos
    by_cases hij : i = j
    · subst hij; exact Relation.ReflTransGen.refl
    · rw [if_neg hij] at hpos; exact absurd hpos (lt_irrefl 0)
  | succ k ih =>
    intro i j hpos
    rw [pow_succ, Matrix.mul_apply] at hpos
    -- some intermediate `m` carries positive `k`-step weight into `j` with a positive last step.
    have hterm : ∃ m ∈ Finset.univ, (P ^ k) i m * P m j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hpos.ne' (Finset.sum_eq_zero hcon)
    obtain ⟨m, -, hm⟩ := hterm
    have hkpos : 0 < (P ^ k) i m :=
      (matrix_pow_nonneg P hP k i m).lt_of_ne fun h => hm (by rw [← h, zero_mul])
    have hlast : P m j ≠ 0 := fun h => hm (by rw [h, mul_zero])
    exact Relation.ReflTransGen.tail (ih hkpos) hlast
theorem tendsto_natDiv_atTop {N : ℕ} (hN : 0 < N) :
    Tendsto (fun n => n / N) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨b * N, fun n hn => ?_⟩
  rw [Nat.le_div_iff_mul_le hN]
  exact le_trans (Nat.mul_comm b N ▸ le_refl (b * N)) hn

/-- **Geometric convergence under primitivity.** A column-stochastic nonnegative matrix `P` that is
*primitive* — some fixed power `P ^ N` (with `N > 0`) is entrywise strictly positive — carries every
probability vector `x` to the unique stationary probability vector `b`: as `n → ∞`, `P ^ n x → b`,
both in the `ℓ¹` distance and entrywise. This is the standard finite-state
aperiodicity-and-irreducibility condition; the strictly positive power `Q = P ^ N` supplies the
Doeblin contraction of `ErgodicConvergence`, and writing `n = N · (n / N) + n % N` interleaves
`Q`-contraction with per-step nonexpansiveness of the residual `P ^ (n % N)` factor (Meyn & Tweedie,
"Markov Chains and Stochastic Stability"; Perron–Frobenius primitivity). -/
theorem colStochastic_primitive_pow_mulVec_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (P : Matrix ι ι ℝ) (hP : ∀ i j, 0 ≤ P i j) (hcol : ∀ j, ∑ i, P i j = 1)
    {N : ℕ} (hN : 0 < N) (hpos : ∀ i j, 0 < (P ^ N) i j)
    (x : ι → ℝ) (hx : ∑ i, x i = 1) :
    ∃ b : ι → ℝ, (∀ i, 0 < b i) ∧ (∑ i, b i = 1) ∧ P.mulVec b = b ∧
      Tendsto (fun n => l1Dist ((P ^ n).mulVec x) b) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun n => (P ^ n).mulVec x i) atTop (𝓝 (b i)) := by
  classical
  set Q : Matrix ι ι ℝ := P ^ N with hQ
  have hQcol : ∀ j, ∑ i, Q i j = 1 := colStochastic_pow_colStochastic P hcol N
  -- `Q = P ^ N` is strictly positive and column-stochastic, so its powers converge to a unique
  -- stationary probability vector `b`.
  obtain ⟨b, hbpos, hbsum, hbfix, _hl1Q, _hentryQ⟩ :=
    colStochastic_pow_mulVec_tendsto Q hpos hQcol x hx
  -- a positive uniform floor `δ` on `Q`, giving the Doeblin factor `c = 1 - card · δ ∈ [0, 1)`.
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i j, δ ≤ Q i j := by
    obtain ⟨ij, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (ι × ι))
      (fun p => Q p.1 p.2) ⟨(Classical.arbitrary ι, Classical.arbitrary ι), Finset.mem_univ _⟩
    exact ⟨Q ij.1 ij.2, hpos _ _, fun i j => hmin (i, j) (Finset.mem_univ _)⟩
  set c : ℝ := 1 - (Fintype.card ι : ℝ) * δ with hc
  have hcnn : 0 ≤ c := by
    have hsumδ : (Fintype.card ι : ℝ) * δ ≤ 1 := by
      have hq := hQcol (Classical.arbitrary ι)
      calc (Fintype.card ι : ℝ) * δ = ∑ _i : ι, δ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ ∑ i, Q i (Classical.arbitrary ι) := Finset.sum_le_sum fun i _ => hδ i _
        _ = 1 := hq
    linarith
  have hclt : c < 1 := by
    have hcardpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    have : 0 < (Fintype.card ι : ℝ) * δ := mul_pos hcardpos hδpos
    linarith
  -- `b` is `P`-fixed. `P b` is a `Q`-stationary probability vector, and Perron–Frobenius uniqueness
  -- on the strongly connected `Q` forces `P b = b`.
  have hQfixPb : Q.mulVec (P.mulVec b) = P.mulVec b := by
    rw [show Q.mulVec (P.mulVec b) = P.mulVec (Q.mulVec b) by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ, ← pow_succ, ← pow_succ'], hbfix]
  have hPbpos : ∀ i, 0 ≤ P.mulVec b i := by
    intro i
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hP i j) (hbpos j).le
  have hPbsum : ∑ i, P.mulVec b i = 1 := by
    rw [colStochastic_sum_mulVec P hcol, hbsum]
  have hQconn : ∀ i j : ι, supportReaches Q i j := supportReaches_of_pos Q hpos
  obtain ⟨t, ht⟩ := mulVec_fixed_unique_of_stronglyConnected Q (fun i j => (hpos i j).le)
    b (P.mulVec b) hbpos hbfix hQfixPb hQconn
  have ht1 : t = 1 := by
    have hsumeq : (∑ i, P.mulVec b i) = t * ∑ i, b i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [ht]; rfl
    rw [hPbsum, hbsum, mul_one] at hsumeq
    exact hsumeq.symm
  have hPbfix : P.mulVec b = b := by funext i; rw [ht, ht1, one_smul]
  -- the geometric bound `l1Dist (P ^ n x) b ≤ c ^ (n / N) · l1Dist x b`.
  have hbpow : ∀ m, (P ^ m).mulVec b = b := by
    intro m
    induction m with
    | zero => simp [Matrix.one_mulVec]
    | succ m ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hPbfix]
  have hgeom : ∀ n, l1Dist ((P ^ n).mulVec x) b ≤ c ^ (n / N) * l1Dist x b := by
    intro n
    -- residual decomposition `P ^ n = Q ^ (n / N) * P ^ (n % N)`.
    have hsplit : (P ^ n).mulVec x
        = (Q ^ (n / N)).mulVec ((P ^ (n % N)).mulVec x) := by
      rw [Matrix.mulVec_mulVec, hQ, ← pow_mul, ← pow_add, Nat.div_add_mod n N]
    -- the residual factor is a probability vector.
    have hressum : ∑ i, (P ^ (n % N)).mulVec x i = 1 := by
      rw [colStochastic_sum_pow_mulVec P hcol, hx]
    -- `b` equals its residual image, used as the comparison probability vector.
    have hbsplit : b = (Q ^ (n / N)).mulVec ((P ^ (n % N)).mulVec b) := by
      rw [Matrix.mulVec_mulVec, hQ, ← pow_mul, ← pow_add, Nat.div_add_mod n N, hbpow n]
    calc l1Dist ((P ^ n).mulVec x) b
        = l1Dist ((Q ^ (n / N)).mulVec ((P ^ (n % N)).mulVec x))
            ((Q ^ (n / N)).mulVec ((P ^ (n % N)).mulVec b)) := by
          rw [hsplit]; conv_lhs => rw [hbsplit]
      _ ≤ c ^ (n / N) * l1Dist ((P ^ (n % N)).mulVec x) ((P ^ (n % N)).mulVec b) := by
          have hmain := pow_mulVec_l1_le_geometric Q hQcol hδ ((P ^ (n % N)).mulVec x)
            ((P ^ (n % N)).mulVec b) hressum (by rw [colStochastic_sum_pow_mulVec P hcol, hbsum])
            (n / N)
          rw [← hc] at hmain
          exact hmain
      _ ≤ c ^ (n / N) * l1Dist x b := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hcnn _)
          exact colStochastic_pow_mulVec_l1_le P hP hcol x b (n % N)
  -- `c ^ (n / N) · l1Dist x b → 0`, since `n / N → ∞` and `0 ≤ c < 1`.
  have hcpow0 : Tendsto (fun n => c ^ (n / N)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hcnn hclt).comp (tendsto_natDiv_atTop hN)
  have hbound0 : Tendsto (fun n => c ^ (n / N) * l1Dist x b) atTop (𝓝 0) := by
    simpa using hcpow0.mul_const (l1Dist x b)
  have hl1 : Tendsto (fun n => l1Dist ((P ^ n).mulVec x) b) atTop (𝓝 0) :=
    squeeze_zero (fun n => l1Dist_nonneg _ _) hgeom hbound0
  refine ⟨b, hbpos, hbsum, hPbfix, hl1, fun i => ?_⟩
  -- entrywise: `|P ^ n x i - b i| ≤ l1Dist (P ^ n x) b → 0`.
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hl1
  rw [Real.dist_eq]
  exact abs_sub_le_l1Dist _ b i

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- **Primitivity of the restricted transition matrix.** The embedded jump chain restricted to the
region `T` reaches every state from every state in some fixed number `N > 0` of steps:
`(regionMatrix κ T) ^ N` is entrywise strictly positive. This is the standard finite-state
primitivity (irreducibility together with aperiodicity) condition, weaker than `regionPositive`
(which is the `N = 1` case), and it supplies the `N`-step Doeblin floor that drives geometric
mixing. -/
def regionPrimitive (N : Network S) (κ : RateConstants N) (T : Set (S → ℕ)) [Fintype ↥T] : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∀ i j : ↥T, 0 < (N.regionMatrix κ T ^ k) i j

/-- The one-step strictly positive case `regionPositive` is the `k = 1` instance of primitivity. -/
theorem regionPrimitive_of_regionPositive (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    [Fintype ↥T] (hpos : N.regionPositive κ T) : N.regionPrimitive κ T :=
  ⟨1, Nat.one_pos, fun i j => by rw [pow_one]; exact hpos i j⟩

/-- **Convergence to the stationary law on a finite, primitive region.** On a finite closed enabled
region `T` whose restricted transition matrix is primitive (`regionPrimitive` — some power is
strictly positive, the standard irreducibility-and-aperiodicity condition), the embedded jump chain
mixes geometrically: for every initial probability measure `μ` supported on `T`, the singleton-mass
vector of the `n`-step matrix evolution `(regionMatrix κ T) ^ n` applied to `μ`'s mass vector
converges entrywise to the singleton-mass vector of the canonical stationary probability measure
`stationaryProbabilityMeasure`. The matrix `regionMatrix κ T` is column-stochastic and nonnegative
(`regionMatrix_colStochastic`, `regionMatrix_nonneg`);
`colStochastic_primitive_pow_mulVec_tendsto` produces a positive stationary probability vector that
the powers converge to, and Perron–Frobenius uniqueness
(`mulVec_fixed_unique_of_stronglyConnected`, the primitive matrix being strongly connected) identifies
it with `stationaryVec` of the canonical stationary measure. This is the finite-state
Perron–Frobenius / Doeblin convergence theorem under the general primitivity hypothesis
(Meyn & Tweedie, "Markov Chains and Stochastic Stability"). -/
theorem regionMatrix_primitive_pow_mulVec_tendsto_stationaryVec (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c) {T : Set (S → ℕ)}
    [Fintype ↥T] (hT : N.ClosedEnabledRegion κ T) (hne : T.Nonempty)
    (hprim : N.regionPrimitive κ T)
    (μ : Measure (S → ℕ)) [IsProbabilityMeasure μ] (hμsupp : μ Tᶜ = 0) :
    ∀ i : ↥T, Tendsto
        (fun n => ((N.regionMatrix κ T) ^ n).mulVec (stationaryVec (T := T) μ) i) atTop
        (𝓝 (stationaryVec (T := T) (N.stationaryProbabilityMeasure κ c T) i)) := by
  classical
  haveI : Nonempty ↥T := hne.to_subtype
  set P : Matrix ↥T ↥T ℝ := N.regionMatrix κ T with hP
  set ρ := N.stationaryProbabilityMeasure κ c T with hρ
  obtain ⟨k, hk, hkpos⟩ := hprim
  have hPnn : ∀ i j, 0 ≤ P i j := N.regionMatrix_nonneg κ T
  have hPcol : ∀ j, ∑ i, P i j = 1 := N.regionMatrix_colStochastic κ hT
  -- the initial mass vector is a probability vector.
  have hxsum : ∑ i, stationaryVec (T := T) μ i = 1 := stationaryVec_sum_eq_one μ hμsupp
  -- the matrix powers converge to a positive stationary probability vector `b`.
  obtain ⟨b, hbpos, hbsum, hbfix, _hl1, hentry⟩ :=
    colStochastic_primitive_pow_mulVec_tendsto P hPnn hPcol hk hkpos
      (stationaryVec (T := T) μ) hxsum
  -- the matrix is strongly connected: from primitivity, `P ^ k` strictly positive reaches every
  -- state, so `P` reaches every state along the same `k`-step support path.
  have hPconn : N.regionStronglyConnected κ T := by
    intro i j
    -- a `k`-step strictly positive entry yields a support walk of length `k` from `i` to `j`.
    have hij : 0 < (P ^ k) i j := hkpos i j
    -- reduce strong connectivity to reachability in the support digraph of `P`.
    exact supportReaches_of_pow_pos P hPnn k hij
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
    (stationaryVec (T := T) ρ) b hρpos hρfix hbfix hPconn
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

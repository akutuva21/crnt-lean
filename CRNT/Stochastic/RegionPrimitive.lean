import CRNT.Stochastic.ErgodicConvergenceGeneral

/-!
# Primitivity from strong connectivity and a self-loop

The geometric-convergence theorem
`regionMatrix_primitive_pow_mulVec_tendsto_stationaryVec` assumes the region-level primitivity
hypothesis `regionPrimitive` — that some fixed power of the restricted transition matrix is
entrywise strictly positive. This module discharges that hypothesis for a concrete, checkable
structural class: a strongly connected support digraph carrying a single self-loop.

The finite-state Perron–Frobenius criterion for primitivity is irreducibility together with
aperiodicity (Meyn & Tweedie, "Markov Chains and Stochastic Stability"; Perron–Frobenius primitive
matrices). Irreducibility is `regionStronglyConnected`: every state reaches every state along the
support digraph. Aperiodicity is supplied by a *self-loop* — a state `s` with strictly positive
diagonal entry `0 < P s s`, breaking the period to one.

The combinatorial mechanism: a positive matrix-power entry `0 < (P ^ ℓ) i j` is exactly a length-`ℓ`
walk along strictly positive single-step entries (`exists_pos_pow_of_supportReaches`). Strong
connectivity gives, for each ordered pair `(i, j)`, a walk `i ⇝ s` and a walk `s ⇝ j`; composing
them through the self-loop state and padding the walk length at `s` with the loop yields walks of
*any* length above a per-pair threshold (`pos_pow_of_loop_le`). The finite type has finitely many
pairs, so a single common length `N` works for all of them, giving an entrywise strictly positive
power `P ^ N` and hence primitivity.

## Main results

* `exists_pos_pow_of_supportReaches` — a support-digraph walk yields a strictly positive
  matrix-power entry of the matching length.
* `pos_pow_self_loop_succ` — a self-loop lets a positive power entry into the loop state be extended
  by one step.
* `pos_pow_of_loop_le` — through a self-loop state, a positive power entry persists at every larger
  exponent.
* `primitive_of_stronglyConnected_self_loop` — a nonnegative matrix with strongly connected support
  digraph and a self-loop has a strictly positive fixed power: `∃ N > 0, ∀ i j, 0 < (P ^ N) i j`.
* `regionPrimitive_of_stronglyConnected_self_loop` — the region-level corollary: strong connectivity
  plus a positive diagonal entry of `regionMatrix κ T` gives `regionPrimitive κ T`.
* `regionMatrix_self_loop_of_jumpProb_pos` — a network-level source of the self-loop: a region state
  `n` carrying a reaction that returns to `n` with positive jump probability has a positive diagonal
  entry.

Depends on:
`CRNT.Stochastic.ErgodicConvergenceGeneral`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace CRNT

/-- **Walks give positive power entries.** If `i` reaches `j` in the support digraph of a
nonnegative matrix `P`, then some power `(P ^ ℓ) i j` is strictly positive: a length-`ℓ` walk along
strictly positive single-step entries multiplies to a strictly positive `ℓ`-step weight. -/
theorem exists_pos_pow_of_supportReaches {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : ∀ i j, 0 ≤ P i j) {i j : ι} (hij : supportReaches P i j) :
    ∃ ℓ : ℕ, 0 < (P ^ ℓ) i j := by
  induction hij using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨0, ?_⟩
    rw [pow_zero, Matrix.one_apply_eq]; exact zero_lt_one
  | @head a c e _ ih =>
    obtain ⟨ℓ, hℓ⟩ := ih
    refine ⟨ℓ + 1, ?_⟩
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_pos' (fun k _ => mul_nonneg (hP a k) (matrix_pow_nonneg P hP ℓ k j))
      ⟨c, Finset.mem_univ c, ?_⟩
    exact mul_pos ((hP a c).lt_of_ne (Ne.symm e)) hℓ

/-- **Power entries compose.** A strictly positive `a`-step weight from `i` to `m` followed by a
strictly positive `b`-step weight from `m` to `j` gives a strictly positive `(a + b)`-step weight
from `i` to `j`. -/
theorem pos_pow_add_of_pos_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : ∀ i j, 0 ≤ P i j) {i m j : ι} {a b : ℕ}
    (ha : 0 < (P ^ a) i m) (hb : 0 < (P ^ b) m j) :
    0 < (P ^ (a + b)) i j := by
  rw [pow_add, Matrix.mul_apply]
  refine Finset.sum_pos'
    (fun k _ => mul_nonneg (matrix_pow_nonneg P hP a i k) (matrix_pow_nonneg P hP b k j))
    ⟨m, Finset.mem_univ m, mul_pos ha hb⟩

/-- **A self-loop powers up.** A strictly positive diagonal entry `0 < P s s` gives a strictly
positive `k`-step weight from `s` to itself for every `k`: the length-`k` walk that loops at `s`. -/
theorem pos_pow_self_loop {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : ∀ i j, 0 ≤ P i j) {s : ι} (hs : 0 < P s s) (k : ℕ) :
    0 < (P ^ k) s s := by
  induction k with
  | zero => rw [pow_zero, Matrix.one_apply_eq]; exact zero_lt_one
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_pos' (fun n _ => mul_nonneg (hP s n) (matrix_pow_nonneg P hP k n s))
      ⟨s, Finset.mem_univ s, mul_pos hs ih⟩

/-- **A self-loop extends a positive power by one step.** If `0 < P s s` and some power
`(P ^ ℓ) i s` is positive, then `(P ^ (ℓ + 1)) i s` is positive: loop once more at `s`. -/
theorem pos_pow_self_loop_succ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : ∀ i j, 0 ≤ P i j) {s i : ι} (hs : 0 < P s s) {ℓ : ℕ}
    (hℓ : 0 < (P ^ ℓ) i s) :
    0 < (P ^ (ℓ + 1)) i s :=
  pos_pow_add_of_pos_pos P hP hℓ (pos_pow_self_loop P hP hs 1)

/-- **Routing through a self-loop fills an interval of lengths.** With a self-loop at `s`, a
strictly positive `a`-step weight `i ⇝ s` and a strictly positive `b`-step weight `s ⇝ j` give a
strictly positive `N`-step weight `i ⇝ j` for *every* `N ≥ a + b`: spend `a` steps reaching `s`,
loop at `s` for the surplus `N - (a + b)` steps, then spend `b` steps reaching `j`. -/
theorem pos_pow_of_loop_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : ∀ i j, 0 ≤ P i j) {s i j : ι} (hs : 0 < P s s) {a b N : ℕ}
    (ha : 0 < (P ^ a) i s) (hb : 0 < (P ^ b) s j) (hN : a + b ≤ N) :
    0 < (P ^ N) i j := by
  -- write `N = a + (N - a - b) + b`, looping at `s` for the surplus.
  obtain ⟨d, hd⟩ := Nat.le.dest hN
  -- `N = a + b + d`; loop `d` times at `s`.
  have hloop : 0 < (P ^ (b + d)) s j :=
    pos_pow_add_of_pos_pos P hP (pos_pow_self_loop P hP hs d) hb |>.trans_eq
      (by rw [Nat.add_comm d b])
  have := pos_pow_add_of_pos_pos P hP ha hloop
  rwa [show a + (b + d) = N by omega] at this

/-- **Primitivity from strong connectivity and a self-loop.** A nonnegative matrix `P` whose support
digraph is strongly connected (`∀ i j, supportReaches P i j`) and which carries a self-loop
(`0 < P s s` for some `s`) is *primitive*: there is a fixed exponent `N > 0` with `P ^ N` entrywise
strictly positive. This is the standard finite-state Perron–Frobenius criterion — irreducibility
plus aperiodicity, the latter coming from the period-one self-loop (Meyn & Tweedie, "Markov Chains
and Stochastic Stability").

For each ordered pair `(i, j)` strong connectivity yields a walk `i ⇝ s` of some length `a i` and a
walk `s ⇝ j` of some length `b j` (`exists_pos_pow_of_supportReaches`); through the self-loop the
`(i, j)` weight is then positive at every exponent `≥ a i + b j` (`pos_pow_of_loop_le`). Taking `N`
strictly above the finite supremum of `a i + b j + 1` over the finite index type makes every entry
of `P ^ N` positive at once. -/
theorem primitive_of_stronglyConnected_self_loop {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : Matrix ι ι ℝ) (hP : ∀ i j, 0 ≤ P i j) (hsc : ∀ i j, supportReaches P i j)
    {s : ι} (hs : 0 < P s s) :
    ∃ N : ℕ, 0 < N ∧ ∀ i j, 0 < (P ^ N) i j := by
  classical
  -- a uniform length reaching `s` from any `i`, and reaching any `j` from `s`.
  choose a ha using fun i => exists_pos_pow_of_supportReaches P hP (hsc i s)
  choose b hb using fun j => exists_pos_pow_of_supportReaches P hP (hsc s j)
  -- a common exponent dominating every per-pair threshold `a i + b j`, and positive.
  set N : ℕ := 1 + (Finset.univ.sup a + Finset.univ.sup b) with hNdef
  refine ⟨N, by omega, fun i j => ?_⟩
  have hai : a i ≤ Finset.univ.sup a := Finset.le_sup (Finset.mem_univ i)
  have hbj : b j ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ j)
  exact pos_pow_of_loop_le P hP hs (ha i) (hb j) (by omega)

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- **Region primitivity from strong connectivity and a region self-loop.** On a finite region `T`,
if the restricted transition matrix is strongly connected (`regionStronglyConnected`) and carries a
self-loop — a state with strictly positive diagonal entry `0 < regionMatrix κ T s s` — then the
region is primitive (`regionPrimitive`): some fixed power of `regionMatrix κ T` is entrywise
strictly positive. This discharges the primitivity hypothesis of
`regionMatrix_primitive_pow_mulVec_tendsto_stationaryVec` for the concrete
irreducible-plus-aperiodic structural class, the finite-state Perron–Frobenius criterion (Meyn &
Tweedie, "Markov Chains and Stochastic Stability"). -/
theorem regionPrimitive_of_stronglyConnected_self_loop (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} [Fintype ↥T] [Nonempty ↥T]
    (hsc : N.regionStronglyConnected κ T) {s : ↥T} (hs : 0 < N.regionMatrix κ T s s) :
    N.regionPrimitive κ T := by
  obtain ⟨k, hk, hkpos⟩ :=
    primitive_of_stronglyConnected_self_loop (N.regionMatrix κ T) (N.regionMatrix_nonneg κ T) hsc hs
  exact ⟨k, hk, hkpos⟩

/-- **A network self-loop is a positive region diagonal entry.** A region state `n ∈ T` with
strictly positive exit rate carrying a reaction `r` that returns to the same count
(`jumpNextCount n r = n`) with strictly positive jump probability `0 < jumpProb κ n r` has a
strictly positive diagonal entry `0 < regionMatrix κ T ⟨n⟩ ⟨n⟩`: the embedded jump chain holds at
`n` along that reaction. This is the network-level source of the self-loop driving aperiodicity. -/
theorem regionMatrix_self_loop_of_jumpProb_pos (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} [Fintype ↥T] {n : S → ℕ} (hn : n ∈ T)
    (hexit : N.exitRate κ n ≠ 0) {r : N.R} (hr : N.jumpNextCount n r = n)
    (hprob : 0 < N.jumpProb κ n r) :
    0 < N.regionMatrix κ T ⟨n, hn⟩ ⟨n, hn⟩ := by
  classical
  -- the diagonal entry is the kernel mass of the singleton `{n}` from `n`.
  have hmass : N.jumpKernel κ n {n} =
      ∑ r' : N.R, ENNReal.ofReal (N.jumpProb κ n r') * ({n} : Set (S → ℕ)).indicator 1
        (N.jumpNextCount n r') :=
    N.jumpKernel_apply_of_exitRate_pos κ n hexit {n}
  -- the `r`-term is strictly positive; the whole nonnegative sum is therefore positive.
  have hterm : 0 < ENNReal.ofReal (N.jumpProb κ n r) * ({n} : Set (S → ℕ)).indicator 1
      (N.jumpNextCount n r) := by
    rw [hr, Set.indicator_of_mem (Set.mem_singleton n), Pi.one_apply, mul_one]
    exact ENNReal.ofReal_pos.mpr hprob
  have hpos : 0 < N.jumpKernel κ n {n} := by
    rw [hmass]
    refine lt_of_lt_of_le hterm
      (Finset.single_le_sum (f := fun r' : N.R =>
        ENNReal.ofReal (N.jumpProb κ n r') * ({n} : Set (S → ℕ)).indicator 1
          (N.jumpNextCount n r'))
        (fun r' _ => bot_le) (Finset.mem_univ r))
  have hne : N.jumpKernel κ n {n} ≠ ∞ := measure_ne_top _ _
  show 0 < (N.jumpKernel κ (⟨n, hn⟩ : ↥T) {((⟨n, hn⟩ : ↥T) : S → ℕ)}).toReal
  exact ENNReal.toReal_pos hpos.ne' hne

end Network

end CRNT

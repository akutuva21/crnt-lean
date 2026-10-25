import CRNT.Stochastic.FullyOpenErgodic
import CRNT.Stochastic.BinaryFlowsMixed
import CRNT.Graph.LinkageClass

/-!
# Positive recurrence of binary strongly connected networks with in- and outflows

This module proves, for leaf **P7** of `docs/field-map.md`, the theorem of Anderson–Kim
(*Some network conditions for positive recurrence of stochastically modeled reaction networks*,
SIAM J. Appl. Math. 78 (2018), Theorem 2.1): a **binary** network whose complex graph is
**strongly connected** (weakly reversible with a single linkage class), with every inflow
`0 → S` and every outflow `S → 0` added, is ergodic for every choice of rate constants
(`binaryStronglyConnected_fullyOpen_ergodic`).

The published proof uses the entropy `U(x) = ∑ (xᵢ(log xᵢ − 1) + 1)` and claims `LU ≤ −1` off a
finite set; `CRNT.Examples.ACKEntropyObstruction` shows that this fails for `2A ⇄ 2B`.  The proof
here splits into two cases.

* **Every complex has two molecules.**  Then every reaction conserves the molecule count and
  `CRNT.Network.fullyOpen_ergodic` applies with the total count as Lyapunov function.
* **Some complex has at most one molecule** (`entropy_drift_le`).  Then `U` *is* a Foster
  function, by a finite "empty band" argument that replaces the tier sequences of the literature.

## The empty-band argument

Write `z = max(x, 1)` coordinatewise, `ζ_y = z^y` for a complex `y`, `ζ* = max_y ζ_y` and
`X = max(maxᵢ xᵢ, 1)`.  Every reaction `y → y'` contributes at most
`κ (1/e + C₀) max(ζ_y, ζ_{y'}) ≤ κ (1/e + C₀) ζ*` to `LU` (`term_le`), because
`U(x + y' − y) − U(x) ≤ log ζ_{y'} − log ζ_y + C₀` (`countU_step_le`, `C₀ = 4|S|`) and
`a (log b − log a) ≤ b/e`.  Two cases:

* `ζ* ≤ B X`: the reaction part of `LU` is at most `A B X`.
* `ζ* > B X`: choose thresholds `2 = K₀ < K₁ < … < K_m` (`m` the number of complexes) with
  `K_{j+1} = K_j exp(C₀ + 4 K_j (A + 1)/κ_min)`, and `B = K_m`.  Some band `[K_j, K_{j+1})` contains
  no ratio `ζ*/ζ_y` (`exists_empty_band`, pigeonhole: the top complex has ratio `1 < K₀`).  The
  set `T = {y | ζ*/ζ_y < K_j}` contains the top complex and misses the small complex `y₀` (whose
  `ζ_{y₀} ≤ X`); strong connectivity gives a reaction from `T` to its complement, which crosses
  the empty band.  Its source is enabled (a disabled binary source has `ζ ≤ X`), so it contributes
  at most `−(A + 1) ζ*`, which beats the `A ζ*` of all other reactions: the reaction part is `≤ 0`.

In both cases the reaction part is `≤ A B X`, while the outflows contribute
`≤ −κ_out X log X + O(X)` and the inflows `O(log X)`, so `LU ≤ −X + K` (`entropy_drift_le`).

The argument is local to a class of reactions (`core_part_le_on`), so it also gives ergodicity
when the reactions split into several classes, each strongly connected and each containing a
complex with at most one molecule (`fullyOpen_ergodic_of_classes`; for weakly reversible
networks, the linkage classes).  The case it does not cover is a network with one linkage class
made only of two-molecule complexes and another containing a smaller complex.
-/

namespace CRNT
namespace BinaryFlows

open Network Filter Topology

/-! ## Scalar facts about `u(t) = t (log t − 1) + 1` -/

/-- `u(t) = t (log t − 1) + 1` (so `u 0 = 1` with `log 0 = 0`). -/
noncomputable def uE (t : ℝ) : ℝ := t * (Real.log t - 1) + 1

/-- Convexity of `u`: `(s − t) log t ≤ u s − u t` for `t > 0`, `s ≥ 0`. -/
theorem uE_sub_ge {s t : ℝ} (ht : 0 < t) (hs : 0 ≤ s) :
    (s - t) * Real.log t ≤ uE s - uE t := by
  unfold uE
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    simp only [zero_mul, zero_sub]
    nlinarith [ht]
  · have hsne : s ≠ 0 := hpos.ne'
    have h1 := Real.log_le_sub_one_of_pos (div_pos ht hpos)
    rw [Real.log_div ht.ne' hsne] at h1
    have h2 : s * (Real.log t - Real.log s) ≤ s * (t / s - 1) :=
      mul_le_mul_of_nonneg_left h1 hpos.le
    have h3 : s * (t / s - 1) = t - s := by
      rw [mul_sub, mul_one, mul_comm s (t / s), div_mul_cancel₀ t hsne]
    nlinarith [h2, h3]

theorem uE_one : uE 1 = 0 := by simp [uE]

theorem uE_zero : uE 0 = 1 := by simp [uE]

theorem uE_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ uE t := by
  have h := uE_sub_ge (s := t) (t := 1) one_pos ht
  rw [uE_one, Real.log_one, mul_zero] at h
  linarith

theorem half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h
  linarith

/-- `u` grows at least linearly: `t/2 − 1 ≤ u t`. -/
theorem uE_ge {t : ℝ} (ht : 0 ≤ t) : t / 2 - 1 ≤ uE t := by
  have h := uE_sub_ge (s := t) (t := 2) two_pos ht
  have h2 : uE 2 = 2 * Real.log 2 - 1 := by unfold uE; ring
  rw [h2] at h
  have hl := half_le_log_two
  nlinarith

/-- `(a − b)(log a − log b) ≤ (a − b)²` for `a, b ≥ 1`. -/
theorem mul_log_sub_le_sq {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a - b) * (Real.log a - Real.log b) ≤ (a - b) ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rcases le_total b a with h | h
  · have hl := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    rw [Real.log_div ha0.ne' hb0.ne'] at hl
    have e : (a - b) / b = a / b - 1 := by rw [sub_div, div_self hb0.ne']
    have h2 : (a - b) / b ≤ a - b := div_le_self (sub_nonneg.mpr h) hb
    have h3 : Real.log a - Real.log b ≤ a - b := by linarith
    have := mul_le_mul_of_nonneg_left h3 (sub_nonneg.mpr h)
    nlinarith [this]
  · have hl := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    rw [Real.log_div hb0.ne' ha0.ne'] at hl
    have e : (b - a) / a = b / a - 1 := by rw [sub_div, div_self ha0.ne']
    have h2 : (b - a) / a ≤ b - a := div_le_self (sub_nonneg.mpr h) ha
    have h3 : Real.log b - Real.log a ≤ b - a := by linarith
    have := mul_le_mul_of_nonneg_left h3 (sub_nonneg.mpr h)
    nlinarith [this]

/-- **One-species entropy step**: for counts with `|m − n| ≤ 2`,
`u(m) − u(n) ≤ (m − n) log max(n, 1) + 4`. -/
theorem uE_step (n m : ℕ) (h1 : m ≤ n + 2) (h2 : n ≤ m + 2) :
    uE m - uE n ≤ ((m : ℝ) - n) * Real.log (max (n : ℝ) 1) + 4 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [uE]
    · have hmax : max (n : ℝ) 1 = n := max_eq_left (by exact_mod_cast hn)
      rw [hmax]
      have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
      unfold uE
      push_cast
      nlinarith
  · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have key := uE_sub_ge (s := (n : ℝ)) (t := (m : ℝ)) hmR (Nat.cast_nonneg n)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hm2 : (m : ℝ) ≤ 2 := by exact_mod_cast (by omega : m ≤ 2)
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hlog := Real.log_le_sub_one_of_pos hmR
      have h3 : (m : ℝ) * Real.log m ≤ (m : ℝ) * ((m : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hlog hmR.le
      have hmax : max ((0 : ℕ) : ℝ) 1 = 1 := by simp
      rw [hmax, Real.log_one, mul_zero, zero_add]
      push_cast at key ⊢
      nlinarith
    · have hmax : max (n : ℝ) 1 = n := max_eq_left (by exact_mod_cast hn)
      rw [hmax]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hsq := mul_log_sub_le_sq hm1 hn1
      have hd : ((m : ℝ) - n) ^ 2 ≤ 4 := by
        have h1' : (m : ℝ) ≤ n + 2 := by exact_mod_cast h1
        have h2' : (n : ℝ) ≤ m + 2 := by exact_mod_cast h2
        nlinarith
      nlinarith [key, hsq, hd]

/-- `(a − b)(log a − log b) ≤ (a − b)² / min(a, b)` for `a, b > 0`. -/
theorem mul_log_sub_le_sq_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) * (Real.log a - Real.log b) ≤ (a - b) ^ 2 / min a b := by
  rcases le_total b a with h | h
  · rw [min_eq_right h]
    have hl := Real.log_le_sub_one_of_pos (div_pos ha hb)
    rw [Real.log_div ha.ne' hb.ne'] at hl
    have e : (a - b) / b = a / b - 1 := by rw [sub_div, div_self hb.ne']
    rw [← e] at hl
    have := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr h)
    calc (a - b) * (Real.log a - Real.log b) ≤ (a - b) * ((a - b) / b) := this
      _ = (a - b) ^ 2 / b := by ring
  · rw [min_eq_left h]
    have hl := Real.log_le_sub_one_of_pos (div_pos hb ha)
    rw [Real.log_div hb.ne' ha.ne'] at hl
    have e : (b - a) / a = b / a - 1 := by rw [sub_div, div_self ha.ne']
    rw [← e] at hl
    have := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr h)
    calc (a - b) * (Real.log a - Real.log b) = (b - a) * (Real.log b - Real.log a) := by ring
      _ ≤ (b - a) * ((b - a) / a) := this
      _ = (a - b) ^ 2 / a := by ring

/-- **The refined one-species entropy step**: for positive counts with `|m − n| ≤ 2`,
`u(m) − u(n) ≤ (m − n) log n + 4 / min(m, n)`.  This is the estimate the all-two-molecule
classes of the mixed case need (`docs/notes/binary-flows-mixed-complex-balanced.md`): the error is
of order `1 / min`, not `O(1)`. -/
theorem uE_step_fine (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (h1 : m ≤ n + 2) (h2 : n ≤ m + 2) :
    uE m - uE n ≤ ((m : ℝ) - n) * Real.log n + 4 / min (m : ℝ) n := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have key := uE_sub_ge (s := (n : ℝ)) (t := (m : ℝ)) hmR hnR.le
  have hsq := mul_log_sub_le_sq_div hmR hnR
  have hd : ((m : ℝ) - n) ^ 2 ≤ 4 := by
    have h1' : (m : ℝ) ≤ n + 2 := by exact_mod_cast h1
    have h2' : (n : ℝ) ≤ m + 2 := by exact_mod_cast h2
    nlinarith
  have hmin : 0 < min (m : ℝ) n := lt_min hmR hnR
  have h4 : ((m : ℝ) - n) ^ 2 / min (m : ℝ) n ≤ 4 / min (m : ℝ) n :=
    (div_le_div_iff_of_pos_right hmin).mpr hd
  nlinarith [key, hsq, h4]

/-- `a (log b − log a) ≤ b / e` for `a, b > 0`. -/
theorem mul_log_sub_le_div_exp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * (Real.log b - Real.log a) ≤ b / Real.exp 1 := by
  have he := Real.exp_pos 1
  have h := Real.log_le_sub_one_of_pos (show 0 < b / (a * Real.exp 1) by positivity)
  rw [Real.log_div hb.ne' (by positivity), Real.log_mul ha.ne' he.ne', Real.log_exp] at h
  calc a * (Real.log b - Real.log a) ≤ a * (b / (a * Real.exp 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) ha.le
    _ = b / Real.exp 1 := by rw [← mul_div_assoc, mul_div_mul_left b (Real.exp 1) ha.ne']

/-- `c₁ X + c₂ log X + c₃ − κ X log X ≤ −X + K` for `X ≥ 1`. -/
theorem scalar_drift {c₁ c₂ c₃ κ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hκ : 0 < κ) {X : ℝ}
    (hX : 1 ≤ X) :
    c₁ * X + c₂ * Real.log X + c₃ - κ * (X * Real.log X) ≤
      -X + ((c₁ + c₂ + 1) * Real.exp ((c₁ + c₂ + 1) / κ) + c₃) := by
  have hX0 : 0 < X := by linarith
  have hlogX : Real.log X ≤ X := by linarith [Real.log_le_sub_one_of_pos hX0]
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have h1 : c₂ * Real.log X ≤ c₂ * X := mul_le_mul_of_nonneg_left hlogX hc₂
  obtain ⟨M, hM⟩ : ∃ M, M = c₁ + c₂ + 1 := ⟨_, rfl⟩
  rw [← hM]
  have hM1 : 1 ≤ M := by rw [hM]; linarith
  have hXl : 0 ≤ X * Real.log X := mul_nonneg hX0.le hlog0
  rcases le_or_gt (M / κ) (Real.log X) with hbig | hsmall
  · have h2 : M * X ≤ κ * (X * Real.log X) := by
      have := mul_le_mul_of_nonneg_left hbig hX0.le
      rw [mul_div_assoc', div_le_iff₀ hκ] at this
      nlinarith [this]
    have he : 0 ≤ M * Real.exp (M / κ) := by positivity
    nlinarith [h1, h2, he]
  · have hXlt : X < Real.exp (M / κ) := by
      rw [← Real.exp_log hX0]; exact Real.exp_lt_exp.mpr hsmall
    have h3 : M * X ≤ M * Real.exp (M / κ) := mul_le_mul_of_nonneg_left hXlt.le (by linarith)
    have h4 : 0 ≤ κ * (X * Real.log X) := mul_nonneg hκ.le hXl
    nlinarith [h1, h3, h4]

/-! ## Count-level quantities -/

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The entropy `U(n) = ∑ₛ u(nₛ)`. -/
noncomputable def countU (n : S → ℕ) : ℝ := ∑ s, uE (n s)

/-- `zₛ = max(nₛ, 1)`. -/
noncomputable def zc (n : S → ℕ) (s : S) : ℝ := max ((n s : ℕ) : ℝ) 1

/-- `ζ_y = ∏ₛ zₛ^{yₛ}`. -/
noncomputable def zeta (y : Complex S) (n : S → ℕ) : ℝ := ∏ s, zc n s ^ (y s)

/-- `log ζ_y = ∑ₛ yₛ log zₛ`. -/
noncomputable def logZeta (y : Complex S) (n : S → ℕ) : ℝ := ∑ s, (y s : ℝ) * Real.log (zc n s)

/-- The largest count, at least `1`. -/
noncomputable def Xmax (n : S → ℕ) : ℝ := max ((Finset.univ.sup n : ℕ) : ℝ) 1

theorem one_le_zc (n : S → ℕ) (s : S) : 1 ≤ zc n s := le_max_right _ _

theorem zc_pos (n : S → ℕ) (s : S) : 0 < zc n s := lt_of_lt_of_le one_pos (one_le_zc n s)

theorem one_le_Xmax (n : S → ℕ) : 1 ≤ Xmax n := le_max_right _ _

theorem zc_le_Xmax (n : S → ℕ) (s : S) : zc n s ≤ Xmax n := by
  unfold zc Xmax
  have h : n s ≤ Finset.univ.sup n := Finset.le_sup (f := n) (Finset.mem_univ s)
  have h' : ((n s : ℕ) : ℝ) ≤ ((Finset.univ.sup n : ℕ) : ℝ) := by exact_mod_cast h
  exact max_le_max h' le_rfl

theorem zeta_pos (y : Complex S) (n : S → ℕ) : 0 < zeta y n :=
  Finset.prod_pos fun s _ => pow_pos (zc_pos n s) _

theorem log_zeta (y : Complex S) (n : S → ℕ) : Real.log (zeta y n) = logZeta y n := by
  unfold zeta logZeta
  rw [Real.log_prod (fun s _ => (pow_pos (zc_pos n s) _).ne')]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Real.log_pow]

theorem zeta_le_pow (y : Complex S) (n : S → ℕ) : zeta y n ≤ Xmax n ^ (∑ s, y s) := by
  unfold zeta
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun s _ => pow_nonneg (zc_pos n s).le _)
    (fun s _ => pow_le_pow_left₀ (zc_pos n s).le (zc_le_Xmax n s) _)

/-- A complex with at most one molecule has `ζ ≤ X`. -/
theorem zeta_le_Xmax_of_small (y : Complex S) (n : S → ℕ) (hy : ∑ s, y s ≤ 1) :
    zeta y n ≤ Xmax n :=
  (zeta_le_pow y n).trans (by
    calc Xmax n ^ (∑ s, y s) ≤ Xmax n ^ 1 := pow_le_pow_right₀ (one_le_Xmax n) hy
      _ = Xmax n := pow_one _)

/-- A binary complex that is not contained in the count has `ζ ≤ X`. -/
theorem zeta_le_Xmax_of_disabled (y : Complex S) (n : S → ℕ) (hy : ∑ s, y s ≤ 2) (s : S)
    (hs : n s < y s) : zeta y n ≤ Xmax n := by
  have hz : zc n s = 1 := by
    unfold zc
    have : (n s : ℝ) ≤ 1 := by
      have h1 : y s ≤ ∑ t, y t := Finset.single_le_sum (f := y) (fun t _ => Nat.zero_le _)
        (Finset.mem_univ s)
      exact_mod_cast (by omega : n s ≤ 1)
    exact max_eq_right this
  unfold zeta
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s), hz, one_pow, one_mul]
  have hsum : ∑ t ∈ Finset.univ.erase s, y t ≤ 1 := by
    have h := Finset.add_sum_erase Finset.univ y (Finset.mem_univ s)
    omega
  calc ∏ t ∈ Finset.univ.erase s, zc n t ^ y t ≤ ∏ t ∈ Finset.univ.erase s, Xmax n ^ y t :=
        Finset.prod_le_prod₀ (fun t _ => pow_nonneg (zc_pos n t).le _)
          (fun t _ => pow_le_pow_left₀ (zc_pos n t).le (zc_le_Xmax n t) _)
    _ = Xmax n ^ (∑ t ∈ Finset.univ.erase s, y t) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ Xmax n ^ 1 := pow_le_pow_right₀ (one_le_Xmax n) hsum
    _ = Xmax n := pow_one _

/-! ## Propensities -/

/-- The propensity is at most `κ ζ_y`. -/
theorem rate_le (M : Network S) (κ : RateConstants M) (n : S → ℕ) (r : M.R) :
    M.stochasticMassActionRate κ n r ≤ κ.k r * zeta (M.reaction r).source n := by
  unfold stochasticMassActionRate zeta
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun s _ => Nat.cast_nonneg _)
    (fun s _ => ?_)) (κ.positive r).le
  have h1 : ((n s).descFactorial ((M.reaction r).source s) : ℝ) ≤
      ((n s : ℕ) : ℝ) ^ ((M.reaction r).source s) := by
    exact_mod_cast Nat.descFactorial_le_pow _ _
  exact h1.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_left _ _) _)

/-- A disabled reaction has propensity `0`. -/
theorem rate_eq_zero_of_disabled (M : Network S) (κ : RateConstants M) (n : S → ℕ) (r : M.R)
    (s : S) (hs : n s < (M.reaction r).source s) : M.stochasticMassActionRate κ n r = 0 := by
  unfold stochasticMassActionRate
  rw [Finset.prod_eq_zero (Finset.mem_univ s)]
  · ring
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hs]; simp

/-- An enabled binary reaction has propensity at least `κ ζ_y / 4`. -/
theorem rate_ge (M : Network S) (κ : RateConstants M) (n : S → ℕ) (r : M.R)
    (hbin : ∑ s, (M.reaction r).source s ≤ 2) (hen : ∀ s, (M.reaction r).source s ≤ n s) :
    κ.k r * zeta (M.reaction r).source n / 4 ≤ M.stochasticMassActionRate κ n r := by
  obtain ⟨y, hy⟩ : ∃ y, y = (M.reaction r).source := ⟨_, rfl⟩
  rw [← hy] at hbin hen ⊢
  have hfac : ∀ s, zc n s ^ (y s) / 2 ^ (y s) ≤ ((n s).descFactorial (y s) : ℝ) := by
    intro s
    by_cases hk : y s = 0
    · rw [hk]; simp
    · have hys : y s ≤ 2 := (Finset.single_le_sum (f := y) (fun t _ => Nat.zero_le _)
        (Finset.mem_univ s)).trans hbin
      have hn1 : 1 ≤ n s := (Nat.one_le_iff_ne_zero.mpr hk).trans (hen s)
      have hz : zc n s = n s := by
        unfold zc; exact max_eq_left (by exact_mod_cast hn1)
      rw [hz, ← div_pow]
      have hlow := Nat.pow_sub_le_descFactorial (n s) (y s)
      have hcast : ((n s : ℕ) : ℝ) / 2 ≤ ((n s + 1 - y s : ℕ) : ℝ) := by
        have hle : y s ≤ n s + 1 := by omega
        rw [Nat.cast_sub hle]
        push_cast
        have hns : (1 : ℝ) ≤ n s := by exact_mod_cast hn1
        have hys' : (y s : ℝ) ≤ 2 := by exact_mod_cast hys
        have hen' : (y s : ℝ) ≤ n s := by exact_mod_cast hen s
        rcases Nat.lt_or_ge (n s) 2 with hlt | hge
        · have hn1' : n s = 1 := by omega
          have hy1 : y s = 1 := by
            have hle1 : y s ≤ 1 := by
              calc y s ≤ n s := hen s
                _ = 1 := hn1'
            exact Nat.le_antisymm hle1 (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk))
          rw [hy1, hn1']; norm_num
        · have hns2 : (2 : ℝ) ≤ n s := by exact_mod_cast hge
          linarith
      calc (((n s : ℕ) : ℝ) / 2) ^ (y s) ≤ ((n s + 1 - y s : ℕ) : ℝ) ^ (y s) :=
            pow_le_pow_left₀ (by positivity) hcast _
        _ ≤ ((n s).descFactorial (y s) : ℝ) := by exact_mod_cast hlow
  unfold stochasticMassActionRate
  rw [← hy]
  have hprod : zeta y n / 2 ^ (∑ s, y s) ≤ ∏ s, ((n s).descFactorial (y s) : ℝ) := by
    unfold zeta
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
    exact Finset.prod_le_prod₀
      (fun s _ => div_nonneg (pow_nonneg (zc_pos n s).le _) (by positivity)) (fun s _ => hfac s)
  have h4 : zeta y n / 4 ≤ zeta y n / 2 ^ (∑ s, y s) := by
    apply div_le_div_of_nonneg_left (zeta_pos y n).le (by positivity)
    calc (2 : ℝ) ^ (∑ s, y s) ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hbin
      _ = 4 := by norm_num
  have hk := κ.positive r
  calc κ.k r * zeta y n / 4 = κ.k r * (zeta y n / 4) := by ring
    _ ≤ κ.k r * ∏ s, ((n s).descFactorial (y s) : ℝ) :=
      mul_le_mul_of_nonneg_left (h4.trans hprod) hk.le

/-! ## The entropy step of one reaction -/

/-- **The entropy step**: an enabled binary reaction `y → y'` changes `U` by at most
`log ζ_{y'} − log ζ_y + 4|S|`. -/
theorem countU_step_le (y y' : Complex S) (n : S → ℕ) (hy : ∑ s, y s ≤ 2)
    (hy' : ∑ s, y' s ≤ 2) (hen : ∀ s, y s ≤ n s) :
    countU (fun s => n s - y s + y' s) - countU n ≤
      logZeta y' n - logZeta y n + 4 * Fintype.card S := by
  unfold countU logZeta
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have hcard : (4 : ℝ) * Fintype.card S = ∑ _s : S, (4 : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  rw [hcard, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  show uE ((n s - y s + y' s : ℕ) : ℝ) - uE ((n s : ℕ) : ℝ) ≤
    (y' s : ℝ) * Real.log (zc n s) - (y s : ℝ) * Real.log (zc n s) + 4
  have hys : y s ≤ 2 := (Finset.single_le_sum (f := y) (fun t _ => Nat.zero_le _)
    (Finset.mem_univ s)).trans hy
  have hys' : y' s ≤ 2 := (Finset.single_le_sum (f := y') (fun t _ => Nat.zero_le _)
    (Finset.mem_univ s)).trans hy'
  have h := uE_step (n s) (n s - y s + y' s) (by omega) (by omega)
  have hc : ((n s - y s + y' s : ℕ) : ℝ) - n s = (y' s : ℝ) - y s := by
    rw [Nat.cast_add, Nat.cast_sub (hen s)]; ring
  rw [hc] at h
  have e : ((y' s : ℝ) - y s) * Real.log (max ((n s : ℕ) : ℝ) 1) =
      (y' s : ℝ) * Real.log (zc n s) - (y s : ℝ) * Real.log (zc n s) := by unfold zc; ring
  linarith

/-! ## The refined step with explicit errors -/

/-- The error of the refined one-species entropy step. -/
noncomputable def errS (n m : ℕ) : ℝ :=
  if m = n then 0 else if 1 ≤ n ∧ 1 ≤ m then 4 / min (m : ℝ) n else 4

theorem errS_nonneg (n m : ℕ) : 0 ≤ errS n m := by
  unfold errS
  split_ifs with h1 h2
  · exact le_rfl
  · have hm : (1 : ℝ) ≤ m := by exact_mod_cast h2.2
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast h2.1
    exact div_nonneg (by norm_num) (le_min (by linarith) (by linarith))
  · norm_num

theorem errS_le_four (n m : ℕ) : errS n m ≤ 4 := by
  unfold errS
  split_ifs with h1 h2
  · norm_num
  · have hm : (1 : ℝ) ≤ m := by exact_mod_cast h2.2
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast h2.1
    have hmin : (1 : ℝ) ≤ min (m : ℝ) n := le_min hm hn
    rw [div_le_iff₀ (by linarith)]
    linarith
  · exact le_rfl

/-- A species of the source: `errS ≤ 12 / n`. -/
theorem errS_le_src (n m : ℕ) (hn : 1 ≤ n) (h1 : m ≤ n + 2) (h2 : n ≤ m + 2) :
    errS n m ≤ 12 / (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  unfold errS
  split_ifs with h3 h4
  · positivity
  · have hm : (1 : ℝ) ≤ m := by exact_mod_cast h4.2
    have h2' : (n : ℝ) ≤ m + 2 := by exact_mod_cast h2
    have hmin : (n : ℝ) / 3 ≤ min (m : ℝ) n := by
      apply le_min
      · rcases le_or_gt (n : ℝ) 3 with h | h
        · linarith
        · linarith
      · linarith
    have hminpos : 0 < min (m : ℝ) n := lt_min (by linarith) hnpos
    rw [div_le_div_iff₀ hminpos hnpos]
    nlinarith
  · have hm0 : m = 0 := by
      by_contra hne
      exact h4 ⟨hn, Nat.one_le_iff_ne_zero.mpr hne⟩
    subst hm0
    have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
    rw [le_div_iff₀ hnpos]
    linarith

/-- A species only in the target: `errS ≤ 4 / max(n, 1)`. -/
theorem errS_le_tgt (n m : ℕ) (h : n < m) : errS n m ≤ 4 / max (n : ℝ) 1 := by
  have hmax : (1 : ℝ) ≤ max (n : ℝ) 1 := le_max_right _ _
  unfold errS
  split_ifs with h3 h4
  · positivity
  · have hn : (1 : ℝ) ≤ n := by exact_mod_cast h4.1
    have hnm : (n : ℝ) ≤ m := by exact_mod_cast h.le
    simp only [min_eq_right hnm, max_eq_left hn, le_refl]
  · have hn0 : n = 0 := by
      by_contra hne
      exact h4 ⟨Nat.one_le_iff_ne_zero.mpr hne, by omega⟩
    subst hn0
    norm_num

theorem uE_step_err (n m : ℕ) (h1 : m ≤ n + 2) (h2 : n ≤ m + 2) :
    uE m - uE n ≤ ((m : ℝ) - n) * Real.log (max (n : ℝ) 1) + errS n m := by
  unfold errS
  split_ifs with heq hpos
  · subst heq; simp
  · have hn : (1 : ℝ) ≤ n := by exact_mod_cast hpos.1
    rw [max_eq_left hn]
    exact uE_step_fine n m hpos.1 hpos.2 h1 h2
  · exact uE_step n m h1 h2

/-- **The entropy step of a reaction with explicit errors.** -/
theorem countU_step_err (y y' : Complex S) (n : S → ℕ) (hy : ∑ s, y s ≤ 2)
    (hy' : ∑ s, y' s ≤ 2) (hen : ∀ s, y s ≤ n s) :
    countU (fun s => n s - y s + y' s) - countU n ≤
      logZeta y' n - logZeta y n + ∑ s, errS (n s) (n s - y s + y' s) := by
  unfold countU logZeta
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  show uE ((n s - y s + y' s : ℕ) : ℝ) - uE ((n s : ℕ) : ℝ) ≤
    (y' s : ℝ) * Real.log (zc n s) - (y s : ℝ) * Real.log (zc n s) +
      errS (n s) (n s - y s + y' s)
  have hys : y s ≤ 2 := (Finset.single_le_sum (f := y) (fun t _ => Nat.zero_le _)
    (Finset.mem_univ s)).trans hy
  have hys' : y' s ≤ 2 := (Finset.single_le_sum (f := y') (fun t _ => Nat.zero_le _)
    (Finset.mem_univ s)).trans hy'
  have h := uE_step_err (n s) (n s - y s + y' s) (by omega) (by omega)
  have hc : ((n s - y s + y' s : ℕ) : ℝ) - n s = (y' s : ℝ) - y s := by
    rw [Nat.cast_add, Nat.cast_sub (hen s)]; ring
  rw [hc] at h
  have e : ((y' s : ℝ) - y s) * Real.log (max ((n s : ℕ) : ℝ) 1) =
      (y' s : ℝ) * Real.log (zc n s) - (y s : ℝ) * Real.log (zc n s) := by unfold zc; ring
  linarith

/-- `ζ_y ≤ z_s X` when `s` occurs in the binary complex `y`. -/
theorem zeta_le_zc_mul (y : Complex S) (n : S → ℕ) (hy : ∑ t, y t ≤ 2) (s : S) (hs : 1 ≤ y s) :
    zeta y n ≤ zc n s * Xmax n := by
  set y'' : Complex S := fun t => y t - if t = s then 1 else 0 with hy''
  have hsplit : ∀ t, y t = y'' t + (if t = s then 1 else 0) := by
    intro t
    by_cases h : t = s
    · rw [h]; simp only [hy'', eq_self_iff_true, if_true]; omega
    · simp only [hy'', h, if_false, Nat.sub_zero, add_zero]
  have hz : zeta y n = zeta y'' n * zc n s := by
    have hprod : ∀ t, zc n t ^ y t = zc n t ^ y'' t * zc n t ^ (if t = s then 1 else 0) :=
      fun t => by rw [← pow_add, ← hsplit t]
    unfold zeta
    rw [Finset.prod_congr rfl fun t _ => hprod t, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_eq_single s (fun t _ ht => by rw [if_neg ht, pow_zero])
      (fun h => absurd (Finset.mem_univ s) h), if_pos rfl, pow_one]
  have hsum : ∑ t, y'' t ≤ 1 := by
    have : ∑ t, y t = ∑ t, y'' t + 1 := by
      rw [Finset.sum_congr rfl fun t _ => hsplit t, Finset.sum_add_distrib]
      simp
    omega
  have h1 := zeta_le_pow y'' n
  have h2 : Xmax n ^ (∑ t, y'' t) ≤ Xmax n := by
    have := pow_le_pow_right₀ (one_le_Xmax n) hsum
    rwa [pow_one] at this
  rw [hz]
  calc zeta y'' n * zc n s ≤ Xmax n * zc n s :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (zc_pos n s).le
    _ = zc n s * Xmax n := mul_comm _ _

/-- **The rate gap of a binary source**: `(κ ζ_y − λ)² ≤ κ · κ ζ_y`.  The gap vanishes unless
`y = 2 Sᵢ`, where it is `κ nᵢ` with `ζ = nᵢ²`. -/
theorem rate_gap_sq (M : Network S) (κ : RateConstants M) (n : S → ℕ) (r : M.R)
    (hbin : ∑ s, (M.reaction r).source s ≤ 2) (hen : ∀ s, (M.reaction r).source s ≤ n s) :
    (κ.k r * zeta (M.reaction r).source n - M.stochasticMassActionRate κ n r) ^ 2 ≤
      κ.k r * (κ.k r * zeta (M.reaction r).source n) := by
  obtain ⟨y, hy⟩ : ∃ y, y = (M.reaction r).source := ⟨_, rfl⟩
  rw [← hy] at hbin hen ⊢
  have hk := κ.positive r
  have hrate : M.stochasticMassActionRate κ n r = κ.k r * ∏ s, ((n s).descFactorial (y s) : ℝ) := by
    unfold stochasticMassActionRate; rw [← hy]
  rw [hrate]
  have key : (zeta y n - ∏ s, ((n s).descFactorial (y s) : ℝ)) ^ 2 ≤ zeta y n := by
    unfold zeta
    by_cases h2 : ∃ s₀, y s₀ = 2
    · obtain ⟨s₀, hs₀⟩ := h2
      have hother : ∀ t, t ≠ s₀ → y t = 0 := by
        have hsplit := Finset.add_sum_erase Finset.univ y (Finset.mem_univ s₀)
        have hrest : ∑ t ∈ Finset.univ.erase s₀, y t = 0 := by omega
        intro t ht
        exact (Finset.sum_eq_zero_iff.mp hrest) t (Finset.mem_erase.mpr ⟨ht, Finset.mem_univ t⟩)
      have hP : ∏ s, ((n s).descFactorial (y s) : ℝ) = ((n s₀).descFactorial 2 : ℝ) := by
        rw [Finset.prod_eq_single s₀ (fun t _ ht => by rw [hother t ht]; simp)
          (fun h => absurd (Finset.mem_univ s₀) h), hs₀]
      have hZ : ∏ s, zc n s ^ (y s) = zc n s₀ ^ 2 := by
        rw [Finset.prod_eq_single s₀ (fun t _ ht => by rw [hother t ht, pow_zero])
          (fun h => absurd (Finset.mem_univ s₀) h), hs₀]
      have hn2 : 2 ≤ n s₀ := hs₀ ▸ hen s₀
      have hz : zc n s₀ = n s₀ := by
        unfold zc; exact max_eq_left (by exact_mod_cast (by omega : 1 ≤ n s₀))
      have hd : ((n s₀).descFactorial 2 : ℝ) = (n s₀ : ℝ) * ((n s₀ : ℝ) - 1) := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.descFactorial_succ, Nat.descFactorial_one,
          Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n s₀)]
        push_cast; ring
      rw [hP, hZ, hz, hd]
      nlinarith
    · push_neg at h2
      have hle : ∀ s, y s ≤ 1 := by
        intro s
        have hs2 : y s ≤ 2 := (Finset.single_le_sum (f := y) (fun t _ => Nat.zero_le _)
          (Finset.mem_univ s)).trans hbin
        have := h2 s
        omega
      have heq : ∏ s, ((n s).descFactorial (y s) : ℝ) = ∏ s, zc n s ^ (y s) := by
        refine Finset.prod_congr rfl fun s _ => ?_
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hle s) with h0 | h1
        · rw [h0]; simp
        · rw [h1, Nat.descFactorial_one, pow_one]
          have hn1 : 1 ≤ n s := h1 ▸ hen s
          unfold zc; rw [max_eq_left (by exact_mod_cast hn1)]
      rw [heq, sub_self]
      have := zeta_pos y n
      unfold zeta at this
      nlinarith
  have hz := zeta_pos y n
  calc (κ.k r * zeta y n - κ.k r * ∏ s, ((n s).descFactorial (y s) : ℝ)) ^ 2
      = κ.k r ^ 2 * (zeta y n - ∏ s, ((n s).descFactorial (y s) : ℝ)) ^ 2 := by ring
    _ ≤ κ.k r ^ 2 * zeta y n := mul_le_mul_of_nonneg_left key (by positivity)
    _ = κ.k r * (κ.k r * zeta y n) := by ring

/-! ## The bound for one reaction of the core network -/

variable (N : Network S) (κ : RateConstants N.fullyOpen)

/-- The contribution of the core reaction `r` to the entropy drift. -/
noncomputable def term (n : S → ℕ) (r : N.R) : ℝ :=
  N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) *
    (countU (N.fullyOpen.jumpNextCount n (Sum.inl r)) - countU n)

theorem next_inl (n : S → ℕ) (r : N.R) :
    N.fullyOpen.jumpNextCount n (Sum.inl r) =
      fun s => n s - (N.reaction r).source s + (N.reaction r).target s := rfl

/-- The core propensities obey the bounds of `rate_le`, `rate_ge`, `rate_eq_zero_of_disabled`
with the source of `N`. -/
theorem source_inl (r : N.R) : (N.fullyOpen.reaction (Sum.inl r)).source = (N.reaction r).source :=
  rfl

/-- **Every core reaction contributes at most `κ (1/e + C₀) max(ζ_y, ζ_{y'})`.** -/
theorem term_le (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (n : S → ℕ) (r : N.R) :
    term N κ n r ≤ κ.k (Sum.inl r) * (1 / Real.exp 1 + 4 * Fintype.card S) *
      max (zeta (N.reaction r).source n) (zeta (N.reaction r).target n) := by
  have hk := κ.positive (Sum.inl r)
  have hC : (0 : ℝ) ≤ 4 * Fintype.card S := by positivity
  have he : 0 < 1 / Real.exp 1 := by positivity
  have hzs := zeta_pos (N.reaction r).source n
  have hzt := zeta_pos (N.reaction r).target n
  have hRHS : 0 ≤ κ.k (Sum.inl r) * (1 / Real.exp 1 + 4 * Fintype.card S) *
      max (zeta (N.reaction r).source n) (zeta (N.reaction r).target n) := by positivity
  by_cases hen : ∀ s, (N.reaction r).source s ≤ n s
  · have hstep : countU (N.fullyOpen.jumpNextCount n (Sum.inl r)) - countU n ≤
        logZeta (N.reaction r).target n - logZeta (N.reaction r).source n +
          4 * Fintype.card S :=
      countU_step_le (N.reaction r).source (N.reaction r).target n (hbin r).1 (hbin r).2 hen
    unfold term
    obtain ⟨L, hL⟩ : ∃ L, L = logZeta (N.reaction r).target n - logZeta (N.reaction r).source n :=
      ⟨_, rfl⟩
    have hrate0 := N.fullyOpen.stochasticMassActionRate_nonneg κ n (Sum.inl r)
    have hrate := rate_le N.fullyOpen κ n (Sum.inl r)
    rw [source_inl] at hrate
    rcases le_or_gt (L + 4 * Fintype.card S) 0 with hneg | hpos
    · have : N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) *
          (countU (N.fullyOpen.jumpNextCount n (Sum.inl r)) - countU n) ≤
          N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) * (L + 4 * Fintype.card S) :=
        mul_le_mul_of_nonneg_left (by rw [hL]; linarith) hrate0
      linarith [mul_nonpos_of_nonneg_of_nonpos hrate0 hneg]
    · have h1 : N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) *
          (countU (N.fullyOpen.jumpNextCount n (Sum.inl r)) - countU n) ≤
          κ.k (Sum.inl r) * zeta (N.reaction r).source n * (L + 4 * Fintype.card S) := by
        calc _ ≤ N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) *
              (L + 4 * Fintype.card S) :=
              mul_le_mul_of_nonneg_left (by rw [hL]; linarith) hrate0
          _ ≤ κ.k (Sum.inl r) * zeta (N.reaction r).source n * (L + 4 * Fintype.card S) :=
              mul_le_mul_of_nonneg_right hrate hpos.le
      -- `ζ_y L ≤ ζ_{y'}/e`
      have h2 : zeta (N.reaction r).source n * L ≤ zeta (N.reaction r).target n / Real.exp 1 := by
        rw [hL, ← log_zeta, ← log_zeta]
        exact mul_log_sub_le_div_exp hzs hzt
      have hmax1 : zeta (N.reaction r).source n ≤
          max (zeta (N.reaction r).source n) (zeta (N.reaction r).target n) := le_max_left _ _
      have hmax2 : zeta (N.reaction r).target n ≤
          max (zeta (N.reaction r).source n) (zeta (N.reaction r).target n) := le_max_right _ _
      have h3 : zeta (N.reaction r).source n * (L + 4 * Fintype.card S) ≤
          (1 / Real.exp 1 + 4 * Fintype.card S) *
            max (zeta (N.reaction r).source n) (zeta (N.reaction r).target n) := by
        have h4 : zeta (N.reaction r).target n / Real.exp 1 ≤
            (1 / Real.exp 1) * max (zeta (N.reaction r).source n) (zeta (N.reaction r).target n) := by
          rw [div_eq_mul_one_div]
          have := mul_le_mul_of_nonneg_left hmax2 he.le
          linarith
        have h5 : zeta (N.reaction r).source n * (4 * Fintype.card S) ≤
            (4 * Fintype.card S) * max (zeta (N.reaction r).source n) (zeta (N.reaction r).target n) := by
          have := mul_le_mul_of_nonneg_left hmax1 hC
          linarith
        linarith [h2, h4, h5]
      have := mul_le_mul_of_nonneg_left h3 hk.le
      linarith [h1, this]
  · -- a disabled reaction contributes `0`
    have hnot : ∃ s, n s < (N.reaction r).source s := by
      by_contra hc
      exact hen fun s => le_of_not_gt fun h => hc ⟨s, h⟩
    obtain ⟨s, hs⟩ := hnot
    have h0 : N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) = 0 :=
      rate_eq_zero_of_disabled N.fullyOpen κ n (Sum.inl r) s (by rw [source_inl]; exact hs)
    unfold term
    rw [h0, zero_mul]
    exact hRHS

/-- **The crossing reaction**: an enabled core reaction with
`log ζ_{y'} − log ζ_y + C₀ ≤ 0` contributes at most `(κ ζ_y/4)(log ζ_{y'} − log ζ_y + C₀)`. -/
theorem term_le_of_descent (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧
      ∑ s, (N.reaction r).target s ≤ 2)
    (n : S → ℕ) (r : N.R) (hen : ∀ s, (N.reaction r).source s ≤ n s)
    (hneg : logZeta (N.reaction r).target n - logZeta (N.reaction r).source n +
      4 * Fintype.card S ≤ 0) :
    term N κ n r ≤ κ.k (Sum.inl r) * zeta (N.reaction r).source n / 4 *
      (logZeta (N.reaction r).target n - logZeta (N.reaction r).source n +
        4 * Fintype.card S) := by
  have hstep : countU (N.fullyOpen.jumpNextCount n (Sum.inl r)) - countU n ≤
      logZeta (N.reaction r).target n - logZeta (N.reaction r).source n +
        4 * Fintype.card S :=
    countU_step_le (N.reaction r).source (N.reaction r).target n (hbin r).1 (hbin r).2 hen
  have hrate0 := N.fullyOpen.stochasticMassActionRate_nonneg κ n (Sum.inl r)
  have hge := rate_ge N.fullyOpen κ n (Sum.inl r) (by rw [source_inl]; exact (hbin r).1)
    (by rw [source_inl]; exact hen)
  rw [source_inl] at hge
  unfold term
  calc _ ≤ N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) *
        (logZeta (N.reaction r).target n - logZeta (N.reaction r).source n +
          4 * Fintype.card S) := mul_le_mul_of_nonneg_left hstep hrate0
    _ ≤ κ.k (Sum.inl r) * zeta (N.reaction r).source n / 4 *
        (logZeta (N.reaction r).target n - logZeta (N.reaction r).source n +
          4 * Fintype.card S) := mul_le_mul_of_nonpos_right hge hneg

/-! ## The empty band -/

/-- **Pigeonhole for bands.**  If `K` is strictly increasing and some `y₁ ∈ C` has
`ρ y₁ < K 0`, then one of the `|C|` bands `[K j, K (j+1))` contains no value of `ρ` on `C`. -/
theorem exists_empty_band {ι : Type*} [DecidableEq ι] (C : Finset ι) (ρ : ι → ℝ) (K : ℕ → ℝ)
    (hK : StrictMono K) (y₁ : ι) (hy₁ : y₁ ∈ C) (hρ₁ : ρ y₁ < K 0) :
    ∃ j, j < C.card ∧ ∀ y ∈ C, ¬ (K j ≤ ρ y ∧ ρ y < K (j + 1)) := by
  classical
  by_contra hcon
  have hall : ∀ j, j < C.card → ∃ y, y ∈ C ∧ K j ≤ ρ y ∧ ρ y < K (j + 1) := by
    intro j hj
    by_contra h
    exact hcon ⟨j, hj, fun y hy hb => h ⟨y, hy, hb⟩⟩
  haveI : Nonempty ι := ⟨y₁⟩
  choose! w hwC hwK using hall
  have hmaps : ∀ j ∈ Finset.range C.card, w j ∈ C.erase y₁ := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    refine Finset.mem_erase.mpr ⟨fun heq => ?_, hwC j hj'⟩
    have h1 := (hwK j hj').1
    rw [heq] at h1
    have h2 : K 0 ≤ K j := hK.monotone (Nat.zero_le j)
    linarith
  have hinj : Set.InjOn w (Finset.range C.card : Set ℕ) := by
    intro i hi j hj hij
    have hi' := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hj' := Finset.mem_range.mp (Finset.mem_coe.mp hj)
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := (hwK i hi').2
      have h2 := (hwK j hj').1
      have h3 : K (i + 1) ≤ K j := hK.monotone (by omega : i + 1 ≤ j)
      rw [hij] at h1
      linarith
    · have h1 := (hwK j hj').2
      have h2 := (hwK i hi').1
      have h3 : K (j + 1) ≤ K i := hK.monotone (by omega : j + 1 ≤ i)
      rw [← hij] at h1
      linarith
  have hcard := Finset.card_le_card_of_injOn w (by intro j hj; exact hmaps j hj) hinj
  rw [Finset.card_range, Finset.card_erase_of_mem hy₁] at hcard
  have hpos : 0 < C.card := Finset.card_pos.mpr ⟨y₁, hy₁⟩
  omega

/-! ## The bound for the core part of the drift -/

/-- **Strong connectivity of the complex graph**: every nonempty proper subset of the complexes
has a reaction leaving it. -/
def CutLeaving (N : Network S) : Prop :=
  ∀ T : Finset (Complex S), T ⊆ N.complexes → T.Nonempty → (∃ y ∈ N.complexes, y ∉ T) →
    ∃ r : N.R, (N.reaction r).source ∈ T ∧ (N.reaction r).target ∉ T

/-- The thresholds `K₀ = 2`, `K_{j+1} = K_j exp(c + 4 K_j (A + 1)/κ_min)`. -/
noncomputable def bands (c A κm : ℝ) : ℕ → ℝ
  | 0 => 2
  | j + 1 => bands c A κm j * Real.exp (c + 4 * bands c A κm j * (A + 1) / κm)

theorem bands_pos (c A κm : ℝ) : ∀ j, 0 < bands c A κm j
  | 0 => by simp [bands]
  | j + 1 => by
      have := bands_pos c A κm j
      simp only [bands]
      positivity

theorem bands_succ (c A κm : ℝ) (j : ℕ) :
    bands c A κm (j + 1) = bands c A κm j * Real.exp (c + 4 * bands c A κm j * (A + 1) / κm) :=
  rfl

theorem bands_strictMono {c A κm : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A) (hκm : 0 < κm) :
    StrictMono (bands c A κm) := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  rw [bands_succ]
  have hb := bands_pos c A κm j
  have hpos : 0 < c + 4 * bands c A κm j * (A + 1) / κm := by
    have : 0 < 4 * bands c A κm j * (A + 1) / κm := by positivity
    linarith
  have hexp : 1 < Real.exp (c + 4 * bands c A κm j * (A + 1) / κm) := by
    have := Real.add_one_le_exp (c + 4 * bands c A κm j * (A + 1) / κm)
    linarith
  nlinarith

/-- The complexes of a set of reactions. -/
def complexesOn (N : Network S) (Rc : Finset N.R) : Finset (Complex S) :=
  Rc.image (fun r => (N.reaction r).source) ∪ Rc.image (fun r => (N.reaction r).target)

theorem source_mem_complexesOn (N : Network S) {Rc : Finset N.R} {r : N.R} (hr : r ∈ Rc) :
    (N.reaction r).source ∈ complexesOn N Rc :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ hr)

theorem target_mem_complexesOn (N : Network S) {Rc : Finset N.R} {r : N.R} (hr : r ∈ Rc) :
    (N.reaction r).target ∈ complexesOn N Rc :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ hr)

/-- **Strong connectivity of the complex graph of a set of reactions.** -/
def CutLeavingOn (N : Network S) (Rc : Finset N.R) : Prop :=
  ∀ T : Finset (Complex S), T ⊆ complexesOn N Rc → T.Nonempty →
    (∃ y ∈ complexesOn N Rc, y ∉ T) → ∃ r ∈ Rc, (N.reaction r).source ∈ T ∧ (N.reaction r).target ∉ T

theorem cutLeavingOn_univ {N : Network S} (h : CutLeaving N) : CutLeavingOn N Finset.univ := by
  intro T hT hne hout
  obtain ⟨r, h1, h2⟩ := h T hT hne hout
  exact ⟨r, Finset.mem_univ r, h1, h2⟩

theorem complexesOn_univ (N : Network S) : complexesOn N Finset.univ = N.complexes := rfl

/-- **The band argument for an abstract per-reaction term.**  Any `T` obeying the two bounds that
`term` obeys (`term_le`, `term_le_of_descent`) with some constant `C₀ ≥ 0` has its sum over a
strongly connected class with a small complex bounded by `D X`.  This is the form needed for the
weighted entropy `U_c`, whose per-reaction term obeys the same bounds with a larger constant. -/
theorem core_part_le_on_gen [Nonempty S]
    (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (Φ : (S → ℕ) → N.R → ℝ) (C₀ : ℝ) (hC₀0 : 0 ≤ C₀)
    (hT1 : ∀ n r, Φ n r ≤ κ.k (Sum.inl r) * (1 / Real.exp 1 + C₀) *
      max (zeta (N.reaction r).source n) (zeta (N.reaction r).target n))
    (hT2 : ∀ n r, (∀ s, (N.reaction r).source s ≤ n s) →
      logZeta (N.reaction r).target n - logZeta (N.reaction r).source n + C₀ ≤ 0 →
      Φ n r ≤ κ.k (Sum.inl r) * zeta (N.reaction r).source n / 4 *
        (logZeta (N.reaction r).target n - logZeta (N.reaction r).source n + C₀))
    (Rc : Finset N.R) (hcut : CutLeavingOn N Rc) (y₀ : Complex S) (hy₀ : y₀ ∈ complexesOn N Rc)
    (hsmall : ∑ s, y₀ s ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : S → ℕ, ∑ r ∈ Rc, Φ n r ≤ D * Xmax n := by
  classical
  have hne : (complexesOn N Rc).Nonempty := ⟨y₀, hy₀⟩
  -- `Rc` is nonempty because `y₀` is one of its complexes
  have hRne : Rc.Nonempty := by
    have h := hy₀
    unfold complexesOn at h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨r, hr, -⟩ := Finset.mem_image.mp h; exact ⟨r, hr⟩
    · obtain ⟨r, hr, -⟩ := Finset.mem_image.mp h; exact ⟨r, hr⟩
  obtain ⟨κm, hκm_def⟩ : ∃ κm, κm = Rc.inf' hRne (fun r => κ.k (Sum.inl r)) := ⟨_, rfl⟩
  have hκm : 0 < κm := by
    rw [hκm_def]; exact (Finset.lt_inf'_iff _).mpr fun r _ => κ.positive _
  have hκm_le : ∀ r ∈ Rc, κm ≤ κ.k (Sum.inl r) := fun r hr => by
    rw [hκm_def]; exact Finset.inf'_le _ hr
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (∑ r ∈ Rc, κ.k (Sum.inl r)) * (1 / Real.exp 1 + C₀) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (Finset.sum_nonneg fun r _ => (κ.positive _).le) (by positivity)
  obtain ⟨B, hB⟩ : ∃ B, B = bands C₀ A κm (complexesOn N Rc).card := ⟨_, rfl⟩
  have hK := bands_strictMono hC₀0 hA0 hκm
  have hB0 : 0 < B := by rw [hB]; exact bands_pos _ _ _ _
  refine ⟨A * B, mul_nonneg hA0 hB0.le, fun n => ?_⟩
  -- the top value `ζ*`
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (complexesOn N Rc).sup' hne (fun y => zeta y n) := ⟨_, rfl⟩
  have hZge : ∀ y ∈ complexesOn N Rc, zeta y n ≤ Z := fun y hy => by
    rw [hZ]; exact Finset.le_sup' (fun y => zeta y n) hy
  obtain ⟨ytop, hytop, hZtop⟩ := Finset.exists_mem_eq_sup' hne (fun y => zeta y n)
  rw [← hZ] at hZtop
  have hZpos : 0 < Z := by rw [hZtop]; exact zeta_pos _ _
  have hX1 := one_le_Xmax n
  -- every term is at most `κ (1/e + C₀) ζ*`
  have hterm : ∀ r ∈ Rc, Φ n r ≤ κ.k (Sum.inl r) * (1 / Real.exp 1 + C₀) * Z := by
    intro r hr
    have h := hT1 n r
    have hmax : max (zeta (N.reaction r).source n) (zeta (N.reaction r).target n) ≤ Z :=
      max_le (hZge _ (source_mem_complexesOn N hr)) (hZge _ (target_mem_complexesOn N hr))
    have hc : 0 ≤ κ.k (Sum.inl r) * (1 / Real.exp 1 + C₀) := by
      have := κ.positive (Sum.inl r); positivity
    exact h.trans (mul_le_mul_of_nonneg_left hmax hc)
  have hsumA : ∑ r ∈ Rc, κ.k (Sum.inl r) * (1 / Real.exp 1 + C₀) * Z = A * Z := by
    rw [hA, ← Finset.sum_mul, ← Finset.sum_mul]
  have htotal : ∑ r ∈ Rc, Φ n r ≤ A * Z := by
    rw [← hsumA]; exact Finset.sum_le_sum fun r hr => hterm r hr
  rcases le_or_gt Z (B * Xmax n) with hsmallZ | hbigZ
  · -- Case I: `ζ* ≤ B X`
    calc ∑ r ∈ Rc, Φ n r ≤ A * Z := htotal
      _ ≤ A * (B * Xmax n) := mul_le_mul_of_nonneg_left hsmallZ hA0
      _ = A * B * Xmax n := by ring
  · -- Case II: `ζ* > B X`; find an empty band and a reaction crossing it
    have hDX : 0 ≤ A * B * Xmax n := mul_nonneg (mul_nonneg hA0 hB0.le) (by linarith [hX1])
    obtain ⟨ρ, hρ⟩ : ∃ ρ : Complex S → ℝ, ρ = fun y => Z / zeta y n := ⟨_, rfl⟩
    have hρapp : ∀ y, ρ y = Z / zeta y n := fun y => by rw [hρ]
    have hρtop : ρ ytop < bands C₀ A κm 0 := by
      rw [hρapp, ← hZtop, div_self hZpos.ne']
      simp [bands]
    obtain ⟨j, hjlt, hband⟩ := exists_empty_band (complexesOn N Rc) ρ (bands C₀ A κm) hK ytop hytop hρtop
    -- the top cluster
    obtain ⟨T, hT⟩ : ∃ T, T = (complexesOn N Rc).filter (fun y => ρ y < bands C₀ A κm j) :=
      ⟨_, rfl⟩
    have hTsub : T ⊆ complexesOn N Rc := by rw [hT]; exact Finset.filter_subset _ _
    have hTtop : ytop ∈ T := by
      rw [hT, Finset.mem_filter]
      exact ⟨hytop, lt_of_lt_of_le hρtop (hK.monotone (Nat.zero_le j))⟩
    have hKjB : bands C₀ A κm (j + 1) ≤ B := by
      rw [hB]; exact hK.monotone (by omega)
    have hy₀ρ : B < ρ y₀ := by
      have hz0 := zeta_pos y₀ n
      have hzX := zeta_le_Xmax_of_small y₀ n hsmall
      rw [hρapp, lt_div_iff₀ hz0]
      calc B * zeta y₀ n ≤ B * Xmax n := mul_le_mul_of_nonneg_left hzX hB0.le
        _ < Z := hbigZ
    have hKj : bands C₀ A κm j < bands C₀ A κm (j + 1) := hK (Nat.lt_succ_self j)
    have hy₀T : y₀ ∉ T := by
      rw [hT, Finset.mem_filter]
      intro h
      linarith [h.2]
    obtain ⟨r, hrRc, hrT, hrT'⟩ := hcut T hTsub ⟨ytop, hTtop⟩ ⟨y₀, hy₀, hy₀T⟩
    -- the source is in the top cluster, the target beyond the empty band
    have hsrc : ρ (N.reaction r).source < bands C₀ A κm j := by
      rw [hT, Finset.mem_filter] at hrT; exact hrT.2
    have htgt : bands C₀ A κm (j + 1) ≤ ρ (N.reaction r).target := by
      have hmem := target_mem_complexesOn N hrRc
      have hge : bands C₀ A κm j ≤ ρ (N.reaction r).target := by
        by_contra hc
        exact hrT' (by rw [hT, Finset.mem_filter]; exact ⟨hmem, lt_of_not_ge hc⟩)
      by_contra hc
      exact hband _ hmem ⟨hge, lt_of_not_ge hc⟩
    -- the source is enabled
    have hen : ∀ s, (N.reaction r).source s ≤ n s := by
      intro s
      by_contra hc
      have hdis := zeta_le_Xmax_of_disabled (N.reaction r).source n (hbin r).1 s
        (lt_of_not_ge hc)
      have hz := zeta_pos (N.reaction r).source n
      have : B < ρ (N.reaction r).source := by
        rw [hρapp, lt_div_iff₀ hz]
        calc B * zeta (N.reaction r).source n ≤ B * Xmax n :=
              mul_le_mul_of_nonneg_left hdis hB0.le
          _ < Z := hbigZ
      have hKjB' : bands C₀ A κm j ≤ B := le_of_lt (lt_of_lt_of_le hKj hKjB)
      linarith
    -- the log ratio across the band
    have hzs := zeta_pos (N.reaction r).source n
    have hzt := zeta_pos (N.reaction r).target n
    have hKjpos := bands_pos C₀ A κm j
    have hρs : ρ (N.reaction r).source = Z / zeta (N.reaction r).source n := hρapp _
    have hρt : ρ (N.reaction r).target = Z / zeta (N.reaction r).target n := hρapp _
    have hlogdiff : logZeta (N.reaction r).target n - logZeta (N.reaction r).source n ≤
        Real.log (bands C₀ A κm j) - Real.log (bands C₀ A κm (j + 1)) := by
      rw [← log_zeta, ← log_zeta]
      have hs' : Real.log (Z / zeta (N.reaction r).source n) < Real.log (bands C₀ A κm j) :=
        Real.log_lt_log (by positivity) (by rw [← hρs]; exact hsrc)
      have ht' : Real.log (bands C₀ A κm (j + 1)) ≤ Real.log (Z / zeta (N.reaction r).target n) :=
        Real.log_le_log (bands_pos _ _ _ _) (by rw [← hρt]; exact htgt)
      rw [Real.log_div hZpos.ne' hzs.ne'] at hs'
      rw [Real.log_div hZpos.ne' hzt.ne'] at ht'
      linarith
    have hlogK : Real.log (bands C₀ A κm (j + 1)) =
        Real.log (bands C₀ A κm j) + (C₀ + 4 * bands C₀ A κm j * (A + 1) / κm) := by
      rw [bands_succ, Real.log_mul hKjpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    have hneg : logZeta (N.reaction r).target n - logZeta (N.reaction r).source n + C₀ ≤
        -(4 * bands C₀ A κm j * (A + 1) / κm) := by linarith
    have hneg0 : logZeta (N.reaction r).target n - logZeta (N.reaction r).source n + C₀ ≤ 0 := by
      have : 0 ≤ 4 * bands C₀ A κm j * (A + 1) / κm := by positivity
      linarith
    have hcross := hT2 n r hen hneg0
    -- `κ ζ_y ≥ κ_min ζ*/K_j`
    have hzsrc : Z / bands C₀ A κm j < zeta (N.reaction r).source n := by
      rw [div_lt_iff₀ hKjpos]
      have := hsrc
      rw [hρs, div_lt_iff₀ hzs] at this
      linarith
    have hκz : κm * (Z / bands C₀ A κm j) ≤ κ.k (Sum.inl r) * zeta (N.reaction r).source n :=
      mul_le_mul (hκm_le r hrRc) hzsrc.le (by positivity) (κ.positive _).le
    have hcross' : Φ n r ≤ -(A + 1) * Z := by
      have hfac : κ.k (Sum.inl r) * zeta (N.reaction r).source n / 4 *
          (logZeta (N.reaction r).target n - logZeta (N.reaction r).source n + C₀) ≤
          κm * (Z / bands C₀ A κm j) / 4 * (-(4 * bands C₀ A κm j * (A + 1) / κm)) := by
        have hq : κm * (Z / bands C₀ A κm j) / 4 ≤
            κ.k (Sum.inl r) * zeta (N.reaction r).source n / 4 := by linarith
        have hq0 : 0 ≤ κm * (Z / bands C₀ A κm j) / 4 := by positivity
        calc κ.k (Sum.inl r) * zeta (N.reaction r).source n / 4 *
              (logZeta (N.reaction r).target n - logZeta (N.reaction r).source n + C₀)
            ≤ κm * (Z / bands C₀ A κm j) / 4 *
              (logZeta (N.reaction r).target n - logZeta (N.reaction r).source n + C₀) :=
              mul_le_mul_of_nonpos_right hq hneg0
          _ ≤ κm * (Z / bands C₀ A κm j) / 4 * (-(4 * bands C₀ A κm j * (A + 1) / κm)) :=
              mul_le_mul_of_nonneg_left hneg hq0
      have hκm0 : κm ≠ 0 := hκm.ne'
      have hK0 : bands C₀ A κm j ≠ 0 := hKjpos.ne'
      have heq : κm * (Z / bands C₀ A κm j) / 4 * (-(4 * bands C₀ A κm j * (A + 1) / κm)) =
          -(A + 1) * Z := by
        field_simp
        try ring
      linarith [hcross, hfac, heq]
    -- all the other terms
    have hrest : ∑ r' ∈ Rc.erase r, Φ n r' ≤ A * Z := by
      calc ∑ r' ∈ Rc.erase r, Φ n r'
          ≤ ∑ r' ∈ Rc.erase r, κ.k (Sum.inl r') * (1 / Real.exp 1 + C₀) * Z :=
            Finset.sum_le_sum fun r' hr' => hterm r' (Finset.mem_of_mem_erase hr')
        _ ≤ ∑ r' ∈ Rc, κ.k (Sum.inl r') * (1 / Real.exp 1 + C₀) * Z :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun r' _ _ => by have := κ.positive (Sum.inl r'); positivity)
        _ = A * Z := hsumA
    have hsplit := Finset.add_sum_erase Rc (Φ n) hrRc
    rw [← hsplit]
    linarith [hcross', hrest, hZpos, hDX]


/-- **The core part of the entropy drift over one class of reactions is at most `D X`.**  The
class `Rc` must have a strongly connected complex graph and contain a complex with at most one
molecule. -/
theorem core_part_le_on [Nonempty S]
    (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (Rc : Finset N.R) (hcut : CutLeavingOn N Rc) (y₀ : Complex S) (hy₀ : y₀ ∈ complexesOn N Rc)
    (hsmall : ∑ s, y₀ s ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : S → ℕ, ∑ r ∈ Rc, term N κ n r ≤ D * Xmax n :=
  core_part_le_on_gen N κ hbin (fun n r => term N κ n r) (4 * Fintype.card S : ℝ)
    (by positivity) (fun n r => term_le N κ hbin n r)
    (fun n r hen hneg => term_le_of_descent N κ hbin n r hen hneg) Rc hcut y₀ hy₀ hsmall

/-! ## The weighted entropy `U_c`: the per-reaction term

For a reference vector `c > 0`, the weighted entropy `U_c(n) = U(n) − ∑ₛ nₛ log cₛ` changes along
the core reaction `r` by `ΔU − ⟨ξ_r, log c⟩`.  Its per-reaction term `termC` obeys the two bounds
of `term` with the constant `4|S| + C_c`, `C_c = 2 ∑ₛ |log cₛ|`, so the band argument
`core_part_le_on_gen` applies to it unchanged (`coreC_part_le_on`).  This is the small-class step of
`docs/notes/binary-flows-mixed-complex-balanced.md`. -/

/-- The shift `⟨ξ_r, log c⟩`. -/
noncomputable def shift (c : S → ℝ) (r : N.R) : ℝ :=
  ∑ s, (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) * Real.log (c s)

/-- The bound `C_c = 2 ∑ₛ |log cₛ|` on the shift of a binary reaction. -/
noncomputable def Cc (c : S → ℝ) : ℝ := 2 * ∑ s, |Real.log (c s)|

theorem Cc_nonneg (c : S → ℝ) : 0 ≤ Cc c := by
  unfold Cc; exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ => abs_nonneg _)

theorem abs_shift_le (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (c : S → ℝ) (r : N.R) : |shift N c r| ≤ Cc c := by
  have hξ : ∀ s, |(((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ))| ≤ 2 := by
    intro s
    have ht : (N.reaction r).target s ≤ 2 :=
      le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ s)) (hbin r).2
    have hy : (N.reaction r).source s ≤ 2 :=
      le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ s)) (hbin r).1
    have ht' : ((N.reaction r).target s : ℝ) ≤ 2 := by exact_mod_cast ht
    have hy' : ((N.reaction r).source s : ℝ) ≤ 2 := by exact_mod_cast hy
    have ht0 : (0 : ℝ) ≤ (N.reaction r).target s := Nat.cast_nonneg _
    have hy0 : (0 : ℝ) ≤ (N.reaction r).source s := Nat.cast_nonneg _
    rw [abs_le]; constructor <;> linarith
  unfold shift Cc
  calc |∑ s, (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) * Real.log (c s)|
      ≤ ∑ s, |(((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) *
          Real.log (c s)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, 2 * |Real.log (c s)| := Finset.sum_le_sum fun s _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hξ s) (abs_nonneg _)
    _ = 2 * ∑ s, |Real.log (c s)| := by rw [Finset.mul_sum]

/-- The contribution of the core reaction `r` to the drift of `U_c`. -/
noncomputable def termC (c : S → ℝ) (n : S → ℕ) (r : N.R) : ℝ :=
  term N κ n r - N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) * shift N c r

theorem termC_le (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (c : S → ℝ) (n : S → ℕ) (r : N.R) :
    termC N κ c n r ≤ κ.k (Sum.inl r) * (1 / Real.exp 1 + (4 * Fintype.card S + Cc c)) *
      max (zeta (N.reaction r).source n) (zeta (N.reaction r).target n) := by
  have h1 := term_le N κ hbin n r
  have hrate0 := N.fullyOpen.stochasticMassActionRate_nonneg κ n (Sum.inl r)
  have hrate := rate_le N.fullyOpen κ n (Sum.inl r)
  rw [source_inl] at hrate
  have hsh := abs_shift_le N hbin c r
  have hk := κ.positive (Sum.inl r)
  have hz := zeta_pos (N.reaction r).source n
  have hmax : zeta (N.reaction r).source n ≤
      max (zeta (N.reaction r).source n) (zeta (N.reaction r).target n) := le_max_left _ _
  have hCc := Cc_nonneg c
  have e1 : -(N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) * shift N c r) ≤
      N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) * Cc c := by
    have := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hsh) hrate0
    linarith
  have e2 : N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) * Cc c ≤
      κ.k (Sum.inl r) * max (zeta (N.reaction r).source n) (zeta (N.reaction r).target n) *
        Cc c := by
    apply mul_le_mul_of_nonneg_right _ hCc
    exact hrate.trans (mul_le_mul_of_nonneg_left hmax hk.le)
  unfold termC
  nlinarith [h1, e1, e2]

theorem termC_le_of_descent (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧
      ∑ s, (N.reaction r).target s ≤ 2)
    (c : S → ℝ) (n : S → ℕ) (r : N.R) (hen : ∀ s, (N.reaction r).source s ≤ n s)
    (hneg : logZeta (N.reaction r).target n - logZeta (N.reaction r).source n +
      (4 * Fintype.card S + Cc c) ≤ 0) :
    termC N κ c n r ≤ κ.k (Sum.inl r) * zeta (N.reaction r).source n / 4 *
      (logZeta (N.reaction r).target n - logZeta (N.reaction r).source n +
        (4 * Fintype.card S + Cc c)) := by
  have hstep : countU (N.fullyOpen.jumpNextCount n (Sum.inl r)) - countU n ≤
      logZeta (N.reaction r).target n - logZeta (N.reaction r).source n +
        4 * Fintype.card S :=
    countU_step_le (N.reaction r).source (N.reaction r).target n (hbin r).1 (hbin r).2 hen
  have hsh : -shift N c r ≤ Cc c := by
    have := neg_le_of_abs_le (abs_shift_le N hbin c r); linarith
  have hrate0 := N.fullyOpen.stochasticMassActionRate_nonneg κ n (Sum.inl r)
  have hge := rate_ge N.fullyOpen κ n (Sum.inl r) (by rw [source_inl]; exact (hbin r).1)
    (by rw [source_inl]; exact hen)
  rw [source_inl] at hge
  unfold termC term
  calc N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) *
        (countU (N.fullyOpen.jumpNextCount n (Sum.inl r)) - countU n) -
        N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) * shift N c r
      = N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) *
        ((countU (N.fullyOpen.jumpNextCount n (Sum.inl r)) - countU n) - shift N c r) := by ring
    _ ≤ N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) *
        (logZeta (N.reaction r).target n - logZeta (N.reaction r).source n +
          (4 * Fintype.card S + Cc c)) := mul_le_mul_of_nonneg_left (by linarith) hrate0
    _ ≤ κ.k (Sum.inl r) * zeta (N.reaction r).source n / 4 *
        (logZeta (N.reaction r).target n - logZeta (N.reaction r).source n +
          (4 * Fintype.card S + Cc c)) := mul_le_mul_of_nonpos_right hge hneg

/-! ## Every binary reaction: the bound used with complex balance -/

/-- The weighted log-ratio `L^c_r = log ζ_{y'} − log ζ_y − ⟨ξ_r, log c⟩`. -/
noncomputable def logRatioC (c : S → ℝ) (n : S → ℕ) (r : N.R) : ℝ :=
  logZeta (N.reaction r).target n - logZeta (N.reaction r).source n - shift N c r

/-- **The per-reaction bound for the complex-balanced part**:
`termC_r + κ_r ζ_{y_r} (1 − e^{L^c_r}) ≤ C X` for every binary reaction.  Summed over a
complex-balanced set of reactions the second terms cancel (`sum_complexBalanced_eq_zero`), which
bounds the `U_c`-drift of that set by `C X`. -/
theorem fC_le (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (c : S → ℝ) (r : N.R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : S → ℕ,
      termC N κ c n r + κ.k (Sum.inl r) * zeta (N.reaction r).source n *
        (1 - Real.exp (logRatioC N c n r)) ≤ C * Xmax n := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, k = κ.k (Sum.inl r) := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; exact κ.positive _
  obtain ⟨M₁, hM₁⟩ : ∃ M₁ : ℝ, M₁ = 4 * (4 * Fintype.card S + 1) := ⟨_, rfl⟩
  have hM₁0 : 0 ≤ M₁ := by rw [hM₁]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = k * (12 + 4 * Real.exp (M₁ + Cc c)) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine ⟨k * 2 + Fintype.card S * B, by positivity, fun n => ?_⟩
  have hX1 := one_le_Xmax n
  have hX0 : 0 < Xmax n := by linarith
  have hkX0 : 0 ≤ k * Xmax n := mul_nonneg hk0.le (by linarith)
  have hCc := Cc_nonneg c
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = zeta (N.reaction r).source n := ⟨_, rfl⟩
  obtain ⟨Lc, hLc⟩ : ∃ Lc, Lc = logRatioC N c n r := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) :=
    ⟨_, rfl⟩
  rw [← hk, ← hζ, ← hLc]
  have hζpos : 0 < ζ := by rw [hζ]; exact zeta_pos _ n
  have hkζ : 0 ≤ k * ζ := by positivity
  have hexp := Real.exp_pos Lc
  have h3 : k * ζ * (1 - Real.exp Lc) ≤ k * ζ := by nlinarith [mul_nonneg hkζ hexp.le]
  have hrate0 : 0 ≤ lam := by
    rw [hlam]; exact N.fullyOpen.stochasticMassActionRate_nonneg κ n (Sum.inl r)
  have hrate_le : lam ≤ k * ζ := by
    have h := rate_le N.fullyOpen κ n (Sum.inl r)
    rw [source_inl] at h
    rw [hlam, hk, hζ]; exact h
  by_cases hen : ∀ s, (N.reaction r).source s ≤ n s
  · -- enabled
    have hrate_ge : k * ζ / 4 ≤ lam := by
      have h := rate_ge N.fullyOpen κ n (Sum.inl r) (by rw [source_inl]; exact (hbin r).1)
        (by rw [source_inl]; exact hen)
      rw [source_inl] at h
      rw [hlam, hk, hζ]; exact h
    obtain ⟨E, hE⟩ : ∃ E, E = ∑ s, errS (n s)
        (n s - (N.reaction r).source s + (N.reaction r).target s) := ⟨_, rfl⟩
    have hstep : countU (N.fullyOpen.jumpNextCount n (Sum.inl r)) - countU n ≤
        logZeta (N.reaction r).target n - logZeta (N.reaction r).source n + E := by
      rw [hE]
      exact countU_step_err (N.reaction r).source (N.reaction r).target n (hbin r).1 (hbin r).2 hen
    have hE0 : 0 ≤ E := by rw [hE]; exact Finset.sum_nonneg fun s _ => errS_nonneg _ _
    have hE4 : E ≤ 4 * Fintype.card S := by
      rw [hE]
      calc ∑ s, errS (n s) (n s - (N.reaction r).source s + (N.reaction r).target s)
          ≤ ∑ _s : S, (4 : ℝ) := Finset.sum_le_sum fun s _ => errS_le_four _ _
        _ = 4 * Fintype.card S := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    have htermC : termC N κ c n r ≤ lam * Lc + lam * E := by
      unfold termC term
      rw [← hlam, hLc]
      unfold logRatioC
      have h := mul_le_mul_of_nonneg_left
        (show countU (N.fullyOpen.jumpNextCount n (Sum.inl r)) - countU n - shift N c r ≤
          logZeta (N.reaction r).target n - logZeta (N.reaction r).source n - shift N c r + E
          by linarith) hrate0
      linarith
    rcases le_or_gt Lc (-M₁) with hLneg | hLbig
    · -- a very negative log-ratio: the total is negative
      have hL0 : Lc ≤ 0 := by linarith
      have h1 : lam * Lc ≤ k * ζ / 4 * Lc := mul_le_mul_of_nonpos_right hrate_ge hL0
      have h2 : lam * E ≤ k * ζ * (4 * Fintype.card S) := mul_le_mul hrate_le hE4 hE0 hkζ
      have h4 : k * ζ / 4 * Lc ≤ k * ζ / 4 * (-M₁) :=
        mul_le_mul_of_nonneg_left hLneg (by positivity)
      have hfin : k * ζ / 4 * (-M₁) + k * ζ * (4 * Fintype.card S) + k * ζ = 0 := by
        rw [hM₁]; ring
      have hpos : 0 ≤ (k * 2 + Fintype.card S * B) * Xmax n := by positivity
      linarith [htermC, h1, h2, h3, h4, hfin, hpos]
    · -- the main part is at most `k`
      have hmain : lam * Lc + k * ζ * (1 - Real.exp Lc) ≤ k := by
        rcases le_or_gt 0 Lc with hL | hL
        · have := BinaryFlowsMixed.f_le_zero_of_nonneg hkζ hrate_le hL
          linarith
        · have hgap := rate_gap_sq N.fullyOpen κ n (Sum.inl r)
            (by rw [source_inl]; exact (hbin r).1) (by rw [source_inl]; exact hen)
          rw [source_inl, ← hk, ← hlam, ← hζ] at hgap
          have hkζpos : 0 < k * ζ := by positivity
          have hkζne : k * ζ ≠ 0 := hkζpos.ne'
          obtain ⟨ε, hε⟩ : ∃ ε, ε = (k * ζ - lam) / (k * ζ) := ⟨_, rfl⟩
          have hε0 : 0 ≤ ε := by rw [hε]; exact div_nonneg (by linarith) hkζpos.le
          have hε1 : ε < 1 := by rw [hε, div_lt_one hkζpos]; linarith
          have e1 : k * ζ * ε = k * ζ - lam := by rw [hε, mul_comm, div_mul_cancel₀ _ hkζne]
          have hlam' : k * ζ * (1 - ε) ≤ lam := by
            have : k * ζ * (1 - ε) = lam := by rw [mul_sub, mul_one, e1]; ring
            linarith
          have hf := BinaryFlowsMixed.f_le_eps_sq hkζ hε0 hε1 hlam' hL
          have e2 : k * ζ * ε ^ 2 = (k * ζ - lam) * ε := by rw [sq, ← mul_assoc, e1]
          have e3 : (k * ζ - lam) * ε = (k * ζ - lam) ^ 2 / (k * ζ) := by
            rw [hε, sq, mul_div_assoc]
          have hsq : (k * ζ - lam) ^ 2 / (k * ζ) ≤ k := by
            rw [div_le_iff₀ hkζpos]; linarith
          linarith [hf, e2, e3, hsq]
      -- the errors: each species contributes at most `B X`
      have hζ' : ζ ≤ Real.exp (M₁ + Cc c) * zeta (N.reaction r).target n := by
        have hsh : -Cc c ≤ shift N c r := neg_le_of_abs_le (abs_shift_le N hbin c r)
        have hlog : logZeta (N.reaction r).source n ≤
            logZeta (N.reaction r).target n + (M₁ + Cc c) := by
          have : -M₁ < logZeta (N.reaction r).target n - logZeta (N.reaction r).source n -
              shift N c r := by
            rw [hLc] at hLbig; unfold logRatioC at hLbig; exact hLbig
          linarith
        have hz' := zeta_pos (N.reaction r).target n
        calc ζ = Real.exp (logZeta (N.reaction r).source n) := by
              rw [hζ, ← log_zeta, Real.exp_log (zeta_pos _ n)]
          _ ≤ Real.exp (logZeta (N.reaction r).target n + (M₁ + Cc c)) :=
              Real.exp_le_exp.mpr hlog
          _ = Real.exp (M₁ + Cc c) * zeta (N.reaction r).target n := by
              rw [Real.exp_add, ← log_zeta, Real.exp_log hz', mul_comm]
      have hper : ∀ s, lam * errS (n s)
          (n s - (N.reaction r).source s + (N.reaction r).target s) ≤ B * Xmax n := by
        intro s
        have hys : (N.reaction r).source s ≤ 2 :=
          (Finset.single_le_sum (f := (N.reaction r).source) (fun t _ => Nat.zero_le _)
            (Finset.mem_univ s)).trans (hbin r).1
        have hys' : (N.reaction r).target s ≤ 2 :=
          (Finset.single_le_sum (f := (N.reaction r).target) (fun t _ => Nat.zero_le _)
            (Finset.mem_univ s)).trans (hbin r).2
        have hens := hen s
        have hzs := zc_pos n s
        have herr0 := errS_nonneg (n s) (n s - (N.reaction r).source s + (N.reaction r).target s)
        rcases Nat.eq_zero_or_pos ((N.reaction r).source s) with h0 | hpos
        · rcases Nat.eq_zero_or_pos ((N.reaction r).target s) with h0' | hpos'
          · have hm : n s - (N.reaction r).source s + (N.reaction r).target s = n s := by omega
            rw [hm]
            have e : errS (n s) (n s) = 0 := by unfold errS; simp
            rw [e, mul_zero]; positivity
          · -- a species only in the target
            have hlt : n s < n s - (N.reaction r).source s + (N.reaction r).target s := by omega
            have herr := errS_le_tgt (n s) _ hlt
            have hzeq : max ((n s : ℕ) : ℝ) 1 = zc n s := rfl
            rw [hzeq] at herr
            have hz'le := zeta_le_zc_mul (N.reaction r).target n (hbin r).2 s hpos'
            have hB' : k * (4 * Real.exp (M₁ + Cc c)) ≤ B := by
              rw [hB]; nlinarith [Real.exp_pos (M₁ + Cc c)]
            have hzsne : zc n s ≠ 0 := hzs.ne'
            calc lam * errS (n s) (n s - (N.reaction r).source s + (N.reaction r).target s)
                ≤ k * ζ * (4 / zc n s) := mul_le_mul hrate_le herr herr0 hkζ
              _ ≤ k * (Real.exp (M₁ + Cc c) * (zc n s * Xmax n)) * (4 / zc n s) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  apply mul_le_mul_of_nonneg_left _ hk0.le
                  exact hζ'.trans (mul_le_mul_of_nonneg_left hz'le (Real.exp_pos _).le)
              _ = k * (4 * Real.exp (M₁ + Cc c)) * Xmax n := by first | (field_simp; ring) | field_simp
              _ ≤ B * Xmax n := mul_le_mul_of_nonneg_right hB' (by linarith)
        · -- a species of the source
          have hn1 : 1 ≤ n s := le_trans hpos hens
          have herr := errS_le_src (n s) (n s - (N.reaction r).source s + (N.reaction r).target s)
            hn1 (by omega) (by omega)
          have hzeq : zc n s = n s := by unfold zc; exact max_eq_left (by exact_mod_cast hn1)
          have hzle := zeta_le_zc_mul (N.reaction r).source n (hbin r).1 s hpos
          rw [hzeq, ← hζ] at hzle
          have hnpos : (0 : ℝ) < n s := by exact_mod_cast hn1
          have hnne : (n s : ℝ) ≠ 0 := hnpos.ne'
          have hB' : k * 12 ≤ B := by rw [hB]; nlinarith [Real.exp_pos (M₁ + Cc c)]
          calc lam * errS (n s) (n s - (N.reaction r).source s + (N.reaction r).target s)
              ≤ k * ζ * (12 / (n s : ℝ)) := mul_le_mul hrate_le herr herr0 hkζ
            _ ≤ k * ((n s : ℝ) * Xmax n) * (12 / (n s : ℝ)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact mul_le_mul_of_nonneg_left hzle hk0.le
            _ = k * 12 * Xmax n := by first | (field_simp; ring) | field_simp
            _ ≤ B * Xmax n := mul_le_mul_of_nonneg_right hB' (by linarith)
      have hlamE : lam * E ≤ Fintype.card S * (B * Xmax n) := by
        rw [hE, Finset.mul_sum]
        calc ∑ s, lam * errS (n s) (n s - (N.reaction r).source s + (N.reaction r).target s)
            ≤ ∑ _s : S, B * Xmax n := Finset.sum_le_sum fun s _ => hper s
          _ = Fintype.card S * (B * Xmax n) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hkX : k ≤ k * Xmax n := le_mul_of_one_le_right hk0.le hX1
      nlinarith [htermC, hmain, hlamE, hkX, hkX0]
  · -- disabled: the rate vanishes
    push_neg at hen
    obtain ⟨s, hs⟩ := hen
    have hlam0 : lam = 0 := by
      rw [hlam]
      exact rate_eq_zero_of_disabled N.fullyOpen κ n (Sum.inl r) s (by rw [source_inl]; exact hs)
    have htermC : termC N κ c n r = 0 := by
      unfold termC term; rw [← hlam, hlam0]; ring
    have hzX : ζ ≤ Xmax n := by
      rw [hζ]; exact zeta_le_Xmax_of_disabled (N.reaction r).source n (hbin r).1 s hs
    have h4 : k * ζ ≤ k * Xmax n := mul_le_mul_of_nonneg_left hzX hk0.le
    have hpos : 0 ≤ Fintype.card S * B * Xmax n := by positivity
    rw [htermC]
    nlinarith [h3, h4, hpos, hkX0]

/-- **The small-class part of the drift of `U_c` is at most `D X`.** -/
theorem coreC_part_le_on [Nonempty S]
    (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (c : S → ℝ) (Rc : Finset N.R) (hcut : CutLeavingOn N Rc) (y₀ : Complex S)
    (hy₀ : y₀ ∈ complexesOn N Rc) (hsmall : ∑ s, y₀ s ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : S → ℕ, ∑ r ∈ Rc, termC N κ c n r ≤ D * Xmax n :=
  core_part_le_on_gen N κ hbin (fun n r => termC N κ c n r) (4 * Fintype.card S + Cc c)
    (add_nonneg (by positivity) (Cc_nonneg c)) (fun n r => termC_le N κ hbin c n r)
    (fun n r hen hneg => termC_le_of_descent N κ hbin c n r hen hneg) Rc hcut y₀ hy₀ hsmall

/-- **The core part of the entropy drift is at most `D X`** (one strongly connected class). -/
theorem core_part_le [Nonempty S]
    (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (hcut : CutLeaving N) (y₀ : Complex S) (hy₀ : y₀ ∈ N.complexes) (hsmall : ∑ s, y₀ s ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : S → ℕ, ∑ r, term N κ n r ≤ D * Xmax n :=
  core_part_le_on N κ hbin Finset.univ (cutLeavingOn_univ hcut) y₀
    (by rw [complexesOn_univ]; exact hy₀) hsmall

/-- **The core part over several classes.**  If the reactions are partitioned into classes
(`cls : N.R → ι`), each with a strongly connected complex graph and a complex with at most one
molecule, the core part of the entropy drift is at most `D X`. -/
theorem core_part_le_of_classes [Nonempty S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (cls : N.R → ι)
    (hcls : ∀ c, CutLeavingOn N (Finset.univ.filter (fun r => cls r = c)) ∧
      ∃ y₀ ∈ complexesOn N (Finset.univ.filter (fun r => cls r = c)), ∑ s, y₀ s ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : S → ℕ, ∑ r, term N κ n r ≤ D * Xmax n := by
  classical
  have h : ∀ c, ∃ D : ℝ, 0 ≤ D ∧ ∀ n : S → ℕ,
      ∑ r ∈ Finset.univ.filter (fun r => cls r = c), term N κ n r ≤ D * Xmax n := by
    intro c
    obtain ⟨hcut, y₀, hy₀, hsmall⟩ := hcls c
    exact core_part_le_on N κ hbin _ hcut y₀ hy₀ hsmall
  choose D hD hDle using h
  refine ⟨∑ c, D c, Finset.sum_nonneg fun c _ => hD c, fun n => ?_⟩
  rw [← Finset.sum_fiberwise Finset.univ cls (term N κ n), Finset.sum_mul]
  exact Finset.sum_le_sum fun c _ => hDle c n

/-! ## The flow part and the full drift -/

theorem next_inflow (n : S → ℕ) (s : S) :
    N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inl s)) = fun t => n t + if t = s then 1 else 0 := by
  funext t
  simp [jumpNextCount, inflowReaction, Complex.zero]

theorem next_outflow (n : S → ℕ) (s : S) :
    N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s)) = fun t => n t - if t = s then 1 else 0 := by
  funext t
  simp [jumpNextCount, outflowReaction, Complex.zero]

/-- A change of one coordinate changes `U` by the change of that coordinate's term. -/
theorem countU_update (n m : S → ℕ) (s : S) (h : ∀ t, t ≠ s → m t = n t) :
    countU m - countU n = uE (m s) - uE (n s) := by
  unfold countU
  rw [← Finset.sum_sub_distrib,
    Finset.sum_eq_single s (fun t _ ht => by rw [h t ht, sub_self]) (by simp)]

theorem inflow_step (n : S → ℕ) (s : S) :
    countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inl s))) - countU n ≤
      Real.log (Xmax n) + 4 := by
  rw [next_inflow, countU_update n _ s (fun t ht => by simp [ht])]
  simp only [eq_self_iff_true, ite_true]
  have h := uE_step (n s) (n s + 1) (by omega) (by omega)
  have hz : Real.log (max ((n s : ℕ) : ℝ) 1) ≤ Real.log (Xmax n) :=
    Real.log_le_log (zc_pos n s) (zc_le_Xmax n s)
  push_cast at h ⊢
  nlinarith [h, hz]

theorem outflow_step (n : S → ℕ) (s : S) (hs : 1 ≤ n s) :
    countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s))) - countU n ≤
      -Real.log (n s) + 4 := by
  rw [next_outflow, countU_update n _ s (fun t ht => by simp [ht])]
  simp only [eq_self_iff_true, ite_true]
  have h := uE_step (n s) (n s - 1) (by omega) (by omega)
  have hmax : max ((n s : ℕ) : ℝ) 1 = n s := max_eq_left (by exact_mod_cast hs)
  rw [hmax] at h
  rw [Nat.cast_sub hs] at h ⊢
  push_cast at h ⊢
  nlinarith [h]

/-- The entropy drift of `N.fullyOpen` split into the core, inflow and outflow parts. -/
theorem drift_split (n : S → ℕ) :
    (N.fullyOpen.jumpSystem κ).drift countU n =
      ∑ r, term N κ n r +
      ∑ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inl s)) *
        (countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inl s))) - countU n) +
      ∑ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inr s)) *
        (countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s))) - countU n) := by
  have e : (N.fullyOpen.jumpSystem κ).drift countU n =
      ∑ r : N.R ⊕ S ⊕ S, N.fullyOpen.stochasticMassActionRate κ n r *
        (countU (N.fullyOpen.jumpNextCount n r) - countU n) := rfl
  rw [e, Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
  rfl

/-- **The entropy is a Foster function** as soon as the core part of its drift is `O(X)`:
`L U ≤ −X + K`, `X` the largest count (at least `1`). -/
theorem entropy_drift_le_of_core [Nonempty S]
    (hcoreD : ∃ D : ℝ, 0 ≤ D ∧ ∀ n : S → ℕ, ∑ r, term N κ n r ≤ D * Xmax n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n, (N.fullyOpen.jumpSystem κ).drift countU n ≤ -Xmax n + K := by
  classical
  obtain ⟨D, hD, hcore⟩ := hcoreD
  obtain ⟨κo, hκo_def⟩ : ∃ κo, κo = Finset.univ.inf' Finset.univ_nonempty
      (fun s : S => κ.k (Sum.inr (Sum.inr s))) := ⟨_, rfl⟩
  have hκo : 0 < κo := by
    rw [hκo_def]; exact (Finset.lt_inf'_iff _).mpr fun s _ => κ.positive _
  have hκo_le : ∀ s, κo ≤ κ.k (Sum.inr (Sum.inr s)) := fun s => by
    rw [hκo_def]; exact Finset.inf'_le _ (Finset.mem_univ s)
  obtain ⟨Kin, hKin⟩ : ∃ Kin, Kin = ∑ s : S, κ.k (Sum.inr (Sum.inl s)) := ⟨_, rfl⟩
  obtain ⟨Kout, hKout⟩ : ∃ Kout, Kout = ∑ s : S, κ.k (Sum.inr (Sum.inr s)) := ⟨_, rfl⟩
  have hKin0 : 0 ≤ Kin := by rw [hKin]; exact Finset.sum_nonneg fun s _ => (κ.positive _).le
  have hKout0 : 0 ≤ Kout := by rw [hKout]; exact Finset.sum_nonneg fun s _ => (κ.positive _).le
  refine ⟨(D + 4 * Kout + Kin + 1) * Real.exp ((D + 4 * Kout + Kin + 1) / κo) + 4 * Kin,
    by positivity, fun n => ?_⟩
  have hX1 := one_le_Xmax n
  have hX0 : 0 < Xmax n := by linarith
  rw [drift_split]
  -- inflows
  have hin : ∑ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inl s)) *
      (countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inl s))) - countU n) ≤
      Kin * Real.log (Xmax n) + Kin * 4 := by
    rw [hKin, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [fullyOpen_rate_inflow]
    have := mul_le_mul_of_nonneg_left (inflow_step N n s) (κ.positive (Sum.inr (Sum.inl s))).le
    linarith
  -- outflows: each term is at most `κ n (4 − log n)`; the largest coordinate gives `−κo X log X`
  have hout_term : ∀ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inr s)) *
      (countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s))) - countU n) ≤
      κ.k (Sum.inr (Sum.inr s)) * ((n s : ℝ) * (4 - Real.log (zc n s))) := by
    intro s
    rw [fullyOpen_rate_outflow]
    rcases Nat.eq_zero_or_pos (n s) with h0 | hpos
    · rw [h0]; simp
    · have hstep := outflow_step N n s hpos
      have hz : zc n s = n s := by unfold zc; exact max_eq_left (by exact_mod_cast hpos)
      rw [hz]
      have hk := κ.positive (Sum.inr (Sum.inr s))
      have hn0 : (0 : ℝ) ≤ n s := Nat.cast_nonneg _
      have := mul_le_mul_of_nonneg_left hstep (mul_nonneg hk.le hn0)
      nlinarith [this]
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty n
  have hout : ∑ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inr s)) *
      (countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s))) - countU n) ≤
      4 * Kout * Xmax n - κo * (Xmax n * Real.log (Xmax n)) := by
    calc _ ≤ ∑ s, κ.k (Sum.inr (Sum.inr s)) * ((n s : ℝ) * (4 - Real.log (zc n s))) :=
          Finset.sum_le_sum fun s _ => hout_term s
      _ = ∑ s, κ.k (Sum.inr (Sum.inr s)) * (4 * (n s : ℝ)) -
          ∑ s, κ.k (Sum.inr (Sum.inr s)) * ((n s : ℝ) * Real.log (zc n s)) := by
          rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => by ring
      _ ≤ 4 * Kout * Xmax n - κo * (Xmax n * Real.log (Xmax n)) := by
          have h1 : ∑ s, κ.k (Sum.inr (Sum.inr s)) * (4 * (n s : ℝ)) ≤ Kout * (4 * Xmax n) := by
            rw [hKout, Finset.sum_mul]
            refine Finset.sum_le_sum fun s _ => ?_
            have hns : (n s : ℝ) ≤ Xmax n := (le_max_left _ _).trans (zc_le_Xmax n s)
            have hk := κ.positive (Sum.inr (Sum.inr s))
            nlinarith
          have h2 : κo * (Xmax n * Real.log (Xmax n)) ≤
              ∑ s, κ.k (Sum.inr (Sum.inr s)) * ((n s : ℝ) * Real.log (zc n s)) := by
            have hnonneg : ∀ s, 0 ≤ κ.k (Sum.inr (Sum.inr s)) * ((n s : ℝ) * Real.log (zc n s)) :=
              fun s => mul_nonneg (κ.positive _).le
                (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (one_le_zc n s)))
            have hsingle := Finset.single_le_sum (fun s _ => hnonneg s) (Finset.mem_univ p)
            -- the largest coordinate
            rcases Nat.eq_zero_or_pos (n p) with h0 | hpos
            · have hX : Xmax n = 1 := by
                unfold Xmax; rw [hp, h0]; simp
              rw [hX, Real.log_one, mul_zero, mul_zero]
              exact Finset.sum_nonneg fun s _ => hnonneg s
            · have hX : Xmax n = n p := by
                unfold Xmax; rw [hp]; exact max_eq_left (by exact_mod_cast hpos)
              have hz : zc n p = n p := by unfold zc; exact max_eq_left (by exact_mod_cast hpos)
              have hl : 0 ≤ (n p : ℝ) * Real.log (n p) :=
                mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hpos))
              rw [hX]
              rw [hz] at hsingle
              calc κo * ((n p : ℝ) * Real.log (n p))
                  ≤ κ.k (Sum.inr (Sum.inr p)) * ((n p : ℝ) * Real.log (n p)) :=
                    mul_le_mul_of_nonneg_right (hκo_le p) hl
                _ ≤ _ := hsingle
          linarith
  have hcoreX := hcore n
  have hsc := scalar_drift (c₁ := D + 4 * Kout) (c₂ := Kin) (c₃ := 4 * Kin)
    (by linarith) hKin0 hκo hX1
  linarith [hcoreX, hin, hout, hsc]

/-- **The flow part of the entropy drift** (extracted from `entropy_drift_le_of_core`):
`inflows + outflows ≤ Kin log X + 4 Kin + 4 Kout X − κo X log X`. -/
theorem flows_le [Nonempty S] :
    ∃ κo Kin Kout : ℝ, 0 < κo ∧ 0 ≤ Kin ∧ 0 ≤ Kout ∧
      (∀ s, κ.k (Sum.inr (Sum.inl s)) ≤ Kin) ∧ (∀ s, κ.k (Sum.inr (Sum.inr s)) ≤ Kout) ∧
      (Kin = ∑ s : S, κ.k (Sum.inr (Sum.inl s))) ∧ (Kout = ∑ s : S, κ.k (Sum.inr (Sum.inr s))) ∧
      ∀ n : S → ℕ,
      ∑ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inl s)) *
        (countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inl s))) - countU n) +
      ∑ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inr s)) *
        (countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s))) - countU n) ≤
      Kin * Real.log (Xmax n) + Kin * 4 + (4 * Kout * Xmax n - κo * (Xmax n * Real.log (Xmax n))) := by
  classical
  obtain ⟨κo, hκo_def⟩ : ∃ κo, κo = Finset.univ.inf' Finset.univ_nonempty
      (fun s : S => κ.k (Sum.inr (Sum.inr s))) := ⟨_, rfl⟩
  have hκo : 0 < κo := by
    rw [hκo_def]; exact (Finset.lt_inf'_iff _).mpr fun s _ => κ.positive _
  have hκo_le : ∀ s, κo ≤ κ.k (Sum.inr (Sum.inr s)) := fun s => by
    rw [hκo_def]; exact Finset.inf'_le _ (Finset.mem_univ s)
  obtain ⟨Kin, hKin⟩ : ∃ Kin, Kin = ∑ s : S, κ.k (Sum.inr (Sum.inl s)) := ⟨_, rfl⟩
  obtain ⟨Kout, hKout⟩ : ∃ Kout, Kout = ∑ s : S, κ.k (Sum.inr (Sum.inr s)) := ⟨_, rfl⟩
  have hKin0 : 0 ≤ Kin := by rw [hKin]; exact Finset.sum_nonneg fun s _ => (κ.positive _).le
  have hKout0 : 0 ≤ Kout := by rw [hKout]; exact Finset.sum_nonneg fun s _ => (κ.positive _).le
  refine ⟨κo, Kin, Kout, hκo, hKin0, hKout0, ?_, ?_, hKin, hKout, fun n => ?_⟩
  · intro s; rw [hKin]
    exact Finset.single_le_sum (fun t _ => (κ.positive (Sum.inr (Sum.inl t))).le) (Finset.mem_univ s)
  · intro s; rw [hKout]
    exact Finset.single_le_sum (fun t _ => (κ.positive (Sum.inr (Sum.inr t))).le) (Finset.mem_univ s)
  have hX1 := one_le_Xmax n
  have hX0 : 0 < Xmax n := by linarith
  -- inflows
  have hin : ∑ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inl s)) *
      (countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inl s))) - countU n) ≤
      Kin * Real.log (Xmax n) + Kin * 4 := by
    rw [hKin, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [fullyOpen_rate_inflow]
    have := mul_le_mul_of_nonneg_left (inflow_step N n s) (κ.positive (Sum.inr (Sum.inl s))).le
    linarith
  -- outflows: each term is at most `κ n (4 − log n)`; the largest coordinate gives `−κo X log X`
  have hout_term : ∀ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inr s)) *
      (countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s))) - countU n) ≤
      κ.k (Sum.inr (Sum.inr s)) * ((n s : ℝ) * (4 - Real.log (zc n s))) := by
    intro s
    rw [fullyOpen_rate_outflow]
    rcases Nat.eq_zero_or_pos (n s) with h0 | hpos
    · rw [h0]; simp
    · have hstep := outflow_step N n s hpos
      have hz : zc n s = n s := by unfold zc; exact max_eq_left (by exact_mod_cast hpos)
      rw [hz]
      have hk := κ.positive (Sum.inr (Sum.inr s))
      have hn0 : (0 : ℝ) ≤ n s := Nat.cast_nonneg _
      have := mul_le_mul_of_nonneg_left hstep (mul_nonneg hk.le hn0)
      nlinarith [this]
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty n
  have hout : ∑ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inr s)) *
      (countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s))) - countU n) ≤
      4 * Kout * Xmax n - κo * (Xmax n * Real.log (Xmax n)) := by
    calc _ ≤ ∑ s, κ.k (Sum.inr (Sum.inr s)) * ((n s : ℝ) * (4 - Real.log (zc n s))) :=
          Finset.sum_le_sum fun s _ => hout_term s
      _ = ∑ s, κ.k (Sum.inr (Sum.inr s)) * (4 * (n s : ℝ)) -
          ∑ s, κ.k (Sum.inr (Sum.inr s)) * ((n s : ℝ) * Real.log (zc n s)) := by
          rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => by ring
      _ ≤ 4 * Kout * Xmax n - κo * (Xmax n * Real.log (Xmax n)) := by
          have h1 : ∑ s, κ.k (Sum.inr (Sum.inr s)) * (4 * (n s : ℝ)) ≤ Kout * (4 * Xmax n) := by
            rw [hKout, Finset.sum_mul]
            refine Finset.sum_le_sum fun s _ => ?_
            have hns : (n s : ℝ) ≤ Xmax n := (le_max_left _ _).trans (zc_le_Xmax n s)
            have hk := κ.positive (Sum.inr (Sum.inr s))
            nlinarith
          have h2 : κo * (Xmax n * Real.log (Xmax n)) ≤
              ∑ s, κ.k (Sum.inr (Sum.inr s)) * ((n s : ℝ) * Real.log (zc n s)) := by
            have hnonneg : ∀ s, 0 ≤ κ.k (Sum.inr (Sum.inr s)) * ((n s : ℝ) * Real.log (zc n s)) :=
              fun s => mul_nonneg (κ.positive _).le
                (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (one_le_zc n s)))
            have hsingle := Finset.single_le_sum (fun s _ => hnonneg s) (Finset.mem_univ p)
            -- the largest coordinate
            rcases Nat.eq_zero_or_pos (n p) with h0 | hpos
            · have hX : Xmax n = 1 := by
                unfold Xmax; rw [hp, h0]; simp
              rw [hX, Real.log_one, mul_zero, mul_zero]
              exact Finset.sum_nonneg fun s _ => hnonneg s
            · have hX : Xmax n = n p := by
                unfold Xmax; rw [hp]; exact max_eq_left (by exact_mod_cast hpos)
              have hz : zc n p = n p := by unfold zc; exact max_eq_left (by exact_mod_cast hpos)
              have hl : 0 ≤ (n p : ℝ) * Real.log (n p) :=
                mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hpos))
              rw [hX]
              rw [hz] at hsingle
              calc κo * ((n p : ℝ) * Real.log (n p))
                  ≤ κ.k (Sum.inr (Sum.inr p)) * ((n p : ℝ) * Real.log (n p)) :=
                    mul_le_mul_of_nonneg_right (hκo_le p) hl
                _ ≤ _ := hsingle
          linarith
  linarith [hin, hout]

/-! ## The drift of the weighted entropy `U_c` -/

/-- The linear part `ℓ_c(n) = ∑ₛ nₛ log cₛ`; the weighted entropy is `countU − ℓ_c`. -/
noncomputable def ellC (c : S → ℝ) (n : S → ℕ) : ℝ := ∑ s, (n s : ℝ) * Real.log (c s)

theorem ellC_core_step (c : S → ℝ) (n : S → ℕ) (r : N.R) :
    N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) *
      (ellC c (N.fullyOpen.jumpNextCount n (Sum.inl r)) - ellC c n) =
    N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) * shift N c r := by
  by_cases hen : ∀ s, (N.reaction r).source s ≤ n s
  · congr 1
    simp only [next_inl, ellC, shift]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Nat.cast_add, Nat.cast_sub (hen s)]
    ring
  · push_neg at hen
    obtain ⟨s, hs⟩ := hen
    rw [rate_eq_zero_of_disabled N.fullyOpen κ n (Sum.inl r) s (by rw [source_inl]; exact hs)]
    simp

theorem ellC_inflow_step (c : S → ℝ) (n : S → ℕ) (s : S) :
    ellC c (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inl s))) - ellC c n = Real.log (c s) := by
  simp only [next_inflow, ellC]
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single s]
  · rw [if_pos rfl]; push_cast; ring
  · intro t _ ht; rw [if_neg ht, add_zero, sub_self]
  · intro h; exact absurd (Finset.mem_univ s) h

theorem ellC_outflow_step (c : S → ℝ) (n : S → ℕ) (s : S) (hs : 1 ≤ n s) :
    ellC c (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s))) - ellC c n = -Real.log (c s) := by
  simp only [next_outflow, ellC]
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single s]
  · rw [if_pos rfl, Nat.cast_sub hs]; push_cast; ring
  · intro t _ ht; rw [if_neg ht, Nat.sub_zero, sub_self]
  · intro h; exact absurd (Finset.mem_univ s) h

/-- **The drift of `U_c = countU − ℓ_c`**: core terms `termC`, the flow part of the drift of
`countU`, and the linear corrections of the flows. -/
theorem driftC_eq (c : S → ℝ) (n : S → ℕ) :
    (N.fullyOpen.jumpSystem κ).drift (fun m => countU m - ellC c m) n =
      ∑ r, termC N κ c n r +
      (∑ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inl s)) *
        (countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inl s))) - countU n) +
      ∑ s, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inr s)) *
        (countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s))) - countU n)) -
      ∑ s, κ.k (Sum.inr (Sum.inl s)) * Real.log (c s) +
      ∑ s, κ.k (Sum.inr (Sum.inr s)) * ((n s : ℝ) * Real.log (c s)) := by
  have e : (N.fullyOpen.jumpSystem κ).drift (fun m => countU m - ellC c m) n =
      ∑ r : N.R ⊕ S ⊕ S, N.fullyOpen.stochasticMassActionRate κ n r *
        ((countU (N.fullyOpen.jumpNextCount n r) - ellC c (N.fullyOpen.jumpNextCount n r)) -
          (countU n - ellC c n)) := rfl
  rw [e, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hcore : ∀ r : N.R, N.fullyOpen.stochasticMassActionRate κ n (Sum.inl r) *
      ((countU (N.fullyOpen.jumpNextCount n (Sum.inl r)) -
        ellC c (N.fullyOpen.jumpNextCount n (Sum.inl r))) - (countU n - ellC c n)) =
      termC N κ c n r := by
    intro r
    unfold termC term
    rw [← ellC_core_step N κ c n r]
    ring
  have hin : ∀ s : S, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inl s)) *
      ((countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inl s))) -
        ellC c (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inl s)))) - (countU n - ellC c n)) =
      N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inl s)) *
        (countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inl s))) - countU n) -
      κ.k (Sum.inr (Sum.inl s)) * Real.log (c s) := by
    intro s
    have h := ellC_inflow_step N c n s
    rw [fullyOpen_rate_inflow]
    linear_combination (-(κ.k (Sum.inr (Sum.inl s)))) * h
  have hout : ∀ s : S, N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inr s)) *
      ((countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s))) -
        ellC c (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s)))) - (countU n - ellC c n)) =
      N.fullyOpen.stochasticMassActionRate κ n (Sum.inr (Sum.inr s)) *
        (countU (N.fullyOpen.jumpNextCount n (Sum.inr (Sum.inr s))) - countU n) +
      κ.k (Sum.inr (Sum.inr s)) * ((n s : ℝ) * Real.log (c s)) := by
    intro s
    rw [fullyOpen_rate_outflow]
    rcases Nat.eq_zero_or_pos (n s) with h0 | hpos
    · rw [h0]; simp
    · have h := ellC_outflow_step N c n s hpos
      linear_combination (-(κ.k (Sum.inr (Sum.inr s)) * (n s : ℝ))) * h
  simp only [hcore, hin, hout, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- **The weighted entropy is a Foster function** as soon as the core part of its drift is
`O(X)`: `L U_c ≤ −X + K`. -/
theorem entropyC_drift_le_of_core [Nonempty S] (c : S → ℝ)
    (hcoreD : ∃ D : ℝ, 0 ≤ D ∧ ∀ n : S → ℕ, ∑ r, termC N κ c n r ≤ D * Xmax n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n,
      (N.fullyOpen.jumpSystem κ).drift (fun m => countU m - ellC c m) n ≤ -Xmax n + K := by
  classical
  obtain ⟨D, hD, hcore⟩ := hcoreD
  obtain ⟨κo, Kin, Kout, hκo, hKin0, hKout0, hKin_le, hKout_le, hKin, hKout, hflows⟩ :=
    flows_le N κ
  obtain ⟨M, hM⟩ : ∃ M, M = ∑ s : S, |Real.log (c s)| := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; exact Finset.sum_nonneg fun s _ => abs_nonneg _
  have hlogM : ∀ s, |Real.log (c s)| ≤ M := fun s => by
    rw [hM]; exact Finset.single_le_sum (fun t _ => abs_nonneg (Real.log (c t))) (Finset.mem_univ s)
  have hc₁ : 0 ≤ D + 4 * Kout + Kout * M := by positivity
  have hc₃ : 0 ≤ 4 * Kin + Kin * M := by positivity
  refine ⟨(D + 4 * Kout + Kout * M + Kin + 1) *
      Real.exp ((D + 4 * Kout + Kout * M + Kin + 1) / κo) + (4 * Kin + Kin * M),
    by positivity, fun n => ?_⟩
  have hX1 := one_le_Xmax n
  rw [driftC_eq]
  -- the linear corrections
  have hin_lin : -(∑ s, κ.k (Sum.inr (Sum.inl s)) * Real.log (c s)) ≤ Kin * M := by
    rw [hKin, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    have hk := κ.positive (Sum.inr (Sum.inl s))
    have h1 := neg_abs_le (Real.log (c s))
    have h2 := mul_le_mul_of_nonneg_left (hlogM s) hk.le
    nlinarith [mul_le_mul_of_nonneg_left h1 hk.le]
  have hout_lin : ∑ s, κ.k (Sum.inr (Sum.inr s)) * ((n s : ℝ) * Real.log (c s)) ≤
      Kout * M * Xmax n := by
    rw [hKout, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun s _ => ?_
    have hk := κ.positive (Sum.inr (Sum.inr s))
    have hns : (n s : ℝ) ≤ Xmax n := (le_max_left _ _).trans (zc_le_Xmax n s)
    have hn0 : (0 : ℝ) ≤ n s := Nat.cast_nonneg _
    have h1 : (n s : ℝ) * Real.log (c s) ≤ Xmax n * M := by
      calc (n s : ℝ) * Real.log (c s) ≤ (n s : ℝ) * |Real.log (c s)| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hn0
        _ ≤ Xmax n * M := mul_le_mul hns (hlogM s) (abs_nonneg _) (by linarith)
    have := mul_le_mul_of_nonneg_left h1 hk.le
    nlinarith [this]
  have hsc := scalar_drift (c₁ := D + 4 * Kout + Kout * M) (c₂ := Kin) (c₃ := 4 * Kin + Kin * M)
    hc₁ hKin0 hκo hX1
  have hcoreX := hcore n
  have hfl := hflows n
  linarith [hcoreX, hfl, hin_lin, hout_lin, hsc]

/-- **The entropy is a Foster function** when some complex has at most one molecule. -/
theorem entropy_drift_le [Nonempty S]
    (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (hcut : CutLeaving N) (y₀ : Complex S) (hy₀ : y₀ ∈ N.complexes) (hsmall : ∑ s, y₀ s ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n, (N.fullyOpen.jumpSystem κ).drift countU n ≤ -Xmax n + K :=
  entropy_drift_le_of_core N κ (core_part_le N κ hbin hcut y₀ hy₀ hsmall)

/-! ## Ergodicity -/

theorem countU_nonneg (n : S → ℕ) : 0 ≤ countU n :=
  Finset.sum_nonneg fun s _ => uE_nonneg (Nat.cast_nonneg _)

theorem countU_finite (R : ℝ) : {n : S → ℕ | countU n ≤ R}.Finite := by
  refine (finite_linearObservable_le (S := S) (fun _ => (1 : ℝ)) (fun _ => one_pos)
    (2 * R + 2 * Fintype.card S)).subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  unfold linearObservable
  have h : ∀ s, (n s : ℝ) / 2 - 1 ≤ uE (n s) := fun s => uE_ge (Nat.cast_nonneg _)
  have hsum : ∑ s, ((n s : ℝ) / 2 - 1) ≤ countU n := Finset.sum_le_sum fun s _ => h s
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Finset.sum_div] at hsum
  simp only [one_mul]
  linarith

theorem Xmax_finite (R : ℝ) : {n : S → ℕ | Xmax n ≤ R}.Finite := by
  refine (finite_linearObservable_le (S := S) (fun _ => (1 : ℝ)) (fun _ => one_pos)
    (Fintype.card S * R)).subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  unfold linearObservable
  simp only [one_mul]
  calc ∑ s, (n s : ℝ) ≤ ∑ _s : S, Xmax n :=
        Finset.sum_le_sum fun s _ => (le_max_left _ _).trans (zc_le_Xmax n s)
    _ = Fintype.card S * Xmax n := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ Fintype.card S * R := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)

/-- **Ergodicity with the entropy Lyapunov function**, given the `O(X)` bound on the core part. -/
theorem fullyOpen_ergodic_of_core [Nonempty S]
    (hcoreD : ∃ D : ℝ, 0 ≤ D ∧ ∀ n : S → ℕ, ∑ r, term N κ n r ≤ D * Xmax n) :
    ∃ π : (S → ℕ) → ℝ, (∀ m, 0 < π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * N.fullyOpen.transition κ t x m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |N.fullyOpen.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      ∀ μ : (S → ℕ) → ℝ, (∀ m, 0 ≤ μ m) → HasSum μ 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' x, μ x * N.fullyOpen.transition κ t x m = μ m) → μ = π := by
  classical
  obtain ⟨K, hK, hdr⟩ := entropy_drift_le_of_core N κ hcoreD
  have hf : ∀ n : S → ℕ, 0 ≤ Xmax n := fun n => by linarith [one_le_Xmax n]
  have hstoch : ∀ t, 0 ≤ t → ∀ n, HasSum (fun m => (N.fullyOpen.jumpSystem κ).Pmin t n m) 1 :=
    fun t ht n => (N.fullyOpen.jumpSystem κ).hasSum_Pmin_one_of_drift_affine countU
      countU_nonneg countU_finite le_rfl hK
      (fun m => by have := hdr m; have := hf m; have := countU_nonneg m; linarith) ht n
  obtain ⟨π, hπ0, hπ1, hinv, -, hpos, hconv, huniq⟩ :=
    (N.fullyOpen.jumpSystem κ).foster_lyapunov_ergodic countU Xmax countU_nonneg hf
      Xmax_finite hK hdr hstoch (E := Set.univ)
      (fun _ _ _ _ => Set.mem_univ _) (fun a _ b _ => N.fullyOpen_reachPos κ a b)
      (Set.mem_univ (0 : S → ℕ))
  exact ⟨π, fun m => hpos m (Set.mem_univ m), hπ1, hinv, fun n => hconv n (Set.mem_univ n),
    fun μ hμ0 hμ1 hμinv => huniq μ hμ0 (fun m hm => absurd (Set.mem_univ m) hm) hμ1 hμinv⟩

/-! ## Ergodicity with the weighted entropy -/

/-- The relative entropy is nonnegative: `u(x) − x log c + c − 1 = x log(x/c) − x + c ≥ 0`. -/
theorem uE_sub_mul_log_nonneg {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    0 ≤ uE x - x * Real.log c + c - 1 := by
  have h := uE_sub_ge (s := x) (t := c) hc hx
  unfold uE at h ⊢
  nlinarith [h]

/-- Coercivity of the relative entropy: `u(x) − x log c + c − 1 ≥ x − (e − 1) c`. -/
theorem uE_sub_mul_log_ge {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    x - (Real.exp 1 - 1) * c ≤ uE x - x * Real.log c + c - 1 := by
  have ht : 0 < Real.exp 1 * c := mul_pos (Real.exp_pos 1) hc
  have h := uE_sub_ge (s := x) (t := Real.exp 1 * c) ht hx
  have hlog : Real.log (Real.exp 1 * c) = 1 + Real.log c := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hc.ne', Real.log_exp]
  unfold uE at h ⊢
  rw [hlog] at h
  nlinarith [h]

/-- **The weighted entropy, shifted to be nonnegative**:
`U_c(n) = ∑ₛ (u(nₛ) − nₛ log cₛ + cₛ − 1)`. -/
noncomputable def countUc (c : S → ℝ) (n : S → ℕ) : ℝ :=
  ∑ s, (uE (n s) - (n s : ℝ) * Real.log (c s) + c s - 1)

theorem countUc_eq (c : S → ℝ) (n : S → ℕ) :
    countUc c n = countU n - ellC c n + ∑ s, (c s - 1) := by
  unfold countUc countU ellC
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

theorem countUc_nonneg {c : S → ℝ} (hc : ∀ s, 0 < c s) (n : S → ℕ) : 0 ≤ countUc c n :=
  Finset.sum_nonneg fun s _ => uE_sub_mul_log_nonneg (hc s) (Nat.cast_nonneg _)

theorem countUc_finite {c : S → ℝ} (hc : ∀ s, 0 < c s) (R : ℝ) :
    {n : S → ℕ | countUc c n ≤ R}.Finite := by
  refine (finite_linearObservable_le (S := S) (fun _ => (1 : ℝ)) (fun _ => one_pos)
    (R + ∑ s, (Real.exp 1 - 1) * c s)).subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  unfold linearObservable
  have hsum : ∑ s, ((n s : ℝ) - (Real.exp 1 - 1) * c s) ≤ countUc c n :=
    Finset.sum_le_sum fun s _ => uE_sub_mul_log_ge (hc s) (Nat.cast_nonneg _)
  rw [Finset.sum_sub_distrib] at hsum
  simp only [one_mul]
  linarith

theorem drift_countUc (c : S → ℝ) (n : S → ℕ) :
    (N.fullyOpen.jumpSystem κ).drift (countUc c) n =
      (N.fullyOpen.jumpSystem κ).drift (fun m => countU m - ellC c m) n := by
  have e1 : (N.fullyOpen.jumpSystem κ).drift (countUc c) n =
      ∑ r : N.R ⊕ S ⊕ S, N.fullyOpen.stochasticMassActionRate κ n r *
        (countUc c (N.fullyOpen.jumpNextCount n r) - countUc c n) := rfl
  have e2 : (N.fullyOpen.jumpSystem κ).drift (fun m => countU m - ellC c m) n =
      ∑ r : N.R ⊕ S ⊕ S, N.fullyOpen.stochasticMassActionRate κ n r *
        ((countU (N.fullyOpen.jumpNextCount n r) - ellC c (N.fullyOpen.jumpNextCount n r)) -
          (countU n - ellC c n)) := rfl
  rw [e1, e2]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [countUc_eq, countUc_eq]
  ring

/-- **Ergodicity with the weighted entropy**, given the `O(X)` bound on its core part. -/
theorem fullyOpen_ergodic_of_coreC [Nonempty S] (c : S → ℝ) (hc : ∀ s, 0 < c s)
    (hcoreD : ∃ D : ℝ, 0 ≤ D ∧ ∀ n : S → ℕ, ∑ r, termC N κ c n r ≤ D * Xmax n) :
    ∃ π : (S → ℕ) → ℝ, (∀ m, 0 < π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * N.fullyOpen.transition κ t x m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |N.fullyOpen.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      ∀ μ : (S → ℕ) → ℝ, (∀ m, 0 ≤ μ m) → HasSum μ 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' x, μ x * N.fullyOpen.transition κ t x m = μ m) → μ = π := by
  classical
  obtain ⟨K, hK, hdr0⟩ := entropyC_drift_le_of_core N κ c hcoreD
  have hdr : ∀ n, (N.fullyOpen.jumpSystem κ).drift (countUc c) n ≤ -Xmax n + K := fun n => by
    rw [drift_countUc]; exact hdr0 n
  have hf : ∀ n : S → ℕ, 0 ≤ Xmax n := fun n => by linarith [one_le_Xmax n]
  have hstoch : ∀ t, 0 ≤ t → ∀ n, HasSum (fun m => (N.fullyOpen.jumpSystem κ).Pmin t n m) 1 :=
    fun t ht n => (N.fullyOpen.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (countUc c)
      (countUc_nonneg hc) (countUc_finite hc) le_rfl hK
      (fun m => by have := hdr m; have := hf m; have := countUc_nonneg hc m; linarith) ht n
  obtain ⟨π, hπ0, hπ1, hinv, -, hpos, hconv, huniq⟩ :=
    (N.fullyOpen.jumpSystem κ).foster_lyapunov_ergodic (countUc c) Xmax (countUc_nonneg hc) hf
      Xmax_finite hK hdr hstoch (E := Set.univ)
      (fun _ _ _ _ => Set.mem_univ _) (fun a _ b _ => N.fullyOpen_reachPos κ a b)
      (Set.mem_univ (0 : S → ℕ))
  exact ⟨π, fun m => hpos m (Set.mem_univ m), hπ1, hinv, fun n => hconv n (Set.mem_univ n),
    fun μ hμ0 hμ1 hμinv => huniq μ hμ0 (fun m hm => absurd (Set.mem_univ m) hm) hμ1 hμinv⟩

/-! ## The mixed case: small classes plus a complex-balanced part -/

theorem monomial_pos {c : S → ℝ} (hc : ∀ s, 0 < c s) (y : Complex S) :
    0 < y.massActionMonomial c := by
  unfold Complex.massActionMonomial
  exact Finset.prod_pos fun s _ => pow_pos (hc s) _

theorem log_monomial {c : S → ℝ} (hc : ∀ s, 0 < c s) (y : Complex S) :
    Real.log (y.massActionMonomial c) = ∑ s, (y s : ℝ) * Real.log (c s) := by
  unfold Complex.massActionMonomial
  rw [Real.log_prod fun s _ => (pow_pos (hc s) _).ne']
  exact Finset.sum_congr rfl fun s _ => Real.log_pow _ _

theorem exp_neg_shift {c : S → ℝ} (hc : ∀ s, 0 < c s) (r : N.R) :
    Real.exp (-shift N c r) =
      (N.reaction r).source.massActionMonomial c / (N.reaction r).target.massActionMonomial c := by
  have h : -shift N c r = Real.log ((N.reaction r).source.massActionMonomial c) -
      Real.log ((N.reaction r).target.massActionMonomial c) := by
    rw [log_monomial hc, log_monomial hc]
    unfold shift
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [h, Real.exp_sub, Real.exp_log (monomial_pos hc _), Real.exp_log (monomial_pos hc _)]

/-- `κ ζ_y (1 − e^{L^c}) = κ (w_y u_y − w_y u_{y'})` with `w = c^·` and `u_y = ζ_y / c^y`. -/
theorem flux_term_eq {c : S → ℝ} (hc : ∀ s, 0 < c s) (n : S → ℕ) (r : N.R) :
    κ.k (Sum.inl r) * zeta (N.reaction r).source n * (1 - Real.exp (logRatioC N c n r)) =
      κ.k (Sum.inl r) * ((N.reaction r).source.massActionMonomial c *
        (zeta (N.reaction r).source n / (N.reaction r).source.massActionMonomial c) -
        (N.reaction r).source.massActionMonomial c *
        (zeta (N.reaction r).target n / (N.reaction r).target.massActionMonomial c)) := by
  have hz := zeta_pos (N.reaction r).source n
  have hz' := zeta_pos (N.reaction r).target n
  have hw := monomial_pos hc (N.reaction r).source
  have hw' := monomial_pos hc (N.reaction r).target
  have hexp : Real.exp (logRatioC N c n r) =
      zeta (N.reaction r).target n / zeta (N.reaction r).source n *
        ((N.reaction r).source.massActionMonomial c /
          (N.reaction r).target.massActionMonomial c) := by
    unfold logRatioC
    rw [show logZeta (N.reaction r).target n - logZeta (N.reaction r).source n - shift N c r =
        (logZeta (N.reaction r).target n - logZeta (N.reaction r).source n) + -shift N c r by ring,
      Real.exp_add, Real.exp_sub, ← log_zeta, ← log_zeta, Real.exp_log hz', Real.exp_log hz,
      exp_neg_shift N hc]
  rw [hexp]
  have hzne := hz.ne'
  have hwne := hw.ne'
  have hw'ne := hw'.ne'
  first | (field_simp; ring) | field_simp

/-- **The complex-balance identity over a set of reactions.** -/
theorem sum_balance_on (Rb : Finset N.R) (w u : Complex S → ℝ)
    (hbal : ∀ y : Complex S,
      ∑ r ∈ Rb.filter (fun r => (N.reaction r).source = y), κ.k (Sum.inl r) * w y =
        ∑ r ∈ Rb.filter (fun r => (N.reaction r).target = y),
          κ.k (Sum.inl r) * w (N.reaction r).source) :
    ∑ r ∈ Rb, κ.k (Sum.inl r) * (w (N.reaction r).source * u (N.reaction r).source -
      w (N.reaction r).source * u (N.reaction r).target) = 0 := by
  classical
  have e1 : ∑ r ∈ Rb, κ.k (Sum.inl r) * (w (N.reaction r).source * u (N.reaction r).source) =
      ∑ y ∈ complexesOn N Rb, u y * ∑ r ∈ Rb.filter (fun r => (N.reaction r).source = y),
        κ.k (Sum.inl r) * w y := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun r => (N.reaction r).source)
      (t := complexesOn N Rb) (by intro r hr; exact source_mem_complexesOn N hr)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [(Finset.mem_filter.mp hr).2]
    ring
  have e2 : ∑ r ∈ Rb, κ.k (Sum.inl r) * (w (N.reaction r).source * u (N.reaction r).target) =
      ∑ y ∈ complexesOn N Rb, u y * ∑ r ∈ Rb.filter (fun r => (N.reaction r).target = y),
        κ.k (Sum.inl r) * w (N.reaction r).source := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun r => (N.reaction r).target)
      (t := complexesOn N Rb) (by intro r hr; exact target_mem_complexesOn N hr)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [(Finset.mem_filter.mp hr).2]
    ring
  have split : ∑ r ∈ Rb, κ.k (Sum.inl r) * (w (N.reaction r).source * u (N.reaction r).source -
      w (N.reaction r).source * u (N.reaction r).target) =
      ∑ r ∈ Rb, κ.k (Sum.inl r) * (w (N.reaction r).source * u (N.reaction r).source) -
      ∑ r ∈ Rb, κ.k (Sum.inl r) * (w (N.reaction r).source * u (N.reaction r).target) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [split, e1, e2, ← Finset.sum_sub_distrib]
  exact Finset.sum_eq_zero fun y _ => by rw [← mul_sub, hbal y, sub_self, mul_zero]

/-- **The mixed case.**  Let a binary network have its reactions split by `cls : N.R → Option ι`
into small classes `some i` (each strongly connected, with a complex of at most one molecule) and a
part `none` that is complex balanced at a positive `c` for its own rates (`hbal`).  Then
`N.fullyOpen` is ergodic.  Proof: the weighted entropy `U_c`; on the small classes the band
argument (`coreC_part_le_on`), on the complex-balanced part the per-reaction bound `fC_le` summed
with the complex-balance identity (`sum_balance_on`, `flux_term_eq`). -/
theorem fullyOpen_ergodic_of_mixed [Nonempty S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (c : S → ℝ) (hc : ∀ s, 0 < c s) (cls : N.R → Option ι)
    (hsmall : ∀ i, CutLeavingOn N (Finset.univ.filter (fun r => cls r = some i)) ∧
      ∃ y₀ ∈ complexesOn N (Finset.univ.filter (fun r => cls r = some i)), ∑ s, y₀ s ≤ 1)
    (hbal : ∀ y : Complex S,
      ∑ r ∈ (Finset.univ.filter (fun r => cls r = none)).filter
          (fun r => (N.reaction r).source = y), κ.k (Sum.inl r) * y.massActionMonomial c =
        ∑ r ∈ (Finset.univ.filter (fun r => cls r = none)).filter
          (fun r => (N.reaction r).target = y),
          κ.k (Sum.inl r) * (N.reaction r).source.massActionMonomial c) :
    ∃ π : (S → ℕ) → ℝ, (∀ m, 0 < π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * N.fullyOpen.transition κ t x m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |N.fullyOpen.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      ∀ μ : (S → ℕ) → ℝ, (∀ m, 0 ≤ μ m) → HasSum μ 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' x, μ x * N.fullyOpen.transition κ t x m = μ m) → μ = π := by
  classical
  refine fullyOpen_ergodic_of_coreC N κ c hc ?_
  -- the small classes
  have hD : ∀ i, ∃ D : ℝ, 0 ≤ D ∧ ∀ n : S → ℕ,
      ∑ r ∈ Finset.univ.filter (fun r => cls r = some i), termC N κ c n r ≤ D * Xmax n := by
    intro i
    obtain ⟨hcut, y₀, hy₀, hs⟩ := hsmall i
    exact coreC_part_le_on N κ hbin c _ hcut y₀ hy₀ hs
  choose D hD0 hDle using hD
  -- the per-reaction constants
  have hC := fun r => fC_le N κ hbin c r
  choose C hC0 hCle using hC
  refine ⟨∑ i, D i + ∑ r, C r, add_nonneg (Finset.sum_nonneg fun i _ => hD0 i)
    (Finset.sum_nonneg fun r _ => hC0 r), fun n => ?_⟩
  have hX1 := one_le_Xmax n
  -- split by classes
  rw [← Finset.sum_fiberwise Finset.univ cls (termC N κ c n), Fintype.sum_option]
  -- the complex-balanced part
  obtain ⟨Rb, hRb⟩ : ∃ Rb, Rb = Finset.univ.filter (fun r => cls r = none) := ⟨_, rfl⟩
  rw [← hRb] at hbal ⊢
  have hzero : ∑ r ∈ Rb, κ.k (Sum.inl r) * zeta (N.reaction r).source n *
      (1 - Real.exp (logRatioC N c n r)) = 0 := by
    rw [Finset.sum_congr (rfl : Rb = Rb) fun r _ => flux_term_eq N κ hc n r]
    exact sum_balance_on N κ Rb (fun y => y.massActionMonomial c)
      (fun y => zeta y n / y.massActionMonomial c) hbal
  have hbig : ∑ r ∈ Rb, termC N κ c n r ≤ (∑ r, C r) * Xmax n := by
    have h1 : ∑ r ∈ Rb, termC N κ c n r = ∑ r ∈ Rb, (termC N κ c n r +
        κ.k (Sum.inl r) * zeta (N.reaction r).source n * (1 - Real.exp (logRatioC N c n r))) := by
      rw [Finset.sum_add_distrib, hzero, add_zero]
    rw [h1, Finset.sum_mul]
    calc ∑ r ∈ Rb, (termC N κ c n r +
          κ.k (Sum.inl r) * zeta (N.reaction r).source n * (1 - Real.exp (logRatioC N c n r)))
        ≤ ∑ r ∈ Rb, C r * Xmax n := Finset.sum_le_sum fun r _ => hCle r n
      _ ≤ ∑ r, C r * Xmax n := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun r _ _ => mul_nonneg (hC0 r) (by linarith))
  have hsm : ∑ i, ∑ r ∈ Finset.univ.filter (fun r => cls r = some i), termC N κ c n r ≤
      (∑ i, D i) * Xmax n := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hDle i n
  rw [add_mul]
  linarith [hbig, hsm]

/-- **Ergodicity with the entropy Lyapunov function** (some complex has at most one molecule). -/
theorem fullyOpen_ergodic_of_small_complex [Nonempty S]
    (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (hcut : CutLeaving N) (y₀ : Complex S) (hy₀ : y₀ ∈ N.complexes) (hsmall : ∑ s, y₀ s ≤ 1) :
    ∃ π : (S → ℕ) → ℝ, (∀ m, 0 < π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * N.fullyOpen.transition κ t x m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |N.fullyOpen.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      ∀ μ : (S → ℕ) → ℝ, (∀ m, 0 ≤ μ m) → HasSum μ 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' x, μ x * N.fullyOpen.transition κ t x m = μ m) → μ = π :=
  fullyOpen_ergodic_of_core N κ (core_part_le N κ hbin hcut y₀ hy₀ hsmall)

/-- **Several linkage classes, each with a small complex.**  If the reactions of a binary
network are partitioned into classes, each with a strongly connected complex graph containing a
complex with at most one molecule, then `N.fullyOpen` is ergodic for every choice of rates.  (For
weakly reversible networks the classes are the linkage classes.) -/
theorem fullyOpen_ergodic_of_classes [Nonempty S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (cls : N.R → ι)
    (hcls : ∀ c, CutLeavingOn N (Finset.univ.filter (fun r => cls r = c)) ∧
      ∃ y₀ ∈ complexesOn N (Finset.univ.filter (fun r => cls r = c)), ∑ s, y₀ s ≤ 1) :
    ∃ π : (S → ℕ) → ℝ, (∀ m, 0 < π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * N.fullyOpen.transition κ t x m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |N.fullyOpen.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      ∀ μ : (S → ℕ) → ℝ, (∀ m, 0 ≤ μ m) → HasSum μ 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' x, μ x * N.fullyOpen.transition κ t x m = μ m) → μ = π :=
  fullyOpen_ergodic_of_core N κ (core_part_le_of_classes N κ hbin cls hcls)

/-- **Anderson–Kim, Theorem 2.1** (binary network with strongly connected complex graph, all
inflows and outflows): ergodic for every choice of rate constants.  If some complex has at most
one molecule the entropy is a Foster function (`fullyOpen_ergodic_of_small_complex`); otherwise
every complex has two molecules, every reaction conserves the molecule count, and the total
count is a Foster function (`CRNT.Network.fullyOpen_ergodic`). -/
theorem binaryStronglyConnected_fullyOpen_ergodic [Nonempty S]
    (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (hcut : CutLeaving N) :
    ∃ π : (S → ℕ) → ℝ, (∀ m, 0 < π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * N.fullyOpen.transition κ t x m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |N.fullyOpen.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      ∀ μ : (S → ℕ) → ℝ, (∀ m, 0 ≤ μ m) → HasSum μ 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' x, μ x * N.fullyOpen.transition κ t x m = μ m) → μ = π := by
  classical
  by_cases hsmall : ∃ y₀ ∈ N.complexes, ∑ s, y₀ s ≤ 1
  · obtain ⟨y₀, hy₀, hs⟩ := hsmall
    exact fullyOpen_ergodic_of_small_complex N κ hbin hcut y₀ hy₀ hs
  · -- every complex has exactly two molecules
    have htwo : ∀ y ∈ N.complexes, ∑ s, y s = 2 := by
      intro y hy
      have h1 : ¬ ∑ s, y s ≤ 1 := fun h => hsmall ⟨y, hy, h⟩
      have h2 : ∑ s, y s ≤ 2 := by
        unfold Network.complexes at hy
        rcases Finset.mem_union.mp hy with h | h
        · obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp h; exact (hbin r).1
        · obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp h; exact (hbin r).2
      omega
    exact N.fullyOpen_ergodic κ fun r =>
      (htwo _ (N.target_mem_complexes r)).le.trans (htwo _ (N.source_mem_complexes r)).ge

/-! ## Weak reversibility with one linkage class -/

/-- A directed path from inside `T` to outside `T` uses a reaction leaving `T`. -/
theorem exists_reaction_leaving {N : Network S} {T : Finset (Complex S)} {c d : Complex S}
    (h : N.Reaches c d) (hc : c ∈ T) (hd : d ∉ T) :
    ∃ r : N.R, (N.reaction r).source ∈ T ∧ (N.reaction r).target ∉ T := by
  revert hd
  induction h with
  | refl => intro hd; exact absurd hc hd
  | @tail b d' _ hstep ih =>
      intro hd
      obtain ⟨r, hs, ht⟩ := hstep
      by_cases hb : b ∈ T
      · exact ⟨r, by rw [hs]; exact hb, by rw [ht]; exact hd⟩
      · exact ih hb

/-- **A weakly reversible network with one linkage class has a strongly connected complex
graph.** -/
theorem cutLeaving_of_weaklyReversible {N : Network S} (hwr : N.WeaklyReversible)
    (hlink : ∀ c ∈ N.complexes, ∀ d ∈ N.complexes, N.Linked c d) : CutLeaving N := by
  intro T hT hne hout
  obtain ⟨y, hy⟩ := hne
  obtain ⟨y', hy'C, hy'T⟩ := hout
  exact exists_reaction_leaving (hwr.reaches_of_linked (hlink y (hT hy) y' hy'C)) hy hy'T

/-- **Anderson–Kim, Theorem 2.1, in their hypotheses**: a binary weakly reversible network with a
single linkage class, with every inflow and outflow added, is ergodic for every choice of rates. -/
theorem andersonKim_fullyOpen_ergodic [Nonempty S]
    (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (hwr : N.WeaklyReversible) (hlink : ∀ c ∈ N.complexes, ∀ d ∈ N.complexes, N.Linked c d) :
    ∃ π : (S → ℕ) → ℝ, (∀ m, 0 < π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * N.fullyOpen.transition κ t x m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |N.fullyOpen.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      ∀ μ : (S → ℕ) → ℝ, (∀ m, 0 ≤ μ m) → HasSum μ 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' x, μ x * N.fullyOpen.transition κ t x m = μ m) → μ = π :=
  binaryStronglyConnected_fullyOpen_ergodic N κ hbin (cutLeaving_of_weaklyReversible hwr hlink)

end BinaryFlows
end CRNT

#print axioms CRNT.BinaryFlows.exists_empty_band
#print axioms CRNT.BinaryFlows.core_part_le
#print axioms CRNT.BinaryFlows.coreC_part_le_on
#print axioms CRNT.BinaryFlows.uE_step_fine
#print axioms CRNT.BinaryFlows.fC_le
#print axioms CRNT.BinaryFlows.fullyOpen_ergodic_of_mixed
#print axioms CRNT.BinaryFlows.entropyC_drift_le_of_core
#print axioms CRNT.BinaryFlows.fullyOpen_ergodic_of_coreC
#print axioms CRNT.BinaryFlows.fullyOpen_ergodic_of_classes
#print axioms CRNT.BinaryFlows.entropy_drift_le
#print axioms CRNT.BinaryFlows.binaryStronglyConnected_fullyOpen_ergodic
#print axioms CRNT.BinaryFlows.andersonKim_fullyOpen_ergodic

import CRNT.Geometry.EndotacticGlobal
import CRNT.Stochastic.EndotacticPositiveRecurrence
import CRNT.Stochastic.HarrisTheorem
import CRNT.Stochastic.EndotacticTierPositiveRecurrence

set_option maxHeartbeats 1000000

/-!
# The entropy function is not a Foster function for binary strongly endotactic networks with
# outflows

This module records, for leaf **P7** of `docs/field-map.md`, two facts about the
Anderson–Cappelletti–Kim–Nguyen paper (*Tier structure of strongly endotactic reaction networks*,
Stoch. Proc. Appl. 130 (2020); arXiv:1808.05328) that change what "the ACK theorem" can mean.

## 1. Strong endotacticity alone does not give positive recurrence

ACK show (their Examples 3.1 and 3.2) that a strongly endotactic network can be **transient**
(`0 → 2A + B → 4A + 4B → A`) and even **explosive** (`0 → 2A → 4A + B → 6A + 4B → 3A`) for every
choice of rate constants; Agazzi–Mattingly found other examples independently.  So the statement
"every strongly endotactic stochastic mass-action system is positive recurrent", which the field
map listed as the remaining gap of P7, is false.  What ACK prove instead (their Theorem 7.2 and
Corollary 7.1) is positive recurrence for

> a **binary** strongly endotactic network `N`, to which **every outflow** `S → 0` (and any set of
> inflows `0 → S`) is added.

## 2. The Lyapunov function of that proof does not work

ACK prove Theorem 7.2 by showing that the entropy function (their (4.6))

`U(x) = 1 + ∑ᵢ (xᵢ (log xᵢ − 1) + 1)`

satisfies `(LU)(x) < −1` outside a finite set.  This module shows that this step fails, on the
smallest example:

* the core network `N = {2A → 2B, 2B → 2A}` is **binary** (`core_binary`) and **strongly
  endotactic** (`core_stronglyEndotacticStd`);
* the full network `net` adds both outflows `A → 0`, `B → 0` and both inflows `0 → A`, `0 → B`, so
  it is exactly of the form of ACK's Corollary 7.1;
* for the rate constants `κ₀ = (1, 100, 1, 1, 1, 1)` the entropy drift at the counts `(2m, m)` is at
  least `m` (`drift_countEntropy_ge`), so **no finite set `K` has `LU ≤ −1` off `K`**
  (`countEntropy_not_foster`).

The mechanism is that `N` is not *transversal* along `(2m, m)`: both reactions of `N` keep the
ratio `x_A / x_B` bounded, so the tier argument (ACK's Lemma 4.5, which needs a tier sequence
transversal for `N`) gives no strictly descending reaction, and the bounded log-ratio
`log (x_B² / x_A²) = −2 log 2` multiplies a *quadratic* propensity, which the outflows (linear
propensities with logarithmic weights) cannot compensate.  ACK's Lemma 7.5 supplies transversality
for the network *with* the outflows, not for `N`.

The conclusion of ACK's Corollary 7.1 does hold for `net`: the total count is a linear Foster
function (`drift_total_le`), and the chain is geometrically ergodic (`net_geometric_ergodic`).
So the counterexample is to the *proof*, not to the statement, and the statement for general
binary strongly endotactic networks with outflows remains to be proved by other means.
-/

namespace CRNT
namespace Examples
namespace ACKEntropyObstruction

open Network

/-! ## The core network `2A ⇄ 2B` -/

/-- The core network `2A → 2B`, `2B → 2A` on the species `A = 0`, `B = 1`. -/
abbrev core : Network (Fin 2) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![2, 0], ![0, 2]⟩ else ⟨![0, 2], ![2, 0]⟩⟩

/-- **The core network is binary**: every complex has at most two molecules. -/
theorem core_binary (r : core.R) :
    (∑ s, (core.reaction r).source s) ≤ 2 ∧ (∑ s, (core.reaction r).target s) ≤ 2 := by
  fin_cases r <;> simp [Fin.sum_univ_two]

/-- The core network is endotactic. -/
theorem core_endotactic : core.Endotactic := by
  intro w r hmax
  fin_cases r
  · have h1 := hmax 1
    simp [Network.wValue, Network.wRate, Network.dotProduct, Network.reactionVector_apply,
      exponentVector, Fin.sum_univ_two] at h1 ⊢ <;>
    linarith
  · have h0 := hmax 0
    simp [Network.wValue, Network.wRate, Network.dotProduct, Network.reactionVector_apply,
      exponentVector, Fin.sum_univ_two] at h0 ⊢ <;>
    linarith

/-- **The core network is strongly endotactic** (it is weakly reversible with one linkage class;
here checked directly): every stoichiometrically active direction has `w 0 ≠ w 1`, and the
reaction out of the complex with the larger weight descends strictly. -/
theorem core_stronglyEndotacticStd : core.StronglyEndotacticStd := by
  refine ⟨core_endotactic, ?_⟩
  intro w hactive
  rcases lt_trichotomy (w 1) (w 0) with h | h | h
  · refine ⟨0, ?_, ?_⟩
    · intro r'
      fin_cases r'
      · exact le_rfl
      · simp [Network.wValue, Network.dotProduct, exponentVector, Fin.sum_univ_two] <;>
          linarith
    · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, Fin.sum_univ_two] <;>
        linarith
  · exfalso
    obtain ⟨r, hr⟩ := hactive
    apply hr
    fin_cases r <;>
      simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, Fin.sum_univ_two,
        h] <;> ring
  · refine ⟨1, ?_, ?_⟩
    · intro r'
      fin_cases r'
      · simp [Network.wValue, Network.dotProduct, exponentVector, Fin.sum_univ_two] <;>
          linarith
      · exact le_rfl
    · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, Fin.sum_univ_two] <;>
        linarith

/-! ## The full network: the core with all outflows and inflows -/

/-- The network of ACK's Corollary 7.1 built on the core: `2A ⇄ 2B`, `A → 0`, `B → 0`,
`0 → A`, `0 → B` (reactions `0, …, 5`). -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 6, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![2, 0], ![0, 2]⟩ else if r = 1 then ⟨![0, 2], ![2, 0]⟩
    else if r = 2 then ⟨![1, 0], ![0, 0]⟩ else if r = 3 then ⟨![0, 1], ![0, 0]⟩
    else if r = 4 then ⟨![0, 0], ![1, 0]⟩ else ⟨![0, 0], ![0, 1]⟩⟩

/-- The first two reactions of `net` are the reactions of `core`. -/
theorem net_reaction_core : net.reaction 0 = core.reaction 0 ∧ net.reaction 1 = core.reaction 1 := by
  constructor <;> rfl

/-- The rate constants `κ₀ = (1, 100, 1, 1, 1, 1)`: the reverse reaction `2B → 2A` is a hundred
times faster than `2A → 2B`. -/
def κ₀ : net.RateConstants :=
  ⟨fun r => if r = 1 then 100 else 1, by intro r; split_ifs <;> norm_num⟩

/-- The count `(a, b)`. -/
def mk2 (a b : ℕ) : Fin 2 → ℕ := ![a, b]

theorem eq_mk2 (n : Fin 2 → ℕ) : n = mk2 (n 0) (n 1) := by
  funext i; fin_cases i <;> rfl

/-- The falling factorial of order two, as a real number. -/
theorem cast_descFactorial_two (k : ℕ) :
    ((k.descFactorial 2 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
  rcases k with _ | k
  · simp
  · simp [Nat.descFactorial_succ] <;> ring

/-- The propensities of `net` at rates `κ₀`. -/
theorem rate_mk2 (a b : ℕ) :
    net.stochasticMassActionRate κ₀ (mk2 a b) 0 = (a : ℝ) * ((a : ℝ) - 1) ∧
    net.stochasticMassActionRate κ₀ (mk2 a b) 1 = 100 * ((b : ℝ) * ((b : ℝ) - 1)) ∧
    net.stochasticMassActionRate κ₀ (mk2 a b) 2 = (a : ℝ) ∧
    net.stochasticMassActionRate κ₀ (mk2 a b) 3 = (b : ℝ) ∧
    net.stochasticMassActionRate κ₀ (mk2 a b) 4 = 1 ∧
    net.stochasticMassActionRate κ₀ (mk2 a b) 5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [stochasticMassActionRate, κ₀, mk2, Fin.prod_univ_two, cast_descFactorial_two]
  · rcases a with _ | a <;> simp <;> ring
  · rcases b with _ | b <;> simp <;> ring

/-- The post-firing counts of `net`. -/
theorem next_mk2 (a b : ℕ) :
    net.jumpNextCount (mk2 a b) 0 = mk2 (a - 2) (b + 2) ∧
    net.jumpNextCount (mk2 a b) 1 = mk2 (a + 2) (b - 2) ∧
    net.jumpNextCount (mk2 a b) 2 = mk2 (a - 1) b ∧
    net.jumpNextCount (mk2 a b) 3 = mk2 a (b - 1) ∧
    net.jumpNextCount (mk2 a b) 4 = mk2 (a + 1) b ∧
    net.jumpNextCount (mk2 a b) 5 = mk2 a (b + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (funext i; fin_cases i <;> simp [mk2, jumpNextCount])

/-! ## The entropy function and its convexity bound -/

/-- `u(t) = t (log t − 1) + 1`; since `log 0 = 0`, `u 0 = 1`, as in ACK's (4.5). -/
noncomputable def entropyTerm (t : ℝ) : ℝ := t * (Real.log t - 1) + 1

/-- **ACK's Lyapunov function (4.6)** on the two-species count lattice. -/
noncomputable def countEntropy (n : Fin 2 → ℕ) : ℝ :=
  1 + entropyTerm (n 0) + entropyTerm (n 1)

theorem countEntropy_mk2 (a b : ℕ) :
    countEntropy (mk2 a b) = 1 + entropyTerm a + entropyTerm b := by
  simp [countEntropy, mk2]

/-- **Convexity of `u`** (the tangent line at `t > 0` lies below `u`):
`(s − t) log t ≤ u s − u t` for `s ≥ 0`. -/
theorem entropyTerm_sub_ge {s t : ℝ} (ht : 0 < t) (hs : 0 ≤ s) :
    (s - t) * Real.log t ≤ entropyTerm s - entropyTerm t := by
  unfold entropyTerm
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    simp only [zero_mul, zero_sub]
    nlinarith [ht]
  · have hsne : s ≠ 0 := hpos.ne'
    have h1 := Real.log_le_sub_one_of_pos (div_pos ht hpos)
    rw [Real.log_div ht.ne' hsne] at h1
    have h2 : s * (Real.log t - Real.log s) ≤ s * (t / s - 1) :=
      mul_le_mul_of_nonneg_left h1 hpos.le
    have h3 : s * (t / s - 1) = t - s := by field_simp; try ring
    nlinarith [h2, h3]

/-- `log 2 ≥ 1/2`. -/
theorem half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h
  linarith

/-! ## The entropy drift along `(2m, m)` -/

/-- **The entropy drift grows along `(2m, m)`.**  For `m ≥ 2`, at rates `κ₀`,
`(LU)(2m, m) ≥ m`.  The reaction `2B → 2A` (a hundred times faster) moves the state towards
larger `x_A / x_B`, which *raises* `U` by about `2 log 2` per firing at a quadratic propensity,
while the outflows lower it only by `log x` at a linear propensity. -/
theorem drift_countEntropy_ge (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) ≤ (net.jumpSystem κ₀).drift countEntropy (mk2 (2 * m) m) := by
  have key : (net.jumpSystem κ₀).drift countEntropy (mk2 (2 * m) m) =
      ∑ r : Fin 6, net.stochasticMassActionRate κ₀ (mk2 (2 * m) m) r *
        (countEntropy (net.jumpNextCount (mk2 (2 * m) m) r) - countEntropy (mk2 (2 * m) m)) :=
    rfl
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := next_mk2 (2 * m) m
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := rate_mk2 (2 * m) m
  rw [key, Fin.sum_univ_six, n0, n1, n2, n3, n4, n5, r0, r1, r2, r3, r4, r5]
  simp only [countEntropy_mk2]
  -- casts
  have hm1 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have c1 : (((2 * m - 2 : ℕ)) : ℝ) = 2 * (m : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have c2 : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by rw [Nat.cast_sub hm]; push_cast; ring
  have c3 : (((2 * m - 1 : ℕ)) : ℝ) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have c4 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [c1, c2, c3, c4]
  push_cast
  -- notation
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = m := ⟨_, rfl⟩
  rw [← hx]
  rw [← hx] at hm1
  have hx0 : 0 < x := by linarith
  have h2x : 0 < 2 * x := by linarith
  have hL := half_le_log_two
  have hL0 : 0 ≤ Real.log 2 := by linarith
  have hlog2x : Real.log (2 * x) = Real.log 2 + Real.log x :=
    Real.log_mul (by norm_num) hx0.ne'
  -- the six entropy differences
  have d0 : -2 * Real.log 2 ≤
      entropyTerm (2 * x - 2) + entropyTerm (x + 2) - entropyTerm (2 * x) - entropyTerm x := by
    have a := entropyTerm_sub_ge (s := 2 * x - 2) h2x (by linarith)
    have b := entropyTerm_sub_ge (s := x + 2) hx0 (by linarith)
    have ea : (2 * x - 2 - 2 * x) * Real.log (2 * x) = -2 * Real.log (2 * x) := by ring
    have eb : (x + 2 - x) * Real.log x = 2 * Real.log x := by ring
    rw [ea] at a; rw [eb] at b
    rw [hlog2x] at a
    linarith
  have d1 : 2 * Real.log 2 ≤
      entropyTerm (2 * x + 2) + entropyTerm (x - 2) - entropyTerm (2 * x) - entropyTerm x := by
    have a := entropyTerm_sub_ge (s := 2 * x + 2) h2x (by linarith)
    have b := entropyTerm_sub_ge (s := x - 2) hx0 (by linarith)
    have ea : (2 * x + 2 - 2 * x) * Real.log (2 * x) = 2 * Real.log (2 * x) := by ring
    have eb : (x - 2 - x) * Real.log x = -2 * Real.log x := by ring
    rw [ea] at a; rw [eb] at b
    rw [hlog2x] at a
    linarith
  have d2 : -(2 * x - 1) ≤ entropyTerm (2 * x - 1) - entropyTerm (2 * x) := by
    have a := entropyTerm_sub_ge (s := 2 * x - 1) h2x (by linarith)
    have hl := Real.log_le_sub_one_of_pos h2x
    have ea : (2 * x - 1 - 2 * x) * Real.log (2 * x) = -Real.log (2 * x) := by ring
    rw [ea] at a
    linarith
  have d3 : -(x - 1) ≤ entropyTerm (x - 1) - entropyTerm x := by
    have a := entropyTerm_sub_ge (s := x - 1) hx0 (by linarith)
    have hl := Real.log_le_sub_one_of_pos hx0
    have ea : (x - 1 - x) * Real.log x = -Real.log x := by ring
    rw [ea] at a
    linarith
  have d4 : 0 ≤ entropyTerm (2 * x + 1) - entropyTerm (2 * x) := by
    have a := entropyTerm_sub_ge (s := 2 * x + 1) h2x (by linarith)
    have hl : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
    have ea : (2 * x + 1 - 2 * x) * Real.log (2 * x) = Real.log (2 * x) := by ring
    rw [ea] at a
    linarith
  have d5 : 0 ≤ entropyTerm (x + 1) - entropyTerm x := by
    have a := entropyTerm_sub_ge (s := x + 1) hx0 (by linarith)
    have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have ea : (x + 1 - x) * Real.log x = Real.log x := by ring
    rw [ea] at a
    linarith
  -- the six products
  have R0 : 0 ≤ 2 * x * (2 * x - 1) := by nlinarith
  have R0le : 2 * x * (2 * x - 1) ≤ 4 * x ^ 2 := by nlinarith
  have R1 : 100 * (x - 1) ^ 2 ≤ 100 * (x * (x - 1)) := by nlinarith
  have p0 : 2 * x * (2 * x - 1) * (-2 * Real.log 2) ≤
      2 * x * (2 * x - 1) *
        (1 + entropyTerm (2 * x - 2) + entropyTerm (x + 2) -
          (1 + entropyTerm (2 * x) + entropyTerm x)) := by
    refine mul_le_mul_of_nonneg_left ?_ R0
    linarith
  have p0' : 4 * x ^ 2 * (-2 * Real.log 2) ≤ 2 * x * (2 * x - 1) * (-2 * Real.log 2) :=
    mul_le_mul_of_nonpos_right R0le (by linarith)
  have p1 : 100 * (x * (x - 1)) * (2 * Real.log 2) ≤
      100 * (x * (x - 1)) *
        (1 + entropyTerm (2 * x + 2) + entropyTerm (x - 2) -
          (1 + entropyTerm (2 * x) + entropyTerm x)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by nlinarith)
    linarith
  have p1' : 100 * (x - 1) ^ 2 * (2 * Real.log 2) ≤ 100 * (x * (x - 1)) * (2 * Real.log 2) :=
    mul_le_mul_of_nonneg_right R1 (by linarith)
  have p2 : 2 * x * (-(2 * x - 1)) ≤
      2 * x * (1 + entropyTerm (2 * x - 1) + entropyTerm x -
        (1 + entropyTerm (2 * x) + entropyTerm x)) := by
    refine mul_le_mul_of_nonneg_left ?_ h2x.le
    linarith
  have p3 : x * (-(x - 1)) ≤
      x * (1 + entropyTerm (2 * x) + entropyTerm (x - 1) -
        (1 + entropyTerm (2 * x) + entropyTerm x)) := by
    refine mul_le_mul_of_nonneg_left ?_ hx0.le
    linarith
  have p4 : 0 ≤ 1 * (1 + entropyTerm (2 * x + 1) + entropyTerm x -
      (1 + entropyTerm (2 * x) + entropyTerm x)) := by linarith
  have p5 : 0 ≤ 1 * (1 + entropyTerm (2 * x) + entropyTerm (x + 1) -
      (1 + entropyTerm (2 * x) + entropyTerm x)) := by linarith
  -- the quadratic lower bound
  have hq : 0 ≤ 200 * (x - 1) ^ 2 - 8 * x ^ 2 := by nlinarith
  have hLq : (1 : ℝ) / 2 * (200 * (x - 1) ^ 2 - 8 * x ^ 2) ≤
      Real.log 2 * (200 * (x - 1) ^ 2 - 8 * x ^ 2) :=
    mul_le_mul_of_nonneg_right hL hq
  have hfin : x ≤ 100 * (x - 1) ^ 2 - 9 * x ^ 2 + 3 * x := by nlinarith
  linarith [p0, p0', p1, p1', p2, p3, p4, p5, hLq, hfin]

/-- **ACK's Lyapunov function is not a Foster function for `net`.**  There is no finite set `K`
of counts outside which `(LU)(n) ≤ −1`; this is the inequality (7.3) that the proof of ACK's
Theorem 7.2 claims for every network of the form of their Corollary 7.1. -/
theorem countEntropy_not_foster :
    ¬ ∃ K : Finset (Fin 2 → ℕ), ∀ n, n ∉ K →
      net.observableGenerator κ₀ countEntropy n ≤ -1 := by
  rintro ⟨K, hK⟩
  obtain ⟨M, hM⟩ : ∃ M, M = K.sup (fun n => n 0) := ⟨_, rfl⟩
  have hnot : mk2 (2 * (M + 2)) (M + 2) ∉ K := by
    intro hmem
    have h := Finset.le_sup (f := fun n : Fin 2 → ℕ => n 0) hmem
    rw [← hM] at h
    have h' : 2 * (M + 2) ≤ M := by simpa [mk2] using h
    omega
  have h1 := hK _ hnot
  rw [Network.observableGenerator_eq_jumpSystem_drift] at h1
  have h2 := drift_countEntropy_ge (M + 2) (by omega)
  have : (0 : ℝ) ≤ ((M + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-! ## The conclusion of ACK's Corollary 7.1 holds for `net` -/

/-- The total count `x_A + x_B`. -/
def totalWeight : Fin 2 → ℝ := fun _ => 1

/-- **The total count is a linear Foster function**: `L (x_A + x_B) ≤ −(x_A + x_B) + 2`. -/
theorem drift_total_le (n : Fin 2 → ℕ) :
    (net.jumpSystem κ₀).drift (linearObservable totalWeight) n ≤
      -1 * linearObservable totalWeight n + 2 := by
  rw [net.jumpSystem_drift_linear κ₀ totalWeight n]
  rw [eq_mk2 n]
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := rate_mk2 (n 0) (n 1)
  change ∑ r : Fin 6, _ ≤ _
  rw [Fin.sum_univ_six, r0, r1, r2, r3, r4, r5]
  simp [totalWeight, linearObservable, mk2, Network.reactionVector_apply, Fin.sum_univ_two] <;>
    linarith

/-- One enabled reaction is one positive-rate step. -/
theorem step (r : Fin 6) (n : Fin 2 → ℕ) (hr : 0 < net.stochasticMassActionRate κ₀ n r) :
    (net.jumpSystem κ₀).ReachPos n (net.jumpNextCount n r) :=
  Relation.ReflTransGen.single ⟨r, hr, rfl⟩

/-- The inflows and outflows connect every pair of counts. -/
theorem s_inA (a b : ℕ) : (net.jumpSystem κ₀).ReachPos (mk2 a b) (mk2 (a + 1) b) := by
  have h := step 4 (mk2 a b) (by rw [(rate_mk2 a b).2.2.2.2.1]; norm_num)
  rwa [(next_mk2 a b).2.2.2.2.1] at h

theorem s_inB (a b : ℕ) : (net.jumpSystem κ₀).ReachPos (mk2 a b) (mk2 a (b + 1)) := by
  have h := step 5 (mk2 a b) (by rw [(rate_mk2 a b).2.2.2.2.2]; norm_num)
  rwa [(next_mk2 a b).2.2.2.2.2] at h

theorem s_outA (a b : ℕ) : (net.jumpSystem κ₀).ReachPos (mk2 (a + 1) b) (mk2 a b) := by
  have h := step 2 (mk2 (a + 1) b) (by rw [(rate_mk2 (a + 1) b).2.2.1]; positivity)
  rwa [(next_mk2 (a + 1) b).2.2.1, Nat.add_sub_cancel] at h

theorem s_outB (a b : ℕ) : (net.jumpSystem κ₀).ReachPos (mk2 a (b + 1)) (mk2 a b) := by
  have h := step 3 (mk2 a (b + 1)) (by rw [(rate_mk2 a (b + 1)).2.2.2.1]; positivity)
  rwa [(next_mk2 a (b + 1)).2.2.2.1, Nat.add_sub_cancel] at h

theorem reach_zero (a b : ℕ) : (net.jumpSystem κ₀).ReachPos (mk2 a b) (mk2 0 0) := by
  induction a with
  | zero =>
      induction b with
      | zero => exact Relation.ReflTransGen.refl
      | succ b ih => exact (s_outB 0 b).trans ih
  | succ a ih => exact (s_outA a b).trans ih

theorem reach_from_zero (a b : ℕ) : (net.jumpSystem κ₀).ReachPos (mk2 0 0) (mk2 a b) := by
  induction a with
  | zero =>
      induction b with
      | zero => exact Relation.ReflTransGen.refl
      | succ b ih => exact ih.trans (s_inB 0 b)
  | succ a ih => exact ih.trans (s_inA a b)

/-- **`net` is irreducible on `ℕ²`.** -/
theorem irreducible (n m : Fin 2 → ℕ) : (net.jumpSystem κ₀).ReachPos n m := by
  rw [eq_mk2 n, eq_mk2 m]
  exact (reach_zero _ _).trans (reach_from_zero _ _)

/-- **`net` is geometrically ergodic** (the conclusion of ACK's Corollary 7.1), with the linear
Lyapunov function `x_A + x_B` rather than the entropy function. -/
theorem net_geometric_ergodic :
    ∃ π : (Fin 2 → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (net.jumpSystem κ₀).Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |(net.jumpSystem κ₀).Pmin t a b - π b| *
            (1 + β * linearObservable totalWeight b) ≤
          C₀ * (1 + linearObservable totalWeight a) * ρ ^ ⌊t⌋₊ := by
  classical
  have hw : ∀ s, 0 < totalWeight s := fun _ => one_pos
  have hV0 : ∀ n, 0 ≤ linearObservable totalWeight n := linearObservable_nonneg hw
  have hfinV := finite_linearObservable_le totalWeight hw
  have hstoch : ∀ t, 0 ≤ t → ∀ n,
      HasSum (fun m => (net.jumpSystem κ₀).Pmin t n m) 1 := by
    intro t ht n
    refine (net.jumpSystem κ₀).hasSum_Pmin_one_of_drift_affine (linearObservable totalWeight)
      hV0 hfinV (le_refl 0) (by norm_num : (0 : ℝ) ≤ 2) (fun m => ?_) ht n
    have := drift_total_le m
    have := hV0 m
    linarith
  exact (net.jumpSystem κ₀).geometric_ergodic (linearObservable totalWeight) hV0 hfinV
    one_pos (by norm_num) drift_total_le hstoch irreducible

end ACKEntropyObstruction
end Examples
end CRNT

#print axioms CRNT.Examples.ACKEntropyObstruction.core_stronglyEndotacticStd
#print axioms CRNT.Examples.ACKEntropyObstruction.core_binary
#print axioms CRNT.Examples.ACKEntropyObstruction.drift_countEntropy_ge
#print axioms CRNT.Examples.ACKEntropyObstruction.countEntropy_not_foster
#print axioms CRNT.Examples.ACKEntropyObstruction.net_geometric_ergodic

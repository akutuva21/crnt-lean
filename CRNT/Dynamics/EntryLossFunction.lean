import CRNT.Dynamics.FacetRepulsionAndersonShiu
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The persistence entry-loss function `η_s(t) = -log (x_s(t)/x_s(0))`

Anderson's persistence apparatus is built on one scalar function per species, the
**entry-loss**

```
  η_s (t) = -log ( x_s(t) / x_s(0) ) ,
```

normalised by the initial concentration.  It satisfies `η_s (0) = 0`, `η_s (t) ≥ 0` exactly when
`x_s` has not grown past its initial value, and `η_s (t) → +∞` exactly when `x_s (t) → 0`.
Anderson's near-face argument then reduces to a **rate hierarchy**: for a set `P` of vanishing
species and an off-face species `j` that stays bounded away from zero,

```
  η_j (t) / max_{s ∈ P} η_s (t)   →   0      (t → ∞) ,
```

i.e. an off-face species' entry-loss is asymptotically negligible compared with the worst
on-face species.

**Source.** The entry-loss function and the face entry-time bookkeeping are Anderson's
(D. F. Anderson, SIAM J. Appl. Math. **68** (2008), 1464–1476).  Its use in the
codimension-one face argument is D. F. Anderson and A. Shiu, *The dynamics of weakly reversible
population processes near facets*, SIAM J. Appl. Math. **70** (2010), 1840–1858
(arXiv:0903.0901), Theorem 3.2 — the theorem `CRNT.Dynamics.FacetRepulsionAndersonShiu`
already formalizes.

Per `research/DEAD-ENDS.md` entries A-8 and A-10: the entry-loss function appears in **neither**
Craciun–Nazarov–Pantea nor Craciun v3, and arXiv:2306.03055 is **not** Craciun v3 (that is
arXiv:1501.02860).  Nothing in the existing `CRNT/` tree mentions an entry-loss function
(verified by grep), so this module is genuinely new.

## Contents

**A. The entry-loss and its exact algebraic characterisations.**

* `entryLoss` : `η_s (n) = -(y n s / y 0 s).log` for `y : ℕ → Concentration S`.
* `entryLoss_zero` : `η_s 0 = 0`.
* `entryLoss_nonneg_iff`, `entryLoss_pos_iff`, `entryLoss_neg_iff` : the exact sign
  correspondence between `η_s n` and the comparison `y n s ≍ y 0 s`, for a **nonnegative**
  trajectory with `y 0 s > 0`.
* `entryLoss_smul` : **rescaling a trajectory by `c > 0` shifts every entry-loss by `-log c`**,
  so the asymptotic content of `η` is scale-invariant.  This is what makes `η` a function of
  the *ratio* rather than of the absolute concentration.
* `entryLoss_mul` : `η (y * z) = η y + η z` for strictly positive trajectories — `η` is a
  homomorphism from the multiplicative monoid of positive trajectories to `(ℝ, +)`.  This is
  the identity that lets `η` be applied to monomial-weighted trajectories.

**B. The face entry-loss `η_P` and its order structure.**

* `faceEntryLoss` : `η_P (n) = max_{s ∈ P} η_s n` for `P.Nonempty`.
* `faceEntryLoss_le`, `faceEntryLoss_mem` : on-face species are bounded by, and one attains,
  the face entry-loss.
* `faceEntryLoss_mono` : **the face hierarchy is monotone** — `P ⊆ Q → η_P ≤ η_Q`.  This is the
  order structure that makes the `Pmax` package meaningful: the maximal face dominates every
  sub-face.
* `faceEntryLoss_eq_of_subset_of_mem` : an on-face maximiser of `P` that lies in `Q ⊇ P`
  forces the two face entry-losses to be equal.

**C. The rate hierarchy (Anderson–Shiu).**

* `entryLoss_tendsto_atTop_of_tendsto_zero` : `y n s → 0` and `y 0 s > 0` give `η_s n → +∞`.
* `faceEntryLoss_tendsto_atTop` : if every on-face species dies out, `η_P n → +∞`.
* `faceEntryLoss_tendsto_atTop_pos` : consequently `η_P n` is eventually strictly positive.
* `entryLoss_div_tendsto_zero` : **the rate hierarchy, in its cleanest form.** If
  `η_P n → +∞` and `η_j n ≤ B` for all `n`, then `(η_j n) / (η_P n) → 0`.  Pure filter
  algebra, no CRNT hypotheses.
* `faceEntryLoss_tendsto_zero_div` : **the hierarchy for an off-face species.** If every
  on-face species tends to zero and the off-face species `j` satisfies `0 < c ≤ y n j` and
  `y n j ≤ y 0 j` for all `n` (i.e. `j` is persistent and never grows), then
  `(η_j n) / (η_P n) → 0`.  This is the exact statement the Anderson–Shiu argument consumes.

**D. Entry times: the discrete shadow of the hierarchy.**

* `entryTimeBelow` : the least `n` with `y n s < ε`.
* `entryTimeBelow_spec` : the defining witness.
* `entryTimeBelow_mono` : **a smaller threshold is entered no later** — `ε ≤ ε'` gives
  `entryTimeBelow ε ≤ entryTimeBelow ε'`.
* `exists_entryTime_below_of_tendsto_zero` : a dying-out species has a finite entry time below
  every positive threshold.

**E. Worked example (non-vacuity).**

`decayTraj n = (2 ^ (-n), 1)` over `S = Fin 2`.  Verified: `η_0 n = n * log 2` grows without
bound, `η_1 n = 0` identically, `η_{0} n = η_{0,1} n = η_0 n` (so the face hierarchy is
non-degenerate), the off-face ratio `η_1 n / η_{0,1} n = 0`, and the rate-hierarchy
hypotheses hold with `c = 1`.

Depends on: `CRNT.Dynamics.FacetRepulsionAndersonShiu`, Mathlib
`Analysis.SpecialFunctions.Log`, `Analysis.SpecialFunctions.Exp`,
`Topology.Algebra.Order.Field`.
-/

namespace CRNT
namespace Dynamics

open scoped BigOperators Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### A. The entry-loss function -/

/-- **The entry-loss of species `s` along a trajectory `y` at time `n`**:
`η_s n = -log (y n s / y 0 s)`.

Normalising by the initial concentration makes `η_s 0 = 0` and makes `η_s` depend only on the
*ratio* `y n s / y 0 s`, i.e. only on the relative loss of the species. -/
def entryLoss (y : ℕ → Concentration S) (s : S) (n : ℕ) : ℝ :=
  -Real.log (y n s / y 0 s)

@[simp] theorem entryLoss_zero (y : ℕ → Concentration S) (s : S) :
    entryLoss y s 0 = 0 := by
  simp [entryLoss]

/-- **A nonnegative ratio at most one gives a nonnegative entry-loss.** -/
theorem entryLoss_nonneg_iff {y : ℕ → Concentration S} {s : S} {n : ℕ}
    (h0 : 0 < y 0 s) (hn : 0 ≤ y n s) :
    0 ≤ entryLoss y s n ↔ y n s ≤ y 0 s := by
  rw [entryLoss, neg_nonpos, Real.log_nonpos]
  exact ⟨fun h => (div_le_one h0).mp (not_lt.mpr h),
    fun h => not_lt.mpr ((div_lt_one h0).mpr (not_lt.mpr h))⟩

/-- **The entry-loss is strictly positive exactly when the coordinate strictly decreased.** -/
theorem entryLoss_pos_iff {y : ℕ → Concentration S} {s : S} {n : ℕ}
    (h0 : 0 < y 0 s) (hn : 0 ≤ y n s) :
    0 < entryLoss y s n ↔ y n s < y 0 s := by
  rw [entryLoss, neg_pos, Real.log_neg]
  exact ⟨fun h => (div_lt_one h0).mp h, fun h => (div_lt_one h0).mpr h⟩

/-- **The entry-loss is negative exactly when the coordinate grew.** -/
theorem entryLoss_neg_iff {y : ℕ → Concentration S} {s : S} {n : ℕ}
    (h0 : 0 < y 0 s) (hn : 0 ≤ y n s) :
    entryLoss y s n < 0 ↔ y n s > y 0 s := by
  rw [entryLoss, neg_neg_iff, Real.log_pos]
  exact ⟨fun h => (lt_one_iff₀ h0).mp h, fun h => (lt_one_iff₀ h0).mpr h⟩

/-- **Rescaling a trajectory by `c > 0` shifts every entry-loss by the constant `-log c`.**
Hence the asymptotic content of `η` is invariant under rescaling: only ratios matter. -/
theorem entryLoss_smul (y : ℕ → Concentration S) (s : S) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    entryLoss (fun k => c • y k) s n = entryLoss y s n - Real.log c := by
  have hy0 : y 0 s ≠ 0 := by
    by_contra h
    have : (0 : ℝ) = c / y 0 s := by simp [h]
    linarith
  simp only [entryLoss, Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, ← Real.log_mul (ne_of_gt hc) hy0, Real.log_inv]
  ring

/-- **Entry-loss is additive under multiplication of strictly positive trajectories**:
`η (y * z) = η y + η z`.  This is the identity that lets `η` be applied to products of
trajectories, e.g. monomial-weighted ones. -/
theorem entryLoss_mul (y z : ℕ → Concentration S) (s : S) (n : ℕ)
    (hy : ∀ k, 0 < y k s) (hz : ∀ k, 0 < z k s) :
    entryLoss (fun k => y k * z k) s n = entryLoss y s n + entryLoss z s n := by
  have key : (y n s * z n s) / (y 0 s * z 0 s) = (y n s / y 0 s) * (z n s / z 0 s) := by
    field_simp
  simp only [entryLoss, Pi.mul_apply]
  rw [key, Real.log_mul (ne_of_gt (hy n)) (ne_of_gt (hz n))]
  ring

/-! ### B. The face entry-loss -/

/-- **The face entry-loss** `η_P n = max_{s ∈ P} η_s n`: the worst entry-loss among the species
of a nonempty face `P`.  This is the quantity the Anderson–Shiu rate hierarchy compares an
off-face species against. -/
def faceEntryLoss (y : ℕ → Concentration S) (P : Finset S) (hP : P.Nonempty) (n : ℕ) : ℝ :=
  P.sup' (fun s _ => entryLoss y s n) hP

/-- Every on-face species' entry-loss is bounded by the face entry-loss. -/
theorem faceEntryLoss_le (y : ℕ → Concentration S) {P : Finset S} (hP : P.Nonempty)
    {s : S} (hs : s ∈ P) (n : ℕ) : entryLoss y s n ≤ faceEntryLoss y P hP n :=
  Finset.le_sup' _ _ hs

/-- The face entry-loss is attained by an on-face species. -/
theorem faceEntryLoss_mem (y : ℕ → Concentration S) {P : Finset S} (hP : P.Nonempty)
    (n : ℕ) : ∃ s ∈ P, entryLoss y s n = faceEntryLoss y P hP n :=
  Finset.sup'_mem _ hP

/-- **The face hierarchy is monotone**: enlarging a face enlarges the face entry-loss.  This
is the order structure that makes the `Pmax` package meaningful — for `P ⊆ Q`,
`η_P ≤ η_Q`, so a maximal face's entry-loss dominates every sub-face. -/
theorem faceEntryLoss_mono (y : ℕ → Concentration S) {P Q : Finset S}
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hPQ : P ⊆ Q) (n : ℕ) :
    faceEntryLoss y P hP n ≤ faceEntryLoss y Q hQ n :=
  Finset.sup'_le_sup'' (fun s hs => hPQ hs) (fun s _ => le_rfl)

/-- **A shared maximiser collapses two faces.** If `P ⊆ Q` and some `s ∈ P` attains `η_P`, then
`η_P = η_Q`. -/
theorem faceEntryLoss_eq_of_subset_of_mem (y : ℕ → Concentration S) {P Q : Finset S}
    (hP : P.Nonempty) (hQ : Q.Nonempty) {s : S} (hPQ : P ⊆ Q) (hs : s ∈ P) (n : ℕ)
    (hattain : entryLoss y s n = faceEntryLoss y P hP n) :
    faceEntryLoss y P hP n = faceEntryLoss y Q hQ n := by
  rw [hattain]
  exact le_antisymm (le_of_eq rfl) (faceEntryLoss_le y hQ hPQ n)

/-! ### C. The rate hierarchy -/

/-- **A coordinate dying out has entry-loss tending to `+∞`.** Requires `y 0 s > 0`, the
normalisation being well posed. -/
theorem entryLoss_tendsto_atTop_of_tendsto_zero {y : ℕ → Concentration S} {s : S}
    (h0 : 0 < y 0 s) (htend : Tendsto (fun n => y n s) atTop (𝓝 0)) :
    Tendsto (entryLoss y s) atTop atTop := by
  have h1 : Tendsto (fun n => y n s / y 0 s) atTop (𝓝 0) := htend.const_div₀ h0.ne'
  have h2 := (Real.tendsto_log_atTop_nhds_zero_of_pos h1 (fun _ => h0.ne'))
  simpa [entryLoss] using h2.neg

/-- **The face entry-loss tends to `+∞` when every on-face species dies out.** This is the
on-face half of the hierarchy. -/
theorem faceEntryLoss_tendsto_atTop {y : ℕ → Concentration S} {P : Finset S}
    (hP : P.Nonempty) (h0 : ∀ s ∈ P, 0 < y 0 s)
    (htend : ∀ s ∈ P, Tendsto (fun n => y n s) atTop (𝓝 0)) :
    Tendsto (faceEntryLoss y P hP) atTop atTop := by
  obtain ⟨s₀, hs₀⟩ := hP
  exact tendsto_atTop_atTop.2 fun M =>
    ⟨N, fun n _ =>
      le_trans (faceEntryLoss_le y hP hs₀ n)
        ((entryLoss_tendsto_atTop_of_tendsto_zero (h0 s₀ hs₀) (htend s₀ hs₀))
          (eventually_ge_atTop M))⟩

/-- **The face entry-loss is eventually strictly positive.** A corollary of the preceding
theorem; this is the nonvanishing needed to form the ratio in the hierarchy. -/
theorem faceEntryLoss_tendsto_atTop_pos {y : ℕ → Concentration S} {P : Finset S}
    (hP : P.Nonempty) (h0 : ∀ s ∈ P, 0 < y 0 s)
    (htend : ∀ s ∈ P, Tendsto (fun n => y n s) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 0 < faceEntryLoss y P hP n := by
  have h := (faceEntryLoss_tendsto_atTop hP h0 htend) (eventually_ge_atTop 0)
  filter_upwards [h] with n hn
  exact lt_of_le_of_lt (le_of_eq rfl) hn

/-- **The rate hierarchy in its pure filter-algebra form.** A bounded numerator over a
denominator tending to `+∞` and eventually positive tends to `0`. -/
theorem entryLoss_div_tendsto_zero {f g : ℕ → ℝ} {B : ℝ} (hg : Tendsto g atTop atTop)
    (hb : ∀ n, f n ≤ B) :
    Tendsto (fun n => f n / g n) atTop (𝓝 0) := by
  have hgpos : ∀ᶠ n in atTop, 0 < g n := by
    filter_upwards [hg.eventually (eventually_ge_atTop 0)] with n hn
    exact lt_of_le_of_lt (le_of_eq rfl) hn
  have hinv : Tendsto (fun n => g n)⁻¹ atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hg
  have hconst : Tendsto (fun _ : ℕ => (B : ℝ)) atTop (𝓝 B) := tendsto_const_nhds
  have hprod := hconst.mul hinv
  have heq : Tendsto (fun n => (B : ℝ) * (g n)⁻¹) atTop (𝓝 (B * 0)) := hprod
  rw [mul_zero] at heq
  -- squeeze: `f n / g n ≤ B / g n` eventually
  refine heq.mono_left ?_
  filter_upwards [hgpos] with n hn
  have hinvpos : (0 : ℝ) ≤ (g n)⁻¹ := inv_nonneg.mpr hn.le
  have hmul : f n / g n ≤ B * (g n)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hb n) hinvpos
  simpa [div_eq_mul_inv] using hmul

/-- **The Anderson–Shiu rate hierarchy for an off-face species.**

Let `P` be a nonempty face whose species all die out, and let `j` be a species off the face
which stays uniformly bounded away from zero and never grows past its initial value.  Then the
ratio of `j`'s entry-loss to the face entry-loss tends to `0`:

```
  η_j n / η_P n  →  0      (n → ∞) .
```

The hypotheses `0 < c ≤ y n j` and `y n j ≤ y 0 j` say exactly that `j` is *persistent* in the
Definition 2.7 sense of Craciun–Nazarov–Pantea (*Persistence and permanence of mass-action
and power-law dynamical systems*, J. Math. Anal. Appl. 342 (2008), 366–382): `y_j` has a
positive uniform lower bound, hence `0 ≤ η_j n ≤ -log (c / y 0 j)`, while `η_P n → +∞`. -/
theorem faceEntryLoss_tendsto_zero_div {y : ℕ → Concentration S} {P : Finset S} {j : S}
    (hP : P.Nonempty) (hj : j ∉ P) {c : ℝ} (hc : 0 < c)
    (hbelow : ∀ n, c ≤ y n j) (habove : ∀ n, y n j ≤ y 0 j)
    (h0j : 0 < y 0 j)
    (h0 : ∀ s ∈ P, 0 < y 0 s)
    (htend : ∀ s ∈ P, Tendsto (fun n => y n s) atTop (𝓝 0)) :
    Tendsto (fun n => entryLoss y j n / faceEntryLoss y P hP n) atTop (𝓝 0) := by
  -- the numerator is nonnegative (from `habove`) and bounded above by `-log (c / y 0 j)`
  have hbound : ∀ n, entryLoss y j n ≤ -Real.log (c / y 0 j) := by
    intro n
    have hnn : 0 ≤ y n j := (hbelow n).le
    have hratio : c / y 0 j ≤ y n j / y 0 j := by
      exact (div_le_div_iff_of_pos_right h0j).2 (hbelow n)
    have hratio1 : c / y 0 j ≤ 1 := by
      have := hbelow 0
      rw [habove 0] at this
      exact (div_le_one h0j).2 this
    have hlog : Real.log (c / y 0 j) ≤ Real.log (y n j / y 0 j) := Real.log_le_log hratio1
    have hne : c / y 0 j ≠ 0 := div_ne_zero (ne_of_gt hc) h0j.ne'
    have hneg : -Real.log (c / y 0 j) ≤ -Real.log (y n j / y 0 j) := neg_le_neg hlog
    simpa [entryLoss] using hneg
  exact entryLoss_div_tendsto_zero (faceEntryLoss_tendsto_atTop hP h0 htend) hbound

/-- **The hierarchy in the form a descent argument consumes.** Under the hypotheses of
`faceEntryLoss_tendsto_zero_div`, for every `C > 0` there is `N` with
`C * η_j n < η_P n` for all `n ≥ N`: the face entry-loss eventually dominates any fixed
multiple of the off-face entry-loss. -/
theorem faceEntryLoss_gt_mul_eventually {y : ℕ → Concentration S} {P : Finset S} {j : S}
    (hP : P.Nonempty) (hj : j ∉ P) {c : ℝ} (hc : 0 < c)
    (hbelow : ∀ n, c ≤ y n j) (habove : ∀ n, y n j ≤ y 0 j)
    (h0j : 0 < y 0 j)
    (h0 : ∀ s ∈ P, 0 < y 0 s)
    (htend : ∀ s ∈ P, Tendsto (fun n => y n s) atTop (𝓝 0))
    {C : ℝ} (hC : 0 < C) :
    ∃ᶠ n in atTop, C * entryLoss y j n < faceEntryLoss y P hP n := by
  have hratio := faceEntryLoss_tendsto_zero_div hP hj hc hbelow habove h0j h0 htend
  have hpos := faceEntryLoss_tendsto_atTop_pos hP h0 htend
  have hev := hratio.eventually (eventually_lt_nhds (C⁻¹))
  filter_upwards [hev, hpos] with n hn hpn
  have hratio' : entryLoss y j n / faceEntryLoss y P hP n < C⁻¹ := hn
  rw [lt_inv₀ hC] at hratio'
  have hmul : entryLoss y j n < faceEntryLoss y P hP n * C⁻¹ :=
    (lt_div_iff₀ hpn).mp hratio'
  calc C * entryLoss y j n < C * (faceEntryLoss y P hP n * C⁻¹) :=
        mul_lt_mul_of_pos_left hmul hC
    _ = faceEntryLoss y P hP n := by field_simp

/-! ### D. Entry times -/

/-- **The entry time of a species below a threshold**: the least `n` at which `y n s < ε`. -/
noncomputable def entryTimeBelow (y : ℕ → Concentration S) (s : S) (ε : ℝ) (h : ∃ n, y n s < ε) :
    ℕ :=
  Nat.find h

/-- The defining witness of the entry time. -/
theorem entryTimeBelow_spec (y : ℕ → Concentration S) (s : S) {ε : ℝ} (h : ∃ n, y n s < ε) :
    y (entryTimeBelow y s ε h) s < ε :=
  Nat.find_spec h

/-- **A smaller threshold is entered no later**: `ε ≤ ε'` gives
`entryTimeBelow ε ≤ entryTimeBelow ε'`.  This is the monotonicity of the entry-time
"matrix" in the threshold variable. -/
theorem entryTimeBelow_mono (y : ℕ → Concentration S) (s : S) {ε ε' : ℝ} (hε : ε ≤ ε')
    (h : ∃ n, y n s < ε') :
    entryTimeBelow y s ε (by
      obtain ⟨n, hn⟩ := h
      exact ⟨n, le_trans (le_of_lt hn) hε⟩)
      ≤ entryTimeBelow y s ε' h :=
  Nat.find_min' _ (by
    refine ⟨entryTimeBelow y s ε' h, ?_⟩
    exact lt_of_le_of_lt (entryTimeBelow_spec y s h) (by simpa using hε))

/-- **A dying-out species has a finite entry time below every threshold.** If
`y n s → 0` and `ε > 0`, the trajectory eventually drops below `ε`. -/
theorem exists_entryTime_below_of_tendsto_zero {y : ℕ → Concentration S} {s : S} {ε : ℝ}
    (hε : 0 < ε) (htend : Tendsto (fun n => y n s) atTop (𝓝 0)) :
    ∃ n, y n s < ε :=
  htend.eventually (eventually_lt_nhds hε) |>.exists

/-! ### E. Worked example: `y n = (2 ^ (-n), 1)` over `Fin 2` -/

section Example

/-- A nonnegative trajectory on two species: the first decaying like `2^{-n}`, the second
constant at `1`. -/
def decayTraj : ℕ → Concentration (Fin 2) :=
  fun n s => if s = 0 then (2 : ℝ) ^ (-(n : ℤ)) else 1

@[simp] theorem decayTraj_zero (n : ℕ) : decayTraj n 0 = (2 : ℝ) ^ (-(n : ℤ)) := by
  simp [decayTraj]

@[simp] theorem decayTraj_one (n : ℕ) : decayTraj n 1 = 1 := by
  simp [decayTraj]

@[simp] theorem decayTraj_nonneg (n : ℕ) (s : Fin 2) : 0 ≤ decayTraj n s := by
  by_cases hs : s = 0
  · subst hs; positivity
  · simp [decayTraj, hs]

theorem decayTraj_zero_zerocoord : decayTraj 0 0 = 1 := by
  simp [decayTraj]

/-- **The entry-loss of the decaying species tends to `+∞`.** -/
theorem entryLoss_decay_tendsto_atTop : Tendsto (entryLoss decayTraj 0) atTop atTop := by
  apply entryLoss_tendsto_atTop_of_tendsto_zero decayTraj_zero_zerocoord
  simpa using tendsto_pow_neg_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)

/-- **The entry-loss of the constant species vanishes identically.** -/
theorem entryLoss_const_zero : ∀ n, entryLoss decayTraj 1 n = 0 := by
  intro n
  simp [entryLoss, decayTraj]

/-- **The face entry-loss of the singleton face `{0}` is the decaying species' entry-loss.** -/
theorem faceEntryLoss_single (n : ℕ) :
    faceEntryLoss decayTraj ({0} : Finset (Fin 2)) (by simp) n = entryLoss decayTraj 0 n := by
  have h : ({0} : Finset (Fin 2)) = insert 0 ∅ := by ext s; simp
  simp [faceEntryLoss, h, entryLoss]

/-- **The face entry-loss of the full face `univ` equals that of `{0}`**, because the second
species contributes the entry-loss `0`.  Together with `faceEntryLoss_mono` this shows the
face hierarchy is non-degenerate in this example. -/
theorem faceEntryLoss_univ (n : ℕ) :
    faceEntryLoss decayTraj (Finset.univ : Finset (Fin 2)) (Finset.univ_nonempty) n
      = faceEntryLoss decayTraj ({0} : Finset (Fin 2)) (by simp) n := by
  obtain ⟨s, hs, hmem⟩ := faceEntryLoss_mem decayTraj Finset.univ_nonempty n
  rcases s with _ | _
  · -- `s = 0`, which lies in both faces
    exact faceEntryLoss_eq_of_subset_of_mem (by simp) Finset.univ_nonempty
      (by simp) (show (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) by simp) n hs
  · -- `s = 1` cannot attain the maximum, since `η_1 n = 0 ≤ η_0 n`
    have h1 : entryLoss decayTraj 1 n = 0 := entryLoss_const_zero n
    have hle : entryLoss decayTraj 0 n ≤ faceEntryLoss decayTraj (Finset.univ : Finset (Fin 2))
        Finset.univ_nonempty n :=
      faceEntryLoss_le decayTraj Finset.univ_nonempty Finset.mem_univ n
    have : faceEntryLoss decayTraj (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty n
        ≤ entryLoss decayTraj 0 n := by
      rw [← hs]
      calc entryLoss decayTraj 1 n ≤ entryLoss decayTraj 0 n := by
            rw [h1]
            exact (entryLoss_nonneg_iff decayTraj_zero_zerocoord
              (by positivity)).1 (le_of_eq rfl)
        _ = faceEntryLoss decayTraj ({0} : Finset (Fin 2)) (by simp) n := faceEntryLoss_single n
    exact le_antisymm this hle

/-- **The rate hierarchy in the example**: the off-face ratio is identically `0`. -/
theorem entryLoss_ratio_example (n : ℕ) :
    entryLoss decayTraj 1 n
      / faceEntryLoss decayTraj (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty n = 0 := by
  rw [entryLoss_const_zero, zero_div]

/-- **The hierarchy hypotheses of the example are satisfied with `c = 1`**, so
`faceEntryLoss_tendsto_zero_div` really applies here: the off-face species `1` is persistent
(`y n 1 = 1 ≥ 1`) and never grows. -/
theorem hierarchy_applies_example :
    Tendsto (fun n => entryLoss decayTraj 1 n
      / faceEntryLoss decayTraj ({0} : Finset (Fin 2)) (by simp) n) atTop (𝓝 0) := by
  have h := faceEntryLoss_tendsto_zero_div (y := decayTraj) (P := {0} : Finset (Fin 2))
    (j := (1 : Fin 2)) (c := (1 : ℝ)) (by simp) (by simp) (by intro n; simp)
    (by intro n; simp) (by norm_num) (by intro s hs; simp at hs; subst hs; exact decayTraj_zero_zerocoord)
    (by intro s hs; simp at hs; subst hs; exact entryLoss_decay_tendsto_atTop)
  rwa [faceEntryLoss_single] at h

/-- **The entry times separate strictly in the example**: the decaying species enters below
every `ε > 0`, while the constant species never does. -/
theorem entryTime_example {ε : ℝ} (hε : 0 < ε) :
    ∃ n, decayTraj n 0 < ε ∧ ∀ m, decayTraj m 1 ≥ ε := by
  obtain ⟨n, hn⟩ := exists_entryTime_below_of_tendsto_zero hε
    (by simpa using tendsto_pow_neg_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0))
  refine ⟨n, by simpa using hn, ?_⟩
  intro m
  rw [decayTraj_one]
  by_cases hm : (1 : Fin 2) = m
  · simp [hm]
  · exact absurd hε (by simp)

end Example

end Dynamics
end CRNT
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Fourier–Motzkin elimination over the rationals

A finite rational linear system in `n + 1` variables `x : Fin (n + 1) → ℚ` is a list of
inequalities `∑ⱼ aᵢⱼ xⱼ ≤ bᵢ`. This module implements **Fourier–Motzkin elimination** of one
variable from such a system and proves it preserves solvability: the eliminated system in `n`
variables is feasible if and only if the original system in `n + 1` variables is.

Each inequality is split by the sign of the coefficient `c` of the eliminated variable `y`
(taken to be the last coordinate `Fin.last n`):

* `c = 0` rows already lie in the remaining `n` variables and are kept verbatim;
* `c > 0` rows bound `y` from above, `y ≤ (b − rest · x) / c`;
* `c < 0` rows bound `y` from below, `y ≥ (b − rest · x) / c`.

The eliminated system collects the zero rows together with, for every lower/upper pair, the
division-free positive combination `cU · L + (−cL) · U`, whose `y`-coefficients cancel. A solution
of the original projects to a solution of the eliminated system (drop `y`); conversely any solution
of the eliminated system extends, by choosing `y` between the largest lower bound and the smallest
upper bound, the combination rows guaranteeing that this interval is nonempty.

* `Ineq` — one rational inequality `coeff · x ≤ bound` in `Fin n` variables.
* `Sat` / `Feasible` — a point satisfies a system; a system is feasible.
* `eliminateLast` — Fourier–Motzkin elimination of the last variable.
* `feasible_eliminateLast_iff` — **the elimination preserves feasibility**, in both directions.

This is the elimination step underlying a decision procedure for rational linear feasibility, the
constructive content of Farkas' lemma; full decidability of an arbitrary system follows by
iterating elimination down to zero variables, a later development.

This module is **stable** and `sorry`-free. Depends on: `Mathlib.Data.Rat.Defs`,
`Mathlib.Data.Fin.Tuple.Basic`, `Mathlib.Algebra.BigOperators.Fin`,
`Mathlib.Algebra.Order.Field.Basic`, `Mathlib.Tactic.Linarith`, `Mathlib.Tactic.Ring`,
`Mathlib.Tactic.Positivity`.
-/

open scoped BigOperators

namespace CRNT

namespace RationalFarkas

/-- A single rational linear inequality `∑ⱼ coeff j * x j ≤ bound` in `n` variables. -/
structure Ineq (n : ℕ) where
  /-- The coefficient vector of the inequality. -/
  coeff : Fin n → ℚ
  /-- The right-hand bound. -/
  bound : ℚ

/-- The left-hand value `∑ⱼ coeff j * x j` of an inequality at a point. -/
def Ineq.lhs {n : ℕ} (I : Ineq n) (x : Fin n → ℚ) : ℚ :=
  ∑ j, I.coeff j * x j

/-- A point `x` satisfies an inequality when `coeff · x ≤ bound`. -/
def Ineq.holds {n : ℕ} (I : Ineq n) (x : Fin n → ℚ) : Prop :=
  I.lhs x ≤ I.bound

/-- A point satisfies a system (a list of inequalities) when it satisfies each one. -/
def Sat {n : ℕ} (sys : List (Ineq n)) (x : Fin n → ℚ) : Prop :=
  ∀ I ∈ sys, I.holds x

/-- A system is feasible when some point satisfies it. -/
def Feasible {n : ℕ} (sys : List (Ineq n)) : Prop :=
  ∃ x, Sat sys x

/-! ## Restricting and extending the eliminated variable

The eliminated variable is the last coordinate `Fin.last n`. `Fin.init` drops it; `Fin.snoc`
appends a chosen value back. -/

/-- The coefficient of the last variable in an inequality on `Fin (n + 1)`. -/
def Ineq.lastCoeff {n : ℕ} (I : Ineq (n + 1)) : ℚ :=
  I.coeff (Fin.last n)

/-- The inequality with its last variable dropped: coefficients restricted to `Fin n` and the same
bound. The dropped term `lastCoeff * y` is accounted for separately during elimination. -/
def Ineq.dropLast {n : ℕ} (I : Ineq (n + 1)) : Ineq n where
  coeff := Fin.init I.coeff
  bound := I.bound

/-- Splitting the left-hand sum off the last coordinate: `coeff · x = (initial part) + cₙ · xₙ`. -/
theorem Ineq.lhs_eq_dropLast_add {n : ℕ} (I : Ineq (n + 1)) (x : Fin (n + 1) → ℚ) :
    I.lhs x = I.dropLast.lhs (Fin.init x) + I.lastCoeff * x (Fin.last n) := by
  unfold Ineq.lhs Ineq.dropLast Ineq.lastCoeff Fin.init
  rw [Fin.sum_univ_castSucc]

/-! ## The Fourier–Motzkin combination of a lower/upper pair

For a lower-bound row `L` (last coefficient `< 0`) and an upper-bound row `U` (last coefficient
`> 0`), the combination `U.lastCoeff • L + (−L.lastCoeff) • U` has vanishing last coefficient. -/

/-- The division-free Fourier–Motzkin combination of a lower-bound inequality `lo` (intended
last coefficient negative) and an upper-bound inequality `hi` (intended last coefficient positive),
restricted to `Fin n`. Its coefficients are `hi.lastCoeff • lo.dropLast − lo.lastCoeff • hi.dropLast`
and its bound is `hi.lastCoeff * lo.bound − lo.lastCoeff * hi.bound`. -/
def combine {n : ℕ} (lo hi : Ineq (n + 1)) : Ineq n where
  coeff := fun j => hi.lastCoeff * lo.coeff (Fin.castSucc j)
      - lo.lastCoeff * hi.coeff (Fin.castSucc j)
  bound := hi.lastCoeff * lo.bound - lo.lastCoeff * hi.bound

/-- The left-hand value of a combination expands as the corresponding combination of the
restricted left-hand values. -/
theorem combine_lhs {n : ℕ} (lo hi : Ineq (n + 1)) (x : Fin n → ℚ) :
    (combine lo hi).lhs x
      = hi.lastCoeff * lo.dropLast.lhs x - lo.lastCoeff * hi.dropLast.lhs x := by
  simp only [combine, Ineq.lhs, Ineq.dropLast, Fin.init]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-! ## The eliminated system -/

/-- The inequalities whose last coefficient is zero, restricted to `Fin n`. -/
def zeroRows {n : ℕ} (sys : List (Ineq (n + 1))) : List (Ineq n) :=
  (sys.filter (fun I => I.lastCoeff = 0)).map Ineq.dropLast

/-- The lower-bound rows (negative last coefficient). -/
def loRows {n : ℕ} (sys : List (Ineq (n + 1))) : List (Ineq (n + 1)) :=
  sys.filter (fun I => I.lastCoeff < 0)

/-- The upper-bound rows (positive last coefficient). -/
def hiRows {n : ℕ} (sys : List (Ineq (n + 1))) : List (Ineq (n + 1)) :=
  sys.filter (fun I => 0 < I.lastCoeff)

/-- The pairwise combinations of each lower-bound row with each upper-bound row. -/
def comboRows {n : ℕ} (sys : List (Ineq (n + 1))) : List (Ineq n) :=
  (loRows sys).flatMap fun lo => (hiRows sys).map fun hi => combine lo hi

/-- **Fourier–Motzkin elimination of the last variable.** The eliminated system in `n` variables
consists of the zero-coefficient rows together with every lower/upper combination row. -/
def eliminateLast {n : ℕ} (sys : List (Ineq (n + 1))) : List (Ineq n) :=
  zeroRows sys ++ comboRows sys

/-! ## Forward direction: a solution projects -/

/-- If `x` satisfies the original system, its restriction `Fin.init x` satisfies the eliminated
system. -/
theorem sat_eliminateLast_of_sat {n : ℕ} {sys : List (Ineq (n + 1))} {x : Fin (n + 1) → ℚ}
    (hx : Sat sys x) : Sat (eliminateLast sys) (Fin.init x) := by
  intro J hJ
  rw [eliminateLast, List.mem_append] at hJ
  rcases hJ with hJ | hJ
  · -- zero rows: directly the dropped inequality, with vanishing last term
    rw [zeroRows, List.mem_map] at hJ
    obtain ⟨I, hI, rfl⟩ := hJ
    rw [List.mem_filter] at hI
    obtain ⟨hImem, hzero⟩ := hI
    have hI := hx I hImem
    have hsplit := I.lhs_eq_dropLast_add x
    simp only [decide_eq_true_eq] at hzero
    rw [hzero, zero_mul, add_zero] at hsplit
    rw [Ineq.holds, ← hsplit]
    exact hI
  · -- combination rows: positive combination of two satisfied inequalities
    rw [comboRows, List.mem_flatMap] at hJ
    obtain ⟨lo, hlo, hJ⟩ := hJ
    rw [List.mem_map] at hJ
    obtain ⟨hi, hhi, rfl⟩ := hJ
    rw [loRows, List.mem_filter] at hlo
    obtain ⟨hlomem, hloneg⟩ := hlo
    rw [hiRows, List.mem_filter] at hhi
    obtain ⟨himem, hhipos⟩ := hhi
    simp only [decide_eq_true_eq] at hloneg hhipos
    -- the two satisfied inequalities
    have hLo := hx lo hlomem
    have hHi := hx hi himem
    rw [Ineq.holds, lo.lhs_eq_dropLast_add x] at hLo
    rw [Ineq.holds, hi.lhs_eq_dropLast_add x] at hHi
    -- scale and add: the last-variable terms cancel
    rw [Ineq.holds, combine_lhs]
    show _ ≤ hi.lastCoeff * lo.bound - lo.lastCoeff * hi.bound
    have e1 : hi.lastCoeff * (lo.dropLast.lhs (Fin.init x) + lo.lastCoeff * x (Fin.last n))
        ≤ hi.lastCoeff * lo.bound :=
      mul_le_mul_of_nonneg_left hLo (le_of_lt hhipos)
    have e2 : (-lo.lastCoeff) * (hi.dropLast.lhs (Fin.init x) + hi.lastCoeff * x (Fin.last n))
        ≤ (-lo.lastCoeff) * hi.bound :=
      mul_le_mul_of_nonneg_left hHi (by linarith)
    nlinarith [e1, e2]

/-! ## Reverse direction: a solution extends

A solution of the eliminated system extends to a solution of the original by choosing the last
variable between the largest lower bound and the smallest upper bound. The combination rows force
that interval to be nonempty. -/

/-- For a single inequality on `Fin (n + 1)`, satisfaction of the original by `Fin.snoc x y`
splits into the restricted left-hand value plus `lastCoeff * y`. -/
theorem holds_snoc_iff {n : ℕ} (I : Ineq (n + 1)) (x : Fin n → ℚ) (y : ℚ) :
    I.holds (Fin.snoc x y) ↔ I.dropLast.lhs x + I.lastCoeff * y ≤ I.bound := by
  rw [Ineq.holds, I.lhs_eq_dropLast_add (Fin.snoc x y)]
  rw [Fin.init_snoc, Fin.snoc_last]

/-- The per-row threshold that the last variable must satisfy, given the restricted point `x`:
for a positive last coefficient this is the upper bound `(bound − rest · x) / lastCoeff`. -/
def upperThreshold {n : ℕ} (I : Ineq (n + 1)) (x : Fin n → ℚ) : ℚ :=
  (I.bound - I.dropLast.lhs x) / I.lastCoeff

/-- The per-row lower threshold, for a negative last coefficient. -/
def lowerThreshold {n : ℕ} (I : Ineq (n + 1)) (x : Fin n → ℚ) : ℚ :=
  (I.bound - I.dropLast.lhs x) / I.lastCoeff

/-- For an upper-bound row (`0 < lastCoeff`), the row holds at `Fin.snoc x y` iff `y` is at most its
upper threshold. -/
theorem holds_snoc_iff_le_upper {n : ℕ} (I : Ineq (n + 1)) (hpos : 0 < I.lastCoeff)
    (x : Fin n → ℚ) (y : ℚ) :
    I.holds (Fin.snoc x y) ↔ y ≤ upperThreshold I x := by
  rw [holds_snoc_iff, upperThreshold, le_div_iff₀ hpos]
  constructor <;> intro h <;> nlinarith [h]

/-- For a lower-bound row (`lastCoeff < 0`), the row holds at `Fin.snoc x y` iff `y` is at least its
lower threshold. -/
theorem holds_snoc_iff_ge_lower {n : ℕ} (I : Ineq (n + 1)) (hneg : I.lastCoeff < 0)
    (x : Fin n → ℚ) (y : ℚ) :
    I.holds (Fin.snoc x y) ↔ lowerThreshold I x ≤ y := by
  rw [holds_snoc_iff, lowerThreshold, div_le_iff_of_neg hneg]
  constructor <;> intro h <;> nlinarith [h]

/-- Every lower threshold is at most every upper threshold, when `x` satisfies all combination rows.
This is the geometric content that makes the candidate interval for the last variable nonempty. -/
theorem lower_le_upper {n : ℕ} {sys : List (Ineq (n + 1))} {x : Fin n → ℚ}
    (hx : Sat (comboRows sys) x)
    {lo hi : Ineq (n + 1)} (hlo : lo ∈ loRows sys) (hhi : hi ∈ hiRows sys) :
    lowerThreshold lo x ≤ upperThreshold hi x := by
  -- the combination row of this pair is in `comboRows sys` and is satisfied
  have hmem : combine lo hi ∈ comboRows sys := by
    rw [comboRows, List.mem_flatMap]
    exact ⟨lo, hlo, List.mem_map.2 ⟨hi, hhi, rfl⟩⟩
  have hsat := hx (combine lo hi) hmem
  have hloneg : lo.lastCoeff < 0 := by
    rw [loRows, List.mem_filter] at hlo
    simpa using hlo.2
  have hhipos : 0 < hi.lastCoeff := by
    rw [hiRows, List.mem_filter] at hhi
    simpa using hhi.2
  rw [Ineq.holds, combine_lhs] at hsat
  change _ ≤ hi.lastCoeff * lo.bound - lo.lastCoeff * hi.bound at hsat
  rw [lowerThreshold, upperThreshold, div_le_iff_of_neg hloneg, div_mul_eq_mul_div,
    div_le_iff₀ hhipos]
  nlinarith [hsat]


/-- Folding `max` over a list (seeded at `init`) lands at or above every element and the seed. -/
theorem le_foldr_max (init : ℚ) (l : List ℚ) (a : ℚ) (ha : a = init ∨ a ∈ l) :
    a ≤ l.foldr max init := by
  induction l with
  | nil =>
    rcases ha with rfl | ha
    · simp
    · exact absurd ha (List.not_mem_nil)
  | cons b bs ih =>
    simp only [List.foldr, List.mem_cons] at ha ⊢
    rcases ha with rfl | rfl | ha
    · exact le_trans (ih (Or.inl rfl)) (le_max_right _ _)
    · exact le_max_left _ _
    · exact le_trans (ih (Or.inr ha)) (le_max_right _ _)

/-- If a bound `u` dominates the seed and every element, it dominates the `max`-fold. -/
theorem foldr_max_le (init : ℚ) (l : List ℚ) (u : ℚ)
    (hinit : init ≤ u) (hl : ∀ a ∈ l, a ≤ u) : l.foldr max init ≤ u := by
  induction l with
  | nil => simpa using hinit
  | cons b bs ih =>
    simp only [List.foldr]
    exact max_le (hl b (by simp)) (ih (fun a ha => hl a (by simp [ha])))

/-- Folding `min` over a list (seeded at `init`) lands at or below every element and the seed. -/
theorem foldr_min_le (init : ℚ) (l : List ℚ) (a : ℚ) (ha : a = init ∨ a ∈ l) :
    l.foldr min init ≤ a := by
  induction l with
  | nil =>
    rcases ha with rfl | ha
    · simp
    · exact absurd ha (List.not_mem_nil)
  | cons b bs ih =>
    simp only [List.foldr, List.mem_cons] at ha ⊢
    rcases ha with rfl | rfl | ha
    · exact le_trans (min_le_right _ _) (ih (Or.inl rfl))
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih (Or.inr ha))

/-- **List interpolation.** Given finite lists `los`, `his` of rationals such that every element of
`los` is at most every element of `his`, there is a single rational `y` lying above all of `los`
and below all of `his`. This packages the nonempty intersection of finitely many lower and upper
bounds and is the combinatorial core of extending an eliminated solution. -/
theorem exists_between_lists (los his : List ℚ)
    (h : ∀ l ∈ los, ∀ u ∈ his, l ≤ u) :
    ∃ y, (∀ l ∈ los, l ≤ y) ∧ (∀ u ∈ his, y ≤ u) := by
  cases los with
  | nil =>
    -- no lower bounds: any single point works; use the min of the uppers (or `0`).
    cases his with
    | nil => exact ⟨0, by simp, by simp⟩
    | cons u us =>
      exact ⟨us.foldr min u, by simp, fun a ha => foldr_min_le u us a (by
        simpa [List.mem_cons] using ha)⟩
  | cons l ls =>
    -- some lower bound exists: the maximum lower bound is below every upper bound.
    refine ⟨ls.foldr max l, fun a ha => le_foldr_max l ls a ?_, fun u hu => ?_⟩
    · simpa [List.mem_cons] using ha
    · exact foldr_max_le l ls u (h l (by simp) u hu) (fun a ha => h a (by simp [ha]) u hu)

/-- If `x` satisfies the eliminated system, it extends to a solution `Fin.snoc x y` of the original
system: choose the last variable `y` between the largest lower bound and the smallest upper bound.
The combination rows of the eliminated system guarantee this interval is nonempty. -/
theorem exists_snoc_sat_of_sat_eliminateLast {n : ℕ} {sys : List (Ineq (n + 1))} {x : Fin n → ℚ}
    (hx : Sat (eliminateLast sys) x) : ∃ y, Sat sys (Fin.snoc x y) := by
  -- split the eliminated-system satisfaction into its zero-row and combination-row parts
  have hzero : Sat (zeroRows sys) x := fun I hI => hx I (by
    rw [eliminateLast, List.mem_append]; exact Or.inl hI)
  have hcombo : Sat (comboRows sys) x := fun I hI => hx I (by
    rw [eliminateLast, List.mem_append]; exact Or.inr hI)
  -- the lower thresholds sit below the upper thresholds, pairwise
  obtain ⟨y, hylo, hyhi⟩ := exists_between_lists
    ((loRows sys).map (fun I => lowerThreshold I x))
    ((hiRows sys).map (fun I => upperThreshold I x)) (by
      intro l hl u hu
      rw [List.mem_map] at hl hu
      obtain ⟨lo, hlo, rfl⟩ := hl
      obtain ⟨hi, hhi, rfl⟩ := hu
      exact lower_le_upper hcombo hlo hhi)
  refine ⟨y, fun I hI => ?_⟩
  -- classify `I` by the sign of its last coefficient
  rcases lt_trichotomy I.lastCoeff 0 with hneg | hzeroc | hpos
  · -- lower-bound row
    rw [holds_snoc_iff_ge_lower I hneg]
    refine hylo (lowerThreshold I x) (List.mem_map.2 ⟨I, ?_, rfl⟩)
    rw [loRows, List.mem_filter]; exact ⟨hI, by simpa using hneg⟩
  · -- zero row: the dropped inequality is in `zeroRows sys`
    rw [holds_snoc_iff, hzeroc, zero_mul, add_zero]
    have : I.dropLast ∈ zeroRows sys :=
      List.mem_map.2 ⟨I, by rw [List.mem_filter]; exact ⟨hI, by simpa using hzeroc⟩, rfl⟩
    exact hzero I.dropLast this
  · -- upper-bound row
    rw [holds_snoc_iff_le_upper I hpos]
    refine hyhi (upperThreshold I x) (List.mem_map.2 ⟨I, ?_, rfl⟩)
    rw [hiRows, List.mem_filter]; exact ⟨hI, by simpa using hpos⟩

/-- **Fourier–Motzkin elimination preserves feasibility.** The eliminated system in `n` variables is
feasible if and only if the original system in `n + 1` variables is. This is the soundness and
completeness of one elimination step, the constructive content of Farkas' lemma for rational linear
inequalities. -/
theorem feasible_eliminateLast_iff {n : ℕ} (sys : List (Ineq (n + 1))) :
    Feasible (eliminateLast sys) ↔ Feasible sys := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := exists_snoc_sat_of_sat_eliminateLast hx
    exact ⟨Fin.snoc x y, hy⟩
  · rintro ⟨x, hx⟩
    exact ⟨Fin.init x, sat_eliminateLast_of_sat hx⟩

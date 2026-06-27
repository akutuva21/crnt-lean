import CRNT.Decision.RationalFarkas

/-!
# Strict-inequality Fourier–Motzkin elimination over the rationals

A finite rational linear system in `n` variables `x : Fin n → ℚ` is a list of inequalities; the
*strict* reading asks for `∑ⱼ aᵢⱼ xⱼ < bᵢ` on every row. This module is the strict-inequality variant
of `CRNT.RationalFarkas`: it eliminates one variable and proves the elimination preserves *strict*
feasibility, then decides strict feasibility by recursion down to zero variables.

Strict feasibility is the form needed by the homogeneous strict-support alternatives — Stiemke's and
Gordan's theorems — that govern the critical-siphon strict-support clause: a strict linear system is
feasible exactly when the dual system has no nonnegative annihilating combination.

The elimination reuses the division-free Fourier–Motzkin combination of `CRNT.RationalFarkas`. The
only change from the non-strict development is that the combined row of a lower/upper pair must hold
*strictly*, and the candidate interval for the eliminated variable must be *open* (`lower < upper`,
not `≤`): a value strictly between the largest lower threshold and the smallest upper threshold then
exists by density of `ℚ` (`exists_between`).

* `Ineq.holdsStrict` — a point satisfies one inequality strictly, `coeff · x < bound`.
* `SatStrict` / `FeasibleStrict` — a point satisfies a system strictly; a system is strictly feasible.
* `feasibleStrict_eliminateLast_iff` — **the elimination preserves strict feasibility**, both ways.
* `feasibleStrict_zero_iff` — a `Fin 0` system is strictly feasible iff every bound is positive.
* `decidableFeasibleStrict` — `Decidable (FeasibleStrict sys)` for every `n`, by recursion on `n`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Decision.RationalFarkas`.
-/

open scoped BigOperators

namespace CRNT

namespace RationalFarkas

/-- A point `x` satisfies an inequality *strictly* when `coeff · x < bound`. -/
def Ineq.holdsStrict {n : ℕ} (I : Ineq n) (x : Fin n → ℚ) : Prop :=
  I.lhs x < I.bound

/-- A point satisfies a system *strictly* when it satisfies each inequality strictly. -/
def SatStrict {n : ℕ} (sys : List (Ineq n)) (x : Fin n → ℚ) : Prop :=
  ∀ I ∈ sys, I.holdsStrict x

/-- A system is *strictly feasible* when some point satisfies it strictly. -/
def FeasibleStrict {n : ℕ} (sys : List (Ineq n)) : Prop :=
  ∃ x, SatStrict sys x

/-! ## Forward direction: a strict solution projects -/

/-- If `x` satisfies the original system strictly, its restriction `Fin.init x` satisfies the
eliminated system strictly. The combination row of a lower/upper pair is a positive combination of
two strictly satisfied inequalities, hence strict. -/
theorem satStrict_eliminateLast_of_satStrict {n : ℕ} {sys : List (Ineq (n + 1))}
    {x : Fin (n + 1) → ℚ} (hx : SatStrict sys x) :
    SatStrict (eliminateLast sys) (Fin.init x) := by
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
    rw [Ineq.holdsStrict, ← hsplit]
    exact hI
  · -- combination rows: positive combination of two strictly satisfied inequalities
    rw [comboRows, List.mem_flatMap] at hJ
    obtain ⟨lo, hlo, hJ⟩ := hJ
    rw [List.mem_map] at hJ
    obtain ⟨hi, hhi, rfl⟩ := hJ
    rw [loRows, List.mem_filter] at hlo
    obtain ⟨hlomem, hloneg⟩ := hlo
    rw [hiRows, List.mem_filter] at hhi
    obtain ⟨himem, hhipos⟩ := hhi
    simp only [decide_eq_true_eq] at hloneg hhipos
    have hLo := hx lo hlomem
    have hHi := hx hi himem
    rw [Ineq.holdsStrict, lo.lhs_eq_dropLast_add x] at hLo
    rw [Ineq.holdsStrict, hi.lhs_eq_dropLast_add x] at hHi
    rw [Ineq.holdsStrict, combine_lhs]
    show _ < hi.lastCoeff * lo.bound - lo.lastCoeff * hi.bound
    have e1 : hi.lastCoeff * (lo.dropLast.lhs (Fin.init x) + lo.lastCoeff * x (Fin.last n))
        < hi.lastCoeff * lo.bound :=
      mul_lt_mul_of_pos_left hLo hhipos
    have e2 : (-lo.lastCoeff) * (hi.dropLast.lhs (Fin.init x) + hi.lastCoeff * x (Fin.last n))
        < (-lo.lastCoeff) * hi.bound :=
      mul_lt_mul_of_pos_left hHi (by linarith)
    nlinarith [e1, e2]

/-! ## Reverse direction: a strict solution extends

A strict solution of the eliminated system extends to a strict solution of the original by choosing
the last variable strictly between the largest lower threshold and the smallest upper threshold. The
strictly satisfied combination rows force that *open* interval to be nonempty. -/

/-- For an upper-bound row (`0 < lastCoeff`), the row holds strictly at `Fin.snoc x y` iff `y` is
strictly below its upper threshold. -/
theorem holdsStrict_snoc_iff_lt_upper {n : ℕ} (I : Ineq (n + 1)) (hpos : 0 < I.lastCoeff)
    (x : Fin n → ℚ) (y : ℚ) :
    I.holdsStrict (Fin.snoc x y) ↔ y < upperThreshold I x := by
  rw [Ineq.holdsStrict, I.lhs_eq_dropLast_add (Fin.snoc x y), Fin.init_snoc, Fin.snoc_last,
    upperThreshold, lt_div_iff₀ hpos]
  constructor <;> intro h <;> nlinarith [h]

/-- For a lower-bound row (`lastCoeff < 0`), the row holds strictly at `Fin.snoc x y` iff `y` is
strictly above its lower threshold. -/
theorem holdsStrict_snoc_iff_gt_lower {n : ℕ} (I : Ineq (n + 1)) (hneg : I.lastCoeff < 0)
    (x : Fin n → ℚ) (y : ℚ) :
    I.holdsStrict (Fin.snoc x y) ↔ lowerThreshold I x < y := by
  rw [Ineq.holdsStrict, I.lhs_eq_dropLast_add (Fin.snoc x y), Fin.init_snoc, Fin.snoc_last,
    lowerThreshold, div_lt_iff_of_neg hneg]
  constructor <;> intro h <;> nlinarith [h]

/-- Every lower threshold is *strictly* below every upper threshold, when `x` satisfies all
combination rows strictly. This is the open-interval content that makes the candidate interval for
the last variable a nonempty open interval. -/
theorem lower_lt_upper {n : ℕ} {sys : List (Ineq (n + 1))} {x : Fin n → ℚ}
    (hx : SatStrict (comboRows sys) x)
    {lo hi : Ineq (n + 1)} (hlo : lo ∈ loRows sys) (hhi : hi ∈ hiRows sys) :
    lowerThreshold lo x < upperThreshold hi x := by
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
  rw [Ineq.holdsStrict, combine_lhs] at hsat
  change _ < hi.lastCoeff * lo.bound - lo.lastCoeff * hi.bound at hsat
  rw [lowerThreshold, upperThreshold, div_lt_iff_of_neg hloneg, div_mul_eq_mul_div,
    div_lt_iff₀ hhipos]
  nlinarith [hsat]

/-- The `max`-fold of a nonempty list (seed `init`, tail `l`) is one of its elements: either the
seed or an element of the tail. -/
theorem foldr_max_mem (init : ℚ) (l : List ℚ) : l.foldr max init = init ∨ l.foldr max init ∈ l := by
  induction l with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    simp only [List.foldr]
    rcases max_choice b (bs.foldr max init) with h | h
    · rw [h]; exact Or.inr (List.mem_cons_self)
    · rw [h]
      rcases ih with hi | hi
      · exact Or.inl hi
      · exact Or.inr (List.mem_cons_of_mem _ hi)

/-- The `min`-fold of a nonempty list (seed `init`, tail `l`) is one of its elements: either the
seed or an element of the tail. -/
theorem foldr_min_mem (init : ℚ) (l : List ℚ) : l.foldr min init = init ∨ l.foldr min init ∈ l := by
  induction l with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    simp only [List.foldr]
    rcases min_choice b (bs.foldr min init) with h | h
    · rw [h]; exact Or.inr (List.mem_cons_self)
    · rw [h]
      rcases ih with hi | hi
      · exact Or.inl hi
      · exact Or.inr (List.mem_cons_of_mem _ hi)

/-- **Open-interval list interpolation.** Given finite lists `los`, `his` of rationals such that
every element of `los` is *strictly* below every element of `his`, there is a single rational `y`
lying strictly above all of `los` and strictly below all of `his`. This packages the nonempty
*open* intersection of finitely many strict lower and upper bounds, the combinatorial core of
extending an eliminated strict solution; density of `ℚ` (`exists_between`) supplies the interior
point of an open interval. -/
theorem exists_strictBetween_lists (los his : List ℚ)
    (h : ∀ l ∈ los, ∀ u ∈ his, l < u) :
    ∃ y, (∀ l ∈ los, l < y) ∧ (∀ u ∈ his, y < u) := by
  cases los with
  | nil =>
    cases his with
    | nil => exact ⟨0, by simp, by simp⟩
    | cons u us =>
      -- no lower bounds: sit strictly below the smallest upper bound
      refine ⟨us.foldr min u - 1, by simp, fun a ha => ?_⟩
      have : us.foldr min u ≤ a :=
        foldr_min_le u us a (by simpa [List.mem_cons] using ha)
      linarith
  | cons l ls =>
    cases his with
    | nil =>
      -- no upper bounds: sit strictly above the largest lower bound
      refine ⟨ls.foldr max l + 1, fun a ha => ?_, by simp⟩
      have : a ≤ ls.foldr max l :=
        le_foldr_max l ls a (by simpa [List.mem_cons] using ha)
      linarith
    | cons u us =>
      -- the largest lower bound is strictly below the smallest upper bound
      set lo := ls.foldr max l with hlodef
      set hi := us.foldr min u with hhidef
      have hgap : lo < hi := by
        -- realize `lo` as an element of `l :: ls` and `hi` as an element of `u :: us`
        have hlomemList : lo ∈ l :: ls := by
          rcases foldr_max_mem l ls with hc | hc
          · rw [hlodef, hc]; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ hc
        have hhimemList : hi ∈ u :: us := by
          rcases foldr_min_mem u us with hc | hc
          · rw [hhidef, hc]; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ hc
        exact h lo hlomemList hi hhimemList
      obtain ⟨y, hy1, hy2⟩ := exists_between hgap
      refine ⟨y, fun a ha => ?_, fun b hb => ?_⟩
      · have : a ≤ lo := le_foldr_max l ls a (by simpa [List.mem_cons] using ha)
        linarith
      · have : hi ≤ b := foldr_min_le u us b (by simpa [List.mem_cons] using hb)
        linarith

/-- If `x` satisfies the eliminated system strictly, it extends to a strict solution `Fin.snoc x y`
of the original system: choose the last variable `y` strictly between the largest lower threshold and
the smallest upper threshold. The strictly satisfied combination rows guarantee this open interval is
nonempty. -/
theorem exists_snoc_satStrict_of_satStrict_eliminateLast {n : ℕ} {sys : List (Ineq (n + 1))}
    {x : Fin n → ℚ} (hx : SatStrict (eliminateLast sys) x) : ∃ y, SatStrict sys (Fin.snoc x y) := by
  have hzero : SatStrict (zeroRows sys) x := fun I hI => hx I (by
    rw [eliminateLast, List.mem_append]; exact Or.inl hI)
  have hcombo : SatStrict (comboRows sys) x := fun I hI => hx I (by
    rw [eliminateLast, List.mem_append]; exact Or.inr hI)
  obtain ⟨y, hylo, hyhi⟩ := exists_strictBetween_lists
    ((loRows sys).map (fun I => lowerThreshold I x))
    ((hiRows sys).map (fun I => upperThreshold I x)) (by
      intro l hl u hu
      rw [List.mem_map] at hl hu
      obtain ⟨lo, hlo, rfl⟩ := hl
      obtain ⟨hi, hhi, rfl⟩ := hu
      exact lower_lt_upper hcombo hlo hhi)
  refine ⟨y, fun I hI => ?_⟩
  rcases lt_trichotomy I.lastCoeff 0 with hneg | hzeroc | hpos
  · rw [holdsStrict_snoc_iff_gt_lower I hneg]
    refine hylo (lowerThreshold I x) (List.mem_map.2 ⟨I, ?_, rfl⟩)
    rw [loRows, List.mem_filter]; exact ⟨hI, by simpa using hneg⟩
  · rw [Ineq.holdsStrict, I.lhs_eq_dropLast_add (Fin.snoc x y), Fin.init_snoc, Fin.snoc_last,
      hzeroc, zero_mul, add_zero]
    have : I.dropLast ∈ zeroRows sys :=
      List.mem_map.2 ⟨I, by rw [List.mem_filter]; exact ⟨hI, by simpa using hzeroc⟩, rfl⟩
    exact hzero I.dropLast this
  · rw [holdsStrict_snoc_iff_lt_upper I hpos]
    refine hyhi (upperThreshold I x) (List.mem_map.2 ⟨I, ?_, rfl⟩)
    rw [hiRows, List.mem_filter]; exact ⟨hI, by simpa using hpos⟩

/-- **Fourier–Motzkin elimination preserves strict feasibility.** The eliminated system in `n`
variables is strictly feasible iff the original system in `n + 1` variables is. This is the soundness
and completeness of one strict-elimination step, the constructive content of the strict alternatives
of Stiemke and Gordan for rational linear inequalities. -/
theorem feasibleStrict_eliminateLast_iff {n : ℕ} (sys : List (Ineq (n + 1))) :
    FeasibleStrict (eliminateLast sys) ↔ FeasibleStrict sys := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := exists_snoc_satStrict_of_satStrict_eliminateLast hx
    exact ⟨Fin.snoc x y, hy⟩
  · rintro ⟨x, hx⟩
    exact ⟨Fin.init x, satStrict_eliminateLast_of_satStrict hx⟩

/-! ## Base case and the decision procedure -/

/-- In zero variables every left-hand sum is the empty sum `0`, so a row holds strictly at any point
iff its bound is positive. -/
theorem holdsStrict_zero_iff (I : Ineq 0) (x : Fin 0 → ℚ) : I.holdsStrict x ↔ 0 < I.bound := by
  rw [Ineq.holdsStrict, Ineq.lhs, Fin.sum_univ_zero]

/-- **Base case of the strict decision procedure.** A `Fin 0` system is strictly feasible iff every
row's bound is positive. The unique point `0 : Fin 0 → ℚ` witnesses strict feasibility when the
condition holds. -/
theorem feasibleStrict_zero_iff (sys : List (Ineq 0)) :
    FeasibleStrict sys ↔ ∀ row ∈ sys, 0 < row.bound := by
  constructor
  · rintro ⟨x, hx⟩ row hrow
    exact (holdsStrict_zero_iff row x).1 (hx row hrow)
  · intro h
    refine ⟨0, fun I hI => ?_⟩
    exact (holdsStrict_zero_iff I 0).2 (h I hI)

/-- Strict feasibility of a `Fin 0` system is decidable: it reduces to the positivity of every
bound. -/
instance decidableFeasibleStrictZero (sys : List (Ineq 0)) : Decidable (FeasibleStrict sys) :=
  decidable_of_iff _ (feasibleStrict_zero_iff sys).symm

/-- **Decision procedure for strict rational linear feasibility.** `FeasibleStrict sys` is decidable
for every number of variables `n` and every system `sys : List (Ineq n)`. The recursion eliminates
the last variable via `feasibleStrict_eliminateLast_iff` down to the `Fin 0` base case, the
computational content of the strict alternatives of Stiemke and Gordan by Fourier–Motzkin
elimination. -/
instance decidableFeasibleStrict : ∀ {n : ℕ} (sys : List (Ineq n)), Decidable (FeasibleStrict sys)
  | 0, sys => decidableFeasibleStrictZero sys
  | _ + 1, sys =>
    have : Decidable (FeasibleStrict (eliminateLast sys)) := decidableFeasibleStrict (eliminateLast sys)
    decidable_of_iff _ (feasibleStrict_eliminateLast_iff sys)

end RationalFarkas

end CRNT

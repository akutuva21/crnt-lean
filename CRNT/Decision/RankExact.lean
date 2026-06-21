import CRNT.Decision.Rank

/-!
# A computable stoichiometric-rank lower bound

The stoichiometric rank `s = finrank ℝ stoichSubspace` and Mathlib's matrix rank are
noncomputable. `CRNT.Decision.Rank` provides a one-sided *minor certificate*: a square
selection of `k` reactions and `k` species whose rational stoichiometric minor has nonzero
determinant witnesses `k ≤ s`. That certificate takes the selection as an explicit input.

This module turns the certificate into an automatic search. `HasMinorRankGe N k` asserts the
existence of some such `k × k` nonsingular minor; it is decidable because the selecting
functions range over finite types carrying the computable `Pi.instFintype`, and nonzero
rational determinant is decidable. `computeStoichRankLB` is then the largest `k ≤ card S` for
which `HasMinorRankGe N k` holds, a *computable* lower bound on `s` with a verified
`computeStoichRankLB ≤ stoichRank` correctness theorem. A full-size bound discharges
`DeficiencyZero`.

The matching upper bound `stoichRank ≤ computeStoichRankLB` (which would make the bound an
exact computable rank) is not provided: it requires the theorem that a matrix rank equals the
maximal size of a square submatrix with nonzero determinant, which Mathlib lacks. These
one-sided bounds are what the structural deficiency-zero theory consumes.

This module is **stable**. Depends on: `CRNT.Decision.Rank`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **There exists a nonsingular `k × k` rational stoichiometric minor.** Selecting `k`
reactions `f` and `k` species `σ`, the `k × k` matrix of rational reaction-vector entries
`target - source` has nonzero determinant for some such selection. This is the searchable
form of the minor certificate `stoichRank_ge_of_det_ne_zero`. -/
def HasMinorRankGe (N : Network S) (k : ℕ) : Prop :=
  ∃ (f : Fin k → N.R) (σ : Fin k → S),
    (Matrix.of fun i j : Fin k =>
        ((N.reaction (f j)).target (σ i) : ℚ) - ((N.reaction (f j)).source (σ i) : ℚ)).det ≠ 0

/-- `HasMinorRankGe N k` is decidable: the selecting functions `Fin k → N.R` and `Fin k → S`
range over finite types (the computable `Pi.instFintype`), and a nonzero rational determinant
is decidable from `DecidableEq ℚ`. -/
instance decidableHasMinorRankGe (N : Network S) (k : ℕ) :
    Decidable (N.HasMinorRankGe k) := by
  unfold HasMinorRankGe
  infer_instance

/-- The empty `0 × 0` minor has determinant `1 ≠ 0`, so every network has a rank `≥ 0`
certificate. -/
theorem hasMinorRankGe_zero (N : Network S) : N.HasMinorRankGe 0 :=
  ⟨Fin.elim0, Fin.elim0, by simp [Matrix.det_fin_zero]⟩

/-- **A `HasMinorRankGe k` certificate bounds the stoichiometric rank below.** -/
theorem stoichRank_ge_of_hasMinorRankGe (N : Network S) {k : ℕ}
    (h : N.HasMinorRankGe k) : k ≤ N.stoichRank := by
  obtain ⟨f, σ, hdet⟩ := h
  exact N.stoichRank_ge_of_det_ne_zero f σ hdet

/-- **A computable lower bound on the stoichiometric rank.** The largest `k ≤ card S` admitting
a nonsingular `k × k` rational stoichiometric minor. It reduces by `decide`/`#eval`. -/
def computeStoichRankLB (N : Network S) : ℕ :=
  Nat.findGreatest N.HasMinorRankGe (Fintype.card S)

/-- **The computable lower bound is a genuine lower bound on the stoichiometric rank.** -/
theorem computeStoichRankLB_le_stoichRank (N : Network S) :
    N.computeStoichRankLB ≤ N.stoichRank :=
  N.stoichRank_ge_of_hasMinorRankGe
    (Nat.findGreatest_spec (Nat.zero_le _) N.hasMinorRankGe_zero)

/-- **A full-size computable lower bound forces deficiency zero.** If `n ≤ s_LB + ℓ` then,
since `s_LB ≤ s ≤ n − ℓ`, the deficiency `δ = n − ℓ − s` is zero. -/
theorem deficiencyZero_of_computeStoichRankLB (N : Network S)
    (hk : N.numComplexes ≤ N.computeStoichRankLB + N.numLinkageClasses) : N.DeficiencyZero := by
  apply N.deficiencyZero_of_numComplexes_le
  have := N.computeStoichRankLB_le_stoichRank
  omega

end Network

/-! ## Worked example: the irreversible reaction `X → Y` -/

namespace RankExactExample

/-- Two species `X` and `Y`, indexed by `Fin 2` (`0 = X`, `1 = Y`). -/
abbrev Species := Fin 2

/-- The complex `X`. -/
def cX : Complex Species := fun s => if s = 0 then 1 else 0

/-- The complex `Y`. -/
def cY : Complex Species := fun s => if s = 1 then 1 else 0

/-- One reaction channel, the irreversible `X → Y`. -/
abbrev Rxn := Fin 1

/-- The reaction map: the single channel is `X → Y`. -/
def rxn : Rxn → Reaction Species := fun _ => { source := cX, target := cY }

/-- The network `X → Y`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- The `1 × 1` minor on reaction `0` and species `0` has determinant
`target(X) − source(X) = 0 − 1 = -1 ≠ 0`, so `HasMinorRankGe N 1` holds. -/
theorem hasMinorRankGe_one : N.HasMinorRankGe 1 :=
  ⟨fun _ => (0 : Fin 1), fun _ => 0, by
    rw [Matrix.det_fin_one]
    simp [N, rxn, cX, cY]⟩

/-- No `2 × 2` minor is nonsingular: the network has a single reaction channel, so both
columns of any `2 × 2` minor are equal and the determinant vanishes. -/
theorem not_hasMinorRankGe_two : ¬ N.HasMinorRankGe 2 := by
  rintro ⟨f, σ, hdet⟩
  apply hdet
  refine Matrix.det_zero_of_column_eq (i := 0) (j := 1) (by decide) ?_
  intro k
  have hf : f 0 = f 1 := @Subsingleton.elim (Fin 1) _ (f 0) (f 1)
  simp [Matrix.of_apply, hf]

/-- The single reaction vector is `(-1, +1)`, so the largest nonsingular rational minor is
`1 × 1`. The computable lower bound is therefore `1`, matching the true stoichiometric rank. -/
example : N.computeStoichRankLB = 1 := by
  rw [Network.computeStoichRankLB, show Fintype.card Species = 2 from rfl]
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by norm_num, fun _ => hasMinorRankGe_one, ?_⟩
  intro n h1 h2
  interval_cases n
  exact not_hasMinorRankGe_two

end RankExactExample

end CRNT

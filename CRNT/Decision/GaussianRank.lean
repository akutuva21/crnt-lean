import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Computable matrix rank over `ℚ` via nonsingular minors

Mathlib's `Matrix.rank` is noncomputable, Mathlib carries no row-reduction / pivot
infrastructure, and Mathlib has no theorem identifying the rank with the maximal size of a
square submatrix of nonzero determinant. This module supplies a *computable* rank over `ℚ` and
proves it equals `Matrix.rank`.

For a matrix `A : Matrix m n ℚ` over finite, decidable index types:

* `HasNonsingularMinor A k : Prop` — there is a `k × k` submatrix of `A` (selected by index maps
  `r : Fin k → m`, `c : Fin k → n`) with nonzero determinant. It is `Decidable`: the selecting
  functions range over finite Pi types and `DecidableEq ℚ` decides `det ≠ 0`.
* `computeRank A : ℕ` — `Nat.findGreatest (HasNonsingularMinor A) (min (card m) (card n))`, the
  largest minor size that is nonsingular; it reduces by `decide`/`#eval`.

The correctness theorem is the two-sided

* `computeRank_eq_rank : computeRank A = A.rank`,

with the equivalent pointwise form `le_rank_iff_hasNonsingularMinor : k ≤ A.rank ↔
HasNonsingularMinor A k`. Its two halves are:

* `hasNonsingularMinor_le_rank`: a nonsingular `k × k` minor has linearly independent columns, so
  `k ≤ A.rank`.
* `exists_nonsingularMinor_of_le_rank`: if `k ≤ A.rank`, extract `k` independent columns to form a
  full-column-rank `m × k` block, then extract `k` independent rows of that block; the resulting
  `k × k` minor has linearly independent rows, hence is a unit, hence has nonzero determinant.

The column/row extraction is packaged by `exists_injOn_linearIndependent_of_le_finrank_span`: from
`k ≤ finrank K (span K (range v))` over a finite index type, it produces an injective `Fin k → ι`
whose image under `v` is linearly independent.

Depends on: `Mathlib.LinearAlgebra.Matrix.Rank`,
`Mathlib.LinearAlgebra.Matrix.NonsingularInverse`, `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`,
`Mathlib.LinearAlgebra.Dimension.Finite`, `Mathlib.LinearAlgebra.Dimension.Constructions`,
`Mathlib.LinearAlgebra.LinearIndependent.Lemmas`.
-/

namespace CRNT.GaussianRank

open Matrix Module Submodule Set Function

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Extracting an independent injectively-indexed subfamily of a spanning family.** Over a
finite index type `ι`, if `k` does not exceed the dimension of the span of `v`, then `k` of the
vectors `v i` are linearly independent, selected by an injective index map `a : Fin k → ι`. -/
theorem exists_injOn_linearIndependent_of_le_finrank_span
    {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [Fintype ι]
    (v : ι → V) (k : ℕ) (hk : k ≤ finrank K (span K (range v))) :
    ∃ a : Fin k → ι, Injective a ∧ LinearIndependent K (v ∘ a) := by
  classical
  obtain ⟨b, hbsub, _, hspan, hli⟩ :=
    exists_linearIndepOn_id_extension (linearIndependent_empty K V) (Set.empty_subset (range v))
  have hbfin : b.Finite := (Set.finite_range v).subset hbsub
  have : Fintype b := hbfin.fintype
  have hspaneq : span K b = span K (range v) :=
    le_antisymm (span_mono hbsub) (by rw [span_le]; exact hspan)
  have hcard : k ≤ b.toFinset.card := by
    have := finrank_span_set_eq_card (R := K) hli
    rw [hspaneq] at this; omega
  have hsec : ∀ x : b, ∃ i : ι, v i = (x : V) := fun x => hbsub x.2
  choose g hg using hsec
  have hginj : Injective g := by
    intro x y hxy; apply Subtype.ext; rw [← hg x, ← hg y, hxy]
  have hembed : Nonempty (Fin k ↪ b) := by
    have : k ≤ Fintype.card b := by rw [Set.toFinset_card] at hcard; exact hcard
    exact Function.Embedding.nonempty_of_card_le (by simpa using this)
  obtain ⟨e⟩ := hembed
  refine ⟨fun i => g (e i), hginj.comp e.injective, ?_⟩
  have hind : LinearIndependent K ((Subtype.val : b → V) ∘ e) := hli.comp e e.injective
  have heq : (v ∘ fun i => g (e i)) = (Subtype.val : b → V) ∘ e := by ext i; exact hg (e i)
  rw [heq]; exact hind

/-- **`A` has a nonsingular `k × k` minor.** There are index selections `r : Fin k → m` and
`c : Fin k → n` whose `k × k` submatrix `A.submatrix r c` has nonzero determinant. -/
def HasNonsingularMinor (A : Matrix m n ℚ) (k : ℕ) : Prop :=
  ∃ (r : Fin k → m) (c : Fin k → n), (A.submatrix r c).det ≠ 0

/-- `HasNonsingularMinor A k` is decidable: the selecting functions `Fin k → m` and `Fin k → n`
range over finite types (the computable `Pi.instFintype`), and a nonzero rational determinant is
decidable from `DecidableEq ℚ`. -/
instance decidableHasNonsingularMinor (A : Matrix m n ℚ) (k : ℕ) :
    Decidable (HasNonsingularMinor A k) := by
  unfold HasNonsingularMinor
  infer_instance

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The empty `0 × 0` minor has determinant `1 ≠ 0`, so every matrix has a nonsingular minor of
size `0`. -/
theorem hasNonsingularMinor_zero (A : Matrix m n ℚ) : HasNonsingularMinor A 0 :=
  ⟨Fin.elim0, Fin.elim0, by simp [Matrix.det_fin_zero]⟩

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- **A nonsingular `k × k` minor bounds the rank below.** The columns of a nonsingular square
matrix are linearly independent, so the `k` selected columns of `A` are independent in the column
space, giving `k ≤ A.rank`. -/
theorem hasNonsingularMinor_le_rank {A : Matrix m n ℚ} {k : ℕ}
    (h : HasNonsingularMinor A k) : k ≤ A.rank := by
  obtain ⟨r, c, hdet⟩ := h
  have hunit : IsUnit (A.submatrix r c) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hrk : (A.submatrix r c).rank = Fintype.card (Fin k) := rank_of_isUnit _ hunit
  rw [Fintype.card_fin] at hrk
  calc k = (A.submatrix r c).rank := hrk.symm
    _ ≤ A.rank := rank_submatrix_le A r c

omit [DecidableEq m] [DecidableEq n] in
/-- **A rank lower bound yields a nonsingular minor.** If `k ≤ A.rank`, choose `k` independent
columns of `A` to form a full-column-rank `m × k` block `B`, then `k` independent rows of `B`; the
resulting `k × k` minor has independent rows, hence is a unit, hence has nonzero determinant. -/
theorem exists_nonsingularMinor_of_le_rank {A : Matrix m n ℚ} {k : ℕ}
    (hk : k ≤ A.rank) : HasNonsingularMinor A k := by
  classical
  have hcolrank : k ≤ finrank ℚ (span ℚ (range A.col)) := by rwa [← rank_eq_finrank_span_cols]
  obtain ⟨c, _hcinj, hcli⟩ := exists_injOn_linearIndependent_of_le_finrank_span A.col k hcolrank
  set B : Matrix m (Fin k) ℚ := A.submatrix id c with hB
  have hBcol : B.col = A.col ∘ c := by
    ext j i; simp [hB, Matrix.col_apply, Matrix.submatrix_apply, Function.comp]
  have hBcoli : LinearIndependent ℚ B.col := by rw [hBcol]; exact hcli
  have hBtrow : (Bᵀ).row = B.col := by ext j i; simp [Matrix.row_apply, Matrix.col_apply]
  have hBtrank : (Bᵀ).rank = k := by
    have := LinearIndependent.rank_matrix (M := Bᵀ) (by rw [hBtrow]; exact hBcoli)
    rwa [Fintype.card_fin] at this
  have hBrank : B.rank = k := by rw [← rank_transpose B]; exact hBtrank
  have hrowrank : k ≤ finrank ℚ (span ℚ (range B.row)) := by
    rw [← rank_eq_finrank_span_row]; omega
  obtain ⟨r, _hrinj, hrli⟩ := exists_injOn_linearIndependent_of_le_finrank_span B.row k hrowrank
  set C : Matrix (Fin k) (Fin k) ℚ := B.submatrix r id with hC
  have hCrow : C.row = B.row ∘ r := by
    ext i j; simp [hC, Matrix.row_apply, Matrix.submatrix_apply, Function.comp]
  have hCli : LinearIndependent ℚ C.row := by rw [hCrow]; exact hrli
  have hCunit : IsUnit C := Matrix.linearIndependent_rows_iff_isUnit.1 hCli
  have hCdet : C.det ≠ 0 := isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 hCunit)
  have hCeq : C = A.submatrix r c := by ext i j; simp [hC, hB, Matrix.submatrix_apply]
  exact ⟨r, c, by rw [← hCeq]; exact hCdet⟩

omit [DecidableEq m] [DecidableEq n] in
/-- **A rank lower bound is equivalent to the existence of a nonsingular minor of that size.** -/
theorem le_rank_iff_hasNonsingularMinor {A : Matrix m n ℚ} {k : ℕ} :
    k ≤ A.rank ↔ HasNonsingularMinor A k :=
  ⟨exists_nonsingularMinor_of_le_rank, hasNonsingularMinor_le_rank⟩

/-- **A computable rank over `ℚ`.** The largest minor size `k ≤ min (card m) (card n)` admitting a
nonsingular `k × k` submatrix. It reduces by `decide`/`#eval`. -/
def computeRank (A : Matrix m n ℚ) : ℕ :=
  Nat.findGreatest (HasNonsingularMinor A) (min (Fintype.card m) (Fintype.card n))

omit [DecidableEq m] [DecidableEq n] in
/-- **The computable rank is at most the true rank.** -/
theorem computeRank_le_rank (A : Matrix m n ℚ) : computeRank A ≤ A.rank :=
  hasNonsingularMinor_le_rank
    (Nat.findGreatest_spec (Nat.zero_le _) (hasNonsingularMinor_zero A))

omit [DecidableEq m] [DecidableEq n] in
/-- The true rank is bounded by both index cardinalities, hence by their minimum. -/
theorem rank_le_min_card (A : Matrix m n ℚ) :
    A.rank ≤ min (Fintype.card m) (Fintype.card n) :=
  le_min (rank_le_card_height A) (rank_le_card_width A)

omit [DecidableEq m] [DecidableEq n] in
/-- **The computable rank equals the true rank.** Combining the two one-sided bounds: every
nonsingular minor has size `≤ A.rank` (`hasNonsingularMinor_le_rank`), and a minor of size exactly
`A.rank` exists (`exists_nonsingularMinor_of_le_rank`), so the largest nonsingular-minor size is
exactly `A.rank`. -/
theorem computeRank_eq_rank (A : Matrix m n ℚ) : computeRank A = A.rank := by
  refine le_antisymm (computeRank_le_rank A) ?_
  exact Nat.le_findGreatest (rank_le_min_card A)
    (exists_nonsingularMinor_of_le_rank (le_refl A.rank))

end CRNT.GaussianRank

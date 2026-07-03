import CRNT.LinearAlgebra.DetCycleCover

/-!
# Sign-definiteness of a determinant from its cycle-cover terms

The injectivity criterion of Craciun and Feinberg ("Multiple equilibria in complex
chemical reaction networks: I. The injectivity property") reads the sign of a Jacobian
determinant off the cycle structure of the underlying species–reaction graph. The
algebraic engine is the Leibniz expansion of the determinant grouped by permutation
cycle type: each permutation `σ` contributes the **cycle-cover term**
`(sign σ) · ∏ i, M (σ i) i`, and the sign `sign σ` is fixed by `σ`'s cycle lengths
(`CRNT.coverCoeff`). When every cycle-cover term carries one common sign, the
determinant is sign-definite — strictly positive or strictly negative — and in
particular nonzero, which is the kernel-emptiness conclusion driving the injectivity
theory.

This module proves that sign half at the level of an abstract square matrix over a
linearly ordered commutative ring.

* `coverTerm` — the cycle-cover term `(coverCoeff σ : R) * ∏ i, M (σ i) i` of a
  permutation `σ`, a real-valued summand of the determinant.
* `det_eq_sum_coverTerm` — the determinant is the sum of its cycle-cover terms, the
  Leibniz expansion read through `coverCoeff`.
* `det_pos_of_coverTerm_nonneg` / `det_neg_of_coverTerm_nonpos` — if every cycle-cover
  term is nonnegative (resp. nonpositive) and the diagonal (identity-permutation) term
  is strictly positive (resp. negative), the determinant is strictly positive (resp.
  negative).
* `det_ne_zero_of_coverTerm_signDefinite` — the consistent-cycle-sign criterion: under
  either one-sided hypothesis the determinant is nonzero.

The cycle-cover terms here are summands of the determinant of a *given* matrix. The
chemical content — that the cycle-cover terms of the factored mass-action Jacobian
`J = stoich · diag(rate) · grad` are governed by the signs of the network's signed
species–reaction-graph cycles — relates each `coverTerm` to a `walkSign` of an
SR-graph cycle and is not carried out here.

Depends on:
`CRNT.LinearAlgebra.DetCycleCover`.
-/

namespace CRNT

open Equiv Equiv.Perm Finset

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **The cycle-cover term of a permutation.** The real-valued summand
`(coverCoeff σ : R) * ∏ i, M (σ i) i` of the Leibniz determinant expansion, whose unit
coefficient `coverCoeff σ = sign σ` is determined by the cycle lengths of `σ`. -/
def coverTerm (M : Matrix n n R) (σ : Perm n) : R :=
  ((coverCoeff σ : ℤ) : R) * ∏ i, M (σ i) i

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The unit `coverCoeff σ`, cast into `R`, scales the diagonal product to the
real-valued cycle-cover term: `(coverCoeff σ) • p = (coverCoeff σ : ℤ : R) * p`. -/
theorem coverCoeff_smul_eq (σ : Perm n) (p : R) :
    (coverCoeff σ : ℤˣ) • p = ((coverCoeff σ : ℤ) : R) * p := by
  rcases Int.units_eq_one_or (coverCoeff σ) with h | h <;>
    simp [h, Units.smul_def]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **The determinant is the sum of its cycle-cover terms.** The Leibniz expansion with
the sign read off the cycle type (`det_eq_sum_over_perm_cycleType`), repackaged with the
real-valued coefficient. -/
theorem det_eq_sum_coverTerm (M : Matrix n n R) :
    M.det = ∑ σ : Perm n, coverTerm M σ := by
  rw [det_eq_sum_over_perm_cycleType M]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coverTerm, show (Multiset.map (fun k => -(-1 : ℤˣ) ^ k) σ.cycleType).prod
        = (coverCoeff σ : ℤˣ) from rfl, coverCoeff_smul_eq]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The identity permutation's cycle-cover term is the diagonal product `∏ i, M i i`. -/
@[simp] theorem coverTerm_one (M : Matrix n n R) :
    coverTerm M (1 : Perm n) = ∏ i, M i i := by
  simp [coverTerm, coverCoeff, Equiv.Perm.cycleType_one]

/-- **One-sided sign-definiteness: nonnegative cycle-cover terms with a positive
diagonal term force a positive determinant.** If every cycle-cover term is nonnegative
and the identity-permutation (diagonal) term is strictly positive, the determinant is
strictly positive. -/
theorem det_pos_of_coverTerm_nonneg (M : Matrix n n R)
    (hnonneg : ∀ σ : Perm n, 0 ≤ coverTerm M σ)
    (hdiag : 0 < coverTerm M (1 : Perm n)) :
    0 < M.det := by
  rw [det_eq_sum_coverTerm M]
  refine Finset.sum_pos' (fun σ _ => hnonneg σ) ?_
  exact ⟨1, Finset.mem_univ _, hdiag⟩

/-- **One-sided sign-definiteness: nonpositive cycle-cover terms with a negative
diagonal term force a negative determinant.** If every cycle-cover term is nonpositive
and the identity-permutation (diagonal) term is strictly negative, the determinant is
strictly negative. -/
theorem det_neg_of_coverTerm_nonpos (M : Matrix n n R)
    (hnonpos : ∀ σ : Perm n, coverTerm M σ ≤ 0)
    (hdiag : coverTerm M (1 : Perm n) < 0) :
    M.det < 0 := by
  rw [det_eq_sum_coverTerm M]
  refine Finset.sum_neg' (fun σ _ => hnonpos σ) ?_
  exact ⟨1, Finset.mem_univ _, hdiag⟩

/-- **The consistent-cycle-sign criterion (sign half of Craciun–Feinberg).** If the
cycle-cover terms of `M` share one common sign — all nonnegative with a strictly
positive diagonal term, or all nonpositive with a strictly negative diagonal term — then
the determinant is sign-definite, hence nonzero. This is the determinant-level statement
that consistently signed species–reaction-graph cycles preclude a singular Jacobian. -/
theorem det_ne_zero_of_coverTerm_signDefinite (M : Matrix n n R)
    (h : (∀ σ : Perm n, 0 ≤ coverTerm M σ) ∧ 0 < coverTerm M (1 : Perm n) ∨
         (∀ σ : Perm n, coverTerm M σ ≤ 0) ∧ coverTerm M (1 : Perm n) < 0) :
    M.det ≠ 0 := by
  rcases h with ⟨hnn, hd⟩ | ⟨hnp, hd⟩
  · exact ne_of_gt (det_pos_of_coverTerm_nonneg M hnn hd)
  · exact ne_of_lt (det_neg_of_coverTerm_nonpos M hnp hd)

end CRNT

import Mathlib.Data.Sign.Basic
import CRNT.LinearAlgebra.OrthogonalComplement

/-!
# Sign vectors of subspaces and their orthogonality

The **sign vector** of `v : ι → ℝ` records the sign of each coordinate as an element of
`SignType` (`-1`, `0`, `1`). This is the elementary layer of the oriented-matroid /
sign-vector theory of a subspace: the combinatorial shadow `signVector '' S` of a subspace
`S ⊆ (ι → ℝ)` and the orthogonality between the sign vectors of `S` and those of its
dot-product orthogonal complement `orthSum S`.

The central fact is **covector orthogonality**: for `u ∈ S` and `w ∈ orthSum S` the sign
vectors `signVector u` and `signVector w` are *orthogonal* — the products `(signVector u) i
* (signVector w) i` either all vanish or take both a positive and a negative value. The
analytic engine is the elementary `mul_eq_zero_of_conformal_mem_orthSum`: when `u` and `w`
are **conformal** (no coordinate where they have strictly opposite signs) and lie in
complementary subspaces, every coordinate product `u i * w i` is zero. This is the
order-theoretic heart of Birch-type uniqueness, isolated from any chemistry.

* `signVector` — the coordinatewise `SignType.sign`.
* `Conformal u v` — `u` and `v` never have strictly opposite signs (`0 ≤ u i * v i`).
* `SignVector.Orthogonal` — oriented-matroid orthogonality of two sign vectors.
* `mul_eq_zero_of_conformal_mem_orthSum` — conformal vectors in complementary subspaces have
  pointwise-vanishing products.
* `orthogonal_signVector_of_mem_orthSum` — the sign vectors of `S` and of `orthSum S` are
  orthogonal.

This module is **stable** and `sorry`-free. Depends on: `Mathlib.Data.Sign.Basic`,
`CRNT.LinearAlgebra.OrthogonalComplement`.
-/

namespace CRNT

open scoped BigOperators

variable {ι : Type*}

/-- The **sign vector** of a real vector: its coordinatewise sign in `SignType`. -/
noncomputable def signVector (v : ι → ℝ) : ι → SignType := fun i => SignType.sign (v i)

@[simp] theorem signVector_apply (v : ι → ℝ) (i : ι) :
    signVector v i = SignType.sign (v i) := rfl

/-- The product of two sign-vector coordinates is the sign of the product. -/
theorem signVector_mul_apply (u v : ι → ℝ) (i : ι) :
    signVector u i * signVector v i = SignType.sign (u i * v i) :=
  (sign_mul (u i) (v i)).symm

/-- Two real vectors are **conformal** when they never point in strictly opposite directions
at a coordinate: each coordinate product is nonnegative. -/
def Conformal (u v : ι → ℝ) : Prop := ∀ i, 0 ≤ u i * v i

theorem conformal_comm {u v : ι → ℝ} (h : Conformal u v) : Conformal v u :=
  fun i => by rw [mul_comm]; exact h i

variable [Fintype ι]

/-- **Conformal vectors in complementary subspaces have vanishing coordinate products.** If
`u ∈ S`, `w ∈ orthSum S`, and `u`, `w` are conformal, then `u i * w i = 0` at every
coordinate — the supports of `u` and `w` are disjoint. This is the elementary cancellation
behind sign-based uniqueness: a sum of nonnegative terms that is forced to vanish by
orthogonality must vanish termwise. -/
theorem mul_eq_zero_of_conformal_mem_orthSum {S : Submodule ℝ (ι → ℝ)} {u w : ι → ℝ}
    (hu : u ∈ S) (hw : w ∈ orthSum S) (hconf : Conformal u w) :
    ∀ i, u i * w i = 0 := by
  have h0 : ∑ i, u i * w i = 0 := by
    have := (mem_orthSum.mp hw) u hu
    simpa only [mul_comm] using this
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hconf i).mp h0
  exact fun i => hall i (Finset.mem_univ i)

/-- **Oriented-matroid orthogonality of sign vectors.** Two sign vectors are orthogonal when
the coordinatewise products either all vanish, or include both a `+` and a `-`. Equivalently,
their products never have a single fixed nonzero sign — there is always cancellation. -/
def SignVector.Orthogonal (σ τ : ι → SignType) : Prop :=
  (∀ i, σ i * τ i = 0) ∨ ((∃ i, σ i * τ i = 1) ∧ ∃ i, σ i * τ i = -1)

/-- **The sign vectors of `S` and of `orthSum S` are orthogonal.** For `u ∈ S` and
`w ∈ orthSum S`, the coordinate products of their sign vectors either all vanish (disjoint
supports) or take both signs: the orthogonality `∑ i, u i * w i = 0` cannot be witnessed by
products of one fixed sign. -/
theorem orthogonal_signVector_of_mem_orthSum {S : Submodule ℝ (ι → ℝ)} {u w : ι → ℝ}
    (hu : u ∈ S) (hw : w ∈ orthSum S) :
    SignVector.Orthogonal (signVector u) (signVector w) := by
  have h0 : ∑ i, u i * w i = 0 := by
    have := (mem_orthSum.mp hw) u hu
    simpa only [mul_comm] using this
  by_cases hneg : ∃ i, u i * w i < 0
  · refine Or.inr ⟨?_, ?_⟩
    · -- A strictly negative product forces a strictly positive one, lest the sum be negative.
      obtain ⟨i, hi⟩ := hneg
      by_contra hcon
      simp only [not_exists] at hcon
      have hnonpos : ∀ j, u j * w j ≤ 0 := by
        intro j
        rcases lt_trichotomy (u j * w j) 0 with h | h | h
        · exact h.le
        · exact h.le
        · exact absurd (by rw [signVector_mul_apply]; exact sign_pos h) (hcon j)
      have hq : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ -(u j * w j) := fun j _ => by
        simpa using hnonpos j
      have hsum : ∑ j, -(u j * w j) = 0 := by rw [Finset.sum_neg_distrib, h0, neg_zero]
      have := (Finset.sum_eq_zero_iff_of_nonneg hq).mp hsum i (Finset.mem_univ i)
      rw [neg_eq_zero] at this
      exact absurd this hi.ne
    · obtain ⟨i, hi⟩ := hneg
      exact ⟨i, by rw [signVector_mul_apply]; exact sign_neg hi⟩
  · refine Or.inl fun i => ?_
    simp only [not_exists, not_lt] at hneg
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hneg j).mp h0
    rw [signVector_mul_apply, hall i (Finset.mem_univ i), sign_zero]

end CRNT

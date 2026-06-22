import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

/-!
# P-matrices

A square matrix is a **P-matrix** when every principal minor is positive: for each subset
of the index set, the principal submatrix obtained by restricting both rows and columns to
that subset has strictly positive determinant. P-matrices are the linear-algebraic engine
behind the Craciun–Feinberg Jacobian injectivity criterion for chemical reaction networks:
a vector field whose Jacobian is everywhere a P-matrix is injective, hence the network is
monostationary.

This module develops the standalone, matrix-theoretic P-matrix layer over an arbitrary
`LinearOrderedField`. The central tool is `Matrix.IsPMatrix.submatrix_det_pos`, which says
that the determinant of `M.submatrix f f` is positive for *any* injective index map `f`,
not just for `Finset`-selected principal submatrices. From it follow nonsingularity
(`det_pos`, `det_ne_zero`, `isUnit_det`), closure under principal submatrices
(`submatrix_isPMatrix`), and positivity of the diagonal (`diag_pos`). Over `ℝ` a symmetric
positive-definite matrix is a P-matrix (`Matrix.PosDef.isPMatrix`).

The declarations live in the `Matrix` namespace so that they read as a standalone,
upstreamable layer with the usual dot-notation ergonomics. The Gale–Nikaido
global-injectivity payoff — that a map with everywhere-P-matrix Jacobian is globally
injective — is out of scope: it is not available in Mathlib.

This module is **stable** and `sorry`-free. Depends on:
`Mathlib.LinearAlgebra.Matrix.PosDef`, `Mathlib.Analysis.Matrix.PosDef`.
-/

-- The P-matrix predicate is stated against the full `[Field] [LinearOrder]
-- [IsStrictOrderedRing]` bundle for uniformity; the individual `det`-positivity lemmas use
-- only the subset relevant to each.
set_option linter.unusedSectionVars false

namespace Matrix

variable {n m k R : Type*}
variable [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A **P-matrix** is a square matrix all of whose principal minors are positive: for every
subset `s` of the index set, the principal submatrix restricting both rows and columns to `s`
has strictly positive determinant. -/
def IsPMatrix (M : Matrix n n R) : Prop :=
  ∀ s : Finset n, 0 < (M.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det

namespace IsPMatrix

/-- The defining positivity of a principal minor selected by a finset `s`. -/
theorem finset_det_pos {M : Matrix n n R} (h : M.IsPMatrix) (s : Finset n) :
    0 < (M.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det :=
  h s

/-- **Key reindexing fact.** For a P-matrix `M` and *any* injective index map `f : k → n`,
the determinant of the principal submatrix `M.submatrix f f` is strictly positive. This
subsumes the `Finset`-indexed definition: an injective `f` selects a principal submatrix up
to the relabelling `det_submatrix_equiv_self`, which leaves the determinant unchanged. -/
theorem submatrix_det_pos {M : Matrix n n R} (h : M.IsPMatrix) {f : k → n}
    (hf : Function.Injective f) : 0 < (M.submatrix f f).det := by
  -- `s` is the image finset of `f`; `f` factors as the coercion `s → n` after an equiv `k ≃ s`.
  set s : Finset n := Finset.univ.image f with hs
  let e : k ≃ s :=
    { toFun := fun i => ⟨f i, by simp [hs]⟩
      invFun := fun j => Fintype.choose (fun i => f i = (j : n)) (by
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp j.2
        exact ⟨i, hi, fun i' hi' => hf (hi'.trans hi.symm)⟩)
      left_inv := fun i => by
        apply hf
        exact Fintype.choose_spec (fun i' => f i' = (f i : n)) _
      right_inv := fun j => by
        apply Subtype.ext
        exact Fintype.choose_spec (fun i => f i = (j : n)) _ }
  have hfe : f = (fun j : s => (j : n)) ∘ e := by funext i; rfl
  have hsub : M.submatrix f f
      = (M.submatrix (fun j : s => (j : n)) (fun j : s => (j : n))).submatrix e e := by
    rw [submatrix_submatrix]
    rw [← hfe]
  rw [hsub, det_submatrix_equiv_self e]
  exact h s

/-- The full determinant of a P-matrix is positive. -/
theorem det_pos {M : Matrix n n R} (h : M.IsPMatrix) : 0 < M.det := by
  have := h.submatrix_det_pos (f := (id : n → n)) Function.injective_id
  simpa using this

/-- A P-matrix has nonzero determinant. -/
theorem det_ne_zero {M : Matrix n n R} (h : M.IsPMatrix) : M.det ≠ 0 :=
  ne_of_gt h.det_pos

/-- A P-matrix has a unit determinant; equivalently it is nonsingular. -/
theorem isUnit_det {M : Matrix n n R} (h : M.IsPMatrix) : IsUnit M.det :=
  (isUnit_iff_ne_zero).mpr h.det_ne_zero

/-- A principal submatrix of a P-matrix, selected by any injective index map `e : m → n`, is
again a P-matrix. -/
theorem submatrix_isPMatrix {M : Matrix n n R} {e : m → n} (he : Function.Injective e)
    (h : M.IsPMatrix) : (M.submatrix e e).IsPMatrix := by
  intro t
  have hcomp : ((M.submatrix e e).submatrix (fun i : t => (i : m)) (fun i : t => (i : m)))
      = M.submatrix (e ∘ fun i : t => (i : m)) (e ∘ fun i : t => (i : m)) := by
    rw [submatrix_submatrix]
  rw [hcomp]
  exact h.submatrix_det_pos (he.comp Subtype.coe_injective)

/-- Every diagonal entry of a P-matrix is positive. -/
theorem diag_pos {M : Matrix n n R} (h : M.IsPMatrix) (i : n) : 0 < M i i := by
  have hpos := h.finset_det_pos {i}
  have : Subsingleton ({i} : Finset n) :=
    ⟨fun a b => Subtype.ext <| by
      rw [Finset.mem_singleton.mp a.2, Finset.mem_singleton.mp b.2]⟩
  rw [det_eq_elem_of_subsingleton _ ⟨i, Finset.mem_singleton_self i⟩] at hpos
  simpa using hpos

end IsPMatrix

/-- Over `ℝ`, a symmetric positive-definite matrix is a P-matrix: each principal submatrix is
again positive definite (`Matrix.PosDef.submatrix`, using injectivity of the coercion), and a
positive-definite matrix has positive determinant (`Matrix.PosDef.det_pos`). -/
theorem PosDef.isPMatrix {M : Matrix n n ℝ} (hM : M.PosDef) : M.IsPMatrix :=
  fun s => (hM.submatrix (Subtype.coe_injective (p := fun x => x ∈ s))).det_pos

end Matrix

namespace CRNT

section Examples

open Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The identity matrix is a P-matrix. -/
example : (1 : Matrix n n R).IsPMatrix := by
  intro s
  have h1 : (1 : Matrix n n R).submatrix (fun i : s => (i : n)) (fun i : s => (i : n))
      = (1 : Matrix s s R) := by
    ext a b
    rw [Matrix.submatrix_apply, Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (congrArg (Subtype.val) hab)]
    · rw [if_neg hab, if_neg (fun hc => hab (Subtype.ext hc))]
  rw [h1, Matrix.det_one]
  exact one_pos

/-- A symmetric positive-definite matrix over `ℝ` is a P-matrix, exercising the bridge. -/
example {M : Matrix n n ℝ} (hM : M.PosDef) : M.IsPMatrix :=
  hM.isPMatrix

end Examples

end CRNT

import CRNT.Decision.ExactDeficiency
import CRNT.Deficiency.LinkageDeficiency
import CRNT.Deficiency.DeficiencyOneDecide

/-!
# A decidable per-linkage-class deficiency test

Feinberg's deficiency-one theorem reads off, for each linkage class `θ`, a class deficiency
`δ_θ = n_θ − 1 − s_θ` (number of complexes, minus one, minus the rank of the span of the class's
reaction vectors), and requires `δ_θ ≤ 1` for every class. The class rank `s_θ =
linkageStoichRank θ` is `Module.finrank` of a real submodule, hence noncomputable as written, so
the predicate `δ_θ ≤ 1` carried no `Decidable` instance at all.

This module supplies one, by the same field-extension route that `CRNT.Decision.ExactDeficiency`
uses for the whole network, restricted to a single class: the class rank is pinned to the exact
computable rational rank `computeRank` of the class's stoichiometric submatrix. As with the
whole-network `computeDeficiency`, the resulting instance is total and axiom-clean, but it does
**not** reduce under kernel `decide` — `computeRank` evaluates a determinant over a permutation
sum, which the kernel does not reduce — so concrete values are obtained through the equality bridge
or compiled evaluation (`#eval`), not by `decide`. The columns of the class submatrix are indexed
by the reactions whose source lies in `θ`:

* `linkageStoichMatrixQ N q : Matrix S {r // classOf (sourceIdx r) = q} ℚ` — the rational
  stoichiometric matrix of the class, computable because complex coefficients are `ℕ`-valued;
* `linkageStoichRank_eq_computeRank : linkageStoichRank q = computeRank (linkageStoichMatrixQ q)` —
  the class rank equals the computable `ℚ`-rank, via `linkageStoichRank = rank (map)` (column-span),
  `rank (map) ≤ rank Q` (independent real columns lift to `ℚ`), and `rank Q ≤ linkageStoichRank`
  (a nonsingular `ℚ`-minor casts to a nonsingular `ℝ`-minor of the column matrix);
* `computeLinkageDeficiency` / `linkageDeficiency_eq_computeLinkageDeficiency` — the class
  deficiency in fully computable form (the class complex-count `numComplexesIn` is recomputed with
  the computable linkage-class `DecidableEq`, equal by filter-instance independence);
* `decidableLinkageDeficiency_le_one` — the resulting `Decidable (linkageDeficiency q ≤ 1)` (total
  and axiom-clean; evaluated via `#eval` or the equality bridge, not kernel `decide`).

This module is **stable** and `sorry`-free. Depends on: `CRNT.Decision.ExactDeficiency`,
`CRNT.Deficiency.LinkageDeficiency`, `CRNT.Deficiency.DeficiencyOneDecide`.
-/

namespace CRNT

namespace Network

open Matrix Module Submodule Set Function CRNT.GaussianRank

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The rational stoichiometric matrix of a linkage class.** Rows indexed by species, columns by
the reactions whose source lies in the class `q`; entry `(s, r)` is the rational reaction-vector
coordinate `target(s) − source(s)`. Computable, since complex coefficients are `ℕ`-valued. -/
def linkageStoichMatrixQ (N : Network S) (q : Quotient N.linkedSetoid) :
    Matrix S {r : N.R // N.classOf (N.sourceIdx r) = q} ℚ :=
  Matrix.of fun s r => ((N.reaction r.val).target s : ℚ) - ((N.reaction r.val).source s : ℚ)

/-- Casting the class matrix to `ℝ` recovers the class's reaction vectors as its columns. -/
theorem linkageStoichMatrixQ_map_col (N : Network S) (q : Quotient N.linkedSetoid)
    (j : {r : N.R // N.classOf (N.sourceIdx r) = q}) :
    ((N.linkageStoichMatrixQ q).map (Rat.castHom ℝ)).col j = N.reactionVector j.val := by
  funext s
  simp [linkageStoichMatrixQ, Matrix.col_apply, Matrix.map_apply, reactionVector_apply]

/-- The class stoichiometric subspace is the span of the columns of the class matrix's real cast. -/
theorem linkageStoichSubspace_eq_span_cols (N : Network S) (q : Quotient N.linkedSetoid) :
    N.linkageStoichSubspace q =
      span ℝ (range fun j : {r : N.R // N.classOf (N.sourceIdx r) = q} => N.reactionVector j.val) := by
  rw [linkageStoichSubspace]
  congr 1
  ext v
  constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨⟨r, hr⟩, rfl⟩
  · rintro ⟨j, rfl⟩; exact ⟨j.val, j.property, rfl⟩

/-- The class stoichiometric rank is the column rank of the real-cast class matrix. -/
theorem linkageStoichRank_eq_rank_map (N : Network S) (q : Quotient N.linkedSetoid) :
    N.linkageStoichRank q = ((N.linkageStoichMatrixQ q).map (Rat.castHom ℝ)).rank := by
  rw [Matrix.rank_eq_finrank_span_cols, linkageStoichRank, linkageStoichSubspace_eq_span_cols]
  have hfun : (fun j : {r : N.R // N.classOf (N.sourceIdx r) = q} => N.reactionVector j.val)
      = ((N.linkageStoichMatrixQ q).map (Rat.castHom ℝ)).col := by
    funext j; exact (N.linkageStoichMatrixQ_map_col q j).symm
  rw [hfun]

/-- The species-vector cast sends each class column to the corresponding real-cast class column. -/
theorem castSpeciesLM_linkageCol (N : Network S) (q : Quotient N.linkedSetoid)
    (j : {r : N.R // N.classOf (N.sourceIdx r) = q}) :
    castSpeciesLM S ((N.linkageStoichMatrixQ q).col j) =
      ((N.linkageStoichMatrixQ q).map (Rat.castHom ℝ)).col j := by
  funext s
  simp [castSpeciesLM, linkageStoichMatrixQ, Matrix.col_apply, Matrix.map_apply]

/-- **Field extension does not increase the class rank.** A set of independent real columns lifts,
via the injective `ℚ`-linear cast, to the same number of independent rational columns. -/
theorem rank_map_le_rank_linkage (N : Network S) (q : Quotient N.linkedSetoid) :
    ((N.linkageStoichMatrixQ q).map (Rat.castHom ℝ)).rank ≤ (N.linkageStoichMatrixQ q).rank := by
  classical
  set M := N.linkageStoichMatrixQ q with hM
  set k := (M.map (Rat.castHom ℝ)).rank with hk
  have hle : k ≤ finrank ℝ (span ℝ (range (M.map (Rat.castHom ℝ)).col)) := by
    rw [← Matrix.rank_eq_finrank_span_cols]
  obtain ⟨a, _hainj, hali⟩ :=
    exists_injOn_linearIndependent_of_le_finrank_span (M.map (Rat.castHom ℝ)).col k hle
  have hinj : Injective fun q' : ℚ => q' • (1 : ℝ) := by intro p q' h; simpa using h
  have hQli : LinearIndependent ℚ ((M.map (Rat.castHom ℝ)).col ∘ a) := hali.restrict_scalars hinj
  have hcomp : (M.map (Rat.castHom ℝ)).col ∘ a = (castSpeciesLM S) ∘ (M.col ∘ a) := by
    funext i
    simp only [Function.comp_apply]
    exact (N.castSpeciesLM_linkageCol q (a i)).symm
  rw [hcomp] at hQli
  have hQli' : LinearIndependent ℚ (M.col ∘ a) := LinearIndependent.of_comp (castSpeciesLM S) hQli
  set W : Submodule ℚ (S → ℚ) := span ℚ (range M.col) with hW
  have hmem : ∀ i, (M.col ∘ a) i ∈ W := fun i => subset_span ⟨a i, rfl⟩
  have hWli : LinearIndependent ℚ (fun i : Fin k => (⟨(M.col ∘ a) i, hmem i⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hQli'
  have hcard := hWli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  have hWrank : finrank ℚ W = M.rank := by rw [hW, Matrix.rank_eq_finrank_span_cols]
  rw [hWrank] at hcard
  exact hcard

/-- **The rational class rank is at most the class stoichiometric rank.** A nonsingular `k × k`
minor of the class matrix casts entrywise to a nonsingular minor of the real-cast matrix (the cast
is an injective ring hom, so a nonzero `ℚ`-determinant stays nonzero), bounding the real column rank
below; and that real column rank is exactly `linkageStoichRank`. -/
theorem rank_le_linkageStoichRank (N : Network S) (q : Quotient N.linkedSetoid) :
    (N.linkageStoichMatrixQ q).rank ≤ N.linkageStoichRank q := by
  set M := N.linkageStoichMatrixQ q with hM
  set k := M.rank with hk
  obtain ⟨r, c, hdet⟩ := le_rank_iff_hasNonsingularMinor.mp (le_refl M.rank)
  -- The same minor, cast to `ℝ`, is nonsingular.
  have hmapsub : (M.map (Rat.castHom ℝ)).submatrix r c = (M.submatrix r c).map (Rat.castHom ℝ) := by
    ext i j; simp [Matrix.submatrix_apply, Matrix.map_apply]
  have hdetR : ((M.map (Rat.castHom ℝ)).submatrix r c).det ≠ 0 := by
    rw [hmapsub, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ (Rat.castHom ℝ).injective).mpr hdet
  -- A nonsingular `ℝ`-minor bounds the real column rank below.
  have hk_le : k ≤ (M.map (Rat.castHom ℝ)).rank := by
    have hunit : IsUnit ((M.map (Rat.castHom ℝ)).submatrix r c) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdetR)
    have hrk : ((M.map (Rat.castHom ℝ)).submatrix r c).rank = Fintype.card (Fin k) :=
      rank_of_isUnit _ hunit
    rw [Fintype.card_fin] at hrk
    calc k = ((M.map (Rat.castHom ℝ)).submatrix r c).rank := hrk.symm
      _ ≤ (M.map (Rat.castHom ℝ)).rank := rank_submatrix_le _ r c
  rw [linkageStoichRank_eq_rank_map]
  exact hk_le

/-- **The class stoichiometric rank equals the computable rational rank** of the class matrix. -/
theorem linkageStoichRank_eq_computeRank (N : Network S) (q : Quotient N.linkedSetoid) :
    N.linkageStoichRank q = computeRank (N.linkageStoichMatrixQ q) := by
  have h1 := N.linkageStoichRank_eq_rank_map q
  have h2 := N.rank_map_le_rank_linkage q
  have h3 := N.rank_le_linkageStoichRank q
  rw [computeRank_eq_rank]
  omega

/-- The class complex-count, recomputed with the computable linkage-class `DecidableEq`. Equal to
`numComplexesIn` (filter cardinality does not depend on the `Decidable` instance), but reduces in
the kernel. -/
def computeNumComplexesIn (N : Network S) (q : Quotient N.linkedSetoid) : ℕ :=
  (Finset.univ.filter (fun c : N.ComplexIdx => N.classOf c = q)).card

/-- The recomputed class complex-count agrees with `numComplexesIn`. -/
theorem computeNumComplexesIn_eq (N : Network S) (q : Quotient N.linkedSetoid) :
    N.computeNumComplexesIn q = N.numComplexesIn q := by
  rw [computeNumComplexesIn, numComplexesIn]
  congr 1
  ext c
  simp only [Finset.mem_filter]

/-- **The computable class deficiency** `δ_θ = n_θ − 1 − s_θ`, with both the complex-count and the
class rank in computable form. -/
def computeLinkageDeficiency (N : Network S) (q : Quotient N.linkedSetoid) : ℤ :=
  (N.computeNumComplexesIn q : ℤ) - 1 - (computeRank (N.linkageStoichMatrixQ q) : ℤ)

/-- **The class deficiency equals its computable form.** -/
theorem linkageDeficiency_eq_computeLinkageDeficiency (N : Network S)
    (q : Quotient N.linkedSetoid) :
    N.linkageDeficiency q = N.computeLinkageDeficiency q := by
  rw [linkageDeficiency, computeLinkageDeficiency, ← N.computeNumComplexesIn_eq q,
    ← N.linkageStoichRank_eq_computeRank q]

/-- **The per-linkage-class deficiency test `δ_θ ≤ 1` is decidable**, through the computable class
deficiency. The instance is total and axiom-clean; like the whole-network `computeDeficiency` it is
evaluated via `#eval` or the equality bridge rather than kernel `decide`, since `computeRank`
expands a determinant over a permutation sum. -/
instance decidableLinkageDeficiency_le_one (N : Network S) (q : Quotient N.linkedSetoid) :
    Decidable (N.linkageDeficiency q ≤ 1) :=
  decidable_of_iff (N.computeLinkageDeficiency q ≤ 1)
    (by rw [linkageDeficiency_eq_computeLinkageDeficiency])

end Network

end CRNT

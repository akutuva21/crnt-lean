import CRNT.Decision.ExactDeficiency
import CRNT.Kinetics.MassActionJacobian
import CRNT.Multistationarity.JacobianDeterminantSign
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# A computable rational chart of the stoichiometric subspace

The chart of the stoichiometric subspace used by the reduced-Jacobian injectivity route
(`CRNT.Multistationarity.StoichChart`, `ReducedSRGraphBridge`) is built from
`Module.finBasis`, an arbitrary noncomputable basis, so the chart matrix `stoichChartMatrix`
and its dual projection `stoichProjMatrix` are noncomputable. This module supplies a
*computable* rational chart of the same subspace, built from an explicit nonsingular maximal
minor of the rational stoichiometric matrix — the selection that the Gaussian/minor machinery
of `CRNT.Decision.GaussianRank` and `CRNT.Decision.MinorSearch` produces.

The rational stoichiometric matrix `A = stoichMatrixQ` (rows species, columns reactions) has
column space the rational stoichiometric subspace, of dimension `computeRank A = stoichRank`.
A *maximal* nonsingular minor selects pivot rows `ρ : Fin k → S` and pivot columns
`γ : Fin k → R` with `(A.submatrix ρ γ).det ≠ 0` and `k = computeRank A`
(`exists_pivotSelection`). From an explicit such selection:

* `chartBasisQ ρ γ : Matrix S (Fin k) ℚ` — the `k` pivot columns of `A`, a concrete rational
  basis `B` of the column space of `A`.
* `chartProjQ ρ γ : Matrix (Fin k) S ℚ` — `C⁻¹` times the pivot-row selection, where
  `C = A.submatrix ρ γ` is the (invertible) pivot block; the inverse is the *computable*
  `(C.det)⁻¹ • C.adjugate`.

Both are computable in the given selection. They satisfy the chart law
`chartProjQ * chartBasisQ = 1` (`chartProjQ_mul_chartBasisQ`), and when the selection is maximal
`B` spans the rational stoichiometric subspace (`span_chartBasisQ_col`,
`chartBasisQ_col_mem_span`), whose real cast is the genuine stoichiometric subspace `S(N)`.

The payoff is a *decidable* reduced-compression cover-sign certificate evaluated at a rational
chart point. The mass-action Jacobian has rational entries at a rational concentration
(`massActionJacobianQ_map_eq`), so the chart-transported reduced matrix `P · Mℚ · B` is a
rational matrix, and the cover-sign condition on its principal submatrices — every cycle-cover
term nonnegative, every diagonal cover term positive — is decidable over `ℚ`
(`decidableCompressionCoverSignQ`), since `coverTerm` over `ℚ` has decidable sign.

The certificate is anchored to *this* computable chart `B`/`P`; identifying it with the
noncomputable `stoichChartMatrix`/`stoichProjMatrix` of `ReducedSRGraphBridge` would need a
change-of-basis bridge between the two charts, which is not carried out here.

This is the computable rational linear-algebra foundation (Gaussian elimination over `ℚ`) for
the reduced-coordinate species–reaction-graph injectivity route of Craciun and Feinberg
("Multiple equilibria in complex chemical reaction networks: II. The species–reaction graph").

This module is **stable** and `sorry`-free. Depends on: `CRNT.Decision.ExactDeficiency`,
`CRNT.Kinetics.MassActionJacobian`, `CRNT.Multistationarity.JacobianDeterminantSign`,
`Mathlib.LinearAlgebra.Matrix.Adjugate`, `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`.
-/

namespace CRNT

namespace Network

open Matrix Module Submodule Set Function CRNT.GaussianRank

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## A maximal nonsingular minor exists -/

/-- **The pivot selection of a nonsingular maximal minor.** The rational stoichiometric matrix
`A = stoichMatrixQ` has a nonsingular `k × k` minor with `k = computeRank A` (its rank): pivot
rows `ρ : Fin k → S` and pivot columns `γ : Fin k → R` whose square submatrix has nonzero
determinant. This is the column/row extraction of `GaussianRank` packaged at the network level;
`MinorSearch.findMinorWitness` produces such a selection computably at a concrete network. -/
theorem exists_pivotSelection (N : Network S) :
    ∃ (ρ : Fin (computeRank N.stoichMatrixQ) → S) (γ : Fin (computeRank N.stoichMatrixQ) → N.R),
      (N.stoichMatrixQ.submatrix ρ γ).det ≠ 0 := by
  have h : computeRank N.stoichMatrixQ ≤ N.stoichMatrixQ.rank :=
    (computeRank_eq_rank N.stoichMatrixQ).le
  obtain ⟨ρ, γ, hdet⟩ := le_rank_iff_hasNonsingularMinor.mp h
  exact ⟨ρ, γ, hdet⟩

/-! ## The computable rational chart `B` and projection `P`

These are built from an explicit pivot selection `ρ`, `γ`, kept as parameters so the
construction is computable; `exists_pivotSelection` (or `MinorSearch.findMinorWitness`) supplies
such a selection. -/

variable {k : ℕ}

/-- **The rational chart matrix `B`.** The `k` pivot columns of the rational stoichiometric matrix
`A` selected by `γ`, an `S × Fin k` matrix whose columns form a basis of the column space of `A`
when the selection is maximal. -/
def chartBasisQ (N : Network S) (γ : Fin k → N.R) : Matrix S (Fin k) ℚ :=
  N.stoichMatrixQ.submatrix id γ

/-- The pivot block `C = A.submatrix ρ γ`, invertible when its determinant is nonzero. -/
def pivotBlockQ (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R) : Matrix (Fin k) (Fin k) ℚ :=
  N.stoichMatrixQ.submatrix ρ γ

/-- **The computable inverse of the pivot block.** Over `ℚ` the matrix inverse `C⁻¹ =
(C.det)⁻¹ • C.adjugate` is computable (both the rational reciprocal and the adjugate are), so this
spells it out explicitly rather than through the noncomputable `Ring.inverse`. -/
def pivotBlockInvQ (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R) : Matrix (Fin k) (Fin k) ℚ :=
  ((N.pivotBlockQ ρ γ).det)⁻¹ • (N.pivotBlockQ ρ γ).adjugate

/-- The explicit computable inverse agrees with Mathlib's nonsingular inverse `C⁻¹`. -/
theorem pivotBlockInvQ_eq_inv (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R) :
    N.pivotBlockInvQ ρ γ = (N.pivotBlockQ ρ γ)⁻¹ := by
  rw [pivotBlockInvQ, Matrix.inv_def, Ring.inverse_eq_inv']

/-- The pivot-row selection matrix `Fin k × S`, with a `1` in column `ρ i` of row `i`. As a matrix
product it selects the rows `ρ` of any `S`-rowed matrix. -/
def pivotRowSelQ (ρ : Fin k → S) : Matrix (Fin k) S ℚ :=
  (1 : Matrix S S ℚ).submatrix ρ id

/-- **The rational projection matrix `P`.** The computable pivot-block inverse times the pivot-row
selection, a `Fin k × S` matrix that is a left inverse of the chart `B` whenever the pivot block is
nonsingular. -/
def chartProjQ (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R) : Matrix (Fin k) S ℚ :=
  N.pivotBlockInvQ ρ γ * pivotRowSelQ ρ

/-- Selecting rows of `B` by the pivot rows recovers the pivot block: `selRow * B = C`. -/
theorem pivotRowSelQ_mul_chartBasisQ (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R) :
    pivotRowSelQ ρ * N.chartBasisQ γ = N.pivotBlockQ ρ γ := by
  rw [pivotRowSelQ, chartBasisQ, pivotBlockQ]
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.submatrix_apply, Finset.sum_ite_eq]

/-- **The chart law `P · B = 1`.** With `P = C⁻¹ · selRow` and `selRow · B = C` (the pivot block),
`P · B = C⁻¹ · C = 1` since the pivot block is nonsingular. The computable chart `B` and projection
`P` therefore form a genuine chart of the rational stoichiometric subspace. -/
theorem chartProjQ_mul_chartBasisQ (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R)
    (hdet : (N.stoichMatrixQ.submatrix ρ γ).det ≠ 0) :
    N.chartProjQ ρ γ * N.chartBasisQ γ = 1 := by
  rw [chartProjQ, Matrix.mul_assoc, pivotRowSelQ_mul_chartBasisQ, pivotBlockInvQ_eq_inv]
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)

/-! ## The chart spans the rational stoichiometric subspace -/

/-- Each column of `B` is a column of `A = stoichMatrixQ`. -/
theorem chartBasisQ_col (N : Network S) (γ : Fin k → N.R) (j : Fin k) :
    (N.chartBasisQ γ).col j = N.stoichMatrixQ.col (γ j) := by
  funext s
  simp [chartBasisQ, Matrix.col_apply, Matrix.submatrix_apply]

/-- **The columns of `B` are linearly independent** when the pivot block is nonsingular. Their
restriction to the pivot rows `ρ` is the pivot block `C`, whose columns are independent, so the full
columns of `B` are too. -/
theorem chartBasisQ_col_linearIndependent (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R)
    (hdet : (N.stoichMatrixQ.submatrix ρ γ).det ≠ 0) :
    LinearIndependent ℚ (N.chartBasisQ γ).col := by
  have hCunit : IsUnit (N.pivotBlockQ ρ γ) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hCcol : LinearIndependent ℚ (N.pivotBlockQ ρ γ).col :=
    Matrix.linearIndependent_cols_iff_isUnit.2 hCunit
  -- `C.col = (funLeft ρ ∘ B.col)`, the pivot-row restriction of `B`'s columns.
  have hsel : (N.pivotBlockQ ρ γ).col = (LinearMap.funLeft ℚ ℚ ρ) ∘ (N.chartBasisQ γ).col := by
    funext j i
    simp [pivotBlockQ, chartBasisQ, Matrix.col_apply, Matrix.submatrix_apply,
      LinearMap.funLeft_apply]
  rw [hsel] at hCcol
  exact LinearIndependent.of_comp _ hCcol

/-- **The chart columns span the column space of `A`** for a maximal selection. The `k` columns of
`B` are `k` independent columns of `A`, and `k = rank A = dim (column space)`, so they span it. -/
theorem span_chartBasisQ_col (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R)
    (hdet : (N.stoichMatrixQ.submatrix ρ γ).det ≠ 0)
    (hk : k = computeRank N.stoichMatrixQ) :
    span ℚ (range (N.chartBasisQ γ).col) = span ℚ (range N.stoichMatrixQ.col) := by
  -- `span B.col ⊆ span A.col` since each `B`-column is an `A`-column.
  have hsub : span ℚ (range (N.chartBasisQ γ).col) ≤ span ℚ (range N.stoichMatrixQ.col) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [chartBasisQ_col]
    exact subset_span ⟨γ j, rfl⟩
  -- Both spans have dimension `k`, so the inclusion is an equality.
  refine Submodule.eq_of_le_of_finrank_le hsub ?_
  have hdimA : finrank ℚ (span ℚ (range N.stoichMatrixQ.col)) = computeRank N.stoichMatrixQ := by
    rw [← Matrix.rank_eq_finrank_span_cols, computeRank_eq_rank]
  have hdimB : finrank ℚ (span ℚ (range (N.chartBasisQ γ).col)) = k := by
    rw [finrank_span_eq_card (N.chartBasisQ_col_linearIndependent ρ γ hdet), Fintype.card_fin]
  rw [hdimA, hdimB, hk]

/-- Each chart column lies in the column span of the rational stoichiometric matrix. -/
theorem chartBasisQ_col_mem_span (N : Network S) (γ : Fin k → N.R) (j : Fin k) :
    (N.chartBasisQ γ).col j ∈ span ℚ (range N.stoichMatrixQ.col) := by
  rw [chartBasisQ_col]; exact subset_span ⟨γ j, rfl⟩

/-- **The real cast of a chart column lies in the stoichiometric subspace `S(N)`.** Casting the
rational chart columns along `castSpeciesLM` lands in the real span of the reaction vectors. -/
theorem castSpeciesLM_chartBasisQ_col_mem_stoichSubspace (N : Network S) (γ : Fin k → N.R)
    (j : Fin k) :
    castSpeciesLM S ((N.chartBasisQ γ).col j) ∈ N.stoichSubspace := by
  rw [chartBasisQ_col, castSpeciesLM_col, stoichSubspace, reactionVectors]
  have h : (N.stoichMatrixQ.map (Rat.castHom ℝ)).col (γ j) = N.reactionVector (γ j) :=
    N.stoichMatrixQ_map_col (γ j)
  rw [h]
  exact subset_span ⟨γ j, rfl⟩

/-! ## A rational mass-action Jacobian -/

/-- **The rational source-monomial gradient.** The `j`-th partial of `∏ s, x_s ^ (y_s)` in
polynomial form `y_j · x_j ^ (y_j − 1) · ∏_{s ≠ j} x_s ^ (y_s)`, evaluated over `ℚ`. -/
def massActionMonomialGradQ (y : Complex S) (xq : S → ℚ) (j : S) : ℚ :=
  (y j : ℚ) * xq j ^ (y j - 1) * ∏ s ∈ Finset.univ.erase j, xq s ^ (y s)

/-- The real cast of the rational monomial gradient is the real monomial gradient at the cast
point. -/
theorem massActionMonomialGradQ_cast (y : Complex S) (xq : S → ℚ) (j : S) :
    ((massActionMonomialGradQ y xq j : ℚ) : ℝ)
      = massActionMonomialGrad y (fun s => (xq s : ℝ)) j := by
  simp [massActionMonomialGradQ, massActionMonomialGrad]

/-- **The rational mass-action Jacobian matrix at a rational concentration.** With rational rate
constants `kq` and rational concentration `xq`, entry `(i, j)` is
`∑ r, kq r · (∂_j monomial_r) · reactionVector_ℚ r i`, all in exact rational arithmetic. -/
def massActionJacobianQ (N : Network S) (kq : N.R → ℚ) (xq : S → ℚ) : Matrix S S ℚ :=
  fun i j => ∑ r : N.R,
    kq r * massActionMonomialGradQ (N.reaction r).source xq j
      * (((N.reaction r).target i : ℚ) - ((N.reaction r).source i : ℚ))

/-- **The rational Jacobian casts to the real Jacobian.** The real cast of `massActionJacobianQ
kq xq` is the real mass-action Jacobian at the cast concentration, provided the real rate constants
are the casts of `kq`. The mass-action Jacobian is therefore rational at every rational data
point. -/
theorem massActionJacobianQ_map_eq (N : Network S) (kq : N.R → ℚ) (xq : S → ℚ)
    (κ : N.RateConstants) (hk : ∀ r, κ.k r = (kq r : ℝ)) :
    (N.massActionJacobianQ kq xq).map (Rat.castHom ℝ)
      = N.massActionJacobian κ (fun s => (xq s : ℝ)) := by
  ext i j
  simp only [massActionJacobianQ, massActionJacobian, Matrix.map_apply, Rat.coe_castHom,
    Rat.cast_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Rat.cast_mul, Rat.cast_mul, hk r, massActionMonomialGradQ_cast]
  simp [reactionVector_apply]

/-! ## The decidable reduced-compression cover-sign certificate -/

/-- **The chart-transported rational reduced matrix `P · Mℚ · B`.** With `B = chartBasisQ`,
`P = chartProjQ`, and `Mℚ = massActionJacobianQ kq xq` the rational Jacobian at a rational point,
this is an honest `k × k` rational matrix. -/
def reducedMatrixQ (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R) (kq : N.R → ℚ) (xq : S → ℚ) :
    Matrix (Fin k) (Fin k) ℚ :=
  N.chartProjQ ρ γ * N.massActionJacobianQ kq xq * N.chartBasisQ γ

/-- **The reduced-compression cover-sign condition over `ℚ`.** Reading the rational reduced matrix
`P · Mℚ · B` as a plain `k × k` matrix, this asks that the covers of every principal submatrix
share one sign: every cycle-cover term of every principal submatrix is nonnegative, and the diagonal
cover term of every principal submatrix is strictly positive. It is the rational, pointwise analogue
of `ReducedJacobianCompressionSRSign`. -/
def CompressionCoverSignQ (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R)
    (kq : N.R → ℚ) (xq : S → ℚ) : Prop :=
  ∀ s : Finset (Fin k),
    (∀ σ : Equiv.Perm s,
        0 ≤ coverTerm ((N.reducedMatrixQ ρ γ kq xq).submatrix
          (fun i : s => (i : Fin k)) (fun i : s => (i : Fin k))) σ) ∧
      0 < coverTerm ((N.reducedMatrixQ ρ γ kq xq).submatrix
        (fun i : s => (i : Fin k)) (fun i : s => (i : Fin k))) (1 : Equiv.Perm s)

/-- **The reduced-compression cover-sign condition is decidable.** The reduced matrix `P · Mℚ · B`
is rational, `coverTerm` is a rational polynomial in its entries, and `ℚ` has decidable order, so
each cover-sign comparison is decidable; the conjunction quantifies over the finite types
`Finset (Fin k)` and `Equiv.Perm s`, so the whole condition is decidable. This is the rational,
pointwise payoff: the cover-sign certificate at a rational chart point is a finite decision. -/
instance decidableCompressionCoverSignQ (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R)
    (kq : N.R → ℚ) (xq : S → ℚ) :
    Decidable (N.CompressionCoverSignQ ρ γ kq xq) := by
  unfold CompressionCoverSignQ
  infer_instance

end Network

end CRNT

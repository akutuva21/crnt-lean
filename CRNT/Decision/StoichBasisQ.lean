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

* `chartSectionQ ρ γ = B · C⁻¹` — the chart scaled so that the *pivot-row selection itself*
  `w ↦ w ∘ ρ`, with no change of coordinates, is its left inverse: `selRow · (B · C⁻¹) = 1`
  (`pivotRowSelQ_mul_chartSectionQ`). Its real cast `chartSectionR` is the concrete chart of the
  pivot-row coordinate injectivity route, and the section identity `B (w ∘ ρ) = w` holds for every
  `w ∈ S(N)` (`chartSectionR_mulVec_pivotSel`): the real section columns are independent, span `S(N)`
  (`span_chartSectionR_col`), and the identity holds columnwise and extends by linearity.

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

/-! ## The pivot-section chart and the pivot-row section identity -/

/-- **The rational pivot-section chart `Bsec = B · C⁻¹`.** The chart `B = chartBasisQ` scaled on the
right by the computable pivot-block inverse, an `S × Fin k` matrix. Where `chartBasisQ` is recovered
from its pivot rows through the projection `P = C⁻¹ · selRow` (`chartProjQ`), this scaled chart is
recovered directly from its pivot rows: `selRow * Bsec = 1` (`pivotRowSelQ_mul_chartSectionQ`), so the
pivot-row selection `w ↦ w ∘ ρ`, with no change of coordinates, is a left inverse of `Bsec` — the
section the pivot-row coordinate chart of `PivotReducedInjectivity` requires. -/
def chartSectionQ (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R) : Matrix S (Fin k) ℚ :=
  N.chartBasisQ γ * N.pivotBlockInvQ ρ γ

/-- **The pivot rows of `Bsec` recover the coordinate: `selRow * Bsec = 1`.** Selecting the pivot rows
of `Bsec = B · C⁻¹` gives `(selRow · B) · C⁻¹ = C · C⁻¹ = 1`, so the pivot-row selection is a left
inverse of `Bsec`. This is the rational core of the section identity of the pivot-row coordinate
chart. -/
theorem pivotRowSelQ_mul_chartSectionQ (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R)
    (hdet : (N.stoichMatrixQ.submatrix ρ γ).det ≠ 0) :
    pivotRowSelQ ρ * N.chartSectionQ ρ γ = 1 := by
  rw [chartSectionQ, ← Matrix.mul_assoc, pivotRowSelQ_mul_chartBasisQ, pivotBlockInvQ_eq_inv]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)

/-- **The real cast of a section-chart column lies in the stoichiometric subspace `S(N)`.** `Bsec`'s
column `j` is the `ℚ`-combination `∑ l, (C⁻¹) l j • B.col l`, whose real casts are in `S(N)`. -/
theorem castSpeciesLM_chartSectionQ_col_mem_stoichSubspace (N : Network S) (ρ : Fin k → S)
    (γ : Fin k → N.R) (j : Fin k) :
    castSpeciesLM S ((N.chartSectionQ ρ γ).col j) ∈ N.stoichSubspace := by
  have hcol : (N.chartSectionQ ρ γ).col j
      = ∑ l : Fin k, (N.pivotBlockInvQ ρ γ) l j • (N.chartBasisQ γ).col l := by
    funext s
    simp only [chartSectionQ, Matrix.col_apply, Matrix.mul_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hcol, map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (N.castSpeciesLM_chartBasisQ_col_mem_stoichSubspace γ l)

/-- **The real section chart `Bℝ`.** The real cast of the rational section chart
`chartSectionQ = B · C⁻¹`, an `S × Fin k` real matrix. Its columns are the casts of the rational
section columns; the pivot-row selection `w ↦ w ∘ ρ` is a left inverse of it that, on the
stoichiometric subspace, recovers every element (`chartSectionR_mulVec_pivotSel`), so it is the
concrete chart of the pivot-row coordinate route of `PivotReducedInjectivity`. -/
noncomputable def chartSectionR (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R) :
    Matrix S (Fin k) ℝ :=
  (N.chartSectionQ ρ γ).map (Rat.castHom ℝ)

/-- The columns of the real section chart are the species-vector casts of the rational ones. -/
theorem chartSectionR_col (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R) (j : Fin k) :
    (N.chartSectionR ρ γ).col j = castSpeciesLM S ((N.chartSectionQ ρ γ).col j) := by
  funext s
  simp [chartSectionR, castSpeciesLM, Matrix.col_apply, Matrix.map_apply]

/-- Each real section-chart column lies in the stoichiometric subspace `S(N)`. -/
theorem chartSectionR_col_mem_stoichSubspace (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R)
    (j : Fin k) : (N.chartSectionR ρ γ).col j ∈ N.stoichSubspace := by
  rw [chartSectionR_col]
  exact N.castSpeciesLM_chartSectionQ_col_mem_stoichSubspace ρ γ j

/-- **The pivot-row entries of `Bℝ` form the identity: `Bℝ (ρ i) j = δ_{ij}`.** The real cast of
`selRow * Bsec = 1` says selecting the pivot rows of `Bℝ` is the identity matrix. -/
theorem chartSectionR_pivotRow (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R)
    (hdet : (N.stoichMatrixQ.submatrix ρ γ).det ≠ 0) (i j : Fin k) :
    N.chartSectionR ρ γ (ρ i) j = (if i = j then 1 else 0 : ℝ) := by
  have hsel : ((pivotRowSelQ ρ).map (Rat.castHom ℝ)) * N.chartSectionR ρ γ = 1 := by
    rw [chartSectionR, ← Matrix.map_mul, N.pivotRowSelQ_mul_chartSectionQ ρ γ hdet,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have h := congrFun (congrFun hsel i) j
  rw [Matrix.mul_apply] at h
  rw [Finset.sum_eq_single (ρ i)] at h
  · simpa [pivotRowSelQ, Matrix.map_apply, Matrix.submatrix_apply, Matrix.one_apply] using h
  · intro b _ hb
    have : (pivotRowSelQ ρ).map (Rat.castHom ℝ) i b = 0 := by
      simp [pivotRowSelQ, Matrix.map_apply, Matrix.submatrix_apply, Matrix.one_apply,
        if_neg (Ne.symm hb)]
    rw [this, zero_mul]
  · intro h'; exact absurd (Finset.mem_univ _) h'

/-- **The real section columns are `ℝ`-linearly independent.** Their pivot-row restriction is the
identity matrix's columns (`chartSectionR_pivotRow`), which are independent, so the columns are. -/
theorem chartSectionR_col_linearIndependent (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R)
    (hdet : (N.stoichMatrixQ.submatrix ρ γ).det ≠ 0) :
    LinearIndependent ℝ (N.chartSectionR ρ γ).col := by
  apply LinearIndependent.of_comp (LinearMap.funLeft ℝ ℝ ρ)
  have key : (LinearMap.funLeft ℝ ℝ ρ) ∘ (N.chartSectionR ρ γ).col
      = (1 : Matrix (Fin k) (Fin k) ℝ).col := by
    funext j i
    simp only [Function.comp_apply, LinearMap.funLeft_apply, Matrix.col_apply,
      N.chartSectionR_pivotRow ρ γ hdet i j, Matrix.one_apply]
  rw [key]
  exact Matrix.linearIndependent_cols_iff_isUnit.2 isUnit_one

/-- **The real section chart spans the stoichiometric subspace.** The `k` real section columns are
independent and lie in `S(N)`, and `k = stoichRank = dim S(N)`, so they span `S(N)`. -/
theorem span_chartSectionR_col (N : Network S) (ρ : Fin (computeRank N.stoichMatrixQ) → S)
    (γ : Fin (computeRank N.stoichMatrixQ) → N.R)
    (hdet : (N.stoichMatrixQ.submatrix ρ γ).det ≠ 0) :
    span ℝ (range (N.chartSectionR ρ γ).col) = N.stoichSubspace := by
  have hle : span ℝ (range (N.chartSectionR ρ γ).col) ≤ N.stoichSubspace := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact N.chartSectionR_col_mem_stoichSubspace ρ γ j
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  have hdimB : finrank ℝ (span ℝ (range (N.chartSectionR ρ γ).col))
      = computeRank N.stoichMatrixQ := by
    rw [finrank_span_eq_card (N.chartSectionR_col_linearIndependent ρ γ hdet), Fintype.card_fin]
  have hdimS : finrank ℝ N.stoichSubspace = computeRank N.stoichMatrixQ := by
    rw [← stoichRank, N.stoichRank_eq_computeRank]
  rw [hdimB, hdimS]

/-- **The pivot-row section identity for the real section chart.** For every `w` in the
stoichiometric subspace, applying the real section chart to the pivot rows of `w` recovers `w`:
`Bℝ · (w ∘ ρ) = w`. Since the section columns span `S(N)`, it suffices to check the identity on each
column, where the pivot-row entries `Bℝ (ρ i) j = δ_{ij}` make it immediate; the identity then extends
by linearity. This discharges the section hypothesis `hBsec` of
`massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix` for the concrete chart. -/
theorem chartSectionR_mulVec_pivotSel (N : Network S) (ρ : Fin (computeRank N.stoichMatrixQ) → S)
    (γ : Fin (computeRank N.stoichMatrixQ) → N.R)
    (hdet : (N.stoichMatrixQ.submatrix ρ γ).det ≠ 0)
    {w : S → ℝ} (hw : w ∈ N.stoichSubspace) :
    (N.chartSectionR ρ γ).mulVec (fun i => w (ρ i)) = w := by
  rw [← N.span_chartSectionR_col ρ γ hdet] at hw
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j, rfl⟩ := hv
    -- The pivot coordinate of column `j` is the `j`-th standard vector `Pi.single j 1`.
    have hcoord : (fun i => (N.chartSectionR ρ γ).col j (ρ i)) = Pi.single j (1 : ℝ) := by
      funext i
      rw [Matrix.col_apply, N.chartSectionR_pivotRow ρ γ hdet i j, Pi.single_apply, eq_comm]
    rw [hcoord, Matrix.mulVec_single_one]
  | zero =>
    have : (fun i => (0 : S → ℝ) (ρ i)) = 0 := by funext i; simp
    rw [this, Matrix.mulVec_zero]
  | add v v' _ _ hv hv' =>
    have hsum : (fun i => (v + v') (ρ i)) = (fun i => v (ρ i)) + (fun i => v' (ρ i)) := by
      funext i; simp
    rw [hsum, Matrix.mulVec_add, hv, hv']
  | smul a v _ hv =>
    have hsmul : (fun i => (a • v) (ρ i)) = a • (fun i => v (ρ i)) := by
      funext i; simp
    rw [hsmul, Matrix.mulVec_smul, hv]

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

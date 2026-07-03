import CRNT.Multistationarity.PivotReducedInjectivity

/-!
# A decidable rational cover-sign certificate for the pivot-reduced Jacobian P-matrix property

The pivot-row injectivity route of `CRNT.Multistationarity.PivotReducedInjectivity` reaches
compatibility-class injectivity once the pivot-reduced Jacobian `pivotSel ρ ∘ J ∘ B` — the oblique
compression `selRow · J · Bℝ` of the full mass-action Jacobian through the concrete rational chart
`Bℝ = chartSectionR ρ γ` of `CRNT.Decision.StoichBasisQ` — is a P-matrix on an enclosing box of pivot
coordinates. The pivot-reduced Jacobian is not a principal submatrix of the full Jacobian, so the
point-free full-Jacobian P-matrix verdict of `SRCoverPointIndependence` does not transport to it.

This module supplies the missing pointwise bridge: a *decidable* rational cover-sign certificate that,
at a single rational data point, certifies the P-matrix property of the pivot-reduced Jacobian there.

* `reducedPivotMatrixQ` — the rational matrix `selRow · Mℚ · Bsec` matching the pivot-reduced
  Jacobian, with `Mℚ = massActionJacobianQ kq xq` the rational Jacobian at the rational point and
  `Bsec = chartSectionQ ρ γ` the rational pivot-section chart. Its real cast is exactly the
  pivot-reduced Jacobian at the cast point (`pivotReducedJacobian_eq_map`), so the two charts agree.
* `PivotCoverSignQ` / `decidablePivotCoverSignQ` — the decidable cover-sign condition on
  `reducedPivotMatrixQ`: every cycle-cover term of every principal submatrix is nonnegative and every
  diagonal cover term is strictly positive. Decidable over `ℚ` because `coverTerm` is rational and `ℚ`
  has decidable order.
* `coverTerm_map` — the cycle-cover term commutes with a ring homomorphism, so a rational cover term
  casts to the real cover term of the cast matrix; cover-sign therefore transfers across the cast.
* `isPMatrix_map_of_pivotCoverSignQ` — the generic matrix bridge: the rational cover-sign condition on
  any rational `k × k` matrix makes its real cast a P-matrix, since every principal minor is a sum of
  nonnegative cover terms with a strictly positive diagonal term (`det_pos_of_coverTerm_nonneg`).
* `isPMatrix_pivotReducedJacobian_of_pivotCoverSignQ` — the pointwise verdict at the network level: at
  a rational concentration that is the cast of the pivot-affine chart point, the decidable rational
  cover-sign certificate makes the pivot-reduced Jacobian a P-matrix at that point.

## Point-dependence of the reduced cover-sign pattern

For the *full* mass-action Jacobian the cover-sign pattern is point-independent: every cover product of
every principal submatrix factors as a nonnegative gradient magnitude (carrying all the concentration
dependence) times a point-independent signed-incidence weight, so a single check settles the verdict at
every positive concentration (`SRCoverPointIndependence.isPMatrix_massActionJacobian_box_of_pointIndep`).

That split fails for the pivot-reduced compression. The proper principal minors of `selRow · J · Bsec`
mix full-Jacobian entries across species through the chart columns of `Bsec`, so their cover products do
not separate into a magnitude times a point-independent incidence weight; the reduced cover-sign pattern
is genuinely concentration-dependent. The decidable certificate here is therefore a *pointwise* verdict:
it discharges the P-matrix property at the single rational point it is evaluated at, not over a box. A
fully `decide`-driven box-coverage verdict for the reduced compression would need either a finite
decidable box-check or an explicit per-box hypothesis; it does not follow from a single rational point.
The box hypothesis `hpm` of `massActionInjectiveOnClass_of_concretePivotChart` accordingly remains a
consumer input, which this certificate discharges one point at a time.

This is the species–reaction-graph injectivity route of Craciun and Feinberg ("Multiple equilibria in
complex chemical reaction networks: I. The injectivity property" and "II. The species–reaction graph"),
whose injectivity conclusion feeds the global-univalence theorem of Gale and Nikaido ("The Jacobian
matrix and global univalence of mappings"). The chart is the rational pivot minor of
`CRNT.Decision.StoichBasisQ`.

Depends on:
`CRNT.Multistationarity.PivotReducedInjectivity`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Matrix
open Equiv Equiv.Perm Finset Function CRNT.GaussianRank

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The cycle-cover term commutes with a ring homomorphism -/

/-- **The cycle-cover term commutes with a ring homomorphism.** For a ring hom `f : R₁ →+* R₂` and a
square matrix `M` over `R₁`, the cover term of the entrywise image `M.map f` at `σ` is the image of the
cover term of `M`: `coverTerm (M.map f) σ = f (coverTerm M σ)`. The cover term is a polynomial in the
entries with integer coefficient, which any ring hom preserves. -/
theorem coverTerm_map {n : Type*} [DecidableEq n] [Fintype n] {R₁ R₂ : Type*} [CommRing R₁]
    [CommRing R₂] (f : R₁ →+* R₂) (M : Matrix n n R₁) (σ : Perm n) :
    coverTerm (M.map f) σ = f (coverTerm M σ) := by
  rw [coverTerm, coverTerm, map_mul, map_intCast, map_prod]
  rfl

/-! ## The decidable rational cover-sign certificate, generic matrix level -/

variable {k : ℕ}

/-- **The rational reduced matrix `selRow · Mℚ · Bsec`.** With `Mℚ = massActionJacobianQ kq xq` the
rational Jacobian at a rational point and `Bsec = chartSectionQ ρ γ` the rational pivot-section chart,
this is the rational matrix whose real cast is the pivot-reduced Jacobian
`pivotSel ρ ∘ J ∘ concretePivotChart ρ γ`. -/
def reducedPivotMatrixQ (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R) (kq : N.R → ℚ)
    (xq : S → ℚ) : Matrix (Fin k) (Fin k) ℚ :=
  pivotRowSelQ ρ * N.massActionJacobianQ kq xq * N.chartSectionQ ρ γ

/-- **The reduced-pivot cover-sign condition over `ℚ`.** Reading `selRow · Mℚ · Bsec` as a plain
`k × k` rational matrix, this asks that every cycle-cover term of every principal submatrix is
nonnegative and the diagonal cover term of every principal submatrix is strictly positive — the
sign condition that makes every principal minor positive. -/
def PivotCoverSignQ (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R) (kq : N.R → ℚ) (xq : S → ℚ) :
    Prop :=
  ∀ s : Finset (Fin k),
    (∀ σ : Perm s,
        0 ≤ coverTerm ((N.reducedPivotMatrixQ ρ γ kq xq).submatrix
          (fun i : s => (i : Fin k)) (fun i : s => (i : Fin k))) σ) ∧
      0 < coverTerm ((N.reducedPivotMatrixQ ρ γ kq xq).submatrix
        (fun i : s => (i : Fin k)) (fun i : s => (i : Fin k))) (1 : Perm s)

/-- **The reduced-pivot cover-sign condition is decidable.** The reduced matrix is rational,
`coverTerm` is a rational polynomial in its entries, `ℚ` has decidable order, and the condition
quantifies only over the finite types `Finset (Fin k)` and `Perm s`. -/
instance decidablePivotCoverSignQ (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R)
    (kq : N.R → ℚ) (xq : S → ℚ) : Decidable (N.PivotCoverSignQ ρ γ kq xq) := by
  unfold PivotCoverSignQ
  infer_instance

/-- **A P-matrix from a rational cover-sign certificate, generic matrix level.** If a rational
`k × k` matrix `Mq` satisfies the cover-sign condition `PivotCoverSignQ` (every principal-submatrix
cover term nonnegative, diagonal cover term positive), then its real cast `Mq.map (Rat.castHom ℝ)` is
a P-matrix: each principal minor is a determinant whose cover terms cast from the nonnegative rational
ones (`coverTerm_map`, `Rat.cast_nonneg`) with a strictly positive diagonal term, so it is positive by
`det_pos_of_coverTerm_nonneg`. -/
theorem isPMatrix_map_of_pivotCoverSignQ (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R)
    (kq : N.R → ℚ) (xq : S → ℚ) (h : N.PivotCoverSignQ ρ γ kq xq) :
    ((N.reducedPivotMatrixQ ρ γ kq xq).map (Rat.castHom ℝ)).IsPMatrix := by
  intro s
  -- The principal submatrix of the cast is the cast of the principal submatrix.
  have hsub : ((N.reducedPivotMatrixQ ρ γ kq xq).map (Rat.castHom ℝ)).submatrix
      (fun i : s => (i : Fin k)) (fun i : s => (i : Fin k))
      = ((N.reducedPivotMatrixQ ρ γ kq xq).submatrix
          (fun i : s => (i : Fin k)) (fun i : s => (i : Fin k))).map (Rat.castHom ℝ) := rfl
  rw [hsub]
  set Mq := (N.reducedPivotMatrixQ ρ γ kq xq).submatrix
    (fun i : s => (i : Fin k)) (fun i : s => (i : Fin k)) with hMq
  obtain ⟨hnonneg, hdiag⟩ := h s
  refine det_pos_of_coverTerm_nonneg (Mq.map (Rat.castHom ℝ)) (fun σ => ?_) ?_
  · rw [coverTerm_map]
    exact_mod_cast (Rat.cast_nonneg.mpr (hnonneg σ))
  · rw [coverTerm_map]
    exact_mod_cast (Rat.cast_pos.mpr hdiag)

/-! ## The pivot-reduced Jacobian is the cast of the rational reduced matrix -/

/-- **The pivot-row selection as a rational/real selection matrix.** The pivot-row selection CLM
`pivotSel ρ` acts as the real cast of `pivotRowSelQ ρ`: `pivotSel ρ v = (pivotRowSelQ ρ).map cast *ᵥ v`.
Selecting the pivot rows of `v` is multiplication by the pivot-row selection matrix. -/
theorem pivotSel_eq_mulVec (ρ : Fin k → S) (v : S → ℝ) :
    pivotSel ρ v = ((pivotRowSelQ ρ).map (Rat.castHom ℝ)).mulVec v := by
  funext i
  rw [pivotSel_apply, Matrix.mulVec, dotProduct, Finset.sum_eq_single (ρ i)]
  · simp [pivotRowSelQ, Matrix.map_apply, Matrix.submatrix_apply, Matrix.one_apply]
  · intro b _ hb
    have hz : ((pivotRowSelQ ρ).map (Rat.castHom ℝ)) i b = 0 := by
      simp [pivotRowSelQ, Matrix.map_apply, Matrix.submatrix_apply, Matrix.one_apply,
        if_neg (Ne.symm hb)]
    rw [hz, zero_mul]
  · intro h'; exact absurd (Finset.mem_univ _) h'

/-- The matrix of the pivot-row selection CLM is the real cast of `pivotRowSelQ ρ`. -/
theorem toMatrix'_pivotSel (ρ : Fin k → S) :
    LinearMap.toMatrix' (pivotSel ρ : (S → ℝ) →ₗ[ℝ] (Fin k → ℝ))
      = (pivotRowSelQ ρ).map (Rat.castHom ℝ) := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply]
  exact pivotSel_eq_mulVec ρ v

/-- The matrix of the mass-action Jacobian CLM is the mass-action Jacobian matrix. -/
theorem toMatrix'_massActionJacobianCLM (N : Network S) (κ : N.RateConstants) (x : Concentration S) :
    LinearMap.toMatrix' (N.massActionJacobianCLM κ x : (S → ℝ) →ₗ[ℝ] (S → ℝ))
      = N.massActionJacobian κ x := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply]
  exact N.massActionJacobianCLM_apply κ x v

/-- The matrix of the concrete pivot chart CLM is the real section chart `chartSectionR ρ γ`. -/
theorem toMatrix'_concretePivotChart (N : Network S) (ρ : Fin k → S) (γ : Fin k → N.R) :
    LinearMap.toMatrix' (N.concretePivotChart ρ γ : (Fin k → ℝ) →ₗ[ℝ] (S → ℝ))
      = N.chartSectionR ρ γ := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply]
  exact N.concretePivotChart_apply ρ γ v

/-- **The pivot-reduced Jacobian is the oblique compression `selRow · J · Bℝ`.** With `J` the full
mass-action Jacobian at the chart point, `selRow = (pivotRowSelQ ρ) ⊗ ℝ`, and `Bℝ = chartSectionR ρ γ`,
the pivot-reduced (`k × k`) Jacobian matrix equals the matrix product. -/
theorem pivotReducedJacobian_eq_mul (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (ρ : Fin k → S) (γ : Fin k → N.R) (y : Fin k → ℝ) :
    N.pivotReducedJacobian κ x₀ ρ (N.concretePivotChart ρ γ) y
      = ((pivotRowSelQ ρ).map (Rat.castHom ℝ))
          * N.massActionJacobian κ (pivotAffineChart x₀ (N.concretePivotChart ρ γ) y)
          * N.chartSectionR ρ γ := by
  rw [pivotReducedJacobian, jacobianMatrix, pivotReducedJacobianCLM]
  show LinearMap.toMatrix'
      ((pivotSel ρ : (S → ℝ) →ₗ[ℝ] (Fin k → ℝ)) ∘ₗ
        ((N.massActionJacobianCLM κ (pivotAffineChart x₀ (N.concretePivotChart ρ γ) y) :
          (S → ℝ) →ₗ[ℝ] (S → ℝ)) ∘ₗ
          (N.concretePivotChart ρ γ : (Fin k → ℝ) →ₗ[ℝ] (S → ℝ)))) = _
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, toMatrix'_pivotSel,
    N.toMatrix'_massActionJacobianCLM, N.toMatrix'_concretePivotChart, Matrix.mul_assoc]

/-- **The pivot-reduced Jacobian at a rational point is the cast of the rational reduced matrix.**
Suppose the chart point `pivotAffineChart x₀ B y` is the real cast of a rational concentration `xq`
(`hpt`) and the rate constants are the casts of `kq` (`hk`). Then the pivot-reduced Jacobian matrix is
the entrywise real cast of `reducedPivotMatrixQ ρ γ kq xq`: the selection and section factors cast on
the nose (`pivotRowSelQ`, `chartSectionR = chartSectionQ ⊗ ℝ`) and the middle Jacobian casts by
`massActionJacobianQ_map_eq`. -/
theorem pivotReducedJacobian_eq_map (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (ρ : Fin k → S) (γ : Fin k → N.R) (y : Fin k → ℝ) (kq : N.R → ℚ) (xq : S → ℚ)
    (hk : ∀ r, κ.k r = (kq r : ℝ))
    (hpt : pivotAffineChart x₀ (N.concretePivotChart ρ γ) y = fun s => ((xq s : ℝ))) :
    N.pivotReducedJacobian κ x₀ ρ (N.concretePivotChart ρ γ) y
      = (N.reducedPivotMatrixQ ρ γ kq xq).map (Rat.castHom ℝ) := by
  rw [pivotReducedJacobian_eq_mul, hpt, reducedPivotMatrixQ, Matrix.map_mul, Matrix.map_mul,
    ← N.massActionJacobianQ_map_eq kq xq κ hk]
  rfl

/-! ## The pointwise P-matrix verdict at the network level -/

/-- **The decidable rational cover-sign certificate makes the pivot-reduced Jacobian a P-matrix.**
Fix the concrete pivot chart `B = concretePivotChart ρ γ`. At a pivot coordinate `y` whose chart point
`x₀ + B y` is a rational concentration (`hpt`, with rational rate constants `hk`), if the decidable
rational cover-sign certificate `PivotCoverSignQ ρ γ kq xq` holds, then the pivot-reduced Jacobian
`pivotSel ρ ∘ J ∘ B` is a P-matrix at `y`. The pivot-reduced Jacobian is the real cast of the rational
reduced matrix (`pivotReducedJacobian_eq_map`), and the rational cover-sign condition makes that cast a
P-matrix (`isPMatrix_map_of_pivotCoverSignQ`).

This discharges the per-point instances of the box hypothesis `hpm` of
`massActionInjectiveOnClass_of_concretePivotChart` by a finite rational decision; the box-quantified
verdict is not obtained from a single point, since the reduced cover-sign pattern is concentration
dependent. -/
theorem isPMatrix_pivotReducedJacobian_of_pivotCoverSignQ (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (ρ : Fin k → S) (γ : Fin k → N.R) (y : Fin k → ℝ) (kq : N.R → ℚ)
    (xq : S → ℚ) (hk : ∀ r, κ.k r = (kq r : ℝ))
    (hpt : pivotAffineChart x₀ (N.concretePivotChart ρ γ) y = fun s => ((xq s : ℝ)))
    (h : N.PivotCoverSignQ ρ γ kq xq) :
    (N.pivotReducedJacobian κ x₀ ρ (N.concretePivotChart ρ γ) y).IsPMatrix := by
  rw [N.pivotReducedJacobian_eq_map κ x₀ ρ γ y kq xq hk hpt]
  exact N.isPMatrix_map_of_pivotCoverSignQ ρ γ kq xq h

end Network

end CRNT

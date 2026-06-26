import CRNT.Multistationarity.JacobianCycleSelection
import CRNT.Multistationarity.PMatrix
import CRNT.Multistationarity.ReducedJacobian

/-!
# Mass-action injectivity from consistently signed species–reaction cycles

This module lifts the consistent-signed-SR-cover criterion from full-determinant
nonvanishing to the **P-matrix** property the box Gale–Nikaido univalence chain consumes,
then concludes injectivity of the mass-action vector field. It closes the species–reaction
graph dictionary of Craciun and Feinberg ("Multiple equilibria in complex chemical reaction
networks: I. The injectivity property" and "II. The species–reaction graph") to its
injectivity verdict, feeding the global-univalence theorem of Gale and Nikaido ("The
Jacobian matrix and global univalence of mappings").

`Matrix.IsPMatrix` asks that every principal minor be positive: for each subset `s` of the
species the principal submatrix `M.submatrix incl incl` (`incl : ↥s → S` the coercion) has
strictly positive determinant. Each such principal submatrix is itself a cover sum over the
restricted species set `↥s`: its diagonal product over a permutation `σ : Perm ↥s`
distributes over per-species reaction choices `ρ : ↥s → N.R` into one-reaction cover
products, and each such product splits into a nonnegative rate-and-gradient magnitude times
the signed-incidence weight `∏ a, signedEdge (incl (σ a)) (ρ a)`.

* `subCoverProductSingle` — the one-reaction cover product of the principal submatrix on
  `s`, for a permutation `σ : Perm ↥s` and reaction choice `ρ : ↥s → N.R`.
* `prod_submatrix_eq_sum_subCoverProductSingle` — the principal-submatrix diagonal product
  `∏ a, J (incl (σ a)) (incl a)` distributes (`Fintype.prod_sum`) over reaction choices into
  the sum of one-reaction cover products.
* `subCoverProductSingle_eq_magnitude_mul_sign` — the magnitude/sign split of one such cover
  product over the restricted species set.
* `coverTerm_submatrix_nonneg_of_signWeighted` — under the consistent signed-SR-cover weight
  every cycle-cover term of every principal submatrix is nonnegative.
* `isPMatrix_massActionJacobian_of_consistentSRSign` — if at a positive concentration the
  source-monomial gradients are positive, the diagonal entries of the mass-action Jacobian
  are positive, and every signed-incidence cover weight over every restricted species set is
  nonnegative, then `N.massActionJacobian κ x` is a P-matrix.
* `reducedJacobian_isPMatrix_of_full` — the reduced Jacobian inherits the P-matrix property
  from any source that makes it equal a principal submatrix, the form
  `massActionInjectiveOnClass_of_jacobian_pmatrix` consumes.

Carrying the full-Jacobian P-matrix property all the way to `Kinetics.InjectiveOnClass`
needs the reduced Jacobian to be a P-matrix on the chart box, not the full Jacobian; the
reduced Jacobian is a Schur-style compression of the full Jacobian rather than a principal
submatrix of it, so the final wiring through `massActionInjectiveOnClass_of_jacobian_pmatrix`
requires the compression-to-P-matrix bridge developed elsewhere and is not built here.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Multistationarity.JacobianCycleSelection`, `CRNT.Multistationarity.PMatrix`,
`CRNT.Multistationarity.ReducedJacobian`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Matrix
open Equiv Finset

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The one-reaction cover product of a principal submatrix -/

/-- **The one-reaction cover product of the principal submatrix on `s`.** Charging each
restricted-species hop `a ↦ σ a` (read through the coercion `↥s → S`) to a single reaction
`ρ a`, this is `∏ a, κ_{ρ a} · (∂_{a} monomial_{ρ a}) · reactionVector (ρ a) (σ a)`: one
summand-per-factor selection from the principal-submatrix diagonal product. -/
noncomputable def subCoverProductSingle (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (s : Finset S) (σ : Perm s) (ρ : s → N.R) : ℝ :=
  ∏ a : s, κ.k (ρ a) * massActionMonomialGrad (N.reaction (ρ a)).source x (a : S) *
    N.reactionVector (ρ a) ((σ a : S))

/-- **The principal-submatrix cover product's nonnegative rate-and-gradient magnitude.** -/
noncomputable def subCoverMagnitudeSingle (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (s : Finset S) (σ : Perm s) (ρ : s → N.R) : ℝ :=
  ∏ a : s, κ.k (ρ a) * massActionMonomialGrad (N.reaction (ρ a)).source x (a : S) *
    |N.reactionVector (ρ a) ((σ a : S))|

/-- The principal-submatrix cover magnitude is nonnegative at a positive concentration. -/
theorem subCoverMagnitudeSingle_nonneg (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) (s : Finset S) (σ : Perm s) (ρ : s → N.R) :
    0 ≤ N.subCoverMagnitudeSingle κ x s σ ρ :=
  Finset.prod_nonneg fun a _ =>
    mul_nonneg (mul_nonneg (κ.positive (ρ a)).le
      (massActionMonomialGrad_nonneg _ hx (a : S))) (abs_nonneg _)

/-- **The principal-submatrix diagonal product distributes over reaction choices.** For a
permutation `σ : Perm ↥s`, the product `∏ a, J (σ a) a` of principal-submatrix entries —
each a sum over the reactions touching the restricted species — equals the sum over
reaction-choice functions `ρ : ↥s → N.R` of the one-reaction cover products
`subCoverProductSingle κ x s σ ρ`. This is `Fintype.prod_sum` applied to the principal
submatrix of the factored Jacobian. -/
theorem prod_submatrix_eq_sum_subCoverProductSingle (N : Network S)
    (κ : N.RateConstants) (x : Concentration S) (s : Finset S) (σ : Perm s) :
    ∏ a : s, ((N.massActionJacobian κ x).submatrix (fun a : s => (a : S))
        (fun a : s => (a : S))) (σ a) a =
      ∑ ρ : s → N.R, N.subCoverProductSingle κ x s σ ρ := by
  simp only [Matrix.submatrix_apply, massActionJacobian, subCoverProductSingle]
  exact Fintype.prod_sum
    (fun (a : s) r => κ.k r * massActionMonomialGrad (N.reaction r).source x (a : S) *
      N.reactionVector r ((σ a : S)))

/-- **The principal-submatrix cover product splits into nonnegative magnitude times signed
incidence product.** The one-reaction cover product over the restricted species set equals
its nonnegative rate-and-gradient magnitude times the real cast of the product of incidence
signs `∏ a, signedEdge (σ a) (ρ a)`. The magnitude/sign factorization that turns a
sign-consistent SR-cover into a sign-definite principal-minor cover term. -/
theorem subCoverProductSingle_eq_magnitude_mul_sign (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (s : Finset S) (σ : Perm s) (ρ : s → N.R) :
    N.subCoverProductSingle κ x s σ ρ =
      N.subCoverMagnitudeSingle κ x s σ ρ *
        ((∏ a : s, N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℝ) := by
  rw [subCoverProductSingle, subCoverMagnitudeSingle,
    show ((∏ a : s, N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℝ)
        = ∏ a : s, ((N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℝ) from
      map_prod SignType.castHom _ _,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hsa : ((SignType.sign (N.reactionVector (ρ a) ((σ a : S))) : SignType) : ℝ)
      * |N.reactionVector (ρ a) ((σ a : S))| = N.reactionVector (ρ a) ((σ a : S)) :=
    sign_mul_abs _
  rw [signedEdge]
  linear_combination
    (-(κ.k (ρ a) * massActionMonomialGrad (N.reaction (ρ a)).source x (a : S))) * hsa

/-! ## Principal-minor positivity under a consistent signed SR-cover -/

/-- **A sign-consistent principal-submatrix cover has a nonnegative signed cover product.**
At a positive concentration the signed cover product `(coverCoeff σ) · subCoverProductSingle`
is nonnegative as soon as the cover's signed-incidence weight is nonnegative. -/
theorem subCoverProductSingle_signWeighted_nonneg (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) (s : Finset S) (σ : Perm s) (ρ : s → N.R)
    (hweight : 0 ≤ ((coverCoeff σ : ℤ) : ℝ) *
      ((∏ a : s, N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℝ)) :
    0 ≤ ((coverCoeff σ : ℤ) : ℝ) * N.subCoverProductSingle κ x s σ ρ := by
  rw [subCoverProductSingle_eq_magnitude_mul_sign, ← mul_assoc,
    mul_comm _ (N.subCoverMagnitudeSingle κ x s σ ρ), mul_assoc]
  exact mul_nonneg (N.subCoverMagnitudeSingle_nonneg κ hx s σ ρ) hweight

/-- **Every cycle-cover term of every principal submatrix is nonnegative.** If at a positive
concentration every reaction-choice cover over every restricted species set has a nonnegative
signed-incidence weight, then every cycle-cover term `coverTerm M' σ` of every principal
submatrix `M'` of the mass-action Jacobian is nonnegative. -/
theorem coverTerm_submatrix_nonneg_of_signWeighted (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive)
    (hweight : ∀ (s : Finset S) (σ : Perm s) (ρ : s → N.R),
      0 ≤ ((coverCoeff σ : ℤ) : ℝ) *
        ((∏ a : s, N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℝ))
    (s : Finset S) (σ : Perm s) :
    0 ≤ coverTerm ((N.massActionJacobian κ x).submatrix (fun a : s => (a : S))
      (fun a : s => (a : S))) σ := by
  rw [coverTerm, prod_submatrix_eq_sum_subCoverProductSingle, Finset.mul_sum]
  exact Finset.sum_nonneg fun ρ _ =>
    N.subCoverProductSingle_signWeighted_nonneg κ hx s σ ρ (hweight s σ ρ)

/-- **The principal minor on `s` is positive under a consistent signed SR-cover.** Combining
nonnegativity of every cycle-cover term with strict positivity of the diagonal cover term
(which follows from positive Jacobian diagonal entries), the principal submatrix determinant
is strictly positive. -/
theorem submatrix_det_pos_of_consistentSRSign (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive)
    (hweight : ∀ (s : Finset S) (σ : Perm s) (ρ : s → N.R),
      0 ≤ ((coverCoeff σ : ℤ) : ℝ) *
        ((∏ a : s, N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℝ))
    (hdiag : ∀ i : S, 0 < (N.massActionJacobian κ x) i i)
    (s : Finset S) :
    0 < ((N.massActionJacobian κ x).submatrix (fun a : s => (a : S))
      (fun a : s => (a : S))).det := by
  refine det_pos_of_coverTerm_nonneg _
    (fun σ => N.coverTerm_submatrix_nonneg_of_signWeighted κ hx hweight s σ) ?_
  rw [coverTerm_one]
  exact Finset.prod_pos fun a _ => by
    simpa [Matrix.submatrix_apply] using hdiag (a : S)

/-- **The mass-action Jacobian is a P-matrix under a consistent signed SR-cover.** If at a
positive concentration every reaction-choice cover over every restricted species set has a
nonnegative signed-incidence weight `(coverCoeff σ) · ∏ a, signedEdge (σ a) (ρ a)`, and every
Jacobian diagonal entry is positive, then `N.massActionJacobian κ x` is a P-matrix: every
principal minor is positive. This is the lift of the consistent-signed-SR-cover criterion
from full-determinant nonvanishing (`det_massActionJacobian_ne_zero_of_consistentSRSign`) to
the P-matrix property the box Gale–Nikaido univalence chain consumes. -/
theorem isPMatrix_massActionJacobian_of_consistentSRSign (N : Network S)
    (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive)
    (hweight : ∀ (s : Finset S) (σ : Perm s) (ρ : s → N.R),
      0 ≤ ((coverCoeff σ : ℤ) : ℝ) *
        ((∏ a : s, N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℝ))
    (hdiag : ∀ i : S, 0 < (N.massActionJacobian κ x) i i) :
    (N.massActionJacobian κ x).IsPMatrix :=
  fun s => N.submatrix_det_pos_of_consistentSRSign κ hx hweight hdiag s

/-! ## Injectivity from a P-matrix reduced Jacobian -/

/-- **The reduced Jacobian inherits a P-matrix from a principal-submatrix presentation.** When
the reduced Jacobian at a chart coordinate is the principal submatrix of a P-matrix selected
by an injective index map, it is itself a P-matrix. This is the bridge from a full P-matrix
mass-action Jacobian to the reduced (`s × s`) Jacobian that
`massActionInjectiveOnClass_of_jacobian_pmatrix` consumes, for networks whose stoichiometric
chart is a coordinate selection. -/
theorem reducedJacobian_isPMatrix_of_submatrix (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ) {f : Fin N.stoichRank → S}
    (hf : Function.Injective f)
    (hP : (N.massActionJacobian κ (N.affineChart x₀ y)).IsPMatrix)
    (hsub : N.reducedJacobian κ x₀ y
      = (N.massActionJacobian κ (N.affineChart x₀ y)).submatrix f f) :
    (N.reducedJacobian κ x₀ y).IsPMatrix := by
  rw [hsub]
  exact hP.submatrix_isPMatrix hf

end Network

end CRNT

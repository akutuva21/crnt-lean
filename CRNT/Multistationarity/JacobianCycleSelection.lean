import CRNT.Multistationarity.JacobianCycleSign

/-!
# Selecting a sign-consistent SR-cover of the mass-action Jacobian

This module closes the algebraic half of the Craciun–Feinberg species–reaction-graph
dictionary (Craciun and Feinberg, "Multiple equilibria in complex chemical reaction
networks: I. The injectivity property" and "II. The species–reaction graph"). The
Leibniz expansion of the mass-action Jacobian determinant groups into cycle-cover terms
`coverTerm`, one per permutation `σ`; each such term is a product over species of a
Jacobian diagonal entry, and each entry is itself a sum over the reactions that touch
that species. Distributing the product over the per-species reaction choices turns one
cycle-cover term into a sum over reaction-choice functions `ρ : S → N.R` of the
one-reaction cover products `coverProductSingle` already factored in
`CRNT.Multistationarity.JacobianCycleSign`.

* `prod_massActionJacobian_eq_sum_coverProductSingle` — the Jacobian diagonal product
  `∏ i, J (σ i) i` is the sum over reaction choices `ρ` of `coverProductSingle κ x σ ρ`,
  the `Fintype.prod_sum` distribution of the product-of-sums Jacobian entries.
* `coverTerm_massActionJacobian_eq_sum` — consequently the cycle-cover term
  `coverTerm J σ` is `(coverCoeff σ) · ∑ ρ, coverProductSingle κ x σ ρ`, the
  signed sum of one-reaction cover products.
* `coverProductSingle_signWeighted_nonneg` — at a positive concentration with positive
  source-monomial gradients, the signed cover product `(coverCoeff σ) · coverProductSingle`
  is nonnegative as soon as the cover's signed-incidence weight
  `(coverCoeff σ) · ∏ i, signedEdge (σ i) (ρ i)` is nonnegative: the magnitude/sign split
  of `coverProductSingle_eq_magnitude_mul_sign` carries the sign verdict.
* `coverTerm_nonneg_of_signWeighted` — under that consistent SR-sign weight every
  cycle-cover term of the Jacobian is nonnegative.
* `det_massActionJacobian_ne_zero_of_consistentSRSign` — the consistent-SR-sign criterion:
  if every signed SR-cover weight is nonnegative and the identity (diagonal) cover product
  is strictly positive, then `det_ne_zero_of_coverTerm_signDefinite` fires and the
  mass-action Jacobian determinant is nonzero. A nonzero Jacobian determinant is the
  kernel-emptiness conclusion underlying the injectivity theory.

The selection wired here is the nonnegative branch; the strictly-negative branch is
symmetric. Carrying the nonzero-determinant conclusion all the way to injectivity of the
mass-action vector field additionally needs the box Gale–Nikaido P-matrix chain
(`CRNT.Multistationarity.GaleNikaidoUniv.injOn_of_pmatrix_fderiv`), which asks for all
principal minors positive rather than only the full determinant nonzero; that bridge is
not built here.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Multistationarity.JacobianCycleSign`.
-/

namespace CRNT

namespace Network

open scoped BigOperators
open Equiv Finset

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## Distributing the Jacobian diagonal product over reaction choices -/

/-- **The Jacobian diagonal product distributes over the per-species reaction choices.**
For a permutation `σ`, the product `∏ i, J (σ i) i` of mass-action Jacobian entries —
each entry a sum over the reactions touching species `i` — equals the sum over
reaction-choice functions `ρ : S → N.R` of the one-reaction cover products
`coverProductSingle κ x σ ρ`. This is `Fintype.prod_sum` applied to the
product-of-sums shape of the factored Jacobian. -/
theorem prod_massActionJacobian_eq_sum_coverProductSingle (N : Network S)
    (κ : N.RateConstants) (x : Concentration S) (σ : Perm S) :
    ∏ i, (N.massActionJacobian κ x) (σ i) i =
      ∑ ρ : S → N.R, N.coverProductSingle κ x σ ρ := by
  simp only [massActionJacobian, coverProductSingle]
  exact Fintype.prod_sum
    (fun i r => κ.k r * massActionMonomialGrad (N.reaction r).source x i *
      N.reactionVector r (σ i))

/-- **The cycle-cover term as a signed sum of one-reaction cover products.** The
cycle-cover term `coverTerm J σ` of the mass-action Jacobian is its cover coefficient
`coverCoeff σ` times the sum over reaction choices `ρ` of the one-reaction cover
products. Each summand `(coverCoeff σ : ℝ) · coverProductSingle κ x σ ρ` is a single
signed SR-cover contribution to the determinant. -/
theorem coverTerm_massActionJacobian_eq_sum (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (σ : Perm S) :
    coverTerm (N.massActionJacobian κ x) σ =
      ((coverCoeff σ : ℤ) : ℝ) * ∑ ρ : S → N.R, N.coverProductSingle κ x σ ρ := by
  rw [coverTerm, prod_massActionJacobian_eq_sum_coverProductSingle]

/-! ## The consistent signed SR-cover criterion -/

/-- **A signed-incidence-consistent SR-cover has a nonnegative signed cover product.** At
a positive concentration with positive source-monomial gradients along the cover, the
signed cover product `(coverCoeff σ) · coverProductSingle κ x σ ρ` is nonnegative as soon
as the cover's signed-incidence weight `(coverCoeff σ) · ∏ i, signedEdge (σ i) (ρ i)` is
nonnegative. The nonnegative rate-and-gradient magnitude of
`coverProductSingle_eq_magnitude_mul_sign` carries the inequality. -/
theorem coverProductSingle_signWeighted_nonneg (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) (σ : Perm S) (ρ : S → N.R)
    (hweight : 0 ≤ ((coverCoeff σ : ℤ) : ℝ) *
      ((∏ i, N.signedEdge (σ i) (ρ i) : SignType) : ℝ)) :
    0 ≤ ((coverCoeff σ : ℤ) : ℝ) * N.coverProductSingle κ x σ ρ := by
  rw [coverProductSingle_eq_magnitude_mul_sign, ← mul_assoc, mul_comm _ (N.coverMagnitudeSingle κ x σ ρ),
    mul_assoc]
  exact mul_nonneg (N.coverMagnitudeSingle_nonneg κ hx σ ρ) hweight

/-- **Every cycle-cover term is nonnegative under a consistent signed SR-cover weight.**
If at a positive concentration every reaction-choice cover has a nonnegative
signed-incidence weight, then every cycle-cover term `coverTerm J σ` of the mass-action
Jacobian is nonnegative. The cover coefficient distributes across the reaction-choice sum
(`coverTerm_massActionJacobian_eq_sum`) and each signed summand is nonnegative. -/
theorem coverTerm_nonneg_of_signWeighted (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive)
    (hweight : ∀ (σ : Perm S) (ρ : S → N.R),
      0 ≤ ((coverCoeff σ : ℤ) : ℝ) *
        ((∏ i, N.signedEdge (σ i) (ρ i) : SignType) : ℝ))
    (σ : Perm S) :
    0 ≤ coverTerm (N.massActionJacobian κ x) σ := by
  rw [coverTerm_massActionJacobian_eq_sum, Finset.mul_sum]
  exact Finset.sum_nonneg fun ρ _ =>
    N.coverProductSingle_signWeighted_nonneg κ hx σ ρ (hweight σ ρ)

/-- **The consistent signed SR-cover criterion (sign half of the Craciun–Feinberg
dictionary).** If at a positive concentration every reaction-choice cover of the
mass-action Jacobian has a nonnegative signed-incidence weight `(coverCoeff σ) · ∏ i,
signedEdge (σ i) (ρ i)`, and the identity (diagonal) cover product is strictly positive,
then the mass-action Jacobian determinant is nonzero. Consistently signed
species–reaction-graph cycles thus preclude a singular Jacobian — the kernel-emptiness
conclusion driving the injectivity theory. -/
theorem det_massActionJacobian_ne_zero_of_consistentSRSign (N : Network S)
    (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive)
    (hweight : ∀ (σ : Perm S) (ρ : S → N.R),
      0 ≤ ((coverCoeff σ : ℤ) : ℝ) *
        ((∏ i, N.signedEdge (σ i) (ρ i) : SignType) : ℝ))
    (hdiag : 0 < coverTerm (N.massActionJacobian κ x) (1 : Perm S)) :
    (N.massActionJacobian κ x).det ≠ 0 :=
  det_ne_zero_of_coverTerm_signDefinite _
    (Or.inl ⟨N.coverTerm_nonneg_of_signWeighted κ hx hweight, hdiag⟩)

end Network

end CRNT

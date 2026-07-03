import CRNT.Multistationarity.JacobianDeterminantSign
import CRNT.Multistationarity.SignedSRGraph
import CRNT.Multistationarity.SRGraphCycleDict
import CRNT.Kinetics.MassActionJacobian

/-!
# The Jacobian cycle-cover term as a magnitude times signed SR-cycle signs

The species–reaction-graph criterion of Craciun and Feinberg ("Multiple equilibria in
complex chemical reaction networks: I. The injectivity property") reads the sign of a
cycle-cover term of the mass-action Jacobian off the signed SR-graph. The Jacobian
factors as `J = stoich · diag(rate) · grad`: entry `(i, j)` is
`∑ r, κ_r · (∂_j monomial_r) · reactionVector r i`. When a single reaction `ρ i` is
charged with each species hop `i ↦ σ i`, the resulting one-reaction cover product
`∏ i, κ_{ρ i} · (∂_i monomial_{ρ i}) · reactionVector (ρ i) (σ i)` splits cleanly into a
**nonnegative magnitude** — the rate-and-gradient product — and a **sign** that is the
product of the incidence signs `signedEdge (σ i) (ρ i)` carried by the cover.

* `massActionMonomialGrad_nonneg` — at a positive concentration the source-monomial
  gradient is nonnegative, so the rate-and-gradient magnitudes are nonnegative.
* `walkSign_srStep` — one species→reaction→species segment carries the product of its
  two incidence signs `signedEdge s r · signedEdge s' r`.
* `walkSign_srOrbitWalk` / `walkSign_srCycleWalk` — the orbit (resp. closed orbit) walk
  sign is the product over the orbit of those two-incidence segment signs.
* `coverProductSingle` — the one-reaction cover product of the factored Jacobian for a
  permutation `σ` and a reaction choice `ρ`.
* `sign_coverProductSingle` — when the rate-and-gradient factors are strictly positive,
  its `SignType.sign` is the product of the cover's incidence signs
  `∏ i, signedEdge (σ i) (ρ i)`.
* `coverProductSingle_eq_magnitude_mul_sign` — the cover product is its nonnegative
  rate-and-gradient magnitude times the real cast of that product of incidence signs:
  the magnitude/sign split driving the consistent-cycle-sign criterion.

The Leibniz expansion groups the full Jacobian cover term `coverTerm` over reaction
choices; the per-choice identity proved here is the factorization of a single such
choice. The selection of a sign-consistent cover for an arbitrary network — the
remaining combinatorial half of the dictionary — is not carried out here.

Depends on:
`CRNT.Multistationarity.JacobianDeterminantSign`,
`CRNT.Multistationarity.SignedSRGraph`,
`CRNT.Multistationarity.SRGraphCycleDict`, `CRNT.Kinetics.MassActionJacobian`.
-/

namespace CRNT

namespace Network

open scoped BigOperators
open Equiv SimpleGraph Finset

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## Nonnegativity of the gradient magnitude -/

/-- **At a positive concentration the source-monomial gradient is nonnegative.** The
gradient `(y j) · x_j^(y j − 1) · ∏_{s ≠ j} x_s^(y s)` is a product of a natural-number
cast and positive powers, so it is nonnegative. The rate-and-gradient magnitudes of the
factored Jacobian are therefore nonnegative. -/
theorem massActionMonomialGrad_nonneg (y : Complex S) {x : Concentration S}
    (hx : x.Positive) (j : S) : 0 ≤ massActionMonomialGrad y x j := by
  refine mul_nonneg (mul_nonneg (by positivity) ?_) ?_
  · exact pow_nonneg (hx j).le _
  · exact Finset.prod_nonneg fun s _ => pow_nonneg (hx s).le _

/-! ## Walk signs of the orbit cover -/

/-- **A single species→reaction→species segment carries the product of its two incidence
signs.** The two steps `s—r` and `r—s'` of `srStep s s' r` contribute `signedEdge s r`
and `signedEdge s' r`. -/
theorem walkSign_srStep (N : Network S) (s s' : S) (r : N.R)
    (h1 : N.OccursIn s r) (h2 : N.OccursIn s' r) :
    N.walkSign (N.srStep s s' r h1 h2) = N.signedEdge s r * N.signedEdge s' r := by
  rw [srStep, walkSign_cons, walkSign_cons, walkSign_nil, mul_one]
  have e0 : N.edgeSignAt
      (Walk.cons (show N.srGraph.Adj (Sum.inl s) (Sum.inr r) from h1)
        (Walk.cons (show N.srGraph.Adj (Sum.inr r) (Sum.inl s') from h2) Walk.nil)) 0
      = N.signedEdge s r := by
    simp [edgeSignAt]
  have e1 : N.edgeSignAt
      (Walk.cons (show N.srGraph.Adj (Sum.inr r) (Sum.inl s') from h2) Walk.nil) 0
      = N.signedEdge s' r := by
    simp [edgeSignAt]
  rw [e0, e1]

/-- **The orbit walk sign is the product over the orbit of the two-incidence segment
signs.** Following `σ` from `s` through the reaction choice `ρ`, each hop `t ↦ σ t`
contributes the segment sign `signedEdge t (ρ t) · signedEdge (σ t) (ρ t)`. -/
theorem walkSign_srOrbitWalk (N : Network S) (σ : Perm S) (ρ : S → N.R)
    (hocc : ∀ t : S, N.OccursIn t (ρ t) ∧ N.OccursIn (σ t) (ρ t)) (s : S) :
    ∀ k : ℕ, N.walkSign (N.srOrbitWalk σ ρ hocc s k) =
      ∏ j ∈ Finset.range k,
        N.signedEdge (σ^[j] s) (ρ (σ^[j] s)) * N.signedEdge (σ (σ^[j] s)) (ρ (σ^[j] s))
  | 0 => by rw [Finset.range_zero, Finset.prod_empty]; rfl
  | (k + 1) => by
      rw [srOrbitWalk, walkSign_append, walkSign_copy, walkSign_srStep,
        walkSign_srOrbitWalk N σ ρ hocc s k, Finset.prod_range_succ]

/-- **The closed orbit walk sign is the product over the closed orbit of the
two-incidence segment signs.** -/
theorem walkSign_srCycleWalk (N : Network S) (σ : Perm S) (ρ : S → N.R)
    (hocc : ∀ t : S, N.OccursIn t (ρ t) ∧ N.OccursIn (σ t) (ρ t)) (s : S) (k : ℕ)
    (hk : σ^[k] s = s) :
    N.walkSign (N.srCycleWalk σ ρ hocc s k hk) =
      ∏ j ∈ Finset.range k,
        N.signedEdge (σ^[j] s) (ρ (σ^[j] s)) * N.signedEdge (σ (σ^[j] s)) (ρ (σ^[j] s)) := by
  rw [srCycleWalk, walkSign_copy, walkSign_srOrbitWalk]

/-! ## The one-reaction cover product of the factored Jacobian -/

/-- **The one-reaction cover product.** Charging each species hop `i ↦ σ i` to a single
reaction `ρ i`, this is `∏ i, κ_{ρ i} · (∂_i monomial_{ρ i}) · reactionVector (ρ i) (σ i)`:
one summand-per-factor selection from the factored Jacobian diagonal product
`∏ i, J (σ i) i`. -/
noncomputable def coverProductSingle (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (σ : Perm S) (ρ : S → N.R) : ℝ :=
  ∏ i, κ.k (ρ i) * massActionMonomialGrad (N.reaction (ρ i)).source x i *
    N.reactionVector (ρ i) (σ i)

/-- **The cover product's nonnegative rate-and-gradient magnitude.** The product of the
nonnegative rate-and-gradient factors and the absolute reaction-vector entries. -/
noncomputable def coverMagnitudeSingle (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (σ : Perm S) (ρ : S → N.R) : ℝ :=
  ∏ i, κ.k (ρ i) * massActionMonomialGrad (N.reaction (ρ i)).source x i *
    |N.reactionVector (ρ i) (σ i)|

/-- The cover magnitude is nonnegative at a positive concentration. -/
theorem coverMagnitudeSingle_nonneg (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) (σ : Perm S) (ρ : S → N.R) :
    0 ≤ N.coverMagnitudeSingle κ x σ ρ :=
  Finset.prod_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (κ.positive (ρ i)).le
      (massActionMonomialGrad_nonneg _ hx i)) (abs_nonneg _)

/-- **The cover product's sign is the product of the cover's incidence signs.** When the
rate-and-gradient factors are strictly positive — positive rate constant, and a positive
source-monomial gradient at each species (the nondegeneracy that each chosen reaction
genuinely depends on its species) — the `SignType` sign of the cover product is
`∏ i, signedEdge (σ i) (ρ i)`. -/
theorem sign_coverProductSingle (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (σ : Perm S) (ρ : S → N.R)
    (hgrad : ∀ i, 0 < massActionMonomialGrad (N.reaction (ρ i)).source x i) :
    SignType.sign (N.coverProductSingle κ x σ ρ) =
      ∏ i, N.signedEdge (σ i) (ρ i) := by
  rw [coverProductSingle,
    show SignType.sign (∏ i, κ.k (ρ i) *
          massActionMonomialGrad (N.reaction (ρ i)).source x i * N.reactionVector (ρ i) (σ i))
        = ∏ i, SignType.sign (κ.k (ρ i) *
          massActionMonomialGrad (N.reaction (ρ i)).source x i * N.reactionVector (ρ i) (σ i)) from
      map_prod signHom _ _]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sign_mul, sign_mul, signedEdge, sign_pos (κ.positive (ρ i)), sign_pos (hgrad i),
    one_mul, one_mul]

/-- **The cover product splits into nonnegative magnitude times signed incidence
product.** The one-reaction cover product equals its nonnegative rate-and-gradient
magnitude times the real cast of the product of incidence signs `∏ i, signedEdge (σ i)
(ρ i)`. This is the magnitude/sign factorization that turns a sign-consistent SR-cover
into a sign-definite Jacobian cover term, feeding the consistent-cycle-sign criterion. -/
theorem coverProductSingle_eq_magnitude_mul_sign (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (σ : Perm S) (ρ : S → N.R) :
    N.coverProductSingle κ x σ ρ =
      N.coverMagnitudeSingle κ x σ ρ *
        ((∏ i, N.signedEdge (σ i) (ρ i) : SignType) : ℝ) := by
  rw [coverProductSingle, coverMagnitudeSingle,
    show ((∏ i, N.signedEdge (σ i) (ρ i) : SignType) : ℝ)
        = ∏ i, ((N.signedEdge (σ i) (ρ i) : SignType) : ℝ) from
      map_prod SignType.castHom _ _,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hsa : ((SignType.sign (N.reactionVector (ρ i) (σ i)) : SignType) : ℝ)
      * |N.reactionVector (ρ i) (σ i)| = N.reactionVector (ρ i) (σ i) :=
    sign_mul_abs _
  rw [signedEdge]
  linear_combination (-(κ.k (ρ i) * massActionMonomialGrad (N.reaction (ρ i)).source x i)) * hsa

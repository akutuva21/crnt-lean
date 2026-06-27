import CRNT.Multistationarity.SRCycleInjectivity

/-!
# Point-independence of the consistent signed species–reaction cover verdict

The consistent-signed-SR-cover criterion of `SRCycleInjectivity` makes the full mass-action
Jacobian a P-matrix at a positive concentration. The magnitude/sign split
`subCoverProductSingle_eq_magnitude_mul_sign` factors each one-reaction cover product of every
principal submatrix into a **nonnegative rate-and-gradient magnitude**, which carries all of the
concentration dependence, times a **point-independent signed-incidence weight**
`∏ a, signedEdge (σ a) (ρ a)` built only from the network's signed species–reaction graph. The
sign verdict is therefore determined entirely by point-independent incidence data: the cover-sign
pattern does not move with the concentration.

This module makes that point-independence explicit. The hypotheses that drive the P-matrix verdict
are split into a genuinely point-free part — the signed-incidence cover weights `signCoverWeight`
and a per-species positively-driving reaction `PositiveDiagonalDrive` — and the only point-dependent
facts used, the strict positivity of the source-monomial gradients (`massActionMonomialGrad_pos`),
hold automatically at *every* positive concentration. The conclusion is the box-quantified verdict:
the point-free incidence data, checked once, makes the full mass-action Jacobian a P-matrix at every
positive concentration simultaneously.

* `massActionMonomialGrad_pos` — at a positive concentration the source-monomial gradient is
  strictly positive exactly when the species genuinely participates (`1 ≤ source j`).
* `SignCoverWeightNonneg` — the point-free signed-incidence weight condition: every reaction-choice
  cover over every restricted species set has a nonnegative weight `(coverCoeff σ) · ∏ a,
  signedEdge (σ a) (ρ a)`. It mentions only the signed SR-graph, not the concentration.
* `PositiveDiagonalDrive` — the point-free diagonal-drive condition: each species has a reaction
  that genuinely depends on it and increases it (`signedEdge i r = 1`), so its diagonal Jacobian
  entry receives a strictly positive contribution at every positive concentration.
* `massActionJacobian_diag_pos_of_drive` — under both point-free conditions the Jacobian diagonal
  entries are positive at every positive concentration.
* `isPMatrix_massActionJacobian_of_pointIndep` — the full mass-action Jacobian is a P-matrix at a
  positive concentration under the two point-free conditions alone.
* `isPMatrix_massActionJacobian_box_of_pointIndep` — the box-quantified verdict: the point-free
  conditions make the Jacobian a P-matrix at *every* positive concentration of a set of
  concentrations, so checking the incidence data once discharges the P-matrix verdict over the whole
  set.

The verdict here is for the *full* mass-action Jacobian, whose principal submatrices are genuine
sub-Jacobians over restricted species sets and so admit the magnitude/sign split. The
chart-compressed *reduced* Jacobian `P · M · B` is not a principal submatrix of `M` (its proper
minors mix full-Jacobian entries across species through the chart), so its cover terms do not split
this way and its sign pattern is genuinely basis-dependent; the point-independence proved here does
not extend to the reduced minors. The reduced verdict reaches injectivity only when the chart is a
coordinate selection, via `reducedJacobian_isPMatrix_of_submatrix`.

This is the species–reaction-graph injectivity route of Craciun and Feinberg ("Multiple equilibria
in complex chemical reaction networks: I. The injectivity property" and "II. The species–reaction
graph"), whose injectivity conclusion feeds the global-univalence theorem of Gale and Nikaido ("The
Jacobian matrix and global univalence of mappings").

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Multistationarity.SRCycleInjectivity`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Matrix
open Equiv Finset

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## Strict positivity of the gradient magnitude -/

/-- **At a positive concentration the source-monomial gradient is strictly positive when the
species participates.** The gradient `(y j) · x_j^(y j − 1) · ∏_{s ≠ j} x_s^(y s)` is a product of
the cast coefficient `(y j : ℝ)`, which is positive exactly when `1 ≤ y j`, and strictly positive
powers of the positive coordinates. The magnitude factor of a cover that genuinely depends on its
species is therefore strictly positive — the only point-dependent input to the cover-sign verdict,
and it holds at every positive concentration. -/
theorem massActionMonomialGrad_pos (y : Complex S) {x : Concentration S}
    (hx : x.Positive) {j : S} (hj : 1 ≤ y j) : 0 < massActionMonomialGrad y x j := by
  refine mul_pos (mul_pos ?_ ?_) ?_
  · exact_mod_cast hj
  · exact pow_pos (hx j) _
  · exact Finset.prod_pos fun s _ => pow_pos (hx s) _

/-! ## The point-free hypotheses -/

/-- **The point-free signed-incidence cover-weight condition.** Every reaction-choice cover over
every restricted species set has a nonnegative signed-incidence weight `(coverCoeff σ) · ∏ a,
signedEdge (σ a) (ρ a)`. This mentions only the network's signed species–reaction graph through
`signedEdge` and the cover coefficient — no concentration appears — so it is a genuinely
point-independent condition. -/
def SignCoverWeightNonneg (N : Network S) : Prop :=
  ∀ (s : Finset S) (σ : Perm s) (ρ : s → N.R),
    0 ≤ ((coverCoeff σ : ℤ) : ℝ) *
      ((∏ a : s, N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℝ)

/-- **The point-free positive-diagonal-drive condition.** Each species `i` has a reaction `r` that
genuinely depends on it (`1 ≤ source coefficient at i`) and increases it (`signedEdge i r = 1`, i.e.
a positive net stoichiometric change). At every positive concentration the corresponding diagonal
Jacobian contribution `κ_r · (∂_i monomial_r) · reactionVector r i` is then strictly positive, so —
together with the nonnegativity of the other diagonal contributions under `SignCoverWeightNonneg` —
the diagonal entry is positive. Like `SignCoverWeightNonneg`, this condition is read off the signed
SR-graph alone. -/
def PositiveDiagonalDrive (N : Network S) : Prop :=
  ∀ i : S, ∃ r : N.R, 1 ≤ (N.reaction r).source i ∧ N.signedEdge i r = 1

/-! ## Point-independent diagonal positivity -/

/-- **A single positively-driving reaction makes a strictly positive diagonal contribution.** For a
reaction `r` with `1 ≤ source i` and `signedEdge i r = 1`, at a positive concentration the term
`κ_r · (∂_i monomial_r) · reactionVector r i` of the diagonal entry is strictly positive: the rate
is positive, the gradient is positive since the species participates, and the reaction-vector entry
is positive since its sign is `+1`. -/
theorem diag_contribution_pos (N : Network S) (κ : N.RateConstants) {x : Concentration S}
    (hx : x.Positive) {i : S} {r : N.R} (hsrc : 1 ≤ (N.reaction r).source i)
    (hsign : N.signedEdge i r = 1) :
    0 < κ.k r * massActionMonomialGrad (N.reaction r).source x i * N.reactionVector r i := by
  have hν : 0 < N.reactionVector r i := by
    have : SignType.sign (N.reactionVector r i) = 1 := hsign
    exact sign_eq_one_iff.mp this
  exact mul_pos (mul_pos (κ.positive r) (massActionMonomialGrad_pos _ hx hsrc)) hν

/-- **The Jacobian diagonal entries are positive at every positive concentration under the point-free
conditions.** The diagonal entry `M i i = ∑ r, κ_r · (∂_i monomial_r) · reactionVector r i` is a sum
whose terms each have nonnegative sign under `SignCoverWeightNonneg` (the singleton-cover weight at
`i`), and the positively-driving reaction supplied by `PositiveDiagonalDrive` contributes a strictly
positive term. The sum is therefore strictly positive. The conclusion holds at every positive
concentration: the point-free conditions alone force a positive diagonal. -/
theorem massActionJacobian_diag_pos_of_drive (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive)
    (hweight : N.SignCoverWeightNonneg) (hdrive : N.PositiveDiagonalDrive) (i : S) :
    0 < (N.massActionJacobian κ x) i i := by
  -- Each diagonal term is nonnegative: its incidence sign `signedEdge i r ≥ 0` (the singleton
  -- cover weight at `i`), so its reaction-vector entry is nonnegative.
  have hterm : ∀ r : N.R,
      0 ≤ κ.k r * massActionMonomialGrad (N.reaction r).source x i * N.reactionVector r i := by
    intro r
    have hgrad : 0 ≤ massActionMonomialGrad (N.reaction r).source x i :=
      massActionMonomialGrad_nonneg _ hx i
    -- `signedEdge i r ≥ 0`, extracted from the singleton-cover weight `s = {i}`.
    have hsign_nonneg : (0 : ℝ) ≤ ((N.signedEdge i r : SignType) : ℝ) := by
      have hsingle := hweight {i} (1 : Perm ({i} : Finset S)) (fun _ => r)
      -- The singleton subtype is a `Unique` with sole element `i`, so the product is `signedEdge i r`
      -- and `coverCoeff (1) = 1`.
      have hpt : (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset S)) ∈
          (Finset.univ : Finset ({i} : Finset S)) := Finset.mem_univ _
      have hother : ∀ b : ({i} : Finset S),
          b ≠ (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset S)) → False :=
        fun b hb => hb (Subtype.ext (Finset.mem_singleton.mp b.2))
      rw [Finset.prod_eq_single_of_mem (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset S)) hpt
            (fun b _ hb => (hother b hb).elim)] at hsingle
      rw [show (coverCoeff (1 : Perm ({i} : Finset S)) : ℤ) = 1 from by
            rw [coverCoeff_eq_sign]; simp] at hsingle
      simpa using hsingle
    rw [signedEdge_eq_sign_reactionVector] at hsign_nonneg
    have hν : 0 ≤ N.reactionVector r i := by
      rcases lt_or_ge (N.reactionVector r i) (0 : ℝ) with h | h
      · exact absurd hsign_nonneg (by rw [sign_neg h]; norm_num)
      · exact h
    exact mul_nonneg (mul_nonneg (κ.positive r).le hgrad) hν
  -- The positively-driving reaction supplies a strictly positive term.
  obtain ⟨r₀, hsrc, hsign⟩ := hdrive i
  have hpos : 0 < κ.k r₀ * massActionMonomialGrad (N.reaction r₀).source x i * N.reactionVector r₀ i :=
    N.diag_contribution_pos κ hx hsrc hsign
  rw [massActionJacobian]
  exact Finset.sum_pos' (fun r _ => hterm r) ⟨r₀, Finset.mem_univ r₀, hpos⟩

/-! ## The point-independent P-matrix verdict -/

/-- **The full mass-action Jacobian is a P-matrix at a positive concentration under the point-free
conditions.** Combining the point-free signed-incidence weight `SignCoverWeightNonneg` — which makes
every cover term of every principal submatrix nonnegative (`coverTerm_submatrix_nonneg_of_signWeighted`)
— with the point-free diagonal-drive condition, which forces positive diagonal entries, every
principal minor is positive. No concentration-dependent hypothesis is needed: the verdict is read off
the signed species–reaction graph. -/
theorem isPMatrix_massActionJacobian_of_pointIndep (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive)
    (hweight : N.SignCoverWeightNonneg) (hdrive : N.PositiveDiagonalDrive) :
    (N.massActionJacobian κ x).IsPMatrix :=
  N.isPMatrix_massActionJacobian_of_consistentSRSign κ hx hweight
    (fun i => N.massActionJacobian_diag_pos_of_drive κ hx hweight hdrive i)

/-- **The box-quantified point-independent verdict.** The point-free conditions
`SignCoverWeightNonneg` and `PositiveDiagonalDrive` make the full mass-action Jacobian a P-matrix at
*every* positive concentration of a set `C`. The cover-sign pattern does not move with the
concentration — its only point-dependent input, the strict positivity of the gradient magnitudes,
holds at every positive point — so checking the signed-incidence data once discharges the P-matrix
verdict over the whole set. This is the point-independence keystone: a single check of point-free
incidence data, not a per-point check, settles the verdict throughout the box. -/
theorem isPMatrix_massActionJacobian_box_of_pointIndep (N : Network S) (κ : N.RateConstants)
    (C : Set (Concentration S)) (hC : ∀ x ∈ C, x.Positive)
    (hweight : N.SignCoverWeightNonneg) (hdrive : N.PositiveDiagonalDrive) :
    ∀ x ∈ C, (N.massActionJacobian κ x).IsPMatrix :=
  fun x hx => N.isPMatrix_massActionJacobian_of_pointIndep κ (hC x hx) hweight hdrive

end Network

end CRNT

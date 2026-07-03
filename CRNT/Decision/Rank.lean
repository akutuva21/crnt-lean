import CRNT.Stoich.Subspace
import CRNT.Deficiency.KernelDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Rank and deficiency certificates over `ℚ`

The stoichiometric rank `s = finrank ℝ stoichSubspace` is noncomputable, as is Mathlib's
matrix rank. A *certificate*, however, is computable: a square selection of `k` reactions
and `k` species whose stoichiometric minor has nonzero rational determinant witnesses that
those `k` reaction vectors are linearly independent, hence `s ≥ k`.

* `stoichRank_ge_of_linearIndependent`: an independent family of `k` reaction vectors gives
  `k ≤ s`.
* `stoichRank_ge_of_det_ne_zero`: a `k × k` stoichiometric minor with nonzero **rational**
  determinant gives `k ≤ s`. The determinant is exact rational arithmetic, so the hypothesis
  is discharged by reflection.

Combined with `s ≤ n − ℓ` (`stoichRank_add_numLinkageClasses_le`, the integer form of
`δ ≥ 0`), a full-size minor forces `δ = 0`:

* `deficiencyZero_of_numComplexes_le` / `deficiencyZero_of_minor`: a computable
  `DeficiencyZero` certificate.

The exact computable rank itself (Gaussian elimination over `ℚ` with a proof that it equals
`finrank ℝ stoichSubspace`) is not provided here; these one-sided certificates discharge the
deficiency-zero hypothesis, which is what the structural theory consumes.

Depends on: `CRNT.Stoich.Subspace`,
`CRNT.Deficiency.KernelDimension`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A linearly independent family of reaction vectors bounds the stoichiometric rank
below.** -/
theorem stoichRank_ge_of_linearIndependent (N : Network S) {k : ℕ} (f : Fin k → N.R)
    (h : LinearIndependent ℝ (fun i => N.reactionVector (f i))) : k ≤ N.stoichRank := by
  have hg : LinearIndependent ℝ
      (fun i : Fin k => (⟨N.reactionVector (f i), N.reactionVector_mem_stoichSubspace (f i)⟩ :
        N.stoichSubspace)) :=
    LinearIndependent.of_comp N.stoichSubspace.subtype h
  have hcard := hg.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  exact hcard

/-- **A stoichiometric minor with nonzero rational determinant bounds the stoichiometric rank
below.** Selecting `k` reactions (`f`) and `k` species (`σ`), if the `k × k` matrix of
rational reaction-vector entries is nonsingular then those `k` reaction vectors are linearly
independent, so `k ≤ s`. -/
theorem stoichRank_ge_of_det_ne_zero (N : Network S) {k : ℕ}
    (f : Fin k → N.R) (σ : Fin k → S)
    (h : (Matrix.of fun i j : Fin k =>
            ((N.reaction (f j)).target (σ i) : ℚ) - ((N.reaction (f j)).source (σ i) : ℚ)).det
          ≠ 0) :
    k ≤ N.stoichRank := by
  set MQ : Matrix (Fin k) (Fin k) ℚ :=
    Matrix.of fun i j => ((N.reaction (f j)).target (σ i) : ℚ) - ((N.reaction (f j)).source (σ i) : ℚ)
    with hMQ
  apply N.stoichRank_ge_of_linearIndependent f
  apply LinearIndependent.of_comp (LinearMap.funLeft ℝ ℝ σ)
  have key : (LinearMap.funLeft ℝ ℝ σ) ∘ (fun j => N.reactionVector (f j))
      = (Matrix.of fun i j : Fin k => N.reactionVector (f j) (σ i)).col := by
    funext j i
    simp [LinearMap.funLeft_apply, Matrix.col_apply, Matrix.of_apply]
  rw [key, Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]
  have hmap : (Matrix.of fun i j : Fin k => N.reactionVector (f j) (σ i))
      = MQ.map (Rat.castHom ℝ) := by
    ext i j
    simp only [hMQ, Matrix.of_apply, Matrix.map_apply, Network.reactionVector_apply, map_sub,
      map_natCast]
  have hdet_eq : (MQ.map (Rat.castHom ℝ)).det = (Rat.castHom ℝ) MQ.det :=
    (RingHom.map_det (Rat.castHom ℝ) MQ).symm
  rw [hmap, hdet_eq, ne_eq, map_eq_zero_iff _ (Rat.castHom ℝ).injective]
  exact h

/-- The stoichiometric rank obeys `s + ℓ ≤ n`, the integer form of `δ ≥ 0`. -/
theorem stoichRank_add_numLinkageClasses_le (N : Network S) :
    N.stoichRank + N.numLinkageClasses ≤ N.numComplexes := by
  have h1 : N.stoichRank ≤ N.incidenceRank := by
    rw [incidenceRank_eq_stoichRank_add]; exact Nat.le_add_right _ _
  have h2 := N.incidenceRank_add_numLinkageClasses
  omega

/-- **A lower bound on the stoichiometric rank forces deficiency zero.** Since `s ≤ n − ℓ`
always holds, `n ≤ s + ℓ` pins `s = n − ℓ`, i.e. `δ = 0`. -/
theorem deficiencyZero_of_numComplexes_le (N : Network S)
    (h : N.numComplexes ≤ N.stoichRank + N.numLinkageClasses) : N.DeficiencyZero := by
  rw [deficiencyZero_iff_eq]
  have := N.stoichRank_add_numLinkageClasses_le
  omega

/-- **A computable deficiency-zero certificate.** A `k × k` stoichiometric minor with nonzero
rational determinant, where `k + ℓ ≥ n`, witnesses `DeficiencyZero`. -/
theorem deficiencyZero_of_minor (N : Network S) {k : ℕ}
    (f : Fin k → N.R) (σ : Fin k → S)
    (hdet : (Matrix.of fun i j : Fin k =>
              ((N.reaction (f j)).target (σ i) : ℚ) - ((N.reaction (f j)).source (σ i) : ℚ)).det
            ≠ 0)
    (hk : N.numComplexes ≤ k + N.numLinkageClasses) : N.DeficiencyZero := by
  apply N.deficiencyZero_of_numComplexes_le
  have := N.stoichRank_ge_of_det_ne_zero f σ hdet
  omega

end Network

end CRNT

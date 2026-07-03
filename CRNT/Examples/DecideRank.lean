import CRNT.Decision.Rank
import CRNT.Examples.ReversiblePair

/-!
# A rank/deficiency certificate for `A ⇌ B`

The reversible pair has stoichiometric rank at least one, witnessed by the `1 × 1`
stoichiometric minor at species `A` and reaction `fwd`, whose rational determinant is `-1`.
Together with `n = 2` complexes and `ℓ = 1` linkage class this forces deficiency zero by the
certificate, discharged by exact rational arithmetic.
-/

namespace CRNT.Examples.DecideRank

open CRNT CRNT.Examples.ReversiblePair

/-- The `1 × 1` minor `[A, fwd]` is nonsingular: its determinant is `-1`. -/
theorem stoichRank_ge_one : 1 ≤ N.stoichRank :=
  N.stoichRank_ge_of_det_ne_zero (k := 1) (fun _ => Rxn.fwd) (fun _ => Species.A) (by
    rw [Matrix.det_fin_one, Matrix.of_apply]
    show ((cB Species.A : ℚ) - (cA Species.A : ℚ)) ≠ 0
    norm_num [cA, cB])

/-- Deficiency zero of `A ⇌ B`, obtained from the rank certificate. -/
theorem deficiencyZero : N.DeficiencyZero :=
  N.deficiencyZero_of_numComplexes_le (by
    rw [numComplexes_eq, numLinkageClasses_eq]
    have := stoichRank_ge_one
    omega)

end CRNT.Examples.DecideRank

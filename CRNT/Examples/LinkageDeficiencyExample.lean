import CRNT.Deficiency.LinkageDeficiency
import CRNT.Examples.ReversiblePair

/-!
# Per-linkage-class deficiency of `A ⇌ B`

The reversible pair has a single linkage class, so the per-class deficiency sum equals the
network deficiency. With `δ = 0` the decomposition inequality `∑_θ δ_θ ≤ δ` reads
`∑_θ δ_θ ≤ 0`.

This module is **stable** (example/test). It contains no `sorry`.
-/

namespace CRNT.Examples.LinkageDeficiencyExample

open CRNT CRNT.Examples.ReversiblePair

/-- The decomposition inequality, instantiated on `A ⇌ B`. -/
example : ∑ q, N.linkageDeficiency q ≤ N.deficiencyInt :=
  N.sum_linkageDeficiency_le_deficiency

/-- Since the reversible pair has deficiency zero, the per-class deficiencies sum to at
most zero. -/
example : ∑ q, N.linkageDeficiency q ≤ 0 := by
  have h := N.sum_linkageDeficiency_le_deficiency
  rwa [(deficiencyZero : N.deficiencyInt = 0)] at h

end CRNT.Examples.LinkageDeficiencyExample

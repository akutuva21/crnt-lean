import CRNT.Graph.LinkageClass
import CRNT.Stoich.Subspace

/-!
# Deficiency

The deficiency of a network is `δ = n - ℓ - s`, where `n` is the number of complexes,
`ℓ` is the number of linkage classes, and `s` is the stoichiometric rank. The quantity
is known to be nonnegative, but Lean's natural-number subtraction truncates at zero, so
the canonical definition is over `ℤ` (`deficiencyInt`). `DeficiencyZero` is defined as
`deficiencyInt = 0`, avoiding any truncated-subtraction pitfall.

Depends on: `CRNT.Graph.LinkageClass`, `CRNT.Stoich.Subspace`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The deficiency `δ = n - ℓ - s` as an integer. Computed over `ℤ` to avoid
natural-number truncated subtraction. -/
noncomputable def deficiencyInt (N : Network S) : ℤ :=
  (N.numComplexes : ℤ) - (N.numLinkageClasses : ℤ) - (N.stoichRank : ℤ)

/-- A network has deficiency zero when `n - ℓ - s = 0`. This is the structural
hypothesis of the deficiency-zero theorem. -/
def DeficiencyZero (N : Network S) : Prop :=
  N.deficiencyInt = 0

theorem deficiencyZero_iff (N : Network S) :
    N.DeficiencyZero ↔
      (N.numComplexes : ℤ) - (N.numLinkageClasses : ℤ) - (N.stoichRank : ℤ) = 0 :=
  Iff.rfl

/-- A convenient reformulation: deficiency zero means `n = ℓ + s`. -/
theorem deficiencyZero_iff_eq (N : Network S) :
    N.DeficiencyZero ↔ N.numComplexes = N.numLinkageClasses + N.stoichRank := by
  rw [deficiencyZero_iff]
  constructor
  · intro h; omega
  · intro h; omega

end Network

end CRNT

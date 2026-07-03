import CRNT.Deficiency.KernelDimension

/-!
# Deficiency beyond zero: nonnegativity, the natural-number deficiency, and deficiency one

The integer deficiency `deficiencyInt = n − ℓ − s` equals the dimension of the deficiency
subspace `ker Y ⊓ Im ∂` (`deficiencyInt_eq_finrank_deficiencySubspace`), so it is
**nonnegative**. This module records that fact, packages the deficiency as a natural number
`deficiency`, and derives the structural identity `n = ℓ + s + δ`. It then introduces the
`DeficiencyOne` predicate — the structural class of Feinberg's deficiency-one theory — with its
basic characterizations.

The deficiency-one *theorem* (uniqueness of positive steady states under per-linkage-class
deficiency constraints) builds on this foundation and on the strong-linkage-class machinery in
`CRNT.Decision.StrongLinkage`.

Depends on: `CRNT.Deficiency.KernelDimension`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The **deficiency** as a natural number: the dimension of the deficiency subspace
`ker Y ⊓ Im ∂`. The integer deficiency `deficiencyInt` agrees with it
(`deficiencyInt_eq_deficiency`). -/
noncomputable def deficiency (N : Network S) : ℕ :=
  Module.finrank ℝ N.deficiencySubspace

/-- The integer and natural-number deficiencies agree. -/
theorem deficiencyInt_eq_deficiency (N : Network S) :
    N.deficiencyInt = (N.deficiency : ℤ) :=
  N.deficiencyInt_eq_finrank_deficiencySubspace

/-- **The deficiency is nonnegative.** -/
theorem deficiencyInt_nonneg (N : Network S) : 0 ≤ N.deficiencyInt := by
  rw [deficiencyInt_eq_deficiency]
  exact Int.natCast_nonneg _

/-- **The structural identity `n = ℓ + s + δ`.** With the deficiency nonnegative, the
deficiency formula rearranges to a clean natural-number identity. -/
theorem numComplexes_eq_add (N : Network S) :
    N.numComplexes = N.numLinkageClasses + N.stoichRank + N.deficiency := by
  have h := N.deficiencyInt_eq_deficiency
  rw [deficiencyInt] at h
  omega

/-- Deficiency zero in terms of the natural-number deficiency. -/
theorem deficiencyZero_iff_deficiency_eq_zero (N : Network S) :
    N.DeficiencyZero ↔ N.deficiency = 0 := by
  rw [DeficiencyZero, deficiencyInt_eq_deficiency, Nat.cast_eq_zero]

/-- A network has **deficiency one** when `n − ℓ − s = 1`. This is the structural class of
the deficiency-one theorem. -/
def DeficiencyOne (N : Network S) : Prop :=
  N.deficiencyInt = 1

/-- Deficiency one in terms of the natural-number deficiency. -/
theorem deficiencyOne_iff_deficiency_eq_one (N : Network S) :
    N.DeficiencyOne ↔ N.deficiency = 1 := by
  rw [DeficiencyOne, deficiencyInt_eq_deficiency, Nat.cast_eq_one]

/-- Deficiency zero and deficiency one are mutually exclusive. -/
theorem not_deficiencyZero_of_deficiencyOne (N : Network S) (h : N.DeficiencyOne) :
    ¬ N.DeficiencyZero := by
  intro hz
  rw [DeficiencyOne] at h
  rw [DeficiencyZero] at hz
  omega

end Network

end CRNT

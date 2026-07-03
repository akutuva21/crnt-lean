import CRNT.Open.Augmentation
import CRNT.Deficiency.DeficiencyOne

/-!
# Deficiency and linkage bookkeeping for the fully open extension

The fully open extension `N⁺` adjoins a synthesis `0 → s` and a degradation `s → 0` for
every species. Its stoichiometric subspace is everything, so its rank is `card S`. This
module records the consequences for the deficiency formula `δ = n − ℓ − s` and the linkage
structure.

* `stoichRank_fullyOpen` (from `CRNT.Open.Augmentation`) gives `s⁺ = card S`, so the
  deficiency reads `δ⁺ = n⁺ − ℓ⁺ − card S` (`deficiencyInt_fullyOpen`) and the structural
  identity becomes `n⁺ = ℓ⁺ + card S + δ⁺` (`numComplexes_fullyOpen_eq_add`).
* The synthesis and degradation pseudo-reactions tie the zero complex to every singleton:
  `0` directly reacts to each `e_s` and back, so the zero complex and every singleton share
  one linkage class (`linked_zero_singletonComplex_fullyOpen`,
  `linked_singletonComplex_fullyOpen`). The open extension collapses the inflow and outflow
  material into a single hub class.

Depends on: `CRNT.Open.Augmentation`,
`CRNT.Deficiency.DeficiencyOne`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The deficiency of the fully open extension** reads `δ⁺ = n⁺ − ℓ⁺ − card S`: the
stoichiometric rank is `card S` since the open extension's stoichiometric subspace is the
whole species space. -/
theorem deficiencyInt_fullyOpen (N : Network S) :
    N.fullyOpen.deficiencyInt
      = (N.fullyOpen.numComplexes : ℤ) - (N.fullyOpen.numLinkageClasses : ℤ)
        - (Fintype.card S : ℤ) := by
  rw [deficiencyInt, stoichRank_fullyOpen]

/-- **The structural identity for the fully open extension:** `n⁺ = ℓ⁺ + card S + δ⁺`. The
stoichiometric rank `s⁺` is `card S`. -/
theorem numComplexes_fullyOpen_eq_add (N : Network S) :
    N.fullyOpen.numComplexes
      = N.fullyOpen.numLinkageClasses + Fintype.card S + N.fullyOpen.deficiency := by
  have h := N.fullyOpen.numComplexes_eq_add
  rwa [stoichRank_fullyOpen] at h

/-- The inflow `0 → s` is a directed edge of the open extension's reaction graph. -/
theorem directlyReacts_zero_singletonComplex_fullyOpen (N : Network S) (s : S) :
    N.fullyOpen.DirectlyReacts Complex.zero (singletonComplex s) :=
  ⟨Sum.inr (Sum.inl s), rfl, rfl⟩

/-- The outflow `s → 0` is a directed edge of the open extension's reaction graph. -/
theorem directlyReacts_singletonComplex_zero_fullyOpen (N : Network S) (s : S) :
    N.fullyOpen.DirectlyReacts (singletonComplex s) Complex.zero :=
  ⟨Sum.inr (Sum.inr s), rfl, rfl⟩

/-- **The zero complex and every singleton lie in one linkage class of the open extension.**
The inflow `0 → s` is an undirected edge. -/
theorem linked_zero_singletonComplex_fullyOpen (N : Network S) (s : S) :
    N.fullyOpen.Linked Complex.zero (singletonComplex s) :=
  Relation.ReflTransGen.single (Or.inl (directlyReacts_zero_singletonComplex_fullyOpen N s))

/-- **All singletons share the zero complex's linkage class** in the open extension. -/
theorem linked_singletonComplex_fullyOpen (N : Network S) (s t : S) :
    N.fullyOpen.Linked (singletonComplex s) (singletonComplex t) :=
  (linked_zero_singletonComplex_fullyOpen N s).symm.trans
    (linked_zero_singletonComplex_fullyOpen N t)

end Network

end CRNT

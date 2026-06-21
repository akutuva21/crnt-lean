import CRNT.Open.Augmentation
import CRNT.Examples.ReversiblePair

/-!
# The fully open extension of the reversible pair `A ⇌ B`

Exercises the open-network construction. Adjoining a synthesis and degradation for each of
the two species turns the rank-one closed network into a fully open one whose
stoichiometric subspace is all of `Species → ℝ` (rank `2`) and which has no nontrivial
conservation law.

This module is **stable** (example/test). It contains no `sorry`.
-/

namespace CRNT.Examples.OpenSystem

open CRNT CRNT.Examples.ReversiblePair

/-- The fully open extension of `A ⇌ B`. -/
def Nopen : Network Species := N.fullyOpen

/-- There are two species. -/
theorem card_species : Fintype.card Species = 2 := by decide

/-- Opening the network raises the stoichiometric rank to `2`: the closed network had
rank one (one conservation law `[A] + [B]`); the open one has full rank. -/
theorem stoichRank_open : Nopen.stoichRank = 2 := by
  rw [Nopen, N.stoichRank_fullyOpen, card_species]

/-- The open extension's stoichiometric subspace is everything. -/
example : Nopen.stoichSubspace = ⊤ :=
  N.stoichSubspace_fullyOpen_eq_top

/-- The open extension has no nontrivial conservation law. -/
example : orthSum Nopen.stoichSubspace = ⊥ :=
  N.orthSum_stoichSubspace_fullyOpen_eq_bot

end CRNT.Examples.OpenSystem

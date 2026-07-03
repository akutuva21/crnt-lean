import CRNT.Basic.Network
import Mathlib.Data.Real.Basic

/-!
# Reaction vectors

The stoichiometric reaction vector of a reaction is `target - source`, the column of
the stoichiometric matrix indexed by that reaction. This module collects the network-
level view of reaction vectors used by the stoichiometric subspace and the mass-
action vector field.

Depends on: `CRNT.Basic.Network`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The reaction vector of the reaction indexed by `r`, as a real vector over species.
This is `target - source`. -/
def reactionVector (N : Network S) (r : N.R) : S → ℝ :=
  (N.reaction r).vector

@[simp] theorem reactionVector_apply (N : Network S) (r : N.R) (s : S) :
    N.reactionVector r s = ((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ) :=
  rfl

/-- The set of reaction vectors of the network, whose span is the stoichiometric
subspace. -/
def reactionVectors (N : Network S) : Set (S → ℝ) :=
  Set.range (N.reactionVector)

end Network

end CRNT

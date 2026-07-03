import CRNT.Stoich.Vector
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Stoichiometric subspace and rank

The stoichiometric subspace `S(N)` is the real span of the reaction vectors; its
dimension is the stoichiometric rank `s`, the third term in the deficiency formula
`δ = n - ℓ - s`. The subspace is genuinely defined; the rank is noncomputable
(`Module.finrank`). Exact computable rank over `ℚ` for certificates is future work.

Depends on: `CRNT.Stoich.Vector`, Mathlib linear algebra.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The stoichiometric subspace: the `ℝ`-span of all reaction vectors of the
network, a submodule of the space `S → ℝ` of real species vectors. -/
def stoichSubspace (N : Network S) : Submodule ℝ (S → ℝ) :=
  Submodule.span ℝ N.reactionVectors

/-- Each reaction vector lies in the stoichiometric subspace. -/
theorem reactionVector_mem_stoichSubspace (N : Network S) (r : N.R) :
    N.reactionVector r ∈ N.stoichSubspace :=
  Submodule.subset_span ⟨r, rfl⟩

/-- The stoichiometric rank `s`: the dimension of the stoichiometric subspace. -/
noncomputable def stoichRank (N : Network S) : ℕ :=
  Module.finrank ℝ N.stoichSubspace

/-- The stoichiometric rank is at most the number of species, since the ambient space
`S → ℝ` has dimension `card S`. -/
theorem stoichRank_le_card (N : Network S) : N.stoichRank ≤ Fintype.card S :=
  (Submodule.finrank_le _).trans (Module.finrank_pi ℝ).le

end Network

end CRNT

import CRNT.Geometry.PolyhedralFan

/-!
# Endotactic and strongly endotactic networks

This module defines the endotactic and strongly endotactic predicates on a reaction
network, the geometric backbone of the Gopalkrishnan–Miller–Shiu route to the Global
Attractor Conjecture (strongly endotactic ⇒ permanent ⇒ GAC).

For a direction `w : S → ℝ`, the `wValue` of a reaction is the linear functional
`∑ s, w s * exponentVector (source) s` evaluated at the reactant complex, and
`wRate` is `∑ s, w s * reactionVector r s`, the rate of change of that functional
along the reaction. A reaction is `IsMaxSource w` when its source complex maximizes
`wValue` over all reaction sources.

A network is `Endotactic` when, for every direction `w`, every reaction whose source
is `w`-maximal has `wRate ≤ 0`: no reaction at the `w`-maximal reactant face points
strictly outward in the `+w` direction. It is `StronglyEndotactic` when it is
endotactic and, in addition, whenever `w` is non-constant on the source complexes
there is at least one `w`-maximal reaction with `wRate < 0` (strictly inward).

The structural results are `StronglyEndotactic.endotactic` (the strong condition
refines the plain one), `wRate_eq` (the rate functional unfolds to the dot product of
`w` with the stoichiometric reaction vector), and `endotactic_of_isEmpty` /
`stronglyEndotactic_of_isEmpty` (the empty network is vacuously strongly endotactic).
The condition depends only on the finite reaction data through `wValue`/`wRate`.

The Gopalkrishnan–Miller–Shiu permanence theorem (strongly endotactic ⇒ permanent)
and its consequence for the Global Attractor Conjecture are the residue: they require
the Lyapunov / compactness machinery not yet present in the repo.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Geometry.PolyhedralFan`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The plain dot product `∑ s, w s * v s` of two real species vectors. -/
def dotProduct (w v : S → ℝ) : ℝ := ∑ s, w s * v s

/-- The value of the linear functional `w` at the source (reactant) complex of a
reaction: `∑ s, w s * (source s)`. The `w`-maximal sources define the active face. -/
def wValue (N : Network S) (w : S → ℝ) (r : N.R) : ℝ :=
  dotProduct w (exponentVector (N.reaction r).source)

/-- The rate of change of the functional `w` along a reaction: `∑ s, w s *
reactionVector r s`. Endotacticity bounds this above by `0` at the `w`-maximal face. -/
def wRate (N : Network S) (w : S → ℝ) (r : N.R) : ℝ :=
  dotProduct w (N.reactionVector r)

/-- The rate functional unfolds to the dot product of `w` with the stoichiometric
reaction vector `target - source`. -/
theorem wRate_eq (N : Network S) (w : S → ℝ) (r : N.R) :
    N.wRate w r = ∑ s, w s * ((N.reaction r).target s - (N.reaction r).source s : ℝ) := by
  simp only [wRate, dotProduct, reactionVector_apply]

/-- A reaction is `w`-maximal when its source complex maximizes `wValue` over all
reaction sources of the network. These reactions sit on the `w`-maximal reactant face
of the Newton polytope. -/
def IsMaxSource (N : Network S) (w : S → ℝ) (r : N.R) : Prop :=
  ∀ r' : N.R, N.wValue w r' ≤ N.wValue w r

/-- A network is **endotactic** when, for every direction `w`, every reaction whose
source is `w`-maximal has nonpositive `w`-rate: at the `w`-maximal reactant face no
reaction points strictly in the `+w` direction. -/
def Endotactic (N : Network S) : Prop :=
  ∀ (w : S → ℝ) (r : N.R), N.IsMaxSource w r → N.wRate w r ≤ 0

/-- A network is **strongly endotactic** when it is endotactic and, whenever the
direction `w` is non-constant on the source complexes (so the `w`-maximal face is a
proper face), at least one `w`-maximal reaction has strictly negative `w`-rate. -/
def StronglyEndotactic (N : Network S) : Prop :=
  N.Endotactic ∧
    ∀ w : S → ℝ, (∃ r₁ r₂ : N.R, N.wValue w r₁ ≠ N.wValue w r₂) →
      ∃ r : N.R, N.IsMaxSource w r ∧ N.wRate w r < 0

/-- Strong endotacticity refines plain endotacticity. -/
theorem StronglyEndotactic.endotactic {N : Network S} (h : N.StronglyEndotactic) :
    N.Endotactic :=
  h.1

/-- A network with no reactions is vacuously endotactic: there are no `w`-maximal
reactions to constrain. -/
theorem endotactic_of_isEmpty (N : Network S) [IsEmpty N.R] : N.Endotactic :=
  fun _ r _ => isEmptyElim r

/-- A network with no reactions is vacuously strongly endotactic: there are no two
reactions to make `w` non-constant on the sources. -/
theorem stronglyEndotactic_of_isEmpty (N : Network S) [IsEmpty N.R] :
    N.StronglyEndotactic :=
  ⟨endotactic_of_isEmpty N, fun _ ⟨r, _, _⟩ => isEmptyElim r⟩

/-- The `w`-rate of a self-reaction (`source = target`) is zero: such a reaction sits
at the `w`-maximal face only trivially. -/
theorem wRate_of_source_eq_target {N : Network S} {w : S → ℝ} {r : N.R}
    (h : (N.reaction r).source = (N.reaction r).target) : N.wRate w r = 0 := by
  simp only [wRate, dotProduct, reactionVector, Reaction.vector_of_source_eq_target h,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero]

end Network

end CRNT

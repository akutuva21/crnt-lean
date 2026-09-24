import CRNT.Multistationarity.TrueSRRotate

/-!
# Path endpoints, and when two paths glue to a cycle

The remaining construction on the `hSR.2` route is the glue lemma.  The abstraction is:

**a cycle is exactly two species-to-reaction paths with the same two endpoints and disjoint
interiors.**

Banaji--Craciun Lemma 10 then reads: a chord `P` from a species vertex of `C` to a reaction
vertex of `C` glues to each of the two arcs of `C` between those vertices, giving two cycles
whose common edges are exactly `P` — which `no_shared_path_of_trueSRCriterion` consumes.

This file fixes the interface: the two endpoints of a path as data, and the `Gluable` predicate.
The construction `Gluable P Q → TrueSRCycle _` is **not** built here.

Index conventions, from `TrueSRPath.species_iff_even`: a path of length `L` has species vertices
at even positions and reaction vertices at odd ones, and `L` is odd
(`TrueSRPath.odd_length`), so position `0` is a species and position `L` is a reaction.  Writing
`L = 2j+1`, the path carries `j+1` species and `j+1` reactions, and gluing paths of lengths
`2j+1` and `2i+1` yields a cycle of length `i+j+1`.
-/

namespace CRNT.Network.TrueSRPath

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {L M : ℕ}

/-- The species vertex a path starts at. -/
noncomputable def startSpecies (P : N.TrueSRPath L) : S :=
  P.starts_at_species.choose

theorem vertex_zero (P : N.TrueSRPath L) :
    P.vertex 0 = Sum.inl P.startSpecies :=
  P.starts_at_species.choose_spec

/-- The reaction vertex a path ends at. -/
noncomputable def endReaction (P : N.TrueSRPath L) : N.InternalTrueReaction :=
  P.ends_at_reaction.choose

theorem vertex_last (P : N.TrueSRPath L) :
    P.vertex (Fin.last L) = Sum.inr P.endReaction :=
  P.ends_at_reaction.choose_spec

/-- A path's interior species, i.e. those at even positions other than `0`. -/
def InteriorSpecies (P : N.TrueSRPath L) (s : S) : Prop :=
  ∃ p : Fin (L + 1), p.1 ≠ 0 ∧ P.vertex p = Sum.inl s

/-- A path's interior reactions, i.e. those at odd positions other than `L`. -/
def InteriorReaction (P : N.TrueSRPath L) (ρ : N.InternalTrueReaction) : Prop :=
  ∃ p : Fin (L + 1), p.1 ≠ L ∧ P.vertex p = Sum.inr ρ

/-- **When two species-to-reaction paths glue to a cycle**: they share both endpoints, and
their interiors are disjoint, so the glued closed walk is vertex-simple.

The `edge_disjoint` clause is what Banaji--Craciun's Lemma 10 supplies directly; the interior
disjointness needed for a *simple* cycle follows there by taking a minimal chord, an argument
not carried out here. -/
structure Gluable (P : N.TrueSRPath L) (Q : N.TrueSRPath M) : Prop where
  same_start : P.startSpecies = Q.startSpecies
  same_end : P.endReaction = Q.endReaction
  species_disjoint : ∀ s : S, P.InteriorSpecies s → Q.InteriorSpecies s → False
  reaction_disjoint : ∀ ρ : N.InternalTrueReaction,
    P.InteriorReaction ρ → Q.InteriorReaction ρ → False
  edge_disjoint : ∀ i j, ¬ (P.edge i).SameIncidence (Q.edge j)

/-- Gluability is symmetric. -/
theorem Gluable.symm {P : N.TrueSRPath L} {Q : N.TrueSRPath M} (h : Gluable P Q) :
    Gluable Q P where
  same_start := h.same_start.symm
  same_end := h.same_end.symm
  species_disjoint := fun s hQ hP => h.species_disjoint s hP hQ
  reaction_disjoint := fun ρ hQ hP => h.reaction_disjoint ρ hP hQ
  edge_disjoint := by
    intro i j hij
    refine h.edge_disjoint j i ?_
    obtain ⟨h1, h2, h3⟩ := hij
    exact ⟨h1.symm, h2.symm, h3.symm⟩

/-- The glued cycle's length, in the parametrisation `L = 2j+1`, `M = 2i+1`. -/
theorem glued_length (P : N.TrueSRPath L) (Q : N.TrueSRPath M) :
    ∃ j i : ℕ, L = 2 * j + 1 ∧ M = 2 * i + 1 ∧ (L + M) / 2 = i + j + 1 := by
  obtain ⟨j, hj⟩ := P.odd_length
  obtain ⟨i, hi⟩ := Q.odd_length
  exact ⟨j, i, by omega, by omega, by omega⟩

end CRNT.Network.TrueSRPath

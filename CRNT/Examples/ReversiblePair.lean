import Mathlib.Tactic.DeriveFintype
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import CRNT.Basic.Complex
import CRNT.Basic.Reaction
import CRNT.Basic.Network
import CRNT.Stoich.Vector
import CRNT.Stoich.Subspace
import CRNT.Graph.Reachability
import CRNT.Graph.WeakReversibility
import CRNT.Graph.LinkageClass
import CRNT.Deficiency.Definition
import CRNT.Theorems.DeficiencyZero.Statement

/-!
# Reversible pair `A ⇌ B`

The canonical deficiency-zero network. It has two species, two complexes, two
reactions, one linkage class, and stoichiometric rank one, hence deficiency
`δ = 2 - 1 - 1 = 0`. This module proves all of these, including weak reversibility and
deficiency zero.

This module is **stable** (example/test). It contains no `sorry`.
-/

namespace CRNT.Examples.ReversiblePair

open CRNT

/-- Two species, `A` and `B`. -/
inductive Species
  | A
  | B
  deriving DecidableEq, Fintype, Repr

open Species

/-- The complex `A`. -/
def cA : Complex Species := fun s => match s with | A => 1 | B => 0

/-- The complex `B`. -/
def cB : Complex Species := fun s => match s with | A => 0 | B => 1

/-- Two reaction channels: forward `A → B` and backward `B → A`. -/
inductive Rxn
  | fwd
  | bwd
  deriving DecidableEq, Fintype, Repr

/-- The reaction map. -/
def rxn : Rxn → Reaction Species
  | .fwd => { source := cA, target := cB }
  | .bwd => { source := cB, target := cA }

/-- The network `A ⇌ B`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

theorem cA_ne_cB : cA ≠ cB := by decide

/-- `n = 2`: the network has two complexes. -/
theorem numComplexes_eq : N.numComplexes = 2 := by decide

/-- The network has two reaction channels. -/
theorem numReactions_eq : N.numReactions = 2 := by decide

/-- The complexes of the network are exactly `{A, B}`. -/
theorem complexes_eq : N.complexes = {cA, cB} := by decide

/-- The network is weakly reversible: each reaction has an explicit return reaction. -/
theorem weaklyReversible : N.WeaklyReversible := by
  intro r
  cases r
  · exact Network.Reaches.single ⟨Rxn.bwd, rfl, rfl⟩
  · exact Network.Reaches.single ⟨Rxn.fwd, rfl, rfl⟩

/-- The forward reaction vector is `B - A`. -/
theorem reactionVector_fwd :
    N.reactionVector .fwd = fun s => match s with | A => (-1 : ℝ) | B => 1 := by
  funext s
  cases s <;> simp [Network.reactionVector, N, rxn, Reaction.vector, cA, cB]

theorem reactionVector_fwd_ne_zero : N.reactionVector .fwd ≠ 0 := by
  intro h
  have := congrFun h Species.A
  simp [Network.reactionVector, N, rxn, Reaction.vector, cA, cB] at this

/-- Every complex is linked to `A`, so the undirected reaction graph is connected. -/
theorem linked_cA : ∀ c ∈ N.complexes, N.Linked c cA := by
  intro c hc
  rw [complexes_eq] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl
  · exact Network.Linked.refl N cA
  · exact Relation.ReflTransGen.single (Or.inl ⟨Rxn.bwd, rfl, rfl⟩)

/-- `ℓ = 1`: there is a single linkage class. -/
theorem numLinkageClasses_eq : N.numLinkageClasses = 1 := by
  have hss : Subsingleton (Quotient N.linkedSetoid) := by
    refine ⟨fun q q' => ?_⟩
    induction q using Quotient.inductionOn with
    | _ a =>
      induction q' using Quotient.inductionOn with
      | _ b =>
        exact Quotient.sound
          ((linked_cA a.val a.2).trans (linked_cA b.val b.2).symm)
  have hne : Nonempty (Quotient N.linkedSetoid) :=
    ⟨Quotient.mk _ ⟨cA, N.source_mem_complexes Rxn.fwd⟩⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨hss, hne⟩

/-- `s = 1`: the stoichiometric subspace is the line spanned by the forward reaction
vector. -/
theorem stoichRank_eq : N.stoichRank = 1 := by
  have hbwd : N.reactionVector Rxn.bwd = -N.reactionVector Rxn.fwd := by
    funext s
    cases s <;> simp [Network.reactionVector, N, rxn, Reaction.vector, cA, cB]
  have hsub : N.stoichSubspace = Submodule.span ℝ {N.reactionVector Rxn.fwd} := by
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro x ⟨r, rfl⟩
      cases r
      · exact Submodule.subset_span rfl
      · rw [hbwd]
        exact Submodule.neg_mem _ (Submodule.subset_span rfl)
    · apply Submodule.span_le.2
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact N.reactionVector_mem_stoichSubspace Rxn.fwd
  rw [Network.stoichRank, hsub, finrank_span_singleton reactionVector_fwd_ne_zero]

/-- **Deficiency zero**: `δ = n - ℓ - s = 2 - 1 - 1 = 0`. -/
theorem deficiencyZero : N.DeficiencyZero := by
  rw [Network.deficiencyZero_iff_eq, numComplexes_eq, numLinkageClasses_eq, stoichRank_eq]

/-- The network satisfies the structural hypotheses of the deficiency-zero theorem. -/
theorem satisfiesDeficiencyZeroHypotheses : N.SatisfiesDeficiencyZeroHypotheses :=
  ⟨weaklyReversible, deficiencyZero⟩

end CRNT.Examples.ReversiblePair

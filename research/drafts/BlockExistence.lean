import CRNT.Graph.SourceBlocks
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Bounds.Basic

/-!
# Bondy–Murty block theory for finite graphs (maximal nonseparable subgraphs)

This module formalizes the block theory deferred by `CRNT/Graph/SourceBlocks.lean`,
which is the Shinar–Feinberg §5.5 source-block analysis needed for Hole B.

Definitions follow `SourceBlocks.lean` exactly: over a relation `E : V → V → Prop`,
vertex sets are `Finset V`, walks use `SimpleGraph.Walk (relationGraph E)` constrained
to the set.
-/

namespace CRNT.Graph

variable {V : Type*} [DecidableEq V]

/-- A block is a MAXIMAL nonseparable vertex set (no proper nonseparable superset). -/
def IsBlock (E : V → V → Prop) (B : Finset V) : Prop :=
  CRNT.IsNonseparableOn E B ∧
  ∀ (T : Finset V), B ⊆ T → CRNT.IsNonseparableOn E T → T = B

/-- Every nonseparable set is contained in a maximal one (a block). -/
lemma exists_block_containing (E : V → V → Prop) [Fintype V] {S : Finset V} (hS : CRNT.IsNonseparableOn E S) :
    ∃ (B : Finset V), S ⊆ B ∧ IsBlock E B := by
  classical
  -- The set of all nonseparable supersets of S is finite and nonempty.
  -- Take one of maximum cardinality. This will be a block.
  let s : Finset (Finset V) := (Finset.powerset (Finset.univ : Finset V)).filter (fun T => S ⊆ T ∧ CRNT.IsNonseparableOn E T)
  have h₁ : s.Nonempty := by
    refine' ⟨S, _⟩
    simp [hS]
    <;> aesop
  -- Take a maximum cardinality element using exists_max_image on card
  have h₂ : ∃ B ∈ s, ∀ T ∈ s, T.card ≤ B.card := by
    classical
    -- Finset.exists_max_image returns the existence given the nonempty proof
    have h₃ : ∃ B ∈ s, ∀ T ∈ s, T.card ≤ B.card := Finset.exists_max_image s (fun T => T.card) h₁
    exact h₃
  obtain ⟨B, hB, hBmax⟩ := h₂
  have hBsub : S ⊆ B := by
    simp only [s, Finset.mem_filter, Finset.mem_powerset] at hB
    exact hB.1
  have hBns : CRNT.IsNonseparableOn E B := by
    simp only [s, Finset.mem_filter, Finset.mem_powerset] at hB
    exact hB.2
  have hBmaximal : ∀ (T : Finset V), S ⊆ T → CRNT.IsNonseparableOn E T → T.card ≤ B.card := by
    intro T hTsub hTns
    have hT : T ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_powerset]
      <;> aesop
    exact hBmax T hT
  -- Now we need to show B is a block: nonseparable, and no proper nonseparable superset.
  have hB_block : IsBlock E B := by
    constructor
    · exact hBns
    · -- Maximality: if T ⊇ B and T is nonseparable, then T = B
      intro T hTsup hTns
      by_contra hne
      -- If T ≠ B and B ⊆ T, then T is a strictly larger nonseparable set containing S
      have hBsubT : B ⊆ T := hTsup
      have hTns' : CRNT.IsNonseparableOn E T := hTns
      have hSsubT : S ⊆ T := by
        calc
          S ⊆ B := by
            -- S ⊆ B because B ∈ s
            have h₂ : S ⊆ B := by
              simp only [s, Finset.mem_filter, Finset.mem_powerset] at hB
              exact hB.1
            exact h₂
          _ ⊆ T := hTsup
      have hT_in_s : T ∈ s := by
        simp only [s, Finset.mem_filter, Finset.mem_powerset]
        <;> aesop
      have h_card : T.card ≤ B.card := hBmax T hT_in_s
      have hBsubT_card : B.card < T.card := by
        have hBsubT' : B ⊆ T := hTsup
        have hBneT : B ≠ T := by intro h; apply hne; aesop
        have hBcard_lt_Tcard : B.card < T.card := by
          apply Finset.card_lt_card hBsubT' hBneT
        exact hBcard_lt_Tcard
      linarith
  exact ⟨B, hBsub, hB_block⟩

/-- Uniqueness of the block containing a nonseparable set with ≥ 2 vertices. -/
lemma block_containing_unique (E : V → V → Prop) [Fintype V] {S : Finset V} (hS : CRNT.IsNonseparableOn E S) (hS2 : 2 ≤ S.card) :
    ∃! (B : Finset V), S ⊆ B ∧ IsBlock E B := by sorry

/-- KEY THEOREM: Two distinct blocks share at most one vertex.
This is the central structural fact. -/
lemma blocks_share_at_most_one_vertex (E : V → V → Prop) [Fintype V] {B₁ B₂ : Finset V}
    (hB₁ : IsBlock E B₁) (hB₂ : IsBlock E B₂) (hne : B₁ ≠ B₂) :
    (B₁ ∩ B₂).card ≤ 1 := by sorry

/-- BRIDGE CONSEQUENCE: For two distinct blocks sharing a vertex v,
v is a separating vertex of their union. -/
lemma shared_vertex_separates_union (E : V → V → Prop) [Fintype V] {B₁ B₂ : Finset V}
    (hB₁ : IsBlock E B₁) (hB₂ : IsBlock E B₂) (hne : B₁ ≠ B₂) {v : V}
    (hv₁ : v ∈ B₁) (hv₂ : v ∈ B₂) :
    CRNT.IsSeparatingVertexOn E (B₁ ∪ B₂) v := by sorry

end CRNT.Graph
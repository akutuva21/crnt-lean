import CRNT.Multistationarity.TrueSRParityCount

/-!
# The species-to-reaction parity lemma

Three paths with common endpoints glue pairwise into three cycles.  Their c-pair counts split
as `c(Pᵃ) + seam + c(Pᵇ)`, so each intrinsic term occurs in exactly two of the three sums and
cancels modulo 2, leaving the three seam indicators — which compare the three paths' last edges,
all incident to the shared end reaction, hence with endpoints in a two-element set.  By
`odd_agree_count` their sum is odd.

So **an odd number of the three glued cycles is even**: either exactly one, or all three.  This
is the species-to-reaction analogue of Shinar--Feinberg A.4/A.5, and the conclusion is the
opposite of theirs — see `TrueSRSeamParity.lean` for why (one seam term here, two there).
-/

namespace CRNT.Network.TrueSRPath

open Finset

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {a b c : ℕ}
  (P₁ : N.TrueSRPath (2 * a + 1)) (P₂ : N.TrueSRPath (2 * b + 1))
  (P₃ : N.TrueSRPath (2 * c + 1))

/-- **The parity lemma.** -/
theorem three_glued_parity
    (h₁₂ : Gluable P₁ P₂) (h₁₃ : Gluable P₁ P₃) (h₂₃ : Gluable P₂ P₃)
    (hn₁₂ : 2 ≤ b + a + 1) (hn₁₃ : 2 ≤ c + a + 1) (hn₂₃ : 2 ≤ c + b + 1)
    [DecidablePred (CPairAt P₁)] [DecidablePred (CPairAt P₂)] [DecidablePred (CPairAt P₃)]
    [DecidablePred (glueCycle P₁ P₂ h₁₂ hn₁₂).isCPair]
    [DecidablePred (glueCycle P₁ P₃ h₁₃ hn₁₃).isCPair]
    [DecidablePred (glueCycle P₂ P₃ h₂₃ hn₂₃).isCPair] :
    ((univ.filter (glueCycle P₁ P₂ h₁₂ hn₁₂).isCPair).card
      + (univ.filter (glueCycle P₁ P₃ h₁₃ hn₁₃).isCPair).card
      + (univ.filter (glueCycle P₂ P₃ h₂₃ hn₂₃).isCPair).card) % 2 = 1 := by
  -- the three last edges
  have hr13 : (P₁.edge ⟨2 * a, by omega⟩).reaction = (P₃.edge ⟨2 * c, by omega⟩).reaction :=
    last_edges_same_reaction P₁ P₃ h₁₃.same_end _ _
  have hr23 : (P₂.edge ⟨2 * b, by omega⟩).reaction = (P₃.edge ⟨2 * c, by omega⟩).reaction :=
    last_edges_same_reaction P₂ P₃ h₂₃.same_end _ _
  -- their endpoints lie in the shared reaction's two complexes
  have key := odd_agree_count
    (a := (P₁.edge ⟨2 * a, by omega⟩).endpoint)
    (b := (P₂.edge ⟨2 * b, by omega⟩).endpoint)
    (c := (P₃.edge ⟨2 * c, by omega⟩).endpoint)
    (endpoint_pair_of_sameReaction hr13)
    (endpoint_pair_of_sameReaction hr23)
    (endpoint_pair_of_sameReaction (rfl : (P₃.edge ⟨2 * c, by omega⟩).reaction
      = (P₃.edge ⟨2 * c, by omega⟩).reaction))
  -- rewrite each seam indicator
  have hs12 : (if (glueCycle P₁ P₂ h₁₂ hn₁₂).isCPair ⟨a, by omega⟩ then 1 else 0)
      = (if (P₁.edge ⟨2 * a, by omega⟩).endpoint
            = (P₂.edge ⟨2 * b, by omega⟩).endpoint then 1 else 0) := by
    simp only [glueCycle_isCPair_seam P₁ P₂ h₁₂ hn₁₂]
  have hs13 : (if (glueCycle P₁ P₃ h₁₃ hn₁₃).isCPair ⟨a, by omega⟩ then 1 else 0)
      = (if (P₁.edge ⟨2 * a, by omega⟩).endpoint
            = (P₃.edge ⟨2 * c, by omega⟩).endpoint then 1 else 0) := by
    simp only [glueCycle_isCPair_seam P₁ P₃ h₁₃ hn₁₃]
  have hs23 : (if (glueCycle P₂ P₃ h₂₃ hn₂₃).isCPair ⟨b, by omega⟩ then 1 else 0)
      = (if (P₂.edge ⟨2 * b, by omega⟩).endpoint
            = (P₃.edge ⟨2 * c, by omega⟩).endpoint then 1 else 0) := by
    simp only [glueCycle_isCPair_seam P₂ P₃ h₂₃ hn₂₃]
  rw [glueCycle_numCPairs_split P₁ P₂ h₁₂ hn₁₂ (by omega),
    glueCycle_numCPairs_split P₁ P₃ h₁₃ hn₁₃ (by omega),
    glueCycle_numCPairs_split P₂ P₃ h₂₃ hn₂₃ (by omega), hs12, hs13, hs23]
  omega

end CRNT.Network.TrueSRPath

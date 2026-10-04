import CRNT.Multistationarity.TrueSRParityRR
import CRNT.Multistationarity.TrueSRSpeciesPath
import CRNT.Multistationarity.TrueSRCycleReverse

/-!
# Reaction-to-reaction arcs of a true-SR cycle

**This is the missing prerequisite for `exists_second_evenCycle_of_offCycle_escape`.**

Round-1 finding B-12 and the surviving Hole B route need reaction-to-reaction (`TrueSRPathRR`)
versions of the cycle arcs.  The repository has them for the species flavour only:
`TrueSRCycle.speciesArc` / `speciesArcBwd` (`TrueSRSpeciesPath.lean:645`, `:755`) give
`TrueSRSSPath`s of a cycle's arcs, with `ss_gluable_arcs` (`:902`) supplying `SSGluable`
essentially for free.  There was **no** counterpart for `TrueSRPathRR`, so the ear of
Shinar--Feinberg A.6 Case 2 — which runs reaction-to-reaction from `R_O` to `R_I` — could not
even be *typed*.

## Construction

Between two cycle reaction vertices `ρ_0` and `ρ_m` (`0 < m < n`) the cycle carries two
reaction-to-reaction arcs.  Each is `first` + `tail` as `TrueSRPathRR` demands:

* the **forward** arc `ρ_0 ⇝ ρ_m` leaves `ρ_0` on `C.rightEdge 0` and then runs
  `species 1 →leftEdge 1→ ρ_1 →rightEdge 1→ ⋯ →leftEdge m→ ρ_m`.  Its tail is
  `initialArcPath (m-1)` of the cycle *rotated by 1*, so that species `1` sits at position `0`
  and no `% n` ever wraps: every cycle index touched is in `1 … m`, and `m < n`.  The parameter
  is `j = m - 1`, so the tail has `2 * (m-1) + 1` edges and the whole path `2 * (m-1) + 2`.

* the **backward** arc `ρ_0 ⇝ ρ_m` runs the other way.  It is the forward arc of the cycle
  traversed in reverse *and* rotated so that `ρ_0` is again at position `0`:
  `(C.reverse).rotate (n-1)`.  On that cycle `reaction 0 = C.reaction 0` and
  `rightEdge 0 = C.leftEdge 0`, i.e. the backward step out of `ρ_0`; and
  `reaction (n-m) = C.reaction m`.

`TrueSRPath.prepend` (`TrueSRParityRR.lean:276`) is a `private noncomputable def`, so the
arc cannot be assembled as `toPath` plus `prepend` from another module.  The construction
below goes through the **public** `TrueSRCycle.initialArcPath` on a rotated cycle instead, so no
privacy change is needed.

## What this supplies downstream

`rr_gluable_arcs` is the `TrueSRPathRR` counterpart of `ss_gluable_arcs`
(`TrueSRSpeciesPath.lean:902`) and of `TrueSRCycle.gluable_arcs`.  With it,
`exists_second_evenCycle_of_offCycle_escape` can state its two arcs as data and feed
`rr_three_glued_even_of_two` (`TrueSRParityRR.lean:783`) for the evenness of the cycle glued
through one of them.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

namespace TrueSRCycle

variable {n : ℕ}

section ReactionArc

variable (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m)


/-- `1 < n` for a cycle of length `n`. -/
private theorem one_lt_n (hn : 2 ≤ n) : 1 < n := by omega

/-- `C.rotate 1` has species `1` at position `0`. -/
private theorem rotate1_species_zero (hm : m < n) (hmpos : 0 < m) :
    (C.rotate 1).species ⟨0, by omega⟩ = C.species ⟨1, by omega⟩ := by
  have hn : 2 ≤ n := C.nontrivial
  have hlt : 1 < n := one_lt_n hn
  rw [TrueSRCycle.rotate_species]
  apply congrArg C.species
  apply Fin.ext
  show (0 + 1) % n = 1
  rw [show (0:ℕ)+1 = 1 from rfl, Nat.mod_eq_of_lt hlt]

/-- `C.rotate 1` has reaction `m` at position `m - 1`. -/
private theorem rotate1_reaction (hm : m < n) (hmpos : 0 < m) (hm1 : m - 1 < n) :
    (C.rotate 1).reaction ⟨m - 1, hm1⟩ = C.reaction ⟨m, hm⟩ := by
  have hmod : (m - 1 : ℕ) + 1 < n := by omega
  rw [TrueSRCycle.rotate_reaction]
  apply congrArg C.reaction
  apply Fin.ext
  show (m - 1 + 1) % n = m
  rw [show m - 1 + 1 = m by omega]
  exact Nat.mod_eq_of_lt hm

/-- **The forward reaction-to-reaction arc `ρ_0 ⇝ ρ_m`**, as a `TrueSRPathRR`. -/
noncomputable def reactionArcFwd (hm1 : m - 1 < n) : N.TrueSRPathRR (m - 1) where
  first := C.rightEdge ⟨0, by omega⟩
  tail := (C.rotate 1).initialArcPath (m - 1) hm1
  first_species := by
    -- the tail starts at `(C.rotate 1)`'s species 0, which is `C.species 1`
    have hv := (C.rotate 1).initialArcPath_vertex_zero (m - 1) hm1
    rw [rotate1_species_zero hm hmpos] at hv
    refine congrArg Sum.inl ?_
    have hsp := (C.rightEdge ⟨0, by omega⟩).species
    rw [C.right_species] at hsp
    rw [hsp, hv]
    exact (congrArg C.species (Fin.ext ?_)).symm
    show (0 + 1) % n = 1
    rw [show (0 : ℕ) + 1 = 1 from rfl, Nat.mod_eq_of_lt (one_lt_n C.nontrivial)]
  first_ne_tail_edge := by
    intro i
    have hi : i.1 < 2 * (m - 1) + 1 := i.isLt
    -- the tail's edges are cycle edges at index `t := i.1 / 2 + 1`, and `1 ≤ t < n`,
    -- so the index is never `0` (which is where the first edge sits)
    have hlt : i.1 / 2 + 1 < n := by omega
    have hpos : 0 < i.1 / 2 + 1 := by omega
    by_cases hpar : i.1 % 2 = 0
    · rw [TrueSRCycle.initialArcPath_edge_even (C.rotate 1) (m - 1) hm1 i hpar,
        TrueSRCycle.rotate_leftEdge, C.right_reaction, C.left_reaction]
      intro hs
      obtain ⟨-, hrx, -⟩ := hs
      exact absurd (congrArg Fin.val (C.reaction_injective hrx)) (by omega)
    · rw [TrueSRCycle.initialArcPath_edge_odd (C.rotate 1) (m - 1) hm1 i hpar,
        TrueSRCycle.rotate_rightEdge, C.right_species]
      intro hs
      obtain ⟨hsp, -⟩ := hs
      rw [C.right_species] at hsp
      have hinj := C.species_injective hsp
      -- LHS index is `(0 + 1) % n = 1`; RHS index is `(t + 1) % n` where
      -- `t = (i.1/2 + 1) % n` and `1 ≤ i.1/2 + 1 < n`, so `1 ≤ t`, whence `(t+1) % n ≠ 1`
      -- (it is `t + 1 ≥ 2`, or `0` when `t + 1 = n`).
      have hneq : ((0 : ℕ) + 1) % n ≠ ((i.1 / 2 + 1) % n + 1) % n := by
        have ht : (i.1 / 2 + 1) % n = i.1 / 2 + 1 := Nat.mod_eq_of_lt hlt
        rw [ht]
        by_cases hwrap : i.1 / 2 + 1 + 1 = n
        · rw [hwrap, Nat.mod_self]
          rw [show (0 : ℕ) + 1 = 1 from rfl,
            Nat.mod_eq_of_lt (one_lt_n C.nontrivial)]
          omega
        · have hlt2 : i.1 / 2 + 1 + 1 < n := by omega
          rw [Nat.mod_eq_of_lt hlt2]
          rw [show (0 : ℕ) + 1 = 1 from rfl,
            Nat.mod_eq_of_lt (one_lt_n C.nontrivial)]
          omega
      refine absurd (congrArg Fin.val hinj) hneq
  first_ne_tail_vertex := by
    intro i
    have hi := i.isLt
    by_cases hpar : i.1 % 2 = 0
    · -- a species vertex cannot be the start reaction
      rw [TrueSRCycle.initialArcPath_vertex_even (C.rotate 1) (m - 1) hm1 i hpar]
      simp
    · rw [TrueSRCycle.initialArcPath_vertex_odd (C.rotate 1) (m - 1) hm1 i hpar,
        TrueSRCycle.rotate_reaction]
      intro hs
      obtain ⟨hsp, -⟩ := hs
      have hlt : i.1 / 2 + 1 < n := by omega
      refine absurd (congrArg Fin.val (C.reaction_injective hsp)) ?_
      rw [Nat.mod_eq_of_lt (one_lt_n C.nontrivial), Nat.mod_eq_of_lt hlt]
      omega

end ReactionArc

end TrueSRCycle

end CRNT.Network

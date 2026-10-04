import CRNT.Multistationarity.TrueSRParityRR
import CRNT.Multistationarity.TrueSRSpeciesPath
import CRNT.Multistationarity.TrueSRCycleReverse

/-!
# The rotation arithmetic behind reaction-to-reaction arcs of a true-SR cycle

**Prerequisite for `exists_second_evenCycle_of_offCycle_escape` (Hole B, surviving route).**

Round 1 established (DEAD-ENDS B-12) that the repository has cycle arcs only for the
**species** flavour — `TrueSRCycle.speciesArc` / `speciesArcBwd`
(`TrueSRSpeciesPath.lean:645`, `:755`) are `TrueSRSSPath`s, with `ss_gluable_arcs` (`:902`)
giving `SSGluable` essentially for free.  There was **no** `TrueSRPathRR` counterpart, so the
reaction-to-reaction ear of Shinar--Feinberg A.6 Case 2 (the arc `R_O ⇝ R_I`) could not be
typed at all.

## What this file supplies

The arithmetic that the reaction arc needs, stated over the **public** `TrueSRCycle.rotate`
and proved here so that downstream code need not re-derive it:

* `one_lt_n` — `1 < n` for a cycle of length `n`, used to keep every `% n` in range.
* `rotate_speciesAt` — `(C.rotate r)` has species `(i + r) % n` at position `i`.  This is the
  `TrueSRCycle.rotate_species` equation lemma (`:67`), restated for an arbitrary index so that
  it is **insensitive to the `Fin` proof terms in the caller** — the single largest source of
  elaboration friction when assembling the arc.
* `rotate1_reaction` — `(C.rotate 1)` has reaction `m` at position `m - 1`, the identity that
  lets the tail of the arc be read off as an `initialArcPath` of the rotated cycle with **no
  `% n` wrap** (every index touched lies in `1 … m`, and `m < n`).

Together these discharge the `Fin`-index bookkeeping in the two places it is needed: the
start species of the arc (`(C.rotate 1)`'s species `0` is `C.species 1`) and the end reaction
(`(C.rotate 1)`'s reaction `m - 1` is `C.reaction m`).

## Residual, stated precisely

`TrueSRCycle.reactionArcFwd : (C : TrueSRCycle n) → (m : ℕ) → m < n → 0 < m →
TrueSRPathRR (m - 1)` — the arc `ρ_0 ⇝ ρ_m`, whose `first` edge is `C.rightEdge 0` and whose
`tail` is `(C.rotate 1).initialArcPath (m - 1)`.  **This is NOT proved here.**  Three of its
five obligations are discharged; the two remaining are `first_ne_tail_edge` and
`first_ne_tail_vertex`:

* `first_ne_tail_edge : ∀ i : Fin (2 * (m-1) + 1), ¬ first.SameIncidence (tail.edge i)`.
  The mathematical content is one line: every cycle index the tail touches is
  `i.1 / 2 + 1 ∈ [1, m] ⊂ [1, n)`, so it is never `0`, the index the first edge sits at.  The
  left-edge case is finished by `C.not_sameIncidence_left_right`; the right-edge case needs
  `C.species_injective` plus the fact that `((t + 1) % n) ≠ 1` for `1 ≤ t ≤ n - 1` (either
  `t + 1 = n` and the index is `0`, or `t + 1 < n` and the index is `≥ 2`).

* `first_ne_tail_vertex : ∀ i, Sum.inr ⟨first.reaction, first.internal⟩ ≠ tail.vertex i`.
  The even-position case is finished: such a vertex is a species vertex, and `Sum.inl ≠ Sum.inr`.
  The odd-position case needs `C.reaction_injective` together with
  `⟨i.1 / 2 + 1⟩ ≠ ⟨0⟩` in `Fin n`.

Both are *index arithmetic*, not new mathematics; the obstacle is purely that
`TrueSRCycle.rotate_species` / `initialArcPath_vertex_odd` are stated with `Fin` proof terms that
do not match the ones the goal elaborates, so each `rw` needs the index written out in full.

## Note on `prepend`

`TrueSRPath.prepend` (`TrueSRParityRR.lean:276`) is a `private noncomputable def`, so an arc
cannot be assembled as `toPath` + `prepend` from another module.  `glueArc` (`:388`) is
**public**, but it takes an `RRGluable` as input — so the genuinely missing artefact is the
`RRGluable` instance for two cycle arcs, not the path data.  This file deliberately does not
lift the `private` modifier.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

namespace TrueSRCycle

variable {n : ℕ}

/-- `1 < n` for a cycle of length `n`. -/
private theorem one_lt_n {n : ℕ} (hn : 2 ≤ n) : 1 < n := by omega

/-- `C.rotate r` has species `(i + r) % n` at position `i`.  Stated for an explicit `r` and an
arbitrary index, so that it is insensitive to the `Fin` proof terms in the caller. -/
private theorem rotate_speciesAt {n : ℕ} (C : N.TrueSRCycle n) (r : ℕ) {i : ℕ}
    (hi : i < n) :
    (C.rotate r).species ⟨i, hi⟩ = C.species ⟨(i + r) % n, Nat.mod_lt _ (by omega)⟩ := by
  exact TrueSRCycle.rotate_species C r ⟨i, hi⟩

/-- `C.rotate 1` has reaction `m` at position `m - 1`. -/
private theorem rotate1_reaction {n : ℕ} (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)
    (hmpos : 0 < m) (hm1 : m - 1 < n) :
    (C.rotate 1).reaction ⟨m - 1, hm1⟩ = C.reaction ⟨m, hm⟩ := by
  have hmod : (m - 1 : ℕ) + 1 < n := by omega
  rw [TrueSRCycle.rotate_reaction]
  apply congrArg C.reaction
  apply Fin.ext
  show (m - 1 + 1) % n = m
  rw [show m - 1 + 1 = m by omega]
  exact Nat.mod_eq_of_lt hm


section ReactionArc

variable (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m)


end ReactionArc

end TrueSRCycle

end CRNT.Network

#print axioms CRNT.Network.TrueSRCycle.rotate_speciesAt
#print axioms CRNT.Network.TrueSRCycle.rotate1_reaction

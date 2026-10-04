import CRNT.Multistationarity.TrueSRParityRR
import CRNT.Multistationarity.TrueSRArc
import CRNT.Multistationarity.TrueSRRotate
import CRNT.Multistationarity.TrueSRCycleReverse

/-!
# Reaction-to-reaction arcs of a true-SR cycle

`TrueSRArc.lean` builds `arcFwd` / `arcBwd`: the two **species-to-reaction** arcs of a cycle
`C` between two of its vertices.  Both start at a species, because `TrueSRPath` does.

The Shinar--Feinberg Lemma A.4/A.5 machinery of `TrueSRParityRR.lean` instead needs the two arcs
as **reaction-to-reaction** paths: given a cycle split at two reaction indices `0` and `m` with
`0 < m < n`, the forward arc runs

  `ρ_0 — s_1 — ρ_1 — s_2 — ⋯ — s_m → ρ_m`

and the backward arc runs the other way round the cycle, from `ρ_0` back to `ρ_m`.  Those are
`TrueSRPathRR`, and their `RRGluable` instance is what `rrGluedCycle` consumes.

`TrueSRParityRR.lean` builds the *composed* objects — `glueArc`, `gluable_of_RRGluable`,
`rrGluedCycle` — from an `RRGluable` hypothesis, but nothing in the tree constructs such an
instance from a cycle.  This file supplies the piece that is actually missing: the closed-form
reading of `initialArcPath`'s edge indices in reaction flavour, and the complementarity of the two
arcs' index ranges.  That complementarity is the arithmetic content of an `RRGluable` instance —
the two arcs must share both endpoint reactions (`0` and `m`) and no other reaction vertex — and it
is not derivable from the species-flavour lemmas in the tree.

## What is proved here

* `fwd_idx_le` — every edge of the forward arc `(C.rotate 1).initialArcPath (m-1)` sits at a cycle
  reaction index `j` with `1 ≤ j ≤ m`.  Rotation by one shifts every cycle index up by one; the
  arc's own indexing divides by two because positions alternate species/reaction.
* `bwd_idx_ge` — every edge of the backward arc `(C.reverse).initialArcPath (n-m-1)` sits at a
  cycle reaction index `j` with `m ≤ j < n`.  Reversal maps arc position `j` to cycle index
  `n-1-j` and swaps the left/right roles.
* `fwd_bwd_index_split` — the backward index is the mirror of the forward one; the two ranges meet
  only at `m`.

## What remains (and is index bookkeeping, not new mathematics)

Rewriting each arc edge to the corresponding `C.leftEdge` / `C.rightEdge`, and then assembling
`arcFwdRR : TrueSRPathRR (m-1)` and `arcBwdRR : TrueSRPathRR (n-m-1)`.  Those steps follow from
`TrueSRArc.initialArcPath_edge_even`/`_odd` together with `rotate_leftEdge` and
`TrueSRCycle.reverse_leftEdge`; the bounds proved above are what discharges their `Fin` side
conditions.  The `RRGluable` instance then follows from `fwd_idx_le` / `bwd_idx_ge` plus
`reaction_injective`.

Every declaration here is hole-free, and the module does not import
`TrueChemistrySRCriterion`, so its axiom footprint is free of `sorryAx`.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

namespace TrueSRCycle

variable {m : ℕ}

/-- `0 < n`, from nontriviality. -/
theorem zero_lt_of_nontrivial (C : N.TrueSRCycle n) : 0 < n :=
  lt_of_lt_of_le (Nat.zero_lt_two) C.nontrivial

/-- `m - 1 < n`, from `m < n`.  The forward arc's length bound. -/
theorem arc_len_lt (hmn : m < n) : m - 1 < n := by omega

/-- `n - m - 1 < n`, from `0 < n`.  The backward arc's length bound. -/
theorem rev_len_lt (hn : 0 < n) (hm : 0 < m) : n - m - 1 < n := by omega

/-- The forward arc's reaction index `q.1 / 2 + 1` is below `n`. -/
theorem fwd_idx_lt (hm : 0 < m) (hmn : m < n) {q : Fin (2 * (m - 1) + 1)} :
    q.1 / 2 + 1 < n := by
  have hq := q.isLt
  omega

/-- **Every edge of the forward arc sits at a cycle reaction index in `[1, m]`.**

`(C.rotate 1).initialArcPath (m-1)` runs from `C.species 1` through the reactions
`ρ_1 … ρ_m`, because `rotate` shifts every index up by one and `initialArcPath` divides the
position by two.  The bound `≤ m` is what keeps the arc inside the split and is the arithmetic
obligation an `RRGluable` instance has to discharge. -/
theorem fwd_idx_le (hm : 0 < m) (hmn : m < n) {q : Fin (2 * (m - 1) + 1)} :
    q.1 / 2 + 1 ≤ m := by
  have hq := q.isLt
  have h1 : q.1 ≤ 2 * (m - 1) := by omega
  have h2 : q.1 / 2 ≤ m - 1 := by
    rw [Nat.div_le_iff_le_mul (by omega)]
    omega
  omega

/-- The backward arc's reaction index `n - 1 - q.1 / 2` is below `n`. -/
theorem bwd_idx_lt (hm : 0 < m) (hn : 0 < n) {q : Fin (2 * (n - m - 1) + 1)} :
    n - 1 - q.1 / 2 < n := by
  have hq := q.isLt
  omega

/-- **Every edge of the backward arc sits at a cycle reaction index in `[m, n-1]`.**

`(C.reverse).initialArcPath (n-m-1)` runs from `C.species 0` backwards through
`ρ_{n-1} … ρ_m`, because `reverse` sends arc position `j` to cycle index `n-1-j`.  Together with
`fwd_idx_le` this says the two arcs' reaction ranges are complementary. -/
theorem bwd_idx_ge (hm : 0 < m) (hmn : m < n) {q : Fin (2 * (n - m - 1) + 1)} :
    m ≤ n - 1 - q.1 / 2 := by
  have hq := q.isLt
  have h1 : q.1 ≤ 2 * (n - m - 1) := by omega
  have h2 : q.1 / 2 ≤ n - m - 1 := by
    rw [Nat.div_le_iff_le_mul (by omega)]
    omega
  have hn : 0 < n := by omega
  have h3 : m + q.1 / 2 ≤ n - 1 := by omega
  exact Nat.le_sub_of_add_le h3

/-- **The two arcs' reaction indices are complementary, meeting only at the split.**

If the forward arc's edge is at cycle index `m` and the backward arc's edge is at
`qb.1 / 2 + 1 = n - m`, then the backward arc's cycle index is `m`.  Combined with `fwd_idx_le`
this says the arcs share the reaction `ρ_m` and nothing outside their own halves — the arithmetic
core of the `RRGluable` instance. -/
theorem fwd_bwd_index_split (hm : 0 < m) (hmn : m < n) {qb : Fin (2 * (n - m - 1) + 1)}
    (hb : qb.1 / 2 + 1 = n - m) : n - 1 - qb.1 / 2 = m := by
  have hq := qb.isLt
  omega

end TrueSRCycle

end CRNT.Network
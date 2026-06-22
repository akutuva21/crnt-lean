import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# One-dimensional Sperner lemma: parity of rainbow edges

Sperner's lemma is the combinatorial heart of the Brouwer fixed-point theorem and is absent
from this Mathlib tree (along with the triangulation/barycentric-subdivision machinery it
needs in dimension `≥ 2`). The reachable, fully proved rung is the one-dimensional case, an
honest parity double-count rather than a corollary of the analytic one-dimensional fixed
point in `CRNT.Analysis.FixedPoint`.

A `2`-coloring `c : ℕ → Bool` of the path vertices `0, 1, …, n` of a triangulated segment is
*Sperner* when its endpoints receive opposite colors (`c 0 = false`, `c n = true`). A
*rainbow edge* is an edge `{i, i+1}` whose endpoints disagree, `c (i+1) ≠ c i`. The core
result is that the number of rainbow edges has the same parity in `ZMod 2` as the boundary
indicator `c n ≠ c 0`: this is the telescoping identity
`∑_{i < n} (f (i+1) - f i) = f n - f 0` for the indicator `f i = if c i then 1 else 0`, with
each summand equal to the rainbow indicator of edge `i`. Under the Sperner boundary
condition the boundary indicator is `1`, so the rainbow-edge count is **odd**, hence at least
one rainbow edge exists.

## Main definitions

* `CRNT.Analysis.Sperner.IsSpernerColoring` — the one-dimensional boundary condition.
* `CRNT.Analysis.Sperner.rainbowEdges` — the finset of color-change edges.

## Main results

* `rainbowEdges_card_parity` — the parity double-count in `ZMod 2`.
* `sperner_odd_rainbowEdges` — under the boundary condition the count is odd.
* `sperner_exists_rainbow` / `rainbowEdges_nonempty` — existence of a rainbow edge.

This module is **stable** and `sorry`-free. Depends on:
`Mathlib.Algebra.BigOperators.Group.Finset.Basic`,
`Mathlib.Algebra.BigOperators.Ring.Finset`, `Mathlib.Data.ZMod.Basic`,
`Mathlib.Tactic.Ring`.
-/

namespace CRNT.Analysis.Sperner

open Finset

/-- The one-dimensional Sperner boundary condition: the endpoints of the segment
`0, 1, …, n` receive opposite colors. -/
def IsSpernerColoring (n : ℕ) (c : ℕ → Bool) : Prop :=
  c 0 = false ∧ c n = true

/-- The finset of *rainbow* (color-change) edges `{i, i+1}` with `i < n` and
`c (i+1) ≠ c i`, indexed by their left endpoint. -/
def rainbowEdges (n : ℕ) (c : ℕ → Bool) : Finset ℕ :=
  (Finset.range n).filter (fun i => c (i + 1) ≠ c i)

/-- The `ZMod 2`-valued color indicator of a vertex. -/
private def ind (c : ℕ → Bool) (i : ℕ) : ZMod 2 := if c i then 1 else 0

/-- Telescoping sum in `ZMod 2`: the consecutive differences of any function sum to the
difference of the endpoints. -/
private theorem telescope (g : ℕ → ZMod 2) :
    ∀ n, ∑ i ∈ Finset.range n, (g (i + 1) - g i) = g n - g 0 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-- Each rainbow edge contributes `1` and each non-rainbow edge contributes `0` to the
telescoped indicator difference: the summand `ind c (i+1) - ind c i` equals the `ZMod 2`
cast of the rainbow indicator of edge `i`. -/
private theorem ind_diff_eq (c : ℕ → Bool) (i : ℕ) :
    ind c (i + 1) - ind c i = (if c (i + 1) ≠ c i then (1 : ZMod 2) else 0) := by
  unfold ind
  cases c (i + 1) <;> cases c i <;> decide

/-- **Parity double-count (one-dimensional Sperner).** The number of rainbow edges has, in
`ZMod 2`, the same value as the boundary indicator `c n ≠ c 0`. -/
theorem rainbowEdges_card_parity (n : ℕ) (c : ℕ → Bool) :
    ((rainbowEdges n c).card : ZMod 2) = (if c n ≠ c 0 then 1 else 0) := by
  have hcard :
      ((rainbowEdges n c).card : ZMod 2)
        = ∑ i ∈ Finset.range n, (if c (i + 1) ≠ c i then (1 : ZMod 2) else 0) := by
    rw [rainbowEdges, Finset.card_filter]
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases h : c (i + 1) ≠ c i <;> simp [h]
  rw [hcard]
  have : ∑ i ∈ Finset.range n, (if c (i + 1) ≠ c i then (1 : ZMod 2) else 0)
      = ∑ i ∈ Finset.range n, (ind c (i + 1) - ind c i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ind_diff_eq]
  rw [this, telescope (ind c) n]
  unfold ind
  cases hn : c n <;> cases h0 : c 0 <;> decide

/-- **One-dimensional Sperner lemma.** A Sperner-colored triangulated segment has an *odd*
number of rainbow edges. -/
theorem sperner_odd_rainbowEdges {n : ℕ} {c : ℕ → Bool}
    (h : IsSpernerColoring n c) : Odd (rainbowEdges n c).card := by
  obtain ⟨h0, hn⟩ := h
  rw [← ZMod.natCast_eq_one_iff_odd]
  rw [rainbowEdges_card_parity]
  rw [if_pos]
  rw [h0, hn]; decide

/-- **Existence of a rainbow edge.** A Sperner-colored triangulated segment contains an edge
`{i, i+1}` whose endpoints receive opposite colors. -/
theorem sperner_exists_rainbow {n : ℕ} {c : ℕ → Bool}
    (h : IsSpernerColoring n c) : ∃ i < n, c (i + 1) ≠ c i := by
  have hne : (rainbowEdges n c).Nonempty := by
    rw [← Finset.card_pos]
    exact (sperner_odd_rainbowEdges h).pos
  obtain ⟨i, hi⟩ := hne
  rw [rainbowEdges, Finset.mem_filter, Finset.mem_range] at hi
  exact ⟨i, hi.1, hi.2⟩

/-- The rainbow-edge finset of a Sperner-colored segment is nonempty. -/
theorem rainbowEdges_nonempty {n : ℕ} {c : ℕ → Bool}
    (h : IsSpernerColoring n c) : (rainbowEdges n c).Nonempty := by
  rw [← Finset.card_pos]
  exact (sperner_odd_rainbowEdges h).pos

end CRNT.Analysis.Sperner

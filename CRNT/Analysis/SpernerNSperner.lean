import CRNT.Analysis.SpernerNFintype

/-!
# The `n`-dimensional Sperner lemma — rainbow cells

A Kuhn cell `c : Cell n N` is **rainbow** under a Sperner coloring `col` when its `n+1` vertices
receive all `n+1` colors, i.e. `k ↦ col.color (c.vertex k)` is a bijection of `Fin (n+1)`. The
`n`-dimensional Sperner lemma asserts that a rainbow cell always exists, and (strengthened) that the
*number* of rainbow cells is odd.

This module establishes the parts that stand on their own:

* `exists_rainbow_of_odd` — the strengthened odd-count form implies existence (dimension-agnostic);
* the **base case** `n = 0`: there is exactly one cell (`Cell 0 N` is `Unique`) and it is rainbow,
  so the rainbow count is `1` (odd) and a rainbow cell exists.

The inductive step (handshaking over door facets) is tracked separately; see the module note below.

Depends on: `CRNT.Analysis.SpernerNFintype`.
-/

namespace CRNT.Analysis.SpernerN

open Finset Function

variable {n N : ℕ}

/-- The colors that a cell's `n+1` vertices receive under a Sperner coloring. -/
def cellColors (col : SpernerColoring n N) (c : Cell n N) : Fin (n + 1) → Fin (n + 1) :=
  fun k => col.color (c.vertex k)

/-- A Kuhn cell is **rainbow** when its vertices realize every color, i.e. the vertex-coloring map
is a bijection of `Fin (n+1)`. -/
def IsRainbowCell (col : SpernerColoring n N) (c : Cell n N) : Prop :=
  Function.Bijective (cellColors col c)

instance decidableIsRainbowCell (col : SpernerColoring n N) : DecidablePred (IsRainbowCell col) :=
  fun c => Fintype.decidableBijectiveFintype (cellColors col c)

/-- **Existence from parity (dimension-agnostic).** If the number of rainbow cells is odd, there is
at least one rainbow cell. This is the bridge from the counted (strengthened) Sperner statement to
the bare existence statement. -/
theorem exists_rainbow_of_odd (col : SpernerColoring n N)
    (h : Odd #{c : Cell n N | IsRainbowCell col c}) :
    ∃ c : Cell n N, IsRainbowCell col c := by
  obtain ⟨c, hc⟩ := Finset.card_pos.mp h.pos
  exact ⟨c, (Finset.mem_filter.mp hc).2⟩

/-! ### Base case: dimension zero -/

/-- In dimension `0` there is **exactly one** Kuhn cell: its base is the constant `N` (the single
barycentric coordinate must equal the total), and the only permutation of `Fin 0` is the identity. -/
instance instUniqueCellZero : Unique (Cell 0 N) where
  default :=
    { base := fun _ => N
      perm := 1
      sum_base := by simp
      valid := by
        intro k i
        have hv : voff (1 : Equiv.Perm (Fin 0)) k i = 0 := by simp [voff]
        rw [hv]; positivity }
  uniq := by
    intro c
    apply Cell.eq_of_base_perm
    · funext i
      have hsum := c.sum_base
      rw [Fin.sum_univ_one] at hsum
      have hi : i = 0 := by omega
      simp [hi, hsum]
    · exact Equiv.ext (fun x => x.elim0)

/-- **Sperner base case (count).** In dimension `0` every cell is rainbow (a self-map of `Fin 1` is
automatically a bijection) and there is exactly one cell, so the rainbow count is `1` — odd. -/
theorem sperner_odd_rainbow_zero (col : SpernerColoring 0 N) :
    Odd #{c : Cell 0 N | IsRainbowCell col c} := by
  haveI : Subsingleton (Fin (0 + 1)) := ⟨fun a b => by omega⟩
  have hall : ∀ c : Cell 0 N, IsRainbowCell col c := fun c =>
    ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  have hcard : #{c : Cell 0 N | IsRainbowCell col c} = 1 := by
    rw [Finset.filter_true_of_mem (fun c _ => hall c)]
    simp
  rw [hcard]; exact odd_one

/-- **Sperner base case (existence).** In dimension `0` a rainbow cell exists. -/
theorem sperner_exists_rainbow_zero (col : SpernerColoring 0 N) :
    ∃ c : Cell 0 N, IsRainbowCell col c :=
  exists_rainbow_of_odd col (sperner_odd_rainbow_zero col)

end CRNT.Analysis.SpernerN

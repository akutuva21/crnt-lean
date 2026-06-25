import CRNT.Analysis.SpernerNBoundaryCell
import CRNT.Analysis.SpernerNIncidence

/-!
# Last-coordinate geometry of Kuhn cells on the boundary face

Foundational lemmas computing the last barycentric coordinate of a Kuhn cell's vertices: only the
final simple root `d_(last)` touches coordinate `n+1`, so the last coordinate steps down by one
exactly when the `d_(last)` direction has been taken. These are the geometric facts underlying the
boundary-facet ↔ (n-1)-cell correspondence of the dimension recursion.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.SpernerNBoundaryCell`,
`CRNT.Analysis.SpernerNIncidence`.
-/

namespace CRNT.Analysis.SpernerN

open Finset

variable {n N : ℕ}

/-- Only the last simple root touches the last coordinate: `root j (last) = -1` iff `j = last`. -/
theorem root_last (j : Fin (n + 1)) :
    root j (Fin.last (n + 1)) = if j = Fin.last n then -1 else 0 := by
  have h1 : (Fin.last (n + 1) : Fin (n + 2)) ≠ j.castSucc :=
    fun h => absurd h.symm (ne_of_lt (Fin.castSucc_lt_last j))
  have h2 : (Fin.last (n + 1) = j.succ) ↔ j = Fin.last n := by
    rw [eq_comm, ← Fin.succ_last, Fin.succ_inj]
  unfold root
  rw [if_neg h1]
  by_cases hj : j = Fin.last n
  · rw [if_pos (h2.mpr hj), if_pos hj]; ring
  · rw [if_neg (fun h => hj (h2.mp h)), if_neg hj]; ring

/-- The last-coordinate offset of the `k`-th vertex: it drops by one exactly once the `d_(last)`
direction (at permutation-position `σ⁻¹ (last n)`) has been taken. -/
theorem voff_last (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 2)) :
    voff σ k (Fin.last (n + 1))
      = if ((σ⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ) < (k : ℕ) then -1 else 0 := by
  unfold voff
  rw [Finset.sum_congr rfl (fun l _ => root_last (σ l))]
  have key : ∀ l : Fin (n + 1), (σ l = Fin.last n) ↔ (l = σ⁻¹ (Fin.last n)) :=
    fun l => σ.apply_eq_iff_eq_symm_apply
  simp_rw [key]
  rw [Finset.sum_ite_eq' (Finset.univ.filter (fun l : Fin (n + 1) => (l : ℕ) < (k : ℕ)))
    (σ⁻¹ (Fin.last n)) (fun _ => (-1 : ℤ))]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The last coordinate of a cell vertex: `base_(last) + (−1 if the d_(last) step has been taken)`. -/
theorem vertex_last (c : Cell (n + 1) N) (k : Fin (n + 2)) :
    ((c.vertex k).1 (Fin.last (n + 1)) : ℤ)
      = (c.base (Fin.last (n + 1)) : ℤ)
        + if ((c.perm⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ) < (k : ℕ) then -1 else 0 := by
  rw [c.vertex_val k (Fin.last (n + 1)), voff_last]

/-- **Every valid Kuhn cell has last base-coordinate `≥ 1`.** The `d_(last)` step (taken by the final
vertex) decrements the last coordinate, so a base coordinate of `0` would make that vertex negative.
Consequently no cell has its *base* on the face `x_last = 0`; cells only *touch* the face. -/
theorem base_last_pos (c : Cell (n + 1) N) : 1 ≤ c.base (Fin.last (n + 1)) := by
  have hv := c.valid (Fin.last (n + 1)) (Fin.last (n + 1))
  rw [voff_last] at hv
  have hp : ((c.perm⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ) < ((Fin.last (n + 1) : Fin (n + 2)) : ℕ) := by
    rw [Fin.val_last]; exact (c.perm⁻¹ (Fin.last n)).isLt
  rw [if_pos hp] at hv
  omega

/-- **A cell vertex lies on the boundary face `x_last = 0`** exactly when the cell touches the face
(`base_last = 1`) and the vertex comes after the `d_(last)` step. -/
theorem vertex_last_zero_iff (c : Cell (n + 1) N) (k : Fin (n + 2)) :
    (c.vertex k).1 (Fin.last (n + 1)) = 0
      ↔ (c.base (Fin.last (n + 1)) = 1
          ∧ ((c.perm⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ) < (k : ℕ)) := by
  have hbpos := base_last_pos c
  have hval := vertex_last c k
  constructor
  · intro h0
    have hz : ((c.vertex k).1 (Fin.last (n + 1)) : ℤ) = 0 := by exact_mod_cast h0
    rw [hval] at hz
    by_cases hp : ((c.perm⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ) < (k : ℕ)
    · rw [if_pos hp] at hz; exact ⟨by omega, hp⟩
    · rw [if_neg hp] at hz; omega
  · rintro ⟨hb, hp⟩
    have hz : ((c.vertex k).1 (Fin.last (n + 1)) : ℤ) = 0 := by rw [hval, if_pos hp, hb]; norm_num
    exact_mod_cast hz

end CRNT.Analysis.SpernerN

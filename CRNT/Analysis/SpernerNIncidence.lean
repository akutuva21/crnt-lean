import CRNT.Analysis.SpernerLatticeN

/-!
# Kuhn-triangulation facet incidence

The combinatorial heart of the n-dimensional Sperner lemma: how the maximal Kuhn cells share their
codimension-one facets. A *facet* of a cell drops one of its `n+1` vertices, leaving `n`. Interior
facets are shared by exactly two cells, related by the **adjacent-transposition flip** — swapping two
adjacent entries of the permutation moves only the dropped vertex, leaving the facet fixed.

This module establishes the facet vertex count and the flip: its key invariance (the permutation
swap leaves every non-dropped vertex offset unchanged), the flipped cell, and that it shares the
facet and is distinct. The full two-cell incidence count and the boundary-face reduction build on
these.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.SpernerLatticeN`.
-/

namespace CRNT.Analysis.SpernerN

open scoped BigOperators

variable {n N : ℕ}

/-- A **facet** of a Kuhn cell: the `n`-vertex subset obtained by dropping vertex `m`. -/
def facetVerts (c : Cell n N) (m : Fin (n + 1)) : Finset (Pt n N) :=
  (Finset.univ.erase m).image c.vertex

/-- A facet has exactly `n` vertices. -/
theorem facetVerts_card (c : Cell n N) (m : Fin (n + 1)) : (facetVerts c m).card = n := by
  rw [facetVerts, Finset.card_image_of_injective _ c.vertex_injective]
  simp [Finset.card_erase_of_mem (Finset.mem_univ m)]

/-- **Swap invariance of vertex offsets.** Swapping permutation entries `a, b` leaves the `k`-th
offset unchanged whenever `a` and `b` are *both* before `k` or *both* not before `k` in the prefix
order (the only changed vertex is the one whose prefix separates `a` from `b`). -/
theorem voff_mul_swap_eq (σ : Equiv.Perm (Fin n)) (a b : Fin n) (k : Fin (n + 1))
    (h : ((a : ℕ) < (k : ℕ)) ↔ ((b : ℕ) < (k : ℕ))) :
    voff (σ * Equiv.swap a b) k = voff σ k := by
  funext i
  simp only [voff, Equiv.Perm.mul_apply]
  by_cases ha : (a : ℕ) < (k : ℕ)
  · -- both a, b are in the prefix: reindex the sum by the swap
    have hb : (b : ℕ) < (k : ℕ) := h.mp ha
    refine Equiv.Perm.sum_comp (Equiv.swap a b)
      (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ)))
      (fun l => root (σ l) i) ?_
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    rcases (Equiv.swap_apply_ne_self_iff.mp hx).2 with rfl | rfl
    · simpa using ha
    · simpa using hb
  · -- both a, b are outside the prefix: the swap fixes every prefix element
    have hb : ¬ (b : ℕ) < (k : ℕ) := fun hb => ha (h.mpr hb)
    refine Finset.sum_congr rfl (fun l hl => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [Equiv.swap_apply_of_ne_of_ne]
    · rintro rfl; exact ha hl
    · rintro rfl; exact hb hl

/-! ### The adjacent-transposition flip -/

/-- The **flip permutation** for the facet dropping vertex `m` (`0 < m < n`): swap the two adjacent
permutation entries at positions `m-1` and `m`. This moves only the dropped vertex. -/
def flipPerm (σ : Equiv.Perm (Fin n)) (m : Fin (n + 1)) (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n) :
    Equiv.Perm (Fin n) :=
  σ * Equiv.swap ⟨(m : ℕ) - 1, by omega⟩ ⟨(m : ℕ), hmn⟩

/-- **Flip offset invariance.** Every vertex offset except the dropped one (`k ≠ m`) is unchanged by
the flip. -/
theorem voff_flipPerm_eq (σ : Equiv.Perm (Fin n)) (m : Fin (n + 1)) (hm0 : 0 < (m : ℕ))
    (hmn : (m : ℕ) < n) (k : Fin (n + 1)) (hk : k ≠ m) :
    voff (flipPerm σ m hm0 hmn) k = voff σ k := by
  apply voff_mul_swap_eq
  have hkv : (k : ℕ) ≠ (m : ℕ) := fun h => hk (Fin.ext h)
  simp only
  omega

/-- The **flipped cell** sharing the facet that drops vertex `m`, given that the moved vertex stays
in the nonnegative orthant (the interior condition). Same base, permutation flipped at `m`. -/
def flipCell (c : Cell n N) (m : Fin (n + 1)) (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (hv : ∀ i, 0 ≤ (c.base i : ℤ) + voff (flipPerm c.perm m hm0 hmn) m i) : Cell n N where
  base := c.base
  perm := flipPerm c.perm m hm0 hmn
  sum_base := c.sum_base
  valid := by
    intro k i
    by_cases hk : k = m
    · subst hk; exact hv i
    · rw [voff_flipPerm_eq c.perm m hm0 hmn k hk]; exact c.valid k i

/-- A non-dropped vertex of the flipped cell agrees with the original. -/
theorem flipCell_vertex_eq (c : Cell n N) (m : Fin (n + 1)) (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (hv : ∀ i, 0 ≤ (c.base i : ℤ) + voff (flipPerm c.perm m hm0 hmn) m i)
    (k : Fin (n + 1)) (hk : k ≠ m) :
    (flipCell c m hm0 hmn hv).vertex k = c.vertex k := by
  apply Pt.ext
  funext i
  have hvoff : voff (flipPerm c.perm m hm0 hmn) k i = voff c.perm k i :=
    congrFun (voff_flipPerm_eq c.perm m hm0 hmn k hk) i
  simp only [Cell.vertex, flipCell, hvoff]

/-- **The flip shares the facet** dropping vertex `m`. -/
theorem flipCell_facet (c : Cell n N) (m : Fin (n + 1)) (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (hv : ∀ i, 0 ≤ (c.base i : ℤ) + voff (flipPerm c.perm m hm0 hmn) m i) :
    facetVerts (flipCell c m hm0 hmn hv) m = facetVerts c m := by
  unfold facetVerts
  apply Finset.image_congr
  intro k hk
  rw [Finset.mem_coe, Finset.mem_erase] at hk
  exact flipCell_vertex_eq c m hm0 hmn hv k hk.1

/-- **The flip is a distinct cell.** -/
theorem flipCell_ne (c : Cell n N) (m : Fin (n + 1)) (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (hv : ∀ i, 0 ≤ (c.base i : ℤ) + voff (flipPerm c.perm m hm0 hmn) m i) :
    flipCell c m hm0 hmn hv ≠ c := by
  intro h
  have hp : c.perm * Equiv.swap (⟨(m : ℕ) - 1, by omega⟩ : Fin n) ⟨(m : ℕ), hmn⟩ = c.perm :=
    congrArg Cell.perm h
  have hs1 : Equiv.swap (⟨(m : ℕ) - 1, by omega⟩ : Fin n) ⟨(m : ℕ), hmn⟩ = 1 :=
    mul_left_cancel (by rw [mul_one]; exact hp)
  have key : (⟨(m : ℕ), hmn⟩ : Fin n) = ⟨(m : ℕ) - 1, by omega⟩ :=
    calc (⟨(m : ℕ), hmn⟩ : Fin n)
        = Equiv.swap (⟨(m : ℕ) - 1, by omega⟩ : Fin n) ⟨(m : ℕ), hmn⟩ ⟨(m : ℕ) - 1, by omega⟩ :=
          (Equiv.swap_apply_left _ _).symm
      _ = (1 : Equiv.Perm (Fin n)) ⟨(m : ℕ) - 1, by omega⟩ := by rw [hs1]
      _ = ⟨(m : ℕ) - 1, by omega⟩ := rfl
  have : (m : ℕ) = (m : ℕ) - 1 := congrArg Fin.val key
  omega

end CRNT.Analysis.SpernerN

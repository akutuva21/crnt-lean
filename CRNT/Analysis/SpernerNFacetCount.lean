import CRNT.Analysis.SpernerNIncidence
import CRNT.Analysis.SpernerNFintype

/-!
# Interior facets are shared by exactly two Kuhn cells

The counting half of the n-dimensional Sperner lemma: an *interior* codimension-one facet of the Kuhn
triangulation borders exactly two maximal cells. A facet dropping vertex `m` (with `0 < m < n`, so the
adjacent-transposition flip is defined) is **interior** precisely when the flipped cell stays inside
the nonnegative orthant — the `FlipValid` predicate, the validity obligation `flipCell` already
requires. Under that hypothesis the set of cells sharing the facet is exactly `{c, flipCell c m …}`:
facet rigidity (`facet_eq_imp`) forces every sharer to be `c` or its flip, while `flipCell_facet` and
`flipCell_ne` exhibit the flip as a genuine distinct second cell. Hence the share count is `2`.

Depends on: `CRNT.Analysis.SpernerNIncidence`,
`CRNT.Analysis.SpernerNFintype`.
-/

namespace CRNT.Analysis.SpernerN

open scoped BigOperators

variable {n N : ℕ}

/-- **Flip validity (the interior-facet condition).** The facet of `c` dropping vertex `m`
(`0 < m < n`) is interior when the moved vertex of the adjacent-transposition flip stays in the
nonnegative orthant — exactly the validity obligation of `flipCell`. Holding this, the facet borders a
second cell. -/
def FlipValid (c : Cell n N) (m : Fin (n + 1)) (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n) : Prop :=
  ∀ i, 0 ≤ (c.base i : ℤ) + voff (flipPerm c.perm m hm0 hmn) m i

/-- The cells sharing a given facet of `c`: those carrying a facet (under some dropped index `m'`)
equal to the facet of `c` that drops `m`. -/
noncomputable def facetSharers (c : Cell n N) (m : Fin (n + 1)) : Finset (Cell n N) :=
  Finset.univ.filter (fun c' : Cell n N => ∃ m' : Fin (n + 1), facetVerts c' m' = facetVerts c m)

/-- **Interior facets are shared by exactly two cells.** For an interior facet of `c` dropping vertex
`m` (`0 < m < n`, flip valid), precisely two Kuhn cells carry that facet: `c` itself and its
adjacent-transposition flip. -/
theorem facet_shared_by_two (c : Cell n N) (m : Fin (n + 1)) (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (hv : FlipValid c m hm0 hmn) :
    (facetSharers c m).card = 2 := by
  classical
  have hne : c ≠ flipCell c m hm0 hmn hv := fun h => flipCell_ne c m hm0 hmn hv h.symm
  rw [Finset.card_eq_two]
  refine ⟨c, flipCell c m hm0 hmn hv, hne, ?_⟩
  ext c'
  simp only [facetSharers, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨m', heq'⟩
    obtain ⟨hm'm, -⟩ := facet_eq_index c c' m m' hm0 hmn heq'.symm
    subst m'
    rcases facet_eq_imp c c' m hm0 hmn heq'.symm with rfl | ⟨_, hc'⟩
    · exact Or.inl rfl
    · exact Or.inr hc'
  · rintro (rfl | rfl)
    · exact ⟨m, rfl⟩
    · exact ⟨m, flipCell_facet c m hm0 hmn hv⟩

end CRNT.Analysis.SpernerN

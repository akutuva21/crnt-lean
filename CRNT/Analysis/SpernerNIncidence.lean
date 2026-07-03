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

Depends on: `CRNT.Analysis.SpernerLatticeN`.
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

/-! ### Reconstructing a cell from its vertices -/

/-- `root` evaluated via coordinate values: `+1` at index `j`, `−1` at index `j+1`. -/
theorem root_apply (j : Fin n) (i : Fin (n + 1)) :
    root j i = (if (i : ℕ) = (j : ℕ) then 1 else 0) - (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) := by
  simp only [root, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]

/-- The simple-root directions are distinct. -/
theorem root_injective : Function.Injective (root (n := n)) := by
  intro j j' h
  have hj := congrFun h j.castSucc
  rw [root_apply, root_apply] at hj
  simp only [Fin.val_castSucc] at hj
  refine Fin.ext ?_
  split_ifs at hj <;> omega

/-- The `0`-th vertex's coordinates equal the base. -/
theorem vertex_zero (c : Cell n N) (i : Fin (n + 1)) : (c.vertex 0).1 i = c.base i := by
  have h0 : voff c.perm 0 i = 0 := by
    have he : Finset.univ.filter (fun l : Fin n => (l : ℕ) < ((0 : Fin (n + 1)) : ℕ)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro l _; simp
    simp only [voff, he, Finset.sum_empty]
  have hv := c.vertex_val 0 i
  rw [h0, add_zero] at hv
  exact_mod_cast hv

/-- **Vertex step.** Consecutive vertices differ by the `k`-th permuted simple root. -/
theorem voff_step (σ : Equiv.Perm (Fin n)) (k : Fin n) (i : Fin (n + 1)) :
    voff σ k.succ i - voff σ k.castSucc i = root (σ k) i := by
  simp only [voff, Fin.val_succ, Fin.val_castSucc]
  rw [show Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ) + 1)
        = insert k (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ))) from ?_,
      Finset.sum_insert (by simp)]
  · ring
  · ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hl
      by_cases hlk : l = k
      · exact Or.inl hlk
      · exact Or.inr (by have : (l : ℕ) ≠ (k : ℕ) := fun h => hlk (Fin.ext h); omega)
    · rintro (rfl | h) <;> omega

/-- The cell's vertex-step direction reconstructs the permutation. -/
theorem vertex_step (c : Cell n N) (k : Fin n) (i : Fin (n + 1)) :
    ((c.vertex k.succ).1 i : ℤ) - ((c.vertex k.castSucc).1 i : ℤ) = root (c.perm k) i := by
  rw [c.vertex_val k.succ i, c.vertex_val k.castSucc i,
    show (c.base i : ℤ) + voff c.perm k.succ i - ((c.base i : ℤ) + voff c.perm k.castSucc i)
      = voff c.perm k.succ i - voff c.perm k.castSucc i from by ring]
  exact voff_step c.perm k i

/-- **A Kuhn cell is determined by its vertex function.** -/
theorem Cell.ext_of_vertex_eq {c c' : Cell n N} (h : ∀ k, c.vertex k = c'.vertex k) : c = c' := by
  obtain ⟨b, p, sb, v⟩ := c
  obtain ⟨b', p', sb', v'⟩ := c'
  have hbase : b = b' := by
    funext i
    have hb : ((⟨b, p, sb, v⟩ : Cell n N).vertex 0).1 i = b i := vertex_zero _ i
    have hb' : ((⟨b', p', sb', v'⟩ : Cell n N).vertex 0).1 i = b' i := vertex_zero _ i
    rw [← hb, ← hb', h 0]
  have hperm : p = p' := by
    apply Equiv.ext
    intro k
    apply root_injective
    funext i
    have e1 := vertex_step ⟨b, p, sb, v⟩ k i
    have e2 := vertex_step ⟨b', p', sb', v'⟩ k i
    rw [h k.succ, h k.castSucc, e2] at e1
    exact e1.symm
  subst hbase; subst hperm; rfl

/-! ### Facet rigidity: a shared facet forces the index and the base sum -/

/-- The index-weighted coordinate sum of a lattice point (the cell-vertex separating invariant). -/
def wsumPt (p : Pt n N) : ℤ := ∑ i, (i.val : ℤ) * (p.1 i : ℤ)

/-- The index-weighted sum of a cell's base. -/
def Wb (c : Cell n N) : ℤ := ∑ i, (i.val : ℤ) * (c.base i : ℤ)

/-- The `k`-th vertex has weighted sum `Wb c − k`: strictly decreasing in `k`. -/
theorem wsumPt_vertex (c : Cell n N) (k : Fin (n + 1)) : wsumPt (c.vertex k) = Wb c - (k : ℕ) :=
  c.vertex_wsum k

/-- The total weighted sum over a facet, reindexed by the dropped vertex. -/
theorem facetWsum_image (c : Cell n N) (m : Fin (n + 1)) :
    ∑ v ∈ facetVerts c m, wsumPt v = ∑ k ∈ Finset.univ.erase m, (Wb c - (k : ℕ)) := by
  rw [facetVerts, Finset.sum_image (fun a _ b _ hab => c.vertex_injective hab)]
  exact Finset.sum_congr rfl fun k _ => wsumPt_vertex c k

/-- **Index rigidity.** A shared *interior-chain* facet (`0 < m < n`) forces the dropped index and the
base weighted-sum to agree. -/
theorem facet_eq_index (c c' : Cell n N) (m m' : Fin (n + 1)) (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (heq : facetVerts c m = facetVerts c' m') : m' = m ∧ Wb c = Wb c' := by
  have hs : (∑ k ∈ Finset.univ.erase m, (Wb c - (k : ℕ)))
      = ∑ k ∈ Finset.univ.erase m', (Wb c' - (k : ℕ)) := by
    rw [← facetWsum_image, ← facetWsum_image, heq]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ m), Finset.sum_erase_eq_sub (Finset.mem_univ m'),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin] at hs
  simp only [nsmul_eq_mul] at hs
  have key : (n : ℤ) * Wb c + (m : ℕ) = (n : ℤ) * Wb c' + (m' : ℕ) := by push_cast at hs ⊢; ring_nf at hs ⊢; linarith
  have hn : 0 < n := by omega
  have hub : ((m' : ℕ) : ℤ) - (m : ℕ) < (n : ℤ) := by have := m'.isLt; omega
  have hlb : -(n : ℤ) < ((m' : ℕ) : ℤ) - (m : ℕ) := by omega
  have he : (n : ℤ) * (Wb c - Wb c') = ((m' : ℕ) : ℤ) - (m : ℕ) := by ring_nf; linarith [key]
  have habs : |(n : ℤ) * (Wb c - Wb c')| < n := by rw [he, abs_lt]; exact ⟨hlb, hub⟩
  rw [abs_mul, abs_of_pos (by exact_mod_cast hn : (0 : ℤ) < n)] at habs
  have hD1 : |Wb c - Wb c'| < 1 := by
    by_contra hc; push Not at hc; nlinarith [habs, hc, (by exact_mod_cast hn : (0 : ℤ) < n)]
  have hWb : Wb c = Wb c' := by rw [abs_lt] at hD1; omega
  refine ⟨?_, hWb⟩
  apply Fin.ext
  have : ((m : ℕ) : ℤ) = ((m' : ℕ) : ℤ) := by rw [hWb] at key; linarith
  exact_mod_cast this.symm

/-- **Vertex alignment.** Two cells sharing the facet that drops `m` (with `Wb` agreeing, e.g. from
`facet_eq_index`) agree on every non-dropped vertex. -/
theorem facet_eq_vertex_align (c c' : Cell n N) (m : Fin (n + 1))
    (heq : facetVerts c m = facetVerts c' m) (hWb : Wb c = Wb c')
    (k : Fin (n + 1)) (hk : k ≠ m) : c'.vertex k = c.vertex k := by
  have hmem : c.vertex k ∈ facetVerts c' m := by
    rw [← heq, facetVerts]
    exact Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
  rw [facetVerts, Finset.mem_image] at hmem
  obtain ⟨k', _, hkk'⟩ := hmem
  have hval : Wb c' - ((k' : ℕ) : ℤ) = Wb c - ((k : ℕ) : ℤ) := by
    rw [← wsumPt_vertex, ← wsumPt_vertex, hkk']
  have hkeq : (k : ℕ) = (k' : ℕ) := by rw [hWb] at hval; omega
  exact (congrArg c'.vertex (Fin.ext hkeq)).trans hkk'

/-! ### Facet rigidity: a shared facet is the cell or its flip -/

/-- **Two permutations agreeing off a 2-element set are equal or differ by that transposition.** -/
theorem perm_eq_or_swap {α : Type*} [DecidableEq α] (σ σ' : Equiv.Perm α) (a b : α) (hab : a ≠ b)
    (h : ∀ l, l ≠ a → l ≠ b → σ' l = σ l) :
    σ' = σ ∨ σ' = σ * Equiv.swap a b := by
  have himg : ∀ y : α, (y = a ∨ y = b) → σ' y = σ a ∨ σ' y = σ b := by
    intro y hy
    have hx : σ (σ.symm (σ' y)) = σ' y := Equiv.apply_symm_apply _ _
    by_cases hxa : σ.symm (σ' y) = a
    · exact Or.inl (by rw [← hx, hxa])
    · by_cases hxb : σ.symm (σ' y) = b
      · exact Or.inr (by rw [← hx, hxb])
      · exfalso
        have heq : σ' (σ.symm (σ' y)) = σ' y := by rw [h _ hxa hxb, hx]
        have hxy : σ.symm (σ' y) = y := σ'.injective heq
        rcases hy with rfl | rfl
        · exact hxa hxy
        · exact hxb hxy
  have ha2 : σ' a = σ a ∨ σ' a = σ b := himg a (Or.inl rfl)
  have hb2 : σ' b = σ a ∨ σ' b = σ b := himg b (Or.inr rfl)
  rcases ha2 with ha | ha
  · have hb : σ' b = σ b := by
      rcases hb2 with hb | hb
      · exact absurd (σ'.injective (hb.trans ha.symm)) hab.symm
      · exact hb
    left
    apply Equiv.ext; intro l
    by_cases hla : l = a
    · rw [hla]; exact ha
    · by_cases hlb : l = b
      · rw [hlb]; exact hb
      · exact h l hla hlb
  · have hb : σ' b = σ a := by
      rcases hb2 with hb | hb
      · exact hb
      · exact absurd (σ'.injective (ha.trans hb.symm)) hab
    right
    apply Equiv.ext; intro l
    rw [Equiv.Perm.mul_apply]
    by_cases hla : l = a
    · rw [hla, Equiv.swap_apply_left]; exact ha
    · by_cases hlb : l = b
      · rw [hlb, Equiv.swap_apply_right]; exact hb
      · rw [Equiv.swap_apply_of_ne_of_ne hla hlb]; exact h l hla hlb

/-- A Kuhn cell is determined by its base and permutation. -/
theorem Cell.eq_of_base_perm {c c' : Cell n N} (hb : c.base = c'.base) (hp : c.perm = c'.perm) :
    c = c' := by
  obtain ⟨b, p, sb, v⟩ := c
  obtain ⟨b', p', sb', v'⟩ := c'
  obtain rfl : b = b' := hb
  obtain rfl : p = p' := hp
  rfl

/-- **Facet incidence rigidity.** Any cell sharing the interior-chain facet that drops `m` is either
`c` itself or its adjacent-transposition flip. -/
theorem facet_eq_imp (c c' : Cell n N) (m : Fin (n + 1)) (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (heq : facetVerts c m = facetVerts c' m) :
    c' = c ∨ ∃ hv, c' = flipCell c m hm0 hmn hv := by
  have hWb : Wb c = Wb c' := (facet_eq_index c c' m m hm0 hmn heq).2
  -- bases agree
  have hm_ne0 : (0 : Fin (n + 1)) ≠ m := by rintro rfl; simp at hm0
  have hbase : ∀ i, c'.base i = c.base i := by
    intro i
    rw [← vertex_zero c' i, ← vertex_zero c i,
      facet_eq_vertex_align c c' m heq hWb 0 hm_ne0]
  -- the swap positions
  have hm1 : (m : ℕ) - 1 < n := by omega
  set a : Fin n := ⟨(m : ℕ) - 1, hm1⟩ with ha_def
  set b : Fin n := ⟨(m : ℕ), hmn⟩ with hb_def
  have hab : a ≠ b := by rw [ha_def, hb_def]; intro h; rw [Fin.mk.injEq] at h; omega
  -- permutations agree off {a, b}
  have hpoff : ∀ l, l ≠ a → l ≠ b → c'.perm l = c.perm l := by
    intro l hla hlb
    apply root_injective; funext i
    have hcs : l.castSucc ≠ m := by
      intro hc; apply hlb
      have hv2 : (l : ℕ) = (m : ℕ) := by have := congrArg Fin.val hc; simpa using this
      apply Fin.ext; rw [hb_def]; exact hv2
    have hsc : l.succ ≠ m := by
      intro hc; apply hla
      have hv2 : (l : ℕ) + 1 = (m : ℕ) := by
        have := congrArg Fin.val hc; simpa using this
      have hl : (l : ℕ) = (m : ℕ) - 1 := by omega
      apply Fin.ext; rw [ha_def]; exact hl
    have ec := vertex_step c l i
    have ec' := vertex_step c' l i
    rw [facet_eq_vertex_align c c' m heq hWb l.succ hsc,
      facet_eq_vertex_align c c' m heq hWb l.castSucc hcs] at ec'
    linarith [ec, ec']
  have hflip_eq : c.perm * Equiv.swap a b = flipPerm c.perm m hm0 hmn := rfl
  rcases perm_eq_or_swap c.perm c'.perm a b hab hpoff with hpe | hpe
  · exact Or.inl (Cell.eq_of_base_perm (funext hbase) hpe)
  · rw [hflip_eq] at hpe
    have hv : ∀ i, 0 ≤ (c.base i : ℤ) + voff (flipPerm c.perm m hm0 hmn) m i := by
      intro i
      have hval := c'.valid m i
      rw [hbase i, hpe] at hval
      exact hval
    refine Or.inr ⟨hv, ?_⟩
    apply Cell.eq_of_base_perm
    · funext i; exact hbase i
    · rw [hpe]; rfl

end CRNT.Analysis.SpernerN

import CRNT.Analysis.SpernerNBaseShift
import CRNT.Analysis.SpernerNFacetCount
import CRNT.Analysis.SpernerNBoundaryCount
import CRNT.Analysis.SpernerNDoor

/-!
# The n-dimensional Sperner lemma: the handshaking double-count

The capstone of the Kuhn-triangulation development. A *door incidence* is a pair `(c, m)` where the
facet of cell `c` dropping vertex `m` carries exactly the low colors `{0, …, n}` (a *door facet*).
Counting door incidences two ways gives the Sperner parity:

* grouping by the **cell**, the number of door incidences is `∑_c doorCount (cellColors col c)`, whose
  parity counts the *rainbow* cells (`doorCount_odd_iff`);
* grouping by the **facet vertex-set**, each interior door facet is shared by exactly two incidences
  (`facet_eq_imp` for an interior-chain dropped index, `facet0_eq_imp`/`facetLast_eq_imp` for the
  extreme indices), while a boundary door facet belongs to a single incidence. Hence the count is even
  plus the number of boundary door facets, and the latter biject with the `isBoundaryDoorCell` cells.

Equating the two parities yields `sperner_handshake`: the rainbow cells and the boundary door cells
have the same parity. Feeding `boundary_doors_eq_rainbow` and recursing on the dimension closes the
lemma: every Sperner coloring has an odd number of rainbow cells, hence at least one.

Depends on: `CRNT.Analysis.SpernerNBaseShift`, `CRNT.Analysis.SpernerNFacetCount`,
`CRNT.Analysis.SpernerNBoundaryCount`, `CRNT.Analysis.SpernerNDoor`.
-/

namespace CRNT.Analysis.SpernerN

open scoped BigOperators
open Finset Function

variable {n N : ℕ}

/-! ### Distinct facets -/

/-- A cell's facets for distinct dropped indices are distinct: the dropped vertex `c.vertex m` lies in
`facetVerts c m'` but not in `facetVerts c m`. -/
theorem facetVerts_ne_of_ne (c : Cell n N) {m m' : Fin (n + 1)} (h : m ≠ m') :
    facetVerts c m ≠ facetVerts c m' := by
  intro hfe
  have hmem : c.vertex m ∈ facetVerts c m' :=
    Finset.mem_image_of_mem _ (mem_erase.mpr ⟨h, mem_univ m⟩)
  rw [← hfe, facetVerts, mem_image] at hmem
  obtain ⟨k, hk, hkv⟩ := hmem
  exact (mem_erase.mp hk).1 (c.vertex_injective hkv)

/-! ### The door-incidence count and its cell-parity (P1) -/

/-- The facet of `c` dropping vertex `m` is a **door**: its `n` vertices carry exactly the low
colors. -/
def IsDoorFacet (col : SpernerColoring n N) (c : Cell n N) (m : Fin (n + 1)) : Prop :=
  (facetVerts c m).image col.color = lowColors n

instance (col : SpernerColoring n N) (c : Cell n N) (m : Fin (n + 1)) :
    Decidable (IsDoorFacet col c m) := by unfold IsDoorFacet; infer_instance

/-- The set of door incidences `(c, m)` of a coloring. -/
noncomputable def doorIncidences (col : SpernerColoring n N) : Finset (Cell n N × Fin (n + 1)) :=
  univ.filter (fun p => IsDoorFacet col p.1 p.2)

/-- The image of a facet under the coloring equals the image of `cellColors` on the erased index. -/
theorem image_color_facet (col : SpernerColoring n N) (c : Cell n N) (m : Fin (n + 1)) :
    (facetVerts c m).image col.color = (univ.erase m).image (cellColors col c) := by
  rw [facetVerts, Finset.image_image]
  rfl

/-- The door facets of a fixed cell are counted by `doorCount` of its vertex colors. -/
theorem card_doorFacets_eq_doorCount (col : SpernerColoring n N) (c : Cell n N) :
    (univ.filter (fun m => IsDoorFacet col c m)).card = doorCount (cellColors col c) := by
  rw [doorCount]
  congr 1
  apply Finset.filter_congr
  intro m _
  rw [IsDoorFacet, image_color_facet]

/-- **Grouping by cell.** The number of door incidences equals the sum over cells of their door
count. -/
theorem card_doorIncidences (col : SpernerColoring n N) :
    (doorIncidences col).card = ∑ c : Cell n N, doorCount (cellColors col c) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := doorIncidences col) (t := univ)
    (fun p _ => mem_univ p.1)]
  apply Finset.sum_congr rfl
  intro c _
  rw [← card_doorFacets_eq_doorCount]
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    rw [mem_filter, doorIncidences, mem_filter] at hp
    obtain ⟨⟨_, hdoor⟩, hfst⟩ := hp
    rw [mem_filter]
    exact ⟨mem_univ _, hfst ▸ hdoor⟩
  · intro p hp q hq h
    rw [mem_filter] at hp hq
    exact Prod.ext (hp.2.trans hq.2.symm) h
  · intro m hm
    rw [mem_filter] at hm
    refine ⟨(c, m), ?_, rfl⟩
    rw [mem_filter, doorIncidences, mem_filter]
    exact ⟨⟨mem_univ _, hm.2⟩, rfl⟩

/-- **Parity of a sum of naturals.** A finite sum is congruent mod `2` to the number of odd
summands. -/
theorem sum_mod_two_eq_card_odd {α : Type*} [Fintype α] (g : α → ℕ) :
    (∑ a, g a) % 2 = (univ.filter (fun a => Odd (g a))).card % 2 := by
  rw [Finset.sum_nat_mod]
  congr 1
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro a _
  rcases Nat.even_or_odd (g a) with he | ho
  · rw [if_neg (by simpa [Nat.not_odd_iff_even] using he), Nat.even_iff.mp he]
  · rw [if_pos ho, Nat.odd_iff.mp ho]

/-- **The door-incidence count has rainbow parity (P1).** The number of door incidences is congruent
mod `2` to the number of rainbow cells. -/
theorem card_doorIncidences_mod_two (col : SpernerColoring n N) :
    (doorIncidences col).card % 2 = #{c : Cell n N | IsRainbowCell col c} % 2 := by
  rw [card_doorIncidences, sum_mod_two_eq_card_odd]
  congr 2
  apply Finset.filter_congr
  intro c _
  rw [doorCount_odd_iff]
  rfl

/-! ### Last-facet rigidity -/

/-- **Extreme index dichotomy for the last facet.** A cell sharing `facetVerts c last` either also
drops the last vertex (same weighted sum) or drops vertex `0` (weighted sum one higher). -/
theorem facetLast_eq_index (c c' : Cell (n + 1) N) (m' : Fin (n + 2))
    (heq : facetVerts c (Fin.last (n + 1)) = facetVerts c' m') :
    (m' = Fin.last (n + 1) ∧ Wb c = Wb c') ∨ (m' = 0 ∧ Wb c' = Wb c + 1) := by
  have hs : (∑ k ∈ univ.erase (Fin.last (n + 1)), (Wb c - (k : ℕ)))
      = ∑ k ∈ univ.erase m', (Wb c' - (k : ℕ)) := by
    rw [← facetWsum_image, ← facetWsum_image, heq]
  rw [Finset.sum_erase_eq_sub (mem_univ (Fin.last (n + 1))), Finset.sum_erase_eq_sub (mem_univ m'),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin] at hs
  simp only [nsmul_eq_mul, Fin.val_last] at hs
  have key : ((n : ℤ) + 1) * (Wb c' - Wb c) = ((n : ℤ) + 1) - (m' : ℕ) := by
    push_cast at hs ⊢; ring_nf at hs ⊢; linarith
  have hpos : (0 : ℤ) < (n : ℤ) + 1 := by positivity
  have hm'lt : ((m' : ℕ) : ℤ) < (n : ℤ) + 2 := by exact_mod_cast m'.isLt
  have hm'nn : (0 : ℤ) ≤ ((m' : ℕ) : ℤ) := Int.natCast_nonneg _
  have hDnn : 0 ≤ Wb c' - Wb c := by nlinarith [key, hpos, hm'lt]
  have hDle : Wb c' - Wb c ≤ 1 := by nlinarith [key, hpos, hm'nn]
  have hcases : Wb c' - Wb c = 0 ∨ Wb c' - Wb c = 1 := by omega
  rcases hcases with hD | hD
  · left
    refine ⟨?_, by linarith [hD]⟩
    have hv : ((m' : ℕ) : ℤ) = (n : ℤ) + 1 := by rw [hD] at key; linarith
    exact Fin.ext (by rw [Fin.val_last]; exact_mod_cast hv)
  · right
    refine ⟨?_, by linarith [hD]⟩
    have hv : ((m' : ℕ) : ℤ) = 0 := by rw [hD] at key; linarith
    exact Fin.ext (by rw [Fin.val_zero]; exact_mod_cast hv)

/-- **Last-facet incidence rigidity.** Any cell sharing `facetVerts c last` is either `c` itself or
the base-change predecessor `c'` whose shift is `c`. -/
theorem facetLast_eq_imp (c c' : Cell (n + 1) N) (m' : Fin (n + 2))
    (heq : facetVerts c (Fin.last (n + 1)) = facetVerts c' m') :
    c' = c ∨ (m' = 0 ∧ ∃ h : ShiftValid c', shiftCell c' h = c) := by
  rcases facetLast_eq_index c c' m' heq with ⟨hm', hWb⟩ | ⟨hm', hWb⟩
  · -- `m' = last`, same weighted sum: forces `c' = c`
    subst hm'
    left
    have halign : ∀ k : Fin (n + 2), k ≠ Fin.last (n + 1) → c'.vertex k = c.vertex k :=
      fun k hk => facet_eq_vertex_align c c' (Fin.last (n + 1)) heq hWb k hk
    have hperm : ∀ p : Fin (n + 1), p ≠ Fin.last n → c'.perm p = c.perm p := by
      intro p hp
      apply root_injective; funext i
      have hcs : (p.castSucc : Fin (n + 2)) ≠ Fin.last (n + 1) := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last]; have := p.isLt; omega
      have hsc : (p.succ : Fin (n + 2)) ≠ Fin.last (n + 1) := by
        intro hc
        apply hp
        apply Fin.ext
        have := congrArg Fin.val hc
        rw [Fin.val_succ, Fin.val_last] at this
        rw [Fin.val_last]; omega
      have e := vertex_step c p i
      have e' := vertex_step c' p i
      rw [halign p.succ hsc, halign p.castSucc hcs] at e'
      linarith [e, e']
    have hpermeq : c'.perm = c.perm := perm_eq_of_eq_off_one c.perm c'.perm (Fin.last n) hperm
    have hbaseeq : c'.base = c.base := by
      funext i
      have h1 : ((c'.vertex 0).1 i) = ((c.vertex 0).1 i) := by
        rw [halign 0 (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last]; omega)]
      rw [vertex_zero c' i, vertex_zero c i] at h1
      exact h1
    exact Cell.eq_of_base_perm hbaseeq hpermeq
  · -- `m' = 0`, weighted sum one higher: `c = shiftCell c'`
    subst hm'
    right
    refine ⟨rfl, ?_⟩
    have heq' : facetVerts c' 0 = facetVerts c (Fin.last (n + 1)) := heq.symm
    rcases facet0_eq_imp c' c (Fin.last (n + 1)) heq' with hcc | ⟨h, hc⟩
    · exfalso; rw [hcc] at hWb; omega
    · exact ⟨h, hc.symm⟩

/-! ### The boundary door incidences are the non-shiftable cells -/

/-- **The shift fails exactly on the boundary-door shape.** The base-change neighbour across
`facetVerts c 0` is undefined precisely when `c` touches the face (`base_last = 1`) with its first
Kuhn step in the `last` direction (`perm 0 = last`) — the `isBoundaryDoorCell` configuration. Then the
vertex-`0` facet lies on `x_last = 0`, the simplex boundary, so it has no second cell. -/
theorem not_shiftValid_iff (c : Cell (n + 1) N) :
    ¬ ShiftValid c ↔ (c.base (Fin.last (n + 1)) = 1 ∧ c.perm 0 = Fin.last n) := by
  have hstep : ¬ ShiftValid c ↔ (c.vertex 1).1 (Fin.last (n + 1)) = 0 := by
    rw [ShiftValid, not_forall]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hil : i = Fin.last (n + 1)
      · subst hil
        have hne : (Fin.last (n + 1) : Fin (n + 2)) ≠ 0 := by
          rw [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero]; omega
        rw [if_neg hne, if_pos rfl] at hi
        have hcast : (0 : ℤ) ≤ ((c.vertex 1).1 (Fin.last (n + 1)) : ℤ) := Int.natCast_nonneg _
        have : ((c.vertex 1).1 (Fin.last (n + 1)) : ℤ) = 0 := by omega
        exact_mod_cast this
      · exfalso; apply hi
        rw [if_neg hil]
        have hnn : (0 : ℤ) ≤ ((c.vertex 1).1 i : ℤ) := Int.natCast_nonneg _
        rcases eq_or_ne i 0 with h0 | h0
        · rw [if_pos h0]; omega
        · rw [if_neg h0]; omega
    · intro h0
      refine ⟨Fin.last (n + 1), ?_⟩
      have hne : (Fin.last (n + 1) : Fin (n + 2)) ≠ 0 := by
        rw [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero]; omega
      rw [if_neg hne, if_pos rfl, h0]
      norm_num
  rw [hstep, vertex_last_zero_iff]
  have hpiff : ((c.perm⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ) < ((1 : Fin (n + 2)) : ℕ)
      ↔ c.perm 0 = Fin.last n := by
    rw [Fin.val_one, Nat.lt_one_iff]
    constructor
    · intro h
      have hz : c.perm⁻¹ (Fin.last n) = 0 := Fin.ext (by rw [Fin.val_zero]; exact h)
      calc c.perm 0 = c.perm (c.perm⁻¹ (Fin.last n)) := by rw [hz]
        _ = Fin.last n := by simp
    · intro h
      have hz : c.perm⁻¹ (Fin.last n) = 0 := by rw [← h]; simp
      rw [hz, Fin.val_zero]
  rw [hpiff]

/-! ### Dimension recursion (conditional on the handshake) -/

/-- **The Sperner handshake (the remaining geometric crux).** For a Sperner coloring of the
`(n+1)`-simplex, the rainbow cells and the boundary door cells have the same parity. This is the
double-count `#rainbow ≡ #doorIncidences ≡ #boundaryDoors (mod 2)`; the second congruence requires the
incidence involution whose interior pairs are even, which in turn needs the geometric fact that every
door facet off the face `x_last = 0` has a neighbouring cell. It is isolated here as a hypothesis; all
of the recursion below is unconditional in it. -/
def SpernerHandshake : Prop :=
  ∀ {m : ℕ} (col : SpernerColoring (m + 1) N), 0 < N →
    (Odd #{c : Cell (m + 1) N | IsRainbowCell col c}
      ↔ Odd #{c : Cell (m + 1) N | isBoundaryDoorCell col c})

/-- **Sperner parity from the handshake.** Granting the handshake at every dimension, every Sperner
coloring has an odd number of rainbow cells — by well-founded recursion on the dimension, feeding the
boundary doors of dimension `m+1` to the rainbow cells of dimension `m` via
`boundary_doors_eq_rainbow`. -/
theorem sperner_odd_rainbow_of_handshake (H : ∀ {N : ℕ}, SpernerHandshake (N := N)) :
    ∀ {m : ℕ} (col : SpernerColoring m N), 0 < N → Odd #{c : Cell m N | IsRainbowCell col c}
  | 0, col, _ => sperner_odd_rainbow_zero col
  | (k + 1), col, hN => by
    have hbd : Odd #{c : Cell (k + 1) N | isBoundaryDoorCell col c} := by
      have hrec := sperner_odd_rainbow_of_handshake H (restrictColoring col) hN
      have hbeq : #{c : Cell (k + 1) N | isBoundaryDoorCell col c}
          = #{c : Cell k N | IsRainbowCell (restrictColoring col) c} :=
        boundary_doors_eq_rainbow col hN
      rw [hbeq]; exact hrec
    exact (H col hN).mpr hbd

/-- **The n-dimensional Sperner lemma (existence), conditional on the handshake.** -/
theorem sperner_exists_rainbow_of_handshake (H : ∀ {N : ℕ}, SpernerHandshake (N := N))
    {m : ℕ} (col : SpernerColoring m N) (hN : 0 < N) :
    ∃ c : Cell m N, IsRainbowCell col c :=
  exists_rainbow_of_odd col (sperner_odd_rainbow_of_handshake H col hN)

end CRNT.Analysis.SpernerN

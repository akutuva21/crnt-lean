import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image
import Mathlib.Combinatorics.Pigeonhole

/-!
# Local door-count parity for the n-dimensional Sperner lemma

The dimension-`n` generalization of `Sperner2D.doorCount_odd_iff`. A maximal cell of the Kuhn
triangulation has `n+1` vertices, colored by `c : Fin (n+1) → Fin (n+1)`. The `n` *door colors* are
the low colors `{0, …, n-1}` (`lowColors`); a facet (the cell with one vertex `m` dropped) is a
*door* when its `n` remaining vertices carry exactly the door colors. The local parity lemma
`doorCount_odd_iff` states that the number of door facets is odd exactly when the cell is fully
labeled (`c` is a bijection) — the engine of the handshaking/parity argument.

This module is **stable** and `sorry`-free. Depends on: Mathlib finset/fintype.
-/

namespace CRNT.Analysis.SpernerN

open Finset

variable {n : ℕ}

/-- The `n` "door colors" `{0, …, n-1}` among the `n+1` colors `Fin (n+1)`. -/
def lowColors (n : ℕ) : Finset (Fin (n + 1)) := univ.filter (fun i => i.val < n)

@[simp] theorem mem_lowColors {i : Fin (n + 1)} : i ∈ lowColors n ↔ i.val < n := by
  simp [lowColors]

theorem lowColors_eq_erase : lowColors n = univ.erase (Fin.last n) := by
  ext i
  simp only [mem_lowColors, mem_erase, mem_univ, and_true, ne_eq, Fin.ext_iff, Fin.val_last]
  have := i.isLt
  omega

theorem last_not_mem_lowColors : Fin.last n ∉ lowColors n := by
  simp [lowColors]

theorem lowColors_card : (lowColors n).card = n := by
  rw [lowColors_eq_erase, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  omega

/-- The number of facets of a colored cell carrying exactly the door colors. -/
def doorCount (c : Fin (n + 1) → Fin (n + 1)) : ℕ :=
  (univ.filter (fun m => (univ.erase m).image c = lowColors n)).card

/-- **Bijective ⇒ exactly one door.** -/
theorem doorCount_eq_one_of_bijective {c : Fin (n + 1) → Fin (n + 1)}
    (hc : Function.Bijective c) : doorCount c = 1 := by
  obtain ⟨m0, hm0⟩ := hc.surjective (Fin.last n)
  have huniv : univ.image c = univ := by
    rw [eq_univ_iff_forall]; intro y
    obtain ⟨x, hx⟩ := hc.surjective y
    exact mem_image.mpr ⟨x, mem_univ x, hx⟩
  have hfilter : (univ.filter (fun m => (univ.erase m).image c = lowColors n)) = {m0} := by
    ext m
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hm
      by_contra hne
      have hmem : Fin.last n ∈ (univ.erase m).image c :=
        mem_image.mpr ⟨m0, mem_erase.mpr ⟨fun h => hne h.symm, mem_univ _⟩, hm0⟩
      rw [hm] at hmem
      exact last_not_mem_lowColors hmem
    · intro hm; subst hm
      rw [Finset.image_erase hc.injective, huniv, hm0, ← lowColors_eq_erase]
  rw [doorCount, hfilter, card_singleton]

/-- **Not bijective ⇒ an even number of doors** (in fact `0` or `2`). -/
theorem even_doorCount_of_not_bijective {c : Fin (n + 1) → Fin (n + 1)}
    (hc : ¬ Function.Bijective c) : Even (doorCount c) := by
  by_cases hsub : lowColors n ⊆ univ.image c
  · -- every door color is hit; with ¬bijective this forces image = lowColors and doorCount = 2
    have himg : univ.image c = lowColors n := by
      refine subset_antisymm ?_ hsub
      intro y hy
      rw [mem_lowColors]
      rcases Nat.lt_or_ge y.val n with hlt | hge
      · exact hlt
      · exfalso
        apply hc
        have hsurj : Function.Surjective c := by
          intro z
          have hz : z ∈ univ.image c := by
            rcases Nat.lt_or_ge z.val n with hzlt | hzge
            · exact hsub (mem_lowColors.mpr hzlt)
            · have hzlast : z = Fin.last n := Fin.ext (by have := z.isLt; rw [Fin.val_last]; omega)
              have hylast : y = Fin.last n := Fin.ext (by have := y.isLt; rw [Fin.val_last]; omega)
              rw [hzlast, ← hylast]; exact hy
          obtain ⟨x, _, hx⟩ := mem_image.mp hz; exact ⟨x, hx⟩
        exact ⟨(Finite.injective_iff_surjective).mpr hsurj, hsurj⟩
    set fib : Fin (n + 1) → ℕ := fun j => (univ.filter (fun m => c m = j)).card with hfibdef
    have hmaps : ∀ m ∈ (univ : Finset (Fin (n + 1))), c m ∈ lowColors n :=
      fun m _ => himg ▸ mem_image.mpr ⟨m, mem_univ m, rfl⟩
    have hsum : ∑ j ∈ lowColors n, fib j = n + 1 := by
      have h := Finset.card_eq_sum_card_fiberwise hmaps
      rw [Finset.card_univ, Fintype.card_fin] at h
      exact h.symm
    have hge1 : ∀ j ∈ lowColors n, 1 ≤ fib j := by
      intro j hj
      obtain ⟨m, _, hm⟩ := mem_image.mp (himg ▸ hj)
      exact Finset.card_pos.mpr ⟨m, mem_filter.mpr ⟨mem_univ m, hm⟩⟩
    have hdoor_iff : ∀ m, ((univ.erase m).image c = lowColors n) ↔ 1 < fib (c m) := by
      intro m
      constructor
      · intro hm
        have hcm : c m ∈ (univ.erase m).image c := by
          rw [hm]; exact himg ▸ mem_image.mpr ⟨m, mem_univ m, rfl⟩
        obtain ⟨m', hm', hcm'⟩ := mem_image.mp hcm
        refine Finset.one_lt_card.mpr ⟨m, mem_filter.mpr ⟨mem_univ m, rfl⟩, m',
          mem_filter.mpr ⟨mem_univ m', hcm'⟩, fun h => (mem_erase.mp hm').1 h.symm⟩
      · intro hcard
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
        rw [mem_filter] at ha hb
        obtain ⟨m', hne, hceq⟩ : ∃ m', m' ≠ m ∧ c m' = c m := by
          rcases eq_or_ne a m with rfl | han
          · exact ⟨b, fun h => hab h.symm, hb.2⟩
          · exact ⟨a, han, ha.2⟩
        apply subset_antisymm
        · rw [← himg]; exact Finset.image_subset_image (erase_subset m univ)
        · intro k hk
          obtain ⟨x, _, hxk⟩ := mem_image.mp (himg ▸ hk)
          rcases eq_or_ne x m with rfl | hxm
          · exact mem_image.mpr ⟨m', mem_erase.mpr ⟨hne, mem_univ _⟩, by rw [hceq, hxk]⟩
          · exact mem_image.mpr ⟨x, mem_erase.mpr ⟨hxm, mem_univ _⟩, hxk⟩
    have hdc : doorCount c = (univ.filter (fun m => 1 < fib (c m))).card := by
      rw [doorCount]; congr 1; exact Finset.filter_congr (fun m _ => hdoor_iff m)
    have hfiber : (univ.filter (fun m => 1 < fib (c m))).card
        = ∑ j ∈ lowColors n, (if 1 < fib j then fib j else 0) := by
      rw [Finset.card_eq_sum_card_fiberwise (t := lowColors n)
        (fun m _ => hmaps m (mem_univ m))]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hfj : 1 < fib j
      · rw [if_pos hfj, hfibdef]
        congr 1
        ext m
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨h.symm ▸ hfj, h⟩⟩
      · rw [if_neg hfj, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro m hm hcontra
        exact hfj (hcontra ▸ (mem_filter.mp hm).2)
    rw [hdc, hfiber, ← Finset.sum_filter]
    set B : Finset (Fin (n + 1)) := (lowColors n).filter (fun j => 1 < fib j) with hB
    have hsumA : ∑ j ∈ (lowColors n).filter (fun j => ¬ 1 < fib j), fib j
        = ((lowColors n).filter (fun j => ¬ 1 < fib j)).card := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro j hj
      rw [mem_filter] at hj
      have := hge1 j hj.1; omega
    have hsplit : ∑ j ∈ (lowColors n).filter (fun j => ¬ 1 < fib j), fib j
        + ∑ j ∈ B, fib j = n + 1 := by
      rw [hB, add_comm, Finset.sum_filter_add_sum_filter_not]; exact hsum
    have hAB : ((lowColors n).filter (fun j => ¬ 1 < fib j)).card + B.card = n := by
      rw [hB, add_comm, Finset.card_filter_add_card_filter_not, lowColors_card]
    have hBge : 2 * B.card ≤ ∑ j ∈ B, fib j := by
      have : ∑ _j ∈ B, 2 ≤ ∑ j ∈ B, fib j := by
        apply Finset.sum_le_sum
        intro j hj; rw [hB, mem_filter] at hj; omega
      rwa [Finset.sum_const, smul_eq_mul, mul_comm] at this
    have hBpos : 1 ≤ B.card := by
      have hninj : ¬ Function.Injective c := fun h => hc ((Finite.injective_iff_bijective).mp h)
      rw [Function.not_injective_iff] at hninj
      obtain ⟨a, b, hcab, hab⟩ := hninj
      have hfa : 1 < fib (c a) := Finset.one_lt_card.mpr
        ⟨a, mem_filter.mpr ⟨mem_univ a, rfl⟩, b, mem_filter.mpr ⟨mem_univ b, hcab.symm⟩, hab⟩
      exact Finset.card_pos.mpr ⟨c a, by rw [hB, mem_filter]; exact ⟨hmaps a (mem_univ a), hfa⟩⟩
    have : ∑ j ∈ B, fib j = 2 := by omega
    rw [this]; exact ⟨1, rfl⟩
  · -- some door color is missed: no facet can be a door
    have h0 : doorCount c = 0 := by
      rw [doorCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro m _ hm
      exact hsub (hm ▸ Finset.image_subset_image (erase_subset m univ))
    rw [h0]; exact ⟨0, rfl⟩

/-- **Local door-count parity.** A colored cell has an odd number of door facets exactly when it is
fully labeled (its vertex coloring is a bijection). -/
theorem doorCount_odd_iff (c : Fin (n + 1) → Fin (n + 1)) :
    Odd (doorCount c) ↔ Function.Bijective c := by
  constructor
  · intro hodd
    by_contra hnbij
    obtain ⟨r, hr⟩ := even_doorCount_of_not_bijective hnbij
    obtain ⟨s, hs⟩ := hodd
    omega
  · intro hbij
    rw [doorCount_eq_one_of_bijective hbij]; exact odd_one

end CRNT.Analysis.SpernerN

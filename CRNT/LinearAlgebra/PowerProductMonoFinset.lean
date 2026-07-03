import Mathlib.Data.Fin.Tuple.Sort
import CRNT.LinearAlgebra.PowerProductMono

/-!
# The power-product monotonicity over an unordered finite index set

The strict monotonicity of `β ↦ ∏ᵢ (β + qᵢ)^{aᵢ}` (`powerProd_strictAntiOn`) is stated for an
order on the indices: shifts `q₁ ≥ ⋯ ≥ q_k`. In applications the index set is an unordered finite
set of complexes, and the partial-sum sign condition is naturally a statement about *level sets*
of the shift `q` — the sums over `{i : v < qᵢ}` — rather than about a chosen order.

This module packages that order-free form (`powerProd_strictAntiOn_finset`): for exponents `a`
over a finite set `s`, a positive lump `a₀`, total `a₀ + ∑ a = 0`, and the level-set condition
`0 ≤ a₀ + ∑_{i ∈ s, v < qᵢ} aᵢ` at every threshold `v`, the function
`β ↦ ∏_{i ∈ s} (β + qᵢ)^{aᵢ}` is strictly decreasing above `−min q`. The sort is performed inside
the proof (via `Tuple.sort`), so the caller supplies only the level-set inequalities — exactly the
excess-of-down-set quantities the deficiency-one assembly produces.

A logarithmic corollary records that the log-sum `∑_{i ∈ s} aᵢ · log(β + qᵢ)` is itself strictly
decreasing — the form in which the monotonicity enters the deficiency-one uniqueness argument,
where it is a constant plus `∑_c G_c · log(β · y*_c + b_c)`.

* `powerProd_strictAntiOn_finset` — the order-free strict monotonicity.
* `powerProd_logSum_strictAntiOn` — the log-sum form.

Depends on:
`Mathlib.Data.Fin.Tuple.Sort`, `CRNT.LinearAlgebra.PowerProductMono`.
-/

namespace CRNT

open scoped BigOperators

/-- **Order-free power-product monotonicity.** For exponents `a` on a finite set `s`, a positive
lump `a₀` with `a₀ + ∑_{i ∈ s} aᵢ = 0`, a lower bound `qmin` for the shifts, and the level-set
sign condition `0 ≤ a₀ + ∑_{i ∈ s, v < qᵢ} aᵢ` at every threshold `v`, the function
`β ↦ ∏_{i ∈ s} (β + qᵢ)^{aᵢ}` is strictly decreasing on `(−qmin, ∞)`. -/
theorem powerProd_strictAntiOn_finset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q a : ι → ℝ) (a0 qmin : ℝ)
    (ha0 : 0 < a0)
    (hsum : a0 + ∑ i ∈ s, a i = 0)
    (hqmin : ∀ i ∈ s, qmin ≤ q i)
    (hlevel : ∀ v : ℝ, 0 ≤ a0 + ∑ i ∈ s.filter (fun i => v < q i), a i) :
    StrictAntiOn (fun β => ∏ i ∈ s, (β + q i) ^ a i) (Set.Ioi (- qmin)) := by
  classical
  -- `s` is nonempty: otherwise `a0 = 0`.
  have hne : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with h | h
    · rw [h] at hsum; simp only [Finset.sum_empty, add_zero] at hsum
      exact absurd hsum ha0.ne'
    · exact h
  set m := s.card with hm
  have hm1 : 1 ≤ m := hne.card_pos
  -- Enumerate `s` and sort the enumeration by `q` descending.
  set E : Fin m ≃ {x // x ∈ s} := (s.equivFin).symm with hE
  set e0 : Fin m → ι := fun i => (E i : ι) with he0
  set σ : Equiv.Perm (Fin m) := Tuple.sort (fun i => - q (e0 i)) with hσ
  set G : Fin m ≃ {x // x ∈ s} := σ.trans E with hG
  set g : Fin m → ι := fun i => (G i : ι) with hg
  have hgmem : ∀ i, g i ∈ s := fun i => (G i).2
  have hginj : Function.Injective g := fun i j h => G.injective (Subtype.ext h)
  -- `q ∘ g` is antitone: `Tuple.sort` makes `(-q ∘ e0) ∘ σ` monotone.
  have hmono : Monotone ((fun i => - q (e0 i)) ∘ σ) := by
    rw [hσ]; exact Tuple.monotone_sort _
  have hanti : ∀ i j : Fin m, i ≤ j → q (g j) ≤ q (g i) := by
    intro i j hij
    have h := hmono hij
    simp only [Function.comp_apply] at h
    have hgi : g i = e0 (σ i) := by simp only [hg, hG, he0, Equiv.trans_apply]
    have hgj : g j = e0 (σ j) := by simp only [hg, hG, he0, Equiv.trans_apply]
    rw [hgi, hgj]; linarith [h]
  -- Reindexing sums/products over `s` through the bijection `g`.
  have hreindex_sum : ∀ f : ι → ℝ, ∑ i ∈ s, f i = ∑ i : Fin m, f (g i) := by
    intro f
    rw [← Finset.sum_coe_sort s f]
    exact (Equiv.sum_comp G (fun c => f (c : ι))).symm
  have hreindex_prod : ∀ f : ι → ℝ, ∏ i ∈ s, f i = ∏ i : Fin m, f (g i) := by
    intro f
    rw [← Finset.prod_coe_sort s f]
    exact (Equiv.prod_comp G (fun c => f (c : ι))).symm
  -- The `ℕ`-indexed data fed to `powerProd_strictAntiOn`.
  set qf : Fin (m + 1) → ℝ := Fin.cons 0 (fun i => q (g i)) with hqf
  set af : Fin (m + 1) → ℝ := Fin.cons a0 (fun i => a (g i)) with haf
  set qN : ℕ → ℝ := fun j => if h : j < m + 1 then qf ⟨j, h⟩ else 0 with hqN
  set aN : ℕ → ℝ := fun j => if h : j < m + 1 then af ⟨j, h⟩ else 0 with haN
  have haN0 : aN 0 = a0 := by simp [haN, af]
  have hqNs : ∀ i : Fin m, qN (i.val + 1) = q (g i) := by
    intro i
    have hlt : i.val + 1 < m + 1 := by omega
    simp only [hqN, dif_pos hlt]
    rw [show (⟨i.val + 1, hlt⟩ : Fin (m + 1)) = i.succ from Fin.ext rfl, hqf, Fin.cons_succ]
  have haNs : ∀ i : Fin m, aN (i.val + 1) = a (g i) := by
    intro i
    have hlt : i.val + 1 < m + 1 := by omega
    simp only [haN, dif_pos hlt]
    rw [show (⟨i.val + 1, hlt⟩ : Fin (m + 1)) = i.succ from Fin.ext rfl, haf, Fin.cons_succ]
  -- `qN i = q (g ⟨i-1, _⟩)` on `[1, m]`, with the bound supplied locally.
  have hqNi : ∀ (i : ℕ) (hi1 : 1 ≤ i) (hib : i - 1 < m), qN i = q (g ⟨i - 1, hib⟩) := by
    intro i hi1 hib
    have key := hqNs ⟨i - 1, hib⟩
    have hval : (⟨i - 1, hib⟩ : Fin m).val + 1 = i := by
      have hv0 : (⟨i - 1, hib⟩ : Fin m).val = i - 1 := rfl
      omega
    rwa [hval] at key
  -- `qN` is antitone on `[1, m]`.
  have hqAnti : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m → qN j ≤ qN i := by
    intro i j hi1 hij hjm
    rw [hqNi i hi1 (by omega), hqNi j (by omega) (by omega)]
    exact hanti ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ (by simp only [Fin.mk_le_mk]; omega)
  -- Total sum is zero.
  have hsum' : ∑ i ∈ Finset.range (m + 1), aN i = 0 := by
    have h1 : ∑ i ∈ Finset.range (m + 1), aN i = ∑ i : Fin (m + 1), af i := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => aN j) (m + 1)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [haN, dif_pos i.2]
    rw [h1, haf, Fin.sum_cons, ← hreindex_sum a]
    linarith [hsum]
  -- The partial-sum (level-set) condition at strict drops.
  have hpartial : ∀ i, 1 ≤ i → i < m → qN (i + 1) < qN i →
      0 ≤ ∑ j ∈ Finset.range (i + 1), aN j := by
    intro i hi1 him hdrop
    have hib : i - 1 < m := by omega
    set ii : Fin m := ⟨i, him⟩ with hii
    have hv : qN (i + 1) = q (g ii) := hqNs ii
    have hdropi : q (g ii) < q (g ⟨i - 1, hib⟩) := by
      have h1 : qN i = q (g ⟨i - 1, hib⟩) := hqNi i hi1 hib
      rw [← hv, ← h1]; exact hdrop
    rw [Finset.sum_range_succ', haN0]
    have hbij : ∑ j ∈ Finset.range i, aN (j + 1)
        = ∑ c ∈ s.filter (fun c => q (g ii) < q c), a c := by
      refine Finset.sum_bij (fun j hj => g ⟨j, by rw [Finset.mem_range] at hj; omega⟩)
        ?_ ?_ ?_ ?_
      · intro j hj
        rw [Finset.mem_range] at hj
        rw [Finset.mem_filter]
        refine ⟨hgmem _, ?_⟩
        have hle : (⟨j, by omega⟩ : Fin m) ≤ ⟨i - 1, hib⟩ := by
          simp only [Fin.mk_le_mk]; omega
        have hh := hanti ⟨j, by omega⟩ ⟨i - 1, hib⟩ hle
        linarith [hdropi, hh]
      · intro j1 hj1 j2 hj2 heq
        have := hginj heq
        simpa using this
      · intro c hc
        rw [Finset.mem_filter] at hc
        obtain ⟨j, hj⟩ := G.surjective ⟨c, hc.1⟩
        have hgjc : g j = c := by simp only [hg, hj]
        refine ⟨j.val, ?_, ?_⟩
        · rw [Finset.mem_range]
          by_contra hji
          rw [not_lt] at hji
          have hle : ii ≤ j := by simp only [hii, Fin.le_def]; omega
          have hh := hanti ii j hle
          rw [hgjc] at hh
          linarith [hc.2]
        · exact (congrArg g (Fin.ext rfl)).trans hgjc
      · intro j hj
        rw [Finset.mem_range] at hj
        exact haNs ⟨j, by omega⟩
    rw [hbij]
    linarith [hlevel (q (g ii)), hv]
  -- Apply the ordered lemma.
  have hkey := powerProd_strictAntiOn (q := qN) (a := aN) hm1 hqAnti
    (by rw [haN0]; exact ha0) hsum' hpartial
  -- The ordered product equals the unordered one.
  have hprodeq : ∀ β, (∏ i ∈ Finset.range m, (β + qN (i + 1)) ^ aN (i + 1))
      = ∏ i ∈ s, (β + q i) ^ a i := by
    intro β
    rw [hreindex_prod (fun c => (β + q c) ^ a c),
      ← Fin.prod_univ_eq_prod_range (fun j => (β + qN (j + 1)) ^ aN (j + 1)) m]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hqNs i, haNs i]
  -- Transport the conclusion to the unordered product on `(−qmin, ∞)`.
  have hmin_qN : qmin ≤ qN m := by
    have hmb : m - 1 < m := by omega
    rw [hqNi m hm1 hmb]; exact hqmin _ (hgmem _)
  have hsub : Set.Ioi (- qmin) ⊆ Set.Ioi (- qN m) := by
    intro x hx; simp only [Set.mem_Ioi] at *; linarith [hmin_qN]
  have hkey' := hkey.mono hsub
  intro β₁ hβ₁ β₂ hβ₂ hlt
  have h12 := hkey' hβ₁ hβ₂ hlt
  simp only at h12 ⊢
  rwa [hprodeq, hprodeq] at h12

/-- **Log-sum form of the order-free monotonicity.** Under the same hypotheses, the log-sum
`β ↦ ∑_{i ∈ s} aᵢ · log(β + qᵢ)` is strictly decreasing on `(−qmin, ∞)`. -/
theorem powerProd_logSum_strictAntiOn {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q a : ι → ℝ) (a0 qmin : ℝ)
    (ha0 : 0 < a0)
    (hsum : a0 + ∑ i ∈ s, a i = 0)
    (hqmin : ∀ i ∈ s, qmin ≤ q i)
    (hlevel : ∀ v : ℝ, 0 ≤ a0 + ∑ i ∈ s.filter (fun i => v < q i), a i) :
    StrictAntiOn (fun β => ∑ i ∈ s, a i * Real.log (β + q i)) (Set.Ioi (- qmin)) := by
  have hP := powerProd_strictAntiOn_finset s q a a0 qmin ha0 hsum hqmin hlevel
  have hbase : ∀ β ∈ Set.Ioi (- qmin), ∀ i ∈ s, 0 < β + q i := by
    intro β hβ i hi
    simp only [Set.mem_Ioi] at hβ
    have := hqmin i hi
    linarith
  have hpos : ∀ β ∈ Set.Ioi (- qmin), 0 < ∏ i ∈ s, (β + q i) ^ a i := by
    intro β hβ
    exact Finset.prod_pos fun i hi => Real.rpow_pos_of_pos (hbase β hβ i hi) _
  have hlog : ∀ β ∈ Set.Ioi (- qmin),
      Real.log (∏ i ∈ s, (β + q i) ^ a i) = ∑ i ∈ s, a i * Real.log (β + q i) := by
    intro β hβ
    rw [Real.log_prod (fun i hi => (Real.rpow_pos_of_pos (hbase β hβ i hi) _).ne')]
    exact Finset.sum_congr rfl fun i hi => Real.log_rpow (hbase β hβ i hi) _
  intro β₁ hβ₁ β₂ hβ₂ hlt
  have h12 := hP hβ₁ hβ₂ hlt
  simp only at h12 ⊢
  rw [← hlog β₁ hβ₁, ← hlog β₂ hβ₂]
  exact Real.log_lt_log (hpos β₂ hβ₂) h12

end CRNT

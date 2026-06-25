import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Basic

/-!
# The n-dimensional Sperner lattice (homogeneous barycentric, Kuhn triangulation)

The dimension-general foundation for the n-dimensional Sperner lemma. Lattice points of the
`N`-subdivision of the standard `n`-simplex are the nonnegative integer barycentric coordinate
vectors `x : Fin (n+1) → ℕ` summing to `N` (`Pt n N`); the `n+1` corners are `N • e_i`. The geometric
realization sends `x` to `(x i / N)ᵢ ∈ stdSimplex ℝ (Fin (n+1))`. A proper Sperner coloring assigns
each point a barycentric index that is positive there (`color x = i → x i > 0`), the boundary
condition forcing the corners to distinct colors.

The maximal cells of the Kuhn (Freudenthal) triangulation are indexed by a base point and a
permutation of the `n` simple-root directions `d j = e_{castSucc j} − e_{succ j}`: the `n+1` vertices
are the partial sums `w_k = v + ∑_{l<k} d (σ l)`, valid where they stay nonnegative.

This module is **stable** and `sorry`-free. Depends on: Mathlib `Analysis.Convex.StdSimplex`,
`Algebra.BigOperators.Fin`, `GroupTheory.Perm.Basic`.
-/

namespace CRNT.Analysis.SpernerN

open scoped BigOperators

variable {n N : ℕ}

/-- **Lattice points** of the `N`-subdivision of the standard `n`-simplex: nonnegative integer
barycentric coordinates (`n+1` of them) summing to `N`. -/
def Pt (n N : ℕ) : Type := {x : Fin (n + 1) → ℕ // ∑ i, x i = N}

namespace Pt

instance : DecidableEq (Pt n N) := Subtype.instDecidableEq

@[ext] theorem ext {p q : Pt n N} (h : p.1 = q.1) : p = q := Subtype.ext h

theorem sum_eq (p : Pt n N) : ∑ i, p.1 i = N := p.2

end Pt

/-- The `i`-th **corner** `N • e_i` of the subdivision. -/
def corner (n N : ℕ) (i : Fin (n + 1)) : Pt n N :=
  ⟨fun j => if j = i then N else 0, by simp⟩

@[simp] theorem corner_val (i j : Fin (n + 1)) :
    (corner n N i).1 j = if j = i then N else 0 := rfl

/-- The barycentric **realization** of a lattice point into `Fin (n+1) → ℝ`: `x ↦ (x i / N)`. -/
noncomputable def realize (p : Pt n N) : Fin (n + 1) → ℝ := fun i => (p.1 i : ℝ) / N

@[simp] theorem realize_apply (p : Pt n N) (i : Fin (n + 1)) :
    realize p i = (p.1 i : ℝ) / N := rfl

/-- **The realization lands in the standard `n`-simplex.** -/
theorem realize_mem_stdSimplex (hN : 0 < N) (p : Pt n N) :
    realize p ∈ stdSimplex ℝ (Fin (n + 1)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun i => by simp only [realize_apply]; positivity, ?_⟩
  simp only [realize_apply, div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, p.2]
  exact mul_inv_cancel₀ (ne_of_gt hN')

/-- The corner `N • e_i` realizes to the standard basis vector `e_i` (`Pi.single i 1`). -/
theorem realize_corner (hN : 0 < N) (i : Fin (n + 1)) :
    realize (corner n N i) = Pi.single i 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  funext j
  simp only [realize_apply, corner_val, Pi.single_apply]
  by_cases h : j = i
  · simp [h, div_self hN']
  · simp [h]

/-- A **proper Sperner coloring**: each lattice point gets a barycentric index that is positive
there. The corners thus receive distinct colors, the boundary hypothesis of Sperner's lemma. -/
structure SpernerColoring (n N : ℕ) where
  /-- The color (a barycentric index) of each lattice point. -/
  color : Pt n N → Fin (n + 1)
  /-- A point colored `i` has a positive `i`-th barycentric coordinate. -/
  proper : ∀ (p : Pt n N) (i : Fin (n + 1)), color p = i → 0 < p.1 i

/-! ### Kuhn (Freudenthal) cells -/

/-- The `j`-th **simple root** direction `e_{castSucc j} − e_{succ j}` (sum-zero, integer). -/
def root (j : Fin n) (i : Fin (n + 1)) : ℤ :=
  (if i = j.castSucc then 1 else 0) - (if i = j.succ then 1 else 0)

theorem root_sum (j : Fin n) : ∑ i, root j i = 0 := by
  simp [root, Finset.sum_sub_distrib]

/-- The integer weighted sum `∑ i, i • x i` (the coordinate-index weighting), which detects the
permutation step count and separates the cell vertices. -/
def wsum (x : Fin (n + 1) → ℤ) : ℤ := ∑ i, (i.val : ℤ) * x i

theorem wsum_root (j : Fin n) : wsum (root j) = -1 := by
  simp only [wsum, root, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j.castSucc, Finset.sum_eq_single j.succ]
  · simp [Fin.val_succ]
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem wsum_add (x y : Fin (n + 1) → ℤ) : wsum (x + y) = wsum x + wsum y := by
  simp only [wsum, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem wsum_sum {ι : Type*} (s : Finset ι) (g : ι → (Fin (n + 1) → ℤ)) :
    wsum (∑ a ∈ s, g a) = ∑ a ∈ s, wsum (g a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [wsum]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, wsum_add, ih]

/-- The offset of the `k`-th vertex of a Kuhn cell from its base: the sum of the first `k` permuted
simple roots. -/
def voff (σ : Equiv.Perm (Fin n)) (k : Fin (n + 1)) (i : Fin (n + 1)) : ℤ :=
  ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ)), root (σ l) i

theorem voff_sum (σ : Equiv.Perm (Fin n)) (k : Fin (n + 1)) : ∑ i, voff σ k i = 0 := by
  simp only [voff, Finset.sum_comm (s := Finset.univ) (t := Finset.univ.filter _)]
  exact Finset.sum_eq_zero fun l _ => root_sum (σ l)

theorem card_filter_lt (k : Fin (n + 1)) :
    (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ))).card = (k : ℕ) := by
  rw [← Finset.card_map ⟨Fin.val, Fin.val_injective⟩,
    show (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ))).map ⟨Fin.val, Fin.val_injective⟩
        = Finset.range (k : ℕ) from ?_, Finset.card_range]
  ext m
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, Finset.mem_range]
  constructor
  · rintro ⟨l, hl, rfl⟩; exact hl
  · intro hm
    exact ⟨⟨m, by have := k.isLt; omega⟩, by simpa using hm, rfl⟩

theorem wsum_voff (σ : Equiv.Perm (Fin n)) (k : Fin (n + 1)) :
    wsum (voff σ k) = -(k : ℕ) := by
  have hv : voff σ k = ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ)),
      root (σ l) := by
    funext i; simp [voff, Finset.sum_apply]
  rw [hv, wsum_sum]
  simp only [wsum_root]
  rw [Finset.sum_const, card_filter_lt, nsmul_eq_mul]
  ring

/-- A **maximal Kuhn cell** of the `N`-subdivision: a base lattice point and a permutation of the
`n` simple-root directions, valid where every partial-sum vertex has nonnegative coordinates. -/
structure Cell (n N : ℕ) where
  /-- The base (minimal) vertex's coordinates. -/
  base : Fin (n + 1) → ℕ
  /-- The order in which the `n` simple-root directions are added. -/
  perm : Equiv.Perm (Fin n)
  /-- The base lies on the subdivision. -/
  sum_base : ∑ i, base i = N
  /-- Every partial-sum vertex stays in the nonnegative orthant. -/
  valid : ∀ (k i : Fin (n + 1)), 0 ≤ (base i : ℤ) + voff perm k i

/-- The `k`-th **vertex** of a Kuhn cell. -/
def Cell.vertex (c : Cell n N) (k : Fin (n + 1)) : Pt n N :=
  ⟨fun i => ((c.base i : ℤ) + voff c.perm k i).toNat, by
    have key : ∀ i, (((c.base i : ℤ) + voff c.perm k i).toNat : ℤ)
        = (c.base i : ℤ) + voff c.perm k i := fun i => Int.toNat_of_nonneg (c.valid k i)
    have : ((∑ i, ((c.base i : ℤ) + voff c.perm k i).toNat : ℕ) : ℤ) = (N : ℤ) := by
      push_cast [key]
      rw [Finset.sum_add_distrib, voff_sum, add_zero, ← Nat.cast_sum, c.sum_base]
    exact_mod_cast this⟩

theorem Cell.vertex_val (c : Cell n N) (k i : Fin (n + 1)) :
    (((c.vertex k).1 i : ℤ)) = (c.base i : ℤ) + voff c.perm k i :=
  Int.toNat_of_nonneg (c.valid k i)

theorem Cell.vertex_wsum (c : Cell n N) (k : Fin (n + 1)) :
    (∑ i, (i.val : ℤ) * ((c.vertex k).1 i : ℤ))
      = (∑ i, (i.val : ℤ) * (c.base i : ℤ)) - (k : ℕ) := by
  calc (∑ i, (i.val : ℤ) * ((c.vertex k).1 i : ℤ))
      = ∑ i, (i.val : ℤ) * ((c.base i : ℤ) + voff c.perm k i) := by
        exact Finset.sum_congr rfl fun i _ => by rw [c.vertex_val k i]
    _ = wsum (fun i => (c.base i : ℤ)) + wsum (voff c.perm k) := by
        simp only [wsum, mul_add, Finset.sum_add_distrib]
    _ = (∑ i, (i.val : ℤ) * (c.base i : ℤ)) - (k : ℕ) := by rw [wsum_voff]; rfl

/-- The `n+1` vertices of a Kuhn cell are distinct: the index-weighted sum strictly decreases. -/
theorem Cell.vertex_injective (c : Cell n N) : Function.Injective c.vertex := by
  intro k k' h
  have hw := c.vertex_wsum k
  rw [h, c.vertex_wsum k'] at hw
  have : ((k : ℕ) : ℤ) = ((k' : ℕ) : ℤ) := by linarith
  exact Fin.ext (by exact_mod_cast this)

/-- The vertex set of a Kuhn cell. -/
def Cell.simplexVerts (c : Cell n N) : Finset (Pt n N) :=
  Finset.univ.image c.vertex

/-- **Every Kuhn cell has exactly `n+1` vertices.** -/
theorem Cell.simplexVerts_card (c : Cell n N) : c.simplexVerts.card = n + 1 := by
  rw [Cell.simplexVerts, Finset.card_image_of_injective _ c.vertex_injective,
    Finset.card_univ, Fintype.card_fin]

end CRNT.Analysis.SpernerN

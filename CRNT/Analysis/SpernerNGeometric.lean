import CRNT.Analysis.SpernerLatticeN
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Geometric mesh bound for the n-dimensional Kuhn triangulation

The realization `realize : Pt n N → (Fin (n+1) → ℝ)` carries the discrete `N`-subdivision into the
standard simplex with a mesh shrinking like `1/N`. Two lattice points whose barycentric coordinates
each differ by at most `1` realize within sup-distance `1/N`; and the `n+1` vertices of a single Kuhn
cell satisfy this (their coordinates differ by at most `1`, because along the prefix of permuted
simple roots a coordinate is incremented by at most one direction and decremented by at most one).
Hence as `N → ∞` the cell diameters tend to `0` — the analytic input to the n-dimensional Brouwer
fixed-point theorem.

Depends on: `CRNT.Analysis.SpernerLatticeN`, Mathlib
`Analysis.Convex.StdSimplex`.
-/

namespace CRNT.Analysis.SpernerN

open scoped BigOperators

variable {n N : ℕ}

/-- **Mesh bound from coordinate bounds.** Lattice points whose barycentric coordinates each differ
by at most `1` realize within sup-distance `1/N`. -/
theorem realize_dist_le (hN : 0 < N) (p q : Pt n N)
    (h : ∀ i, |(p.1 i : ℝ) - q.1 i| ≤ 1) :
    dist (realize p) (realize q) ≤ 1 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [dist_pi_le_iff (by positivity)]
  intro i
  rw [realize_apply, realize_apply, Real.dist_eq, div_sub_div_same, abs_div, abs_of_pos hN']
  gcongr
  exact h i

/-- A permutation contributes at most one `+1` and one `−1` to a fixed coordinate over any index
set, so the simple-root sum at coordinate `i` over `T` has absolute value `≤ 1`. -/
theorem segment_root_sum_abs_le (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n)) (i : Fin (n + 1)) :
    |∑ l ∈ T, root (σ l) i| ≤ 1 := by
  have hsplit : ∑ l ∈ T, root (σ l) i
      = ((T.filter (fun l => i = (σ l).castSucc)).card : ℤ)
        - ((T.filter (fun l => i = (σ l).succ)).card : ℤ) := by
    simp only [root, Finset.sum_sub_distrib, Finset.sum_boole]
  have hc1 : (T.filter (fun l => i = (σ l).castSucc)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact σ.injective (Fin.castSucc_injective n (ha.2.symm.trans hb.2))
  have hc2 : (T.filter (fun l => i = (σ l).succ)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact σ.injective (Fin.succ_injective n (ha.2.symm.trans hb.2))
  have h1 : ((T.filter (fun l => i = (σ l).castSucc)).card : ℤ) ≤ 1 := by exact_mod_cast hc1
  have h2 : ((T.filter (fun l => i = (σ l).succ)).card : ℤ) ≤ 1 := by exact_mod_cast hc2
  have h1' : (0 : ℤ) ≤ (T.filter (fun l => i = (σ l).castSucc)).card := Int.natCast_nonneg _
  have h2' : (0 : ℤ) ≤ (T.filter (fun l => i = (σ l).succ)).card := Int.natCast_nonneg _
  rw [hsplit, abs_le]; omega

/-- The vertex offset at a coordinate changes by at most `1` between two vertices of a cell. -/
theorem voff_diff_abs_le (σ : Equiv.Perm (Fin n)) (k k' : Fin (n + 1)) (i : Fin (n + 1)) :
    |voff σ k i - voff σ k' i| ≤ 1 := by
  wlog h : (k' : ℕ) ≤ (k : ℕ) generalizing k k'
  · rw [abs_sub_comm]; exact this k' k (not_le.mp h).le
  have hsub : Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k' : ℕ))
      ⊆ Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ)) := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    omega
  have heq : voff σ k i - voff σ k' i
      = ∑ l ∈ (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ))) \
          (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k' : ℕ))), root (σ l) i := by
    rw [voff, voff, ← Finset.sum_sdiff hsub]; ring
  rw [heq]
  exact segment_root_sum_abs_le σ _ i

/-- Two vertices of a Kuhn cell have barycentric coordinates differing by at most `1`. -/
theorem vertex_coord_diff_le (c : Cell n N) (k k' i : Fin (n + 1)) :
    |((c.vertex k).1 i : ℤ) - ((c.vertex k').1 i : ℤ)| ≤ 1 := by
  rw [c.vertex_val k i, c.vertex_val k' i,
    show (c.base i : ℤ) + voff c.perm k i - ((c.base i : ℤ) + voff c.perm k' i)
        = voff c.perm k i - voff c.perm k' i from by ring]
  exact voff_diff_abs_le c.perm k k' i

/-- The real coordinate gap between two cell vertices is at most `1`. -/
theorem vertex_realize_coord_le (c : Cell n N) (k k' i : Fin (n + 1)) :
    |((c.vertex k).1 i : ℝ) - ((c.vertex k').1 i : ℝ)| ≤ 1 := by
  have h := vertex_coord_diff_le c k k' i
  rw [abs_le] at h ⊢
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- **Cell mesh bound.** Any two vertices of a Kuhn cell realize within sup-distance `1/N`, so the
cell diameter is `≤ 1/N → 0`. -/
theorem cell_vertex_dist_le (hN : 0 < N) (c : Cell n N) (k k' : Fin (n + 1)) :
    dist (realize (c.vertex k)) (realize (c.vertex k')) ≤ 1 / N :=
  realize_dist_le hN _ _ (fun i => vertex_realize_coord_le c k k' i)

end CRNT.Analysis.SpernerN

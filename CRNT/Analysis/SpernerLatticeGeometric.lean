import CRNT.Analysis.SpernerLattice
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Geometric realization of the lattice into the standard 2-simplex

The bridge from the combinatorial `N`-subdivision to the geometric 2-simplex: a lattice point
`(i, j)` with `i + j ≤ N` maps to its barycentric coordinates `(i/N, j/N, (N-i-j)/N)` in
`stdSimplex ℝ (Fin 3)`. Two lattice points whose coordinates differ by at most `1` (in particular,
two vertices of the same triangle of the subdivision) map within sup-distance `2/N`, so as `N → ∞`
the mesh shrinks to `0`. This realization carries the discrete Sperner lemma to the analytic
Brouwer fixed-point theorem.

Depends on: `CRNT.Analysis.SpernerLattice`, Mathlib
`Analysis.Convex.StdSimplex`.
-/

namespace CRNT.Analysis.SpernerLattice

variable {N : ℕ}

/-- The barycentric realization of a lattice point `(i, j)` as the simplex coordinates
`(i/N, j/N, (N-i-j)/N)`. -/
noncomputable def realize (p : Pt N) : Fin 3 → ℝ :=
  ![(p.1.1 : ℝ) / N, (p.1.2 : ℝ) / N, ((N - p.1.1 - p.1.2 : ℕ) : ℝ) / N]

@[simp] theorem realize_zero (p : Pt N) : realize p 0 = (p.1.1 : ℝ) / N := rfl
@[simp] theorem realize_one (p : Pt N) : realize p 1 = (p.1.2 : ℝ) / N := by simp [realize]
@[simp] theorem realize_two (p : Pt N) :
    realize p 2 = ((N - p.1.1 - p.1.2 : ℕ) : ℝ) / N := by simp [realize]

/-- The third barycentric coordinate as a real subtraction. -/
theorem realize_two_eq (p : Pt N) :
    realize p 2 = ((N : ℝ) - p.1.1 - p.1.2) / N := by
  have hle : p.1.1 + p.1.2 ≤ N := mem_ptCarrier.mp p.2
  rw [realize_two, Nat.cast_sub (by omega : p.1.2 ≤ N - p.1.1), Nat.cast_sub (by omega : p.1.1 ≤ N)]

/-- **The realization lands in the standard 2-simplex.** -/
theorem realize_mem_stdSimplex (hN : 0 < N) (p : Pt N) :
    realize p ∈ stdSimplex ℝ (Fin 3) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · show (0 : ℝ) ≤ (p.1.1 : ℝ) / N
      positivity
    · show (0 : ℝ) ≤ (p.1.2 : ℝ) / N
      positivity
    · show (0 : ℝ) ≤ ((N - p.1.1 - p.1.2 : ℕ) : ℝ) / N
      positivity
  · rw [Fin.sum_univ_three, realize_zero, realize_one, realize_two_eq]
    field_simp
    ring

/-- **Mesh bound.** Lattice points whose coordinates each differ by at most `1` realize within
sup-distance `2/N`. -/
theorem realize_dist_le (hN : 0 < N) (p q : Pt N)
    (hi : |(p.1.1 : ℝ) - q.1.1| ≤ 1) (hj : |(p.1.2 : ℝ) - q.1.2| ≤ 1) :
    dist (realize p) (realize q) ≤ 2 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [dist_pi_le_iff (by positivity)]
  intro i
  fin_cases i
  · show dist ((p.1.1 : ℝ) / N) ((q.1.1 : ℝ) / N) ≤ 2 / N
    rw [Real.dist_eq, div_sub_div_same, abs_div, abs_of_pos hN']
    gcongr
    linarith
  · show dist ((p.1.2 : ℝ) / N) ((q.1.2 : ℝ) / N) ≤ 2 / N
    rw [Real.dist_eq, div_sub_div_same, abs_div, abs_of_pos hN']
    gcongr
    linarith
  · show dist (((N - p.1.1 - p.1.2 : ℕ) : ℝ) / N) (((N - q.1.1 - q.1.2 : ℕ) : ℝ) / N) ≤ 2 / N
    have hp : ((N - p.1.1 - p.1.2 : ℕ) : ℝ) = (N : ℝ) - p.1.1 - p.1.2 := by
      have := mem_ptCarrier.mp p.2
      rw [Nat.cast_sub (by omega : p.1.2 ≤ N - p.1.1), Nat.cast_sub (by omega : p.1.1 ≤ N)]
    have hq : ((N - q.1.1 - q.1.2 : ℕ) : ℝ) = (N : ℝ) - q.1.1 - q.1.2 := by
      have := mem_ptCarrier.mp q.2
      rw [Nat.cast_sub (by omega : q.1.2 ≤ N - q.1.1), Nat.cast_sub (by omega : q.1.1 ≤ N)]
    rw [hp, hq, Real.dist_eq, div_sub_div_same, abs_div, abs_of_pos hN']
    gcongr
    have e : ((N : ℝ) - p.1.1 - p.1.2) - ((N : ℝ) - q.1.1 - q.1.2)
        = ((q.1.1 : ℝ) - p.1.1) + ((q.1.2 : ℝ) - p.1.2) := by ring
    rw [e, abs_le]
    obtain ⟨hi1, hi2⟩ := abs_le.mp hi
    obtain ⟨hj1, hj2⟩ := abs_le.mp hj
    constructor <;> linarith

end CRNT.Analysis.SpernerLattice

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Sequences

/-!
# From meshing sequences to a fixed point on the 2-simplex

The analytic core of the mesh-refinement passage to Brouwer's fixed-point theorem on
`stdSimplex ℝ (Fin 3)`. Given a continuous self-map `f` and three sequences `x 0, x 1, x 2` of
simplex points whose pairwise distances tend to `0` (the shrinking rainbow triangles) along which
`f` does not increase the corresponding barycentric coordinate (`(f (x i n)) i ≤ (x i n) i`), a
convergent subsequence collapses the three sequences to a common limit `z`, where
`(f z) i ≤ z i` for every coordinate; since both `f z` and `z` are simplex points (coordinates sum
to `1`), the inequalities are equalities, so `f z = z`.

Depends on: Mathlib `Analysis.Convex.StdSimplex`,
`Topology.Sequences`.
-/

namespace CRNT.Analysis

open Filter Topology

/-- **Meshing sequences yield a fixed point.** A continuous self-map of `stdSimplex ℝ (Fin 3)` along
which three sequences `x 0, x 1, x 2` with pairwise distances `→ 0` are coordinate-non-increasing
(`(f (x i n)) i ≤ (x i n) i`) has a fixed point. -/
theorem brouwer_of_meshing_sequences
    (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (hf : Continuous f)
    (x : Fin 3 → ℕ → ↥(stdSimplex ℝ (Fin 3)))
    (hmesh : ∀ i j : Fin 3, Tendsto (fun n => dist (x i n) (x j n)) atTop (𝓝 0))
    (hdec : ∀ (n : ℕ) (i : Fin 3), (f (x i n) : Fin 3 → ℝ) i ≤ ((x i n : Fin 3 → ℝ) i)) :
    ∃ z : ↥(stdSimplex ℝ (Fin 3)), f z = z := by
  -- Extract a convergent subsequence of `x 0` from compactness of the simplex.
  obtain ⟨z₀, hz₀, φ, hφ, hconv0⟩ := (isCompact_stdSimplex ℝ (Fin 3)).tendsto_subseq
    (x := fun n => (x 0 n : Fin 3 → ℝ)) (fun n => (x 0 n).2)
  set z : ↥(stdSimplex ℝ (Fin 3)) := ⟨z₀, hz₀⟩ with hz
  have hz0' : Tendsto (fun n => x 0 (φ n)) atTop (𝓝 z) := tendsto_subtype_rng.mpr hconv0
  -- Every `x i` converges to the same limit (pairwise distances vanish).
  have hzi : ∀ i, Tendsto (fun n => x i (φ n)) atTop (𝓝 z) := by
    intro i
    rw [tendsto_iff_dist_tendsto_zero]
    have h1 : Tendsto (fun n => dist (x i (φ n)) (x 0 (φ n))) atTop (𝓝 0) :=
      (hmesh i 0).comp hφ.tendsto_atTop
    have h2 : Tendsto (fun n => dist (x 0 (φ n)) z) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.mp hz0'
    refine squeeze_zero (fun n => dist_nonneg)
      (fun n => dist_triangle (x i (φ n)) (x 0 (φ n)) z) ?_
    simpa using h1.add h2
  -- `f` is continuous, so `f (x i (φ n)) → f z`.
  have hfi : ∀ i, Tendsto (fun n => f (x i (φ n))) atTop (𝓝 (f z)) :=
    fun i => (hf.tendsto z).comp (hzi i)
  -- Pass the coordinate inequalities to the limit.
  have hcoord : ∀ i, (f z : Fin 3 → ℝ) i ≤ (z : Fin 3 → ℝ) i := by
    intro i
    have hci : Continuous (fun w : ↥(stdSimplex ℝ (Fin 3)) => (w : Fin 3 → ℝ) i) :=
      (continuous_apply i).comp continuous_subtype_val
    have hfa : Tendsto (fun n => (f (x i (φ n)) : Fin 3 → ℝ) i) atTop
        (𝓝 ((f z : Fin 3 → ℝ) i)) := (hci.tendsto (f z)).comp (hfi i)
    have hga : Tendsto (fun n => (x i (φ n) : Fin 3 → ℝ) i) atTop
        (𝓝 ((z : Fin 3 → ℝ) i)) := (hci.tendsto z).comp (hzi i)
    exact le_of_tendsto_of_tendsto' hfa hga (fun n => hdec (φ n) i)
  -- Equal coordinate sums (both are `1`) turn the inequalities into equalities.
  refine ⟨z, Subtype.ext (funext fun i => ?_)⟩
  have hle : ∀ i ∈ Finset.univ, (f z : Fin 3 → ℝ) i ≤ (z : Fin 3 → ℝ) i := fun i _ => hcoord i
  have hsum : ∑ i, (f z : Fin 3 → ℝ) i = ∑ i, (z : Fin 3 → ℝ) i := (f z).2.2.trans z.2.2.symm
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum i (Finset.mem_univ i)

end CRNT.Analysis

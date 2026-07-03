import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Sequences

/-!
# From meshing sequences to a fixed point on the standard simplex (any dimension)

The dimension-agnostic analytic core of the mesh-refinement passage to Brouwer's fixed-point theorem.
For any finite nonempty index type `ι`, given a continuous self-map `f` of `stdSimplex ℝ ι` and a
family of sequences `x i` (one per coordinate) whose pairwise distances tend to `0` (shrinking
rainbow simplices) along which `f` does not increase the corresponding barycentric coordinate
(`(f (x i n)) i ≤ (x i n) i`), a convergent subsequence collapses all the sequences to a common
limit `z`, where `(f z) i ≤ z i` for every coordinate; since both `f z` and `z` are simplex points
(coordinates sum to `1`), the inequalities are equalities, so `f z = z`.

This is the `Fin 3` lemma `brouwer_of_meshing_sequences` generalized to an arbitrary `Fintype`, using
an arbitrary basepoint coordinate in place of the literal `0`.

Depends on: Mathlib `Analysis.Convex.StdSimplex`,
`Topology.Sequences`.
-/

namespace CRNT.Analysis

open Filter Topology

/-- **Meshing sequences yield a fixed point (any dimension).** A continuous self-map of
`stdSimplex ℝ ι` (with `ι` finite and nonempty) along which a family of sequences `x i` with vanishing
pairwise distances is coordinate-non-increasing (`(f (x i n)) i ≤ (x i n) i`) has a fixed point. -/
theorem brouwer_of_meshing_sequences_fintype {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ↥(stdSimplex ℝ ι) → ↥(stdSimplex ℝ ι)) (hf : Continuous f)
    (x : ι → ℕ → ↥(stdSimplex ℝ ι))
    (hmesh : ∀ i j : ι, Tendsto (fun n => dist (x i n) (x j n)) atTop (𝓝 0))
    (hdec : ∀ (n : ℕ) (i : ι), (f (x i n) : ι → ℝ) i ≤ ((x i n : ι → ℝ) i)) :
    ∃ z : ↥(stdSimplex ℝ ι), f z = z := by
  classical
  -- A basepoint coordinate.
  set i₀ : ι := Classical.arbitrary ι with hi₀
  -- Extract a convergent subsequence of `x i₀` from compactness of the simplex.
  obtain ⟨z₀, hz₀, φ, hφ, hconv0⟩ := (isCompact_stdSimplex ℝ ι).tendsto_subseq
    (x := fun n => (x i₀ n : ι → ℝ)) (fun n => (x i₀ n).2)
  set z : ↥(stdSimplex ℝ ι) := ⟨z₀, hz₀⟩ with hz
  have hz0' : Tendsto (fun n => x i₀ (φ n)) atTop (𝓝 z) := tendsto_subtype_rng.mpr hconv0
  -- Every `x i` converges to the same limit (pairwise distances vanish).
  have hzi : ∀ i, Tendsto (fun n => x i (φ n)) atTop (𝓝 z) := by
    intro i
    rw [tendsto_iff_dist_tendsto_zero]
    have h1 : Tendsto (fun n => dist (x i (φ n)) (x i₀ (φ n))) atTop (𝓝 0) :=
      (hmesh i i₀).comp hφ.tendsto_atTop
    have h2 : Tendsto (fun n => dist (x i₀ (φ n)) z) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.mp hz0'
    refine squeeze_zero (fun n => dist_nonneg)
      (fun n => dist_triangle (x i (φ n)) (x i₀ (φ n)) z) ?_
    simpa using h1.add h2
  -- `f` is continuous, so `f (x i (φ n)) → f z`.
  have hfi : ∀ i, Tendsto (fun n => f (x i (φ n))) atTop (𝓝 (f z)) :=
    fun i => (hf.tendsto z).comp (hzi i)
  -- Pass the coordinate inequalities to the limit.
  have hcoord : ∀ i, (f z : ι → ℝ) i ≤ (z : ι → ℝ) i := by
    intro i
    have hci : Continuous (fun w : ↥(stdSimplex ℝ ι) => (w : ι → ℝ) i) :=
      (continuous_apply i).comp continuous_subtype_val
    have hfa : Tendsto (fun n => (f (x i (φ n)) : ι → ℝ) i) atTop
        (𝓝 ((f z : ι → ℝ) i)) := (hci.tendsto (f z)).comp (hfi i)
    have hga : Tendsto (fun n => (x i (φ n) : ι → ℝ) i) atTop
        (𝓝 ((z : ι → ℝ) i)) := (hci.tendsto z).comp (hzi i)
    exact le_of_tendsto_of_tendsto' hfa hga (fun n => hdec (φ n) i)
  -- Equal coordinate sums (both are `1`) turn the inequalities into equalities.
  refine ⟨z, Subtype.ext (funext fun i => ?_)⟩
  have hle : ∀ i ∈ Finset.univ, (f z : ι → ℝ) i ≤ (z : ι → ℝ) i := fun i _ => hcoord i
  have hsum : ∑ i, (f z : ι → ℝ) i = ∑ i, (z : ι → ℝ) i := (f z).2.2.trans z.2.2.symm
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum i (Finset.mem_univ i)

end CRNT.Analysis

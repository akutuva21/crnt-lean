import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.FixedPoints

/-!
# Degree-free fixed-point existence on a real interval

General Brouwer fixed-point theory rests on infrastructure absent from this Mathlib tree
(Sperner's lemma, no-retraction of the disk, topological degree), so the fully general
`n`-dimensional continuous fixed point is out of reach here. Two degree-free existence
tools are available and proved below.

The first is the one-dimensional Brouwer fixed point: a continuous self-map of a nonempty
closed interval `[a, b] ⊆ ℝ` has a fixed point. It is the intermediate-value statement for
`g x = f x - x`, which is nonnegative at the left endpoint and nonpositive at the right.

The second is the order-theoretic Knaster–Tarski fixed point: a monotone self-map of the
complete lattice `Set.Icc a b` has a fixed point, with no continuity hypothesis. It is the
least fixed point `OrderHom.lfp` of the bundled `OrderHom`, valid in every dimension where
the state space is an order interval.

These supply the degree-free substitute for general Brouwer that a one-dimensional
reduced-coordinate or monotone reaction-network existence argument can consume directly.

Depends on:
`Mathlib.Topology.Order.IntermediateValue`, `Mathlib.Analysis.Normed.Order.Lattice`,
`Mathlib.Order.CompleteLatticeIntervals`, `Mathlib.Order.FixedPoints`.
-/

namespace CRNT.Analysis

open Set

/-- **One-dimensional Brouwer fixed point.** A continuous self-map `f` of a nonempty closed
real interval `[a, b]` has a fixed point in `[a, b]`. The proof is the intermediate value
theorem applied to `g x = f x - x`: at the left endpoint `g a = f a - a ≥ 0` because
`f a ∈ [a, b]`, and at the right endpoint `g b = f b - b ≤ 0` because `f b ∈ [a, b]`, so `g`
vanishes somewhere in between. -/
theorem fixedPoint_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hmaps : Set.MapsTo f (Set.Icc a b) (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b, f x = x := by
  set g : ℝ → ℝ := fun x => f x - x with hg
  have hgcont : ContinuousOn g (Set.Icc a b) := hf.sub continuousOn_id
  have hfa : f a ∈ Set.Icc a b := hmaps (left_mem_Icc.2 hab)
  have hfb : f b ∈ Set.Icc a b := hmaps (right_mem_Icc.2 hab)
  have hga : 0 ≤ g a := by simp only [hg]; linarith [hfa.1]
  have hgb : g b ≤ 0 := by simp only [hg]; linarith [hfb.2]
  have hmem : (0 : ℝ) ∈ g '' Set.Icc a b := intermediate_value_Icc' hab hgcont ⟨hgb, hga⟩
  obtain ⟨x, hx, hgx⟩ := hmem
  refine ⟨x, hx, ?_⟩
  have : f x - x = 0 := hgx
  linarith

/-- The fixed-point set of a continuous self-map of a nonempty closed interval is nonempty.
A `Set.Nonempty` packaging of `fixedPoint_Icc` convenient for `obtain`. -/
theorem fixedPoints_nonempty_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hmaps : Set.MapsTo f (Set.Icc a b) (Set.Icc a b)) :
    {x ∈ Set.Icc a b | f x = x}.Nonempty := by
  obtain ⟨x, hx, hfx⟩ := fixedPoint_Icc hab hf hmaps
  exact ⟨x, hx, hfx⟩

/-- **Knaster–Tarski fixed point on an interval.** A monotone self-map of the complete
lattice `Set.Icc a b` has a fixed point. The fixed point is the least fixed point
`OrderHom.lfp` of the bundled order homomorphism, and `OrderHom.map_lfp` witnesses the
fixed-point equation. No continuity is required, and the statement holds at every dimension
where the state space is realized as an order interval. -/
theorem fixedPoint_monotone_Icc {a b : ℝ} (hab : a ≤ b) (f : Set.Icc a b →o Set.Icc a b) :
    ∃ x, f x = x := by
  haveI : Fact (a ≤ b) := ⟨hab⟩
  exact ⟨f.lfp, f.map_lfp⟩

/-- The fixed-point set of a monotone self-map of `Set.Icc a b` is nonempty. A
`Set.Nonempty` packaging of `fixedPoint_monotone_Icc`. -/
theorem fixedPoints_monotone_nonempty_Icc {a b : ℝ} (hab : a ≤ b)
    (f : Set.Icc a b →o Set.Icc a b) : {x | f x = x}.Nonempty := by
  obtain ⟨x, hx⟩ := fixedPoint_monotone_Icc hab f
  exact ⟨x, hx⟩

end CRNT.Analysis

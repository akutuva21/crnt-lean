import CRNT.Dynamics.GlobalStability

/-!
# Quantitative dissipation bounds

The dissipation functional
`D(x) = ∑ s, (log (x s) - log (xstar s)) * massActionVectorField κ x s`
is the time-derivative of the relative entropy `relEntropy xstar ·` along the mass-action
flow. Relative to a positive complex-balanced reference `xstar`, it is nonpositive
(`dissipation_nonpos`) and vanishes exactly at the complex-balanced concentrations
(`complexBalanced_of_dissipation_eq_zero` / `dissipation_eq_zero_of_complexBalanced`).

This module sharpens those facts into quantitative descents of the Lyapunov function on the
interior of the positive orthant.

* `dissipation_neg_of_not_complexBalanced`: at a positive `x` that is **not** complex-balanced,
  the dissipation is strictly negative, `D(x) < 0`. The relative entropy strictly decreases at
  every interior non-equilibrium.
* `continuous_massActionVectorField` / `dissipation_continuousOn`: the mass-action field is
  globally continuous, so the dissipation is continuous on the open positive orthant.
* `dissipation_coercive_on_compact`: on a compact set `K` of strictly positive concentrations
  containing no complex-balanced point, `-D` attains a uniform positive lower bound
  `∃ δ > 0, ∀ y ∈ K, δ ≤ -D(y)`. This packages the strict Lyapunov decrease quantitatively on
  interior compacta: away from equilibrium the relative entropy decreases at a rate bounded below.

The **uniform** lower bound valid up to the orthant boundary (the Gopalkrishnan–Miller–Shiu
estimate underlying strongly-endotactic global stability) is the named residue: it requires the
endotactic / Newton-polytope geometry, which is not available in this layer.

This module is **stable** and `sorry`-free. Depends on: CRNT.Dynamics.GlobalStability.
-/

open scoped BigOperators Topology

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Strict dissipation at non-equilibria.** Relative to a positive complex-balanced reference
`xstar`, the dissipation at a positive concentration `x` that is **not** complex-balanced is
strictly negative. Together with `dissipation_nonpos` this says the relative entropy decreases
strictly at every positive non-equilibrium, vanishing only at the complex-balanced set. -/
theorem dissipation_neg_of_not_complexBalanced (N : Network S) (κ : RateConstants N)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hnotcb : ¬ N.IsComplexBalanced κ x) :
    (∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) < 0 := by
  rcases lt_or_eq_of_le (dissipation_nonpos N κ hx hxs hcb) with hlt | heq
  · exact hlt
  · exact absurd (complexBalanced_of_dissipation_eq_zero N κ hx hxs hcb heq) hnotcb

omit [DecidableEq S] in
/-- The mass-action monomial of a complex is continuous in the concentration: it is a finite
product of natural-power coordinate maps. -/
theorem continuous_massActionMonomial (y : Complex S) :
    Continuous (fun x : Concentration S => y.massActionMonomial x) := by
  unfold Complex.massActionMonomial
  exact continuous_finsetProd _ fun s _ => (continuous_apply s).pow _

/-- The mass-action rate of a single reaction is continuous in the concentration. -/
theorem continuous_massActionRate (N : Network S) (κ : RateConstants N) (r : N.R) :
    Continuous (fun x : Concentration S => N.massActionRate κ r x) := by
  unfold Network.massActionRate
  exact continuous_const.mul (continuous_massActionMonomial _)

/-- **The mass-action vector field is continuous.** Each coordinate is a finite sum of rate maps
times constants, and the rate maps are continuous. -/
theorem continuous_massActionVectorField (N : Network S) (κ : RateConstants N) :
    Continuous (N.massActionVectorField κ) := by
  rw [continuous_pi_iff]
  intro s
  simp only [massActionVectorField_apply]
  exact continuous_finsetSum _ fun r _ => (continuous_massActionRate N κ r).mul continuous_const

/-- **The dissipation is continuous on the open positive orthant.** As a function of `x`, the
dissipation `D(x)` is continuous wherever every coordinate is positive (so the logarithms are
continuous there). -/
theorem dissipation_continuousOn (N : Network S) (κ : RateConstants N)
    (xstar : Concentration S) :
    ContinuousOn (fun x : Concentration S =>
        ∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s)
      {x | Concentration.Positive x} := by
  apply continuousOn_finsetSum
  intro s _
  apply ContinuousOn.mul
  · refine (Real.continuousOn_log.comp (continuous_apply s).continuousOn ?_).sub continuousOn_const
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (hx s)
  · exact ((continuous_apply s).comp (continuous_massActionVectorField N κ)).continuousOn

/-- **Coercive interior lower bound.** Let `K` be a compact set of strictly positive
concentrations none of which is complex-balanced. Relative to a positive complex-balanced
reference `xstar`, the negated dissipation `-D` attains a uniform positive lower bound on `K`:
there is `δ > 0` with `δ ≤ -D(y)` for every `y ∈ K`. The relative entropy thus decreases at a
rate bounded below on any interior compactum avoiding the equilibrium set. -/
theorem dissipation_coercive_on_compact (N : Network S) (κ : RateConstants N)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {K : Set (Concentration S)} (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (hKpos : ∀ y ∈ K, Concentration.Positive y)
    (hKnotcb : ∀ y ∈ K, ¬ N.IsComplexBalanced κ y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ K,
      δ ≤ -(∑ s, (Real.log (y s) - Real.log (xstar s)) * N.massActionVectorField κ y s) := by
  set g : Concentration S → ℝ := fun y =>
    -(∑ s, (Real.log (y s) - Real.log (xstar s)) * N.massActionVectorField κ y s) with hg
  have hgcont : ContinuousOn g K := by
    refine (dissipation_continuousOn N κ xstar).neg.mono ?_
    intro y hy; exact hKpos y hy
  obtain ⟨y₀, hy₀K, hy₀min⟩ := hKcpt.exists_isMinOn hKne hgcont
  refine ⟨g y₀, ?_, ?_⟩
  · -- the minimum value is strictly positive: it is `-D(y₀)` at a non-equilibrium
    have : (∑ s, (Real.log (y₀ s) - Real.log (xstar s)) * N.massActionVectorField κ y₀ s) < 0 :=
      dissipation_neg_of_not_complexBalanced N κ (hKpos y₀ hy₀K) hxs hcb (hKnotcb y₀ hy₀K)
    simpa [hg] using neg_pos.mpr this
  · intro y hyK
    exact hy₀min hyK

end Network

end CRNT

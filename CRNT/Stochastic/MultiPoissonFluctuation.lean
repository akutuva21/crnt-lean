import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic

/-!
# Aggregate multi-reaction Poisson fluctuation bound

In Kurtz's scaling a reaction network of volume `V` carries one Poisson clock per reaction
`r : R`, with intensity `Λ_r = V · a_r` for a per-volume rate `a_r`. The total scaled
fluctuation is the stoichiometrically weighted sum `∑_r weight_r · (N_r / V)` of the
volume-scaled counts. `CRNT.Stochastic.PoissonFluctuation` establishes the `O(1/V)` second
moment of a single scaled clock; this module aggregates a finite family of independent clocks.

The construction-of-joint-law step is isolated as data: a family of `L²` random variables
`X : R → Ω → ℝ` on one probability space, pairwise independent, whose per-term variances carry
the scaled order `Var[X r] = c r / V`. Mathlib's `ProbabilityTheory.IndepFun.variance_sum`
turns pairwise independence into additivity of variance, so the aggregate inherits the order:

* `variance_aggregate` : `Var[∑_r X r] = (∑_r c r) / V`, the aggregate `O(1/V)` bound.
* `meas_aggregate_ge_le` : Chebyshev tail `μ{ |∑_r X r − mean| ≥ δ } ≤ (∑_r c r) / (V · δ²)`.
* `tendsto_meas_aggregate` : that tail tends to `0` as `V → ∞` — convergence in probability of
  the aggregate scaled fluctuation to its mean, with constant `C = ∑_r c r = ∑_r weight_r² · a_r`.

For the stoichiometric reading, `c r = weight_r ^ 2 · a_r` with `weight_r` the reaction's
coefficient and `a_r` its per-volume rate; then `C = ∑_r weight_r² · a_r`. Assembling the
independent Poisson family with the joint law that realizes `Var[X r] = weight_r² · a_r / V`
(via the random time change of the clocks) is the next development.
-/

namespace CRNT.Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {R : Type*} [Fintype R] {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## Aggregate variance -/

omit [IsProbabilityMeasure μ] in
/-- **The aggregate `O(1/V)` variance bound.** For a finite family `X : R → Ω → ℝ` of pairwise
independent `L²` terms whose per-term variances carry the scaled order `Var[X r] = c r / V`, the
variance of the total `∑_r X r` is `(∑_r c r) / V`. Pairwise independence collapses the
covariance cross terms, so the aggregate inherits the single-term `O(1/V)` order with constant
`C = ∑_r c r`. -/
theorem variance_aggregate {X : R → Ω → ℝ} {c : R → ℝ} {V : ℝ}
    (hmem : ∀ r, MemLp (X r) 2 μ) (hindep : Pairwise fun r s => X r ⟂ᵢ[μ] X s)
    (hvar : ∀ r, variance (X r) μ = c r / V) :
    variance (∑ r, X r) μ = (∑ r, c r) / V := by
  rw [IndepFun.variance_sum (fun r _ => hmem r)
    (fun r _ s _ hrs => hindep hrs)]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun r _ => hvar r)

omit [IsProbabilityMeasure μ] in
/-- The aggregate variance is bounded by `C / V` with `C = ∑_r c r`. -/
theorem variance_aggregate_le {X : R → Ω → ℝ} {c : R → ℝ} {V : ℝ}
    (hmem : ∀ r, MemLp (X r) 2 μ) (hindep : Pairwise fun r s => X r ⟂ᵢ[μ] X s)
    (hvar : ∀ r, variance (X r) μ = c r / V) :
    variance (∑ r, X r) μ ≤ (∑ r, c r) / V :=
  le_of_eq (variance_aggregate hmem hindep hvar)

omit [IsProbabilityMeasure μ] in
/-- The aggregate total `∑_r X r` is square-integrable. -/
theorem memLp_aggregate {X : R → Ω → ℝ} (hmem : ∀ r, MemLp (X r) 2 μ) :
    MemLp (∑ r, X r) 2 μ :=
  memLp_finsetSum' _ (fun r _ => hmem r)

/-! ## Aggregate Chebyshev tail and convergence in probability -/

/-- **Aggregate Chebyshev tail.** Under the same independent `O(1/V)` family, the total
`∑_r X r` deviates from its mean by at least `δ > 0` with probability at most
`(∑_r c r) / (V · δ²)`. This is Chebyshev's inequality applied to the aggregate variance. -/
theorem meas_aggregate_ge_le {X : R → Ω → ℝ} {c : R → ℝ} {V : ℝ}
    (hmem : ∀ r, MemLp (X r) 2 μ) (hindep : Pairwise fun r s => X r ⟂ᵢ[μ] X s)
    (hvar : ∀ r, variance (X r) μ = c r / V) {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | δ ≤ |(∑ r, X r) ω - μ[∑ r, X r]|}
      ≤ ENNReal.ofReal ((∑ r, c r) / (V * δ ^ 2)) := by
  have hcheb := meas_ge_le_variance_div_sq (memLp_aggregate hmem) hδ
  rw [variance_aggregate hmem hindep hvar] at hcheb
  refine le_trans hcheb (le_of_eq ?_)
  congr 1
  rw [div_div]

/-- **Convergence in probability of the aggregate scaled fluctuation.** Along any filter where the
volume `V → ∞`, the aggregate deviation probability tends to `0` for every threshold `δ > 0`. The
constant `C = ∑_r c r` is fixed (volume-independent), so the `O(1/V)` Chebyshev tail vanishes: the
total weighted scaled count obeys a law of large numbers, converging to its mean. -/
theorem tendsto_meas_aggregate {ι : Type*} {ℓ : Filter ι} {V : ι → ℝ}
    {X : ι → R → Ω → ℝ} {c : R → ℝ}
    (hmem : ∀ i r, MemLp (X i r) 2 μ)
    (hindep : ∀ i, Pairwise fun r s => X i r ⟂ᵢ[μ] X i s)
    (hvar : ∀ i r, variance (X i r) μ = c r / V i)
    (hV : Filter.Tendsto V ℓ Filter.atTop) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun i => μ {ω | δ ≤ |(∑ r, X i r) ω - μ[∑ r, X i r]|}) ℓ (nhds 0) := by
  have hbound : ∀ i, μ {ω | δ ≤ |(∑ r, X i r) ω - μ[∑ r, X i r]|}
      ≤ ENNReal.ofReal ((∑ r, c r) / (V i * δ ^ 2)) :=
    fun i => meas_aggregate_ge_le (hmem i) (hindep i) (hvar i) hδ
  have htop : Filter.Tendsto (fun i => ENNReal.ofReal ((∑ r, c r) / (V i * δ ^ 2))) ℓ (nhds 0) := by
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 from (ENNReal.ofReal_zero).symm]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    have hdenom : Filter.Tendsto (fun i => V i * δ ^ 2) ℓ Filter.atTop :=
      hV.atTop_mul_const (by positivity)
    have := (hdenom.inv_tendsto_atTop).const_mul (∑ r, c r)
    rw [mul_zero] at this
    refine this.congr (fun i => ?_)
    simp only [Pi.inv_apply]
    rw [div_eq_mul_inv]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
    (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall hbound)

end CRNT.Stochastic

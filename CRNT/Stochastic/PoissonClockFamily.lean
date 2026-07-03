import CRNT.Stochastic.PoissonFluctuation
import CRNT.Stochastic.MultiPoissonFluctuation
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The independent scaled-Poisson clock family

`CRNT.Stochastic.MultiPoissonFluctuation` aggregates a finite family of pairwise independent
`L²` random variables whose per-term variances carry the scaled order `c r / V`, but it carries
the joint law as data. This module constructs the concrete realization for Kurtz's scaling: one
Poisson clock per reaction, with intensity `Λ_r = V · a_r`, living on a single product probability
space, with the joint law that makes the clocks independent.

The space is the product `Ω = R → ℕ` over a finite reaction set `R`, equipped with the product
measure `μ = ⊗_r Po(V · a_r)`. The coordinate clock `N r ω = ω r` reads off reaction `r`'s count,
and the scaled weighted variable `X r ω = weight_r · (N_r(ω) / V)` is the stoichiometrically
weighted volume-scaled count.

* `clockMeasure` : the product measure `⊗_r Po(V · a_r)`, a probability measure on `R → ℕ`.
* `scaledClock` : the family `X r ω = weight_r · (ω r / V)`.
* `indepFun_scaledClock` : the clocks are pairwise independent under `clockMeasure`, from product
  independence of the coordinates composed with the per-coordinate scaling.
* `variance_scaledClock` : `Var[X r] = weight_r² · a_r / V`, the realized per-term `O(1/V)`
  variance, via the coordinate marginal `Po(V · a_r)`.

Feeding these into the aggregate bounds gives results with **no carried hypotheses** for the
concrete Poisson clock family:

* `variance_aggregate_scaledClock` : `Var[∑_r X r] = (∑_r weight_r² · a_r) / V`.
* `meas_aggregate_scaledClock_ge_le` : the aggregate Chebyshev tail.
* `tendsto_meas_aggregate_scaledClock` : convergence in probability of the total weighted scaled
  count to its mean as `V → ∞` — the realized fluctuation model driving `η_V → 0`.
-/

namespace CRNT.Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {R : Type*} [Fintype R]

/-- The per-reaction Poisson intensity at volume `V`: the scaled rate `V · a_r` as an `ℝ≥0`. -/
def clockIntensity {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0) (r : R) : ℝ≥0 :=
  ⟨V, hV.le⟩ * a r

/-- The product law of the independent Poisson clocks: `⊗_r Po(V · a_r)` on the count space
`R → ℕ`. Each coordinate carries the volume-scaled intensity of one reaction. -/
noncomputable def clockMeasure {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0) : Measure (R → ℕ) :=
  Measure.pi (fun r => poissonMeasure (clockIntensity hV a r))

instance {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0) :
    IsProbabilityMeasure (clockMeasure hV a) := by
  unfold clockMeasure; infer_instance

/-- The coordinate clock: reaction `r`'s count read off the product point. -/
def clockCount (r : R) : (R → ℕ) → ℕ := fun ω => ω r

/-- The stoichiometrically weighted volume-scaled count `X r ω = weight_r · (ω r / V)`. -/
noncomputable def scaledClock (weight : R → ℝ) (V : ℝ) (r : R) : (R → ℕ) → ℝ :=
  fun ω => weight r * ((ω r : ℝ) / V)

omit [Fintype R] in
/-- The scaled clock factors through the coordinate as `(n ↦ weight_r · (n / V)) ∘ eval_r`. -/
theorem scaledClock_eq_comp (weight : R → ℝ) (V : ℝ) (r : R) :
    scaledClock weight V r
      = (fun n : ℕ => weight r * ((n : ℝ) / V)) ∘ (fun ω : R → ℕ => ω r) := rfl

/-! ## Independence of the clock family -/

/-- **The scaled Poisson clocks are pairwise independent.** The coordinates of the product
measure are independent (`iIndepFun_pi`), and post-composing each coordinate with its scaling
`n ↦ weight_r · (n / V)` preserves independence (`IndepFun.comp`). -/
theorem indepFun_scaledClock {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0) (weight : R → ℝ) :
    Pairwise fun r s => scaledClock weight V r ⟂ᵢ[clockMeasure hV a] scaledClock weight V s := by
  intro r s hrs
  have hbase : iIndepFun (fun (r : R) (ω : R → ℕ) => ω r) (clockMeasure hV a) :=
    iIndepFun_pi (X := fun (_ : R) (n : ℕ) => n) (fun _ => aemeasurable_id)
  have hcoord : (fun ω : R → ℕ => ω r) ⟂ᵢ[clockMeasure hV a] (fun ω : R → ℕ => ω s) :=
    hbase.indepFun hrs
  simpa only [scaledClock_eq_comp] using
    hcoord.comp (φ := fun n : ℕ => weight r * ((n : ℝ) / V))
      (ψ := fun n : ℕ => weight s * ((n : ℝ) / V)) (by fun_prop) (by fun_prop)

/-! ## Per-coordinate variance -/

/-- The coordinate marginal of the product law is `Po(V · a_r)`: pushing `clockMeasure` forward
along reaction `r`'s evaluation recovers that single Poisson law. -/
theorem map_eval_clockMeasure {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0) (r : R) :
    (clockMeasure hV a).map (fun ω : R → ℕ => ω r) = poissonMeasure (clockIntensity hV a r) :=
  (measurePreserving_eval (fun r => poissonMeasure (clockIntensity hV a r)) r).map_eq

/-- **The realized per-term `O(1/V)` variance.** Reaction `r`'s scaled clock has variance
`weight_r² · a_r / V`: the coordinate marginal is `Po(V · a_r)`, on which the volume-scaled count
has variance `a_r / V`, and the weight pulls out as `weight_r²`. -/
theorem variance_scaledClock {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0) (weight : R → ℝ) (r : R) :
    variance (scaledClock weight V r) (clockMeasure hV a)
      = weight r ^ 2 * (a r : ℝ) / V := by
  have hpres : MeasurePreserving (fun ω : R → ℕ => ω r) (clockMeasure hV a)
      (poissonMeasure (clockIntensity hV a r)) := by
    have := measurePreserving_eval (fun r => poissonMeasure (clockIntensity hV a r)) r
    simpa only [clockMeasure, Function.eval] using this
  have hmeas : AEMeasurable (fun n : ℕ => weight r * ((n : ℝ) / V))
      (poissonMeasure (clockIntensity hV a r)) := by fun_prop
  show variance (fun ω : R → ℕ => (fun n : ℕ => weight r * ((n : ℝ) / V)) (ω r))
      (clockMeasure hV a) = _
  rw [hpres.variance_fun_comp hmeas, variance_const_mul]
  have hcoord : variance (fun n : ℕ => (n : ℝ) / V)
      (poissonMeasure (clockIntensity hV a r)) = (a r : ℝ) / V := by
    unfold clockIntensity
    exact variance_scaled_intensity_poissonMeasure hV (a r)
  rw [hcoord]; ring

/-! ## Self-contained aggregate bounds for the concrete clock family -/

/-- `L²` membership of each scaled clock, inherited from the marginal `Po(V · a_r)`. -/
theorem memLp_scaledClock {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0) (weight : R → ℝ) (r : R) :
    MemLp (scaledClock weight V r) 2 (clockMeasure hV a) := by
  have hpres : MeasurePreserving (fun ω : R → ℕ => ω r) (clockMeasure hV a)
      (poissonMeasure (clockIntensity hV a r)) := by
    have := measurePreserving_eval (fun r => poissonMeasure (clockIntensity hV a r)) r
    simpa only [clockMeasure, Function.eval] using this
  have hmarg : MemLp (fun n : ℕ => weight r * ((n : ℝ) / V)) 2
      (poissonMeasure (clockIntensity hV a r)) := by
    have hbase : MemLp (fun n : ℕ => (n : ℝ) / V) 2
        (poissonMeasure (clockIntensity hV a r)) := by
      have hid := (memLp_two_id_poissonMeasure (clockIntensity hV a r)).const_mul V⁻¹
      refine MemLp.ae_eq (Filter.Eventually.of_forall fun n => ?_) hid
      simp only [div_eq_inv_mul]
    exact hbase.const_mul (weight r)
  rw [scaledClock_eq_comp]
  exact hmarg.comp_measurePreserving hpres

/-- **The self-contained aggregate `O(1/V)` variance** for the concrete Poisson clock family:
`Var[∑_r weight_r · (N_r / V)] = (∑_r weight_r² · a_r) / V`, with no carried independence or
variance hypotheses — both are discharged from the product law. -/
theorem variance_aggregate_scaledClock {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0) (weight : R → ℝ) :
    variance (∑ r, scaledClock weight V r) (clockMeasure hV a)
      = (∑ r, weight r ^ 2 * (a r : ℝ)) / V :=
  variance_aggregate (fun r => memLp_scaledClock hV a weight r)
    (indepFun_scaledClock hV a weight)
    (fun r => variance_scaledClock hV a weight r)

/-- **The self-contained aggregate Chebyshev tail** for the concrete Poisson clock family. -/
theorem meas_aggregate_scaledClock_ge_le {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0) (weight : R → ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    (clockMeasure hV a)
        {ω | δ ≤ |(∑ r, scaledClock weight V r) ω
          - (clockMeasure hV a)[∑ r, scaledClock weight V r]|}
      ≤ ENNReal.ofReal ((∑ r, weight r ^ 2 * (a r : ℝ)) / (V * δ ^ 2)) :=
  meas_aggregate_ge_le (fun r => memLp_scaledClock hV a weight r)
    (indepFun_scaledClock hV a weight)
    (fun r => variance_scaledClock hV a weight r) hδ

/-- **Convergence in probability of the aggregate scaled fluctuation** for the concrete independent
Poisson clock family. Along any filter where `V → ∞`, the total weighted scaled count
`∑_r weight_r · (N_r / V)` deviates from its mean by at least `δ > 0` with probability tending to
`0`. The constant `C = ∑_r weight_r² · a_r` is volume-independent, so the `O(1/V)` Chebyshev tail
vanishes: the realized fluctuation model obeys a law of large numbers. -/
theorem tendsto_meas_aggregate_scaledClock {ι : Type*} {ℓ : Filter ι} {V : ι → ℝ}
    (hVpos : ∀ i, 0 < V i) (a : R → ℝ≥0) (weight : R → ℝ)
    (hV : Filter.Tendsto V ℓ Filter.atTop) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun i => (clockMeasure (hVpos i) a)
        {ω | δ ≤ |(∑ r, scaledClock weight (V i) r) ω
          - (clockMeasure (hVpos i) a)[∑ r, scaledClock weight (V i) r]|})
      ℓ (nhds 0) := by
  have hbound : ∀ i, (clockMeasure (hVpos i) a)
      {ω | δ ≤ |(∑ r, scaledClock weight (V i) r) ω
        - (clockMeasure (hVpos i) a)[∑ r, scaledClock weight (V i) r]|}
        ≤ ENNReal.ofReal ((∑ r, weight r ^ 2 * (a r : ℝ)) / (V i * δ ^ 2)) :=
    fun i => meas_aggregate_scaledClock_ge_le (hVpos i) a weight hδ
  have htop : Filter.Tendsto
      (fun i => ENNReal.ofReal ((∑ r, weight r ^ 2 * (a r : ℝ)) / (V i * δ ^ 2))) ℓ (nhds 0) := by
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 from (ENNReal.ofReal_zero).symm]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    have hdenom : Filter.Tendsto (fun i => V i * δ ^ 2) ℓ Filter.atTop :=
      hV.atTop_mul_const (by positivity)
    have := (hdenom.inv_tendsto_atTop).const_mul (∑ r, weight r ^ 2 * (a r : ℝ))
    rw [mul_zero] at this
    refine this.congr (fun i => ?_)
    simp only [Pi.inv_apply]
    rw [div_eq_mul_inv]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
    (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall hbound)

end CRNT.Stochastic

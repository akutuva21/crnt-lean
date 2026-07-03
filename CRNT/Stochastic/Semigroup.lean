import CRNT.Stochastic.KernelNormalized
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Uniformized transition semigroup of the chemical master equation

The stochastic mass-action dynamics of a reaction network is a continuous-time Markov chain on the
species-count lattice `ℕ^S`, governed by the chemical-master-equation generator `Q` of
`CRNT.Stochastic.CTMC`. Its transition semigroup `P_t = exp(tQ)` is built here by *uniformization*
(Jensen, "Markoff chains as an aid in the study of Markoff processes"; Norris, "Markov Chains"): on
a finite closed enabled region `T` the exit rate is bounded by a finite maximum `Λ`, so the
generator factors through a single bounded uniformized stochastic kernel `U = I + Q/Λ`, and the
semigroup is recovered as a Poisson-weighted superposition of its powers,

`P_t(n, ·) = ∑_{k ≥ 0} e^{−Λt} (Λt)^k / k! · U^{∘k}(n, ·)`.

Exit rates are unbounded on the full lattice — mass-action propensities grow with the species counts
— so uniformization is scoped to a `ClosedEnabledRegion` of `CRNT.Stochastic.KernelIrreducible`,
where `exitRate` admits the finite dominating bound `uniformizationRate`. The uniformized kernel
`uniformizedKernel` is the state-dependent convex combination
`(1 − uniformWeight n) · δ_n + uniformWeight n · jumpKernel n`, a genuine Markov kernel; its `k`-fold
composition `uniformizedPow k` is Markov by `IsMarkovKernel.comp`, and the Poisson superposition
`cmeSemigroup t` is Markov because the Poisson weights sum to one (`hasSum_one_poissonMeasure`).

The proved content is: each `cmeSemigroup t` is a Markov kernel (`instIsMarkovKernel_cmeSemigroup`);
the initial identity `cmeSemigroup_zero` (`P_0 = id`, the rate-zero Poisson mass concentrating on the
zeroth power); and `cmeSemigroup_preserves_stationarity` — the Anderson–Craciun–Kurtz product-Poisson
law, restricted to the region and normalized, is invariant under every `P_t`. The stationary law
preserved by the continuous-time semigroup is the product-Poisson density itself
(`cmeStationaryMeasure`), *not* the holding-rate-reweighted jump-chain law of
`CRNT.Stochastic.KernelNormalized`: the two differ by the `exitRate` factor, and the uniformized
kernel `U` carries the density `∝ productPoissonPMF` to itself through the embedded jump-chain global
balance `jumpKernel_invariant_restrictedStationaryMeasure` (Anderson, Craciun, Kurtz, "Product-form
stationary distributions for deficiency zero chemical reaction networks").

## Main results

* `uniformizationRate` — the finite exit-rate bound `Λ` over a finite region.
* `uniformizedKernel` — the bounded uniformized stochastic kernel `U = I + Q/Λ`.
* `uniformizedPow` — the `k`-fold composition `U^{∘k}`.
* `cmeSemigroup` — the Poisson-weighted transition semigroup `P_t`.
* `instIsMarkovKernel_cmeSemigroup` — each `P_t` is a Markov kernel.
* `cmeSemigroup_zero` — `P_0 = id`.
* `cmeStationaryMeasure` — the support-restricted continuous-time stationary measure.
* `uniformizedKernel_invariant_cmeStationaryMeasure` — `U`-invariance of the product-Poisson law.
* `cmeSemigroup_preserves_stationarity` — the normalized product-Poisson law is `P_t`-invariant.

The Chapman–Kolmogorov composition law `P_{s+t} = P_s ∘ P_t` reduces
to the scalar Poisson convolution `∑_{j+k=m} poissonPMFReal s j · poissonPMFReal t k =
poissonPMFReal (s+t) m` (the binomial theorem on `(s+t)^m`) threaded through `comp_sum_left` /
`comp_sum_right`.

Depends on: `CRNT.Stochastic.KernelNormalized`,
`Mathlib.Probability.Kernel.Composition.Comp`, `Mathlib.Probability.Distributions.Poisson.Basic`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- The uniformization rate `Λ`: one plus the total exit rate over a finite region. On the full
count lattice the mass-action exit rates grow without bound, but over a finite closed enabled
region they admit the finite dominating bound used here. The `1 +` keeps `Λ` strictly positive
even on an empty or absorbing region, so the uniformized division `Q/Λ` is always well defined. -/
noncomputable def uniformizationRate (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) : ℝ :=
  1 + ∑ n ∈ hTfin.toFinset, N.exitRate κ n

/-- The uniformization rate is strictly positive. -/
theorem uniformizationRate_pos (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) : 0 < N.uniformizationRate κ hTfin := by
  rw [uniformizationRate]
  have : 0 ≤ ∑ n ∈ hTfin.toFinset, N.exitRate κ n :=
    Finset.sum_nonneg fun n _ => N.exitRate_nonneg κ n
  linarith

/-- Every member of the region has exit rate bounded by the uniformization rate: the single term
`exitRate κ n` is dominated by the full nonnegative sum, plus one. -/
theorem exitRate_le_uniformizationRate (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) {n : S → ℕ} (hn : n ∈ T) :
    N.exitRate κ n ≤ N.uniformizationRate κ hTfin := by
  rw [uniformizationRate]
  have hmem : n ∈ hTfin.toFinset := hTfin.mem_toFinset.mpr hn
  have hsingle : N.exitRate κ n ≤ ∑ m ∈ hTfin.toFinset, N.exitRate κ m :=
    Finset.single_le_sum (fun m _ => N.exitRate_nonneg κ m) hmem
  linarith

/-- The uniformization weight at a count `n`: the exit rate divided by the uniformization rate,
clamped to `[0, 1]`. On a closed enabled region this equals `exitRate κ n / Λ` exactly (the exit
rate is dominated by `Λ`), so the uniformized kernel is the genuine `I + Q/Λ` there; the clamp keeps
the weight a valid mixing coefficient everywhere on the lattice. -/
noncomputable def uniformWeight (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (n : S → ℕ) : ℝ :=
  min 1 (N.exitRate κ n / N.uniformizationRate κ hTfin)

/-- The uniformization weight is nonnegative. -/
theorem uniformWeight_nonneg (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (n : S → ℕ) : 0 ≤ N.uniformWeight κ hTfin n :=
  le_min zero_le_one
    (div_nonneg (N.exitRate_nonneg κ n) (N.uniformizationRate_pos κ hTfin).le)

/-- The uniformization weight is at most one. -/
theorem uniformWeight_le_one (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (n : S → ℕ) : N.uniformWeight κ hTfin n ≤ 1 :=
  min_le_left _ _

/-- On a closed enabled region the clamp is inactive: the uniformization weight is exactly
`exitRate κ n / Λ`, since the exit rate is dominated by `Λ` there. -/
theorem uniformWeight_eq_of_mem (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) {n : S → ℕ} (hn : n ∈ T) :
    N.uniformWeight κ hTfin n = N.exitRate κ n / N.uniformizationRate κ hTfin := by
  rw [uniformWeight, min_eq_right]
  rw [div_le_one (N.uniformizationRate_pos κ hTfin)]
  exact N.exitRate_le_uniformizationRate κ hTfin hn

/-- The bounded uniformized stochastic kernel `U = I + Q/Λ`, realized as the state-dependent convex
combination of holding (a self-loop Dirac) and the embedded jump kernel: with weight
`1 − uniformWeight n` the chain holds at `n`, and with weight `uniformWeight n` it takes one
embedded jump step. Uniformization replaces the unbounded-rate continuous-time generator by this
single bounded one-step Markov kernel. -/
noncomputable def uniformizedKernel (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) : Kernel (S → ℕ) (S → ℕ) where
  toFun n :=
    ENNReal.ofReal (1 - N.uniformWeight κ hTfin n) • Measure.dirac n +
      ENNReal.ofReal (N.uniformWeight κ hTfin n) • N.jumpKernel κ n
  measurable' := measurable_from_top

/-- Unfolding of the uniformized kernel as a measure. -/
theorem uniformizedKernel_apply (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (n : S → ℕ) :
    N.uniformizedKernel κ hTfin n =
      ENNReal.ofReal (1 - N.uniformWeight κ hTfin n) • Measure.dirac n +
        ENNReal.ofReal (N.uniformWeight κ hTfin n) • N.jumpKernel κ n :=
  rfl

/-- The uniformized kernel is row-stochastic everywhere on the lattice: the holding weight and the
jump weight are complementary and the jump kernel is itself Markov, so the row mass is
`ofReal (1 − w) + ofReal w · 1 = 1`. -/
theorem uniformizedKernel_univ_eq_one (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (n : S → ℕ) :
    N.uniformizedKernel κ hTfin n Set.univ = 1 := by
  rw [uniformizedKernel_apply, Measure.coe_add, Pi.add_apply, Measure.smul_apply,
    Measure.smul_apply, smul_eq_mul, smul_eq_mul, measure_univ, mul_one,
    N.jumpKernel_univ_eq_one κ n, mul_one,
    ← ENNReal.ofReal_add (by linarith [N.uniformWeight_le_one κ hTfin n])
      (N.uniformWeight_nonneg κ hTfin n)]
  simp

/-- The bounded uniformized kernel is a genuine Markov kernel on the whole count lattice. -/
instance instIsMarkovKernel_uniformizedKernel (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) : IsMarkovKernel (N.uniformizedKernel κ hTfin) :=
  ⟨fun n => ⟨N.uniformizedKernel_univ_eq_one κ hTfin n⟩⟩

/-- The `k`-fold composition `U^{∘k}` of the uniformized kernel: the `k`-step transition kernel of
the uniformized discrete-time chain. The zeroth power is the identity kernel, and each successor
post-composes one more uniformized step. -/
noncomputable def uniformizedPow (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) : ℕ → Kernel (S → ℕ) (S → ℕ)
  | 0 => Kernel.id
  | k + 1 => N.uniformizedKernel κ hTfin ∘ₖ N.uniformizedPow κ hTfin k

/-- Each power of the uniformized kernel is a Markov kernel: the identity kernel is Markov, and a
composition of Markov kernels is Markov. -/
instance instIsMarkovKernel_uniformizedPow (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) (k : ℕ) :
    IsMarkovKernel (N.uniformizedPow κ hTfin k) := by
  induction k with
  | zero => rw [uniformizedPow]; infer_instance
  | succ k ih => rw [uniformizedPow]; infer_instance

/-- The Poisson rate of the uniformized superposition at time `t`: the product `Λ · t` of the
uniformization rate and the elapsed time, as a nonnegative real. The number of uniformized steps
taken in time `t` is Poisson-distributed with this mean. -/
noncomputable def poissonRate (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (t : ℝ≥0) : ℝ≥0 :=
  (N.uniformizationRate κ hTfin).toNNReal * t

/-- The uniformized transition semigroup `P_t = exp(tQ)`: the Poisson-weighted superposition of the
powers of the uniformized kernel. From a count `n`, the chain takes a `Poisson(Λt)`-distributed
number of uniformized steps, so the time-`t` law is `∑_{k ≥ 0} e^{−Λt}(Λt)^k/k! · U^{∘k}(n, ·)`.
This is Jensen's uniformization realization of the chemical-master-equation semigroup over a finite
region. -/
noncomputable def cmeSemigroup (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (t : ℝ≥0) : Kernel (S → ℕ) (S → ℕ) where
  toFun n :=
    Measure.sum fun k =>
      poissonMeasure (N.poissonRate κ hTfin t) {k} • N.uniformizedPow κ hTfin k n
  measurable' := measurable_from_top

/-- Per-set evaluation of the semigroup: the Poisson-weighted lattice tsum of the powers'
transition masses. The weight on the `k`-step power is the Poisson singleton mass
`Po(Λt) {k} = e^{−Λt}(Λt)^k/k!`. -/
theorem cmeSemigroup_apply' (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (t : ℝ≥0) (n : S → ℕ) {s : Set (S → ℕ)} (hs : MeasurableSet s) :
    N.cmeSemigroup κ hTfin t n s =
      ∑' k : ℕ, poissonMeasure (N.poissonRate κ hTfin t) {k} *
        N.uniformizedPow κ hTfin k n s := by
  show (Measure.sum _) s = _
  rw [Measure.sum_apply _ hs]
  refine tsum_congr fun k => ?_
  rw [Measure.smul_apply, smul_eq_mul]

/-- The total mass of every row of the semigroup is one: each power is Markov, so the row mass is
the Poisson-weighted tsum of ones, which is the total Poisson mass `Po(Λt) univ = 1`. -/
theorem cmeSemigroup_univ_eq_one (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (t : ℝ≥0) (n : S → ℕ) :
    N.cmeSemigroup κ hTfin t n Set.univ = 1 := by
  rw [N.cmeSemigroup_apply' κ hTfin t n MeasurableSet.univ]
  have hone : ∀ k : ℕ, N.uniformizedPow κ hTfin k n Set.univ = 1 := fun k =>
    (N.instIsMarkovKernel_uniformizedPow κ hTfin k).isProbabilityMeasure n |>.measure_univ
  simp_rw [hone, mul_one, poissonMeasure_singleton]
  rw [← ENNReal.ofReal_one]
  rw [← (hasSum_one_poissonMeasure (N.poissonRate κ hTfin t)).tsum_eq]
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
    ((hasSum_one_poissonMeasure (N.poissonRate κ hTfin t)).summable)]

/-- Each transition kernel of the semigroup is a genuine Markov kernel on the whole count lattice. -/
instance instIsMarkovKernel_cmeSemigroup (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (t : ℝ≥0) : IsMarkovKernel (N.cmeSemigroup κ hTfin t) :=
  ⟨fun n => ⟨N.cmeSemigroup_univ_eq_one κ hTfin t n⟩⟩

/-- The Poisson rate vanishes at time zero: `Λ · 0 = 0`. -/
theorem poissonRate_zero (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) : N.poissonRate κ hTfin 0 = 0 := by
  rw [poissonRate, mul_zero]

/-- **Initial identity of the semigroup.** At time zero the semigroup is the identity kernel:
`P_0 = id`. The Poisson rate vanishes, so the Poisson superposition concentrates entirely on the
zeroth power `U^{∘0} = id` (the rate-zero Poisson mass is the Dirac at `0`), and every higher power
carries zero weight. -/
theorem cmeSemigroup_zero (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) : N.cmeSemigroup κ hTfin 0 = Kernel.id := by
  ext n s hs
  rw [N.cmeSemigroup_apply' κ hTfin 0 n hs, poissonRate_zero]
  rw [tsum_eq_single 0]
  · rw [uniformizedPow, poissonMeasure_singleton]
    simp [Kernel.id_apply]
  · intro k hk
    rw [poissonMeasure_singleton, NNReal.coe_zero, zero_pow hk]
    simp

/-- The support-restricted continuous-time stationary measure: the Anderson–Craciun–Kurtz
product-Poisson density cut down to the closed enabled region `T`. This is the stationary law of
the *continuous-time* chain — `π ∝ productPoissonPMF`, annihilated by the generator `πQ = 0` — and
differs from the embedded jump-chain stationary measure of `CRNT.Stochastic.KernelInvariant` by the
holding-rate factor `exitRate`. -/
noncomputable def cmeStationaryMeasure (c : Concentration S)
    (T : Set (S → ℕ)) : Measure (S → ℕ) :=
  (Measure.sum fun n => ENNReal.ofReal (productPoissonPMF c n) • Measure.dirac n).restrict T

omit [DecidableEq S] in
/-- The bare product-Poisson density measure singleton mass: the superposition collapses to its
diagonal atom. -/
theorem productPoissonDensity_singleton (c : Concentration S) (m : S → ℕ) :
    (Measure.sum fun n => ENNReal.ofReal (productPoissonPMF c n) • Measure.dirac n) {m} =
      ENNReal.ofReal (productPoissonPMF c m) := by
  rw [Measure.sum_apply _ (MeasurableSpace.measurableSet_top (s := ({m} : Set (S → ℕ))))]
  rw [tsum_eq_single m]
  · rw [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top (s := ({m} : Set (S → ℕ)))),
      Set.indicator_of_mem (Set.mem_singleton m), Pi.one_apply, mul_one]
  · intro n hn
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top (s := ({m} : Set (S → ℕ)))),
      Set.indicator_of_notMem (by simpa [eq_comm] using hn), mul_zero]

omit [DecidableEq S] in
/-- The singleton mass of the restricted continuous-time stationary measure: the product-Poisson
density on the region, zero off it. -/
theorem cmeStationaryMeasure_singleton (c : Concentration S)
    (T : Set (S → ℕ)) (m : S → ℕ) :
    cmeStationaryMeasure c T {m} =
      T.indicator (fun m => ENNReal.ofReal (productPoissonPMF c m)) m := by
  rw [cmeStationaryMeasure,
    Measure.restrict_apply' (MeasurableSpace.measurableSet_top (s := T))]
  by_cases hm : m ∈ T
  · rw [Set.indicator_of_mem hm,
      show ({m} : Set (S → ℕ)) ∩ T = {m} from by
        ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        exact ⟨fun h => h.1, by rintro rfl; exact ⟨rfl, hm⟩⟩]
    exact productPoissonDensity_singleton c m
  · rw [Set.indicator_of_notMem hm,
      show ({m} : Set (S → ℕ)) ∩ T = (∅ : Set (S → ℕ)) from by
        ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false, not_and]
        rintro rfl; exact hm]
    simp

/-- The bind-to-sum identity for the restricted continuous-time stationary measure under the
uniformized kernel: its pushforward evaluates on any set as the lattice tsum of the region-restricted
product-Poisson weight times the uniformized kernel's transition mass. -/
theorem cmeStationaryMeasure_bind_uniformized_apply (N : Network S) (κ : RateConstants N)
    (c : Concentration S) {T : Set (S → ℕ)} (hTfin : T.Finite) (s : Set (S → ℕ)) :
    (cmeStationaryMeasure c T).bind (N.uniformizedKernel κ hTfin) s =
      ∑' n : S → ℕ, T.indicator (fun n => ENNReal.ofReal (productPoissonPMF c n)) n *
        N.uniformizedKernel κ hTfin n s := by
  rw [cmeStationaryMeasure,
    Measure.bind_apply (MeasurableSpace.measurableSet_top (s := s))
      (N.uniformizedKernel κ hTfin).aemeasurable,
    ← lintegral_indicator (MeasurableSpace.measurableSet_top (s := T)),
    lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  by_cases hn : n ∈ T
  · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn]
  · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn, mul_zero, zero_mul]

/-- The region-restricted product-Poisson weight times the uniformization jump weight is the
region-restricted jump-chain weight scaled by `1/Λ`. On the region the uniformization weight is
`exitRate κ n / Λ`, and `productPoissonPMF c n · exitRate κ n = jumpStationaryMass κ c n`; off the
region both sides vanish. This is the bridge converting the continuous-time density balance into the
already-proved embedded jump-chain balance. -/
theorem indicator_productPoisson_mul_uniformWeight (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) {T : Set (S → ℕ)} (hTfin : T.Finite)
    (n : S → ℕ) :
    T.indicator (fun n => ENNReal.ofReal (productPoissonPMF c n)) n *
        ENNReal.ofReal (N.uniformWeight κ hTfin n) =
      ENNReal.ofReal (1 / N.uniformizationRate κ hTfin) *
        T.indicator (fun n => ENNReal.ofReal (N.jumpStationaryMass κ c n)) n := by
  by_cases hn : n ∈ T
  · have hΛ : 0 < N.uniformizationRate κ hTfin := N.uniformizationRate_pos κ hTfin
    rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn,
      N.uniformWeight_eq_of_mem κ hTfin hn,
      ← ENNReal.ofReal_mul (productPoissonPMF_nonneg hc n),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1 / N.uniformizationRate κ hTfin)]
    congr 1
    rw [jumpStationaryMass]
    field_simp
  · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn, zero_mul, mul_zero]

/-- The uniformized-kernel jump-term tsum into a singleton collapses, via the embedded jump-chain
balance, to the region-restricted product-Poisson weight scaled by the jump weight. The constant
`1/Λ` factors out of the tsum, the jump-chain predecessor summation
(`restricted_predecessor_sum_eq`) reduces the inner tsum to `jumpStationaryMass m` inside the region
(and to zero outside it), and the scaling reconstructs `productPoissonPMF m · uniformWeight m`. -/
theorem tsum_uniformized_jump_term (N : Network S) (κ : RateConstants N) (c : Concentration S)
    (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c) {T : Set (S → ℕ)} (hTfin : T.Finite)
    (hT : N.ClosedEnabledRegion κ T) (m : S → ℕ) :
    (∑' n : S → ℕ, T.indicator (fun n => ENNReal.ofReal (productPoissonPMF c n)) n *
        (ENNReal.ofReal (N.uniformWeight κ hTfin n) * N.jumpKernel κ n {m})) =
      T.indicator (fun m => ENNReal.ofReal (productPoissonPMF c m) *
        ENNReal.ofReal (N.uniformWeight κ hTfin m)) m := by
  have hstep : ∀ n : S → ℕ,
      T.indicator (fun n => ENNReal.ofReal (productPoissonPMF c n)) n *
          (ENNReal.ofReal (N.uniformWeight κ hTfin n) * N.jumpKernel κ n {m}) =
        ENNReal.ofReal (1 / N.uniformizationRate κ hTfin) *
          (T.indicator (fun n => ENNReal.ofReal (N.jumpStationaryMass κ c n)) n *
            N.jumpKernel κ n {m}) := by
    intro n
    rw [← mul_assoc, N.indicator_productPoisson_mul_uniformWeight κ c hc hTfin n, mul_assoc]
  simp_rw [hstep]
  rw [ENNReal.tsum_mul_left]
  have hΛ : 0 < N.uniformizationRate κ hTfin := N.uniformizationRate_pos κ hTfin
  by_cases hm : m ∈ T
  · rw [N.restricted_predecessor_sum_eq κ c hc hcb T hT m hm, Set.indicator_of_mem hm,
      N.uniformWeight_eq_of_mem κ hTfin hm,
      ← ENNReal.ofReal_mul (productPoissonPMF_nonneg hc m),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1 / N.uniformizationRate κ hTfin)]
    rw [jumpStationaryMass]
    congr 1
    field_simp
  · rw [N.restricted_predecessor_sum_eq_zero κ c T hT m hm, mul_zero,
      Set.indicator_of_notMem hm]

/-- The uniformized-kernel holding-term tsum into a singleton collapses to its diagonal atom: the
holding Dirac contributes only at `n = m`, leaving the region-restricted product-Poisson weight
times the holding weight `1 − uniformWeight m`. -/
theorem tsum_uniformized_holding_term (N : Network S) (κ : RateConstants N) (c : Concentration S)
    {T : Set (S → ℕ)} (hTfin : T.Finite) (m : S → ℕ) :
    (∑' n : S → ℕ, T.indicator (fun n => ENNReal.ofReal (productPoissonPMF c n)) n *
        (ENNReal.ofReal (1 - N.uniformWeight κ hTfin n) * Measure.dirac n {m})) =
      T.indicator (fun m => ENNReal.ofReal (productPoissonPMF c m)) m *
        ENNReal.ofReal (1 - N.uniformWeight κ hTfin m) := by
  rw [tsum_eq_single m]
  · rw [Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top (s := ({m} : Set (S → ℕ)))),
      Set.indicator_of_mem (Set.mem_singleton m), Pi.one_apply, mul_one]
  · intro n hn
    have : Measure.dirac n ({m} : Set (S → ℕ)) = 0 := by
      rw [Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top (s := ({m} : Set (S → ℕ)))),
        Set.indicator_of_notMem (by rwa [Set.mem_singleton_iff])]
    rw [this, mul_zero, mul_zero]

/-- **Invariance of the continuous-time stationary measure under the uniformized kernel.** Over a
closed enabled region at a complex-balanced concentration, the support-restricted product-Poisson
law is invariant under the uniformized one-step kernel `U = I + Q/Λ`. The two measures agree on
every singleton: the bind splits into a holding term and a jump term; the holding term collapses to
the diagonal (`tsum_uniformized_holding_term`), the jump term reduces through the embedded
jump-chain balance (`tsum_uniformized_jump_term`), and the complementary weights `1 − w` and `w`
recombine to the bare product-Poisson density `ofReal (ppmf m)`. This is the discrete-time invariance
that uniformization lifts to the whole semigroup. -/
theorem uniformizedKernel_invariant_cmeStationaryMeasure (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (hT : N.ClosedEnabledRegion κ T) :
    Kernel.Invariant (N.uniformizedKernel κ hTfin) (cmeStationaryMeasure c T) := by
  unfold Kernel.Invariant
  refine Measure.ext_of_singleton fun m => ?_
  rw [N.cmeStationaryMeasure_bind_uniformized_apply κ c hTfin {m},
    cmeStationaryMeasure_singleton c T m]
  have hsplit : ∀ n : S → ℕ,
      T.indicator (fun n => ENNReal.ofReal (productPoissonPMF c n)) n *
          N.uniformizedKernel κ hTfin n {m} =
        T.indicator (fun n => ENNReal.ofReal (productPoissonPMF c n)) n *
            (ENNReal.ofReal (1 - N.uniformWeight κ hTfin n) * Measure.dirac n {m}) +
          T.indicator (fun n => ENNReal.ofReal (productPoissonPMF c n)) n *
            (ENNReal.ofReal (N.uniformWeight κ hTfin n) * N.jumpKernel κ n {m}) := by
    intro n
    rw [uniformizedKernel_apply, Measure.coe_add, Pi.add_apply, Measure.smul_apply,
      Measure.smul_apply, smul_eq_mul, smul_eq_mul, mul_add]
  rw [tsum_congr hsplit, ENNReal.tsum_add,
    N.tsum_uniformized_holding_term κ c hTfin m,
    N.tsum_uniformized_jump_term κ c hc hcb hTfin hT m]
  have hw0 : 0 ≤ N.uniformWeight κ hTfin m := N.uniformWeight_nonneg κ hTfin m
  have hw1 : N.uniformWeight κ hTfin m ≤ 1 := N.uniformWeight_le_one κ hTfin m
  have hppmf : 0 ≤ productPoissonPMF c m := productPoissonPMF_nonneg hc m
  by_cases hm : m ∈ T
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm,
      ← ENNReal.ofReal_mul hppmf, ← ENNReal.ofReal_mul hppmf,
      ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
    congr 1
    ring
  · simp [Set.indicator_of_notMem hm]

/-- Each power of the uniformized kernel preserves the continuous-time stationary measure: the
identity kernel is trivially invariant, and a composition of invariant kernels is invariant
(`Invariant.comp`). -/
theorem uniformizedPow_invariant_cmeStationaryMeasure (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (hT : N.ClosedEnabledRegion κ T) (k : ℕ) :
    Kernel.Invariant (N.uniformizedPow κ hTfin k) (cmeStationaryMeasure c T) := by
  induction k with
  | zero =>
    rw [uniformizedPow]
    show (cmeStationaryMeasure c T).bind Kernel.id = cmeStationaryMeasure c T
    exact Measure.id_comp
  | succ k ih =>
    rw [uniformizedPow]
    exact (N.uniformizedKernel_invariant_cmeStationaryMeasure κ c hc hcb hTfin hT).comp ih

/-- **The uniformized semigroup preserves the continuous-time stationary law.** Over a finite closed
enabled region at a complex-balanced concentration, the support-restricted product-Poisson measure is
invariant under every transition kernel `P_t` of the semigroup. The bind distributes through the
Poisson superposition: each power preserves the measure
(`uniformizedPow_invariant_cmeStationaryMeasure`), so the row mass at each set is the Poisson-weighted
tsum of `μ s`, and the Poisson weights sum to one. -/
theorem cmeSemigroup_invariant_cmeStationaryMeasure (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (hT : N.ClosedEnabledRegion κ T) (t : ℝ≥0) :
    Kernel.Invariant (N.cmeSemigroup κ hTfin t) (cmeStationaryMeasure c T) := by
  unfold Kernel.Invariant
  ext s hs
  rw [Measure.bind_apply hs (N.cmeSemigroup κ hTfin t).aemeasurable]
  have hpt : ∀ n, N.cmeSemigroup κ hTfin t n s =
      ∑' k : ℕ, poissonMeasure (N.poissonRate κ hTfin t) {k} *
        N.uniformizedPow κ hTfin k n s := fun n =>
    N.cmeSemigroup_apply' κ hTfin t n hs
  simp_rw [hpt]
  rw [lintegral_tsum (fun k => by
    refine Measurable.aemeasurable ?_
    exact (measurable_const.mul ((N.uniformizedPow κ hTfin k).measurable_coe hs)))]
  have hterm : ∀ k : ℕ,
      ∫⁻ n, poissonMeasure (N.poissonRate κ hTfin t) {k} *
          N.uniformizedPow κ hTfin k n s ∂cmeStationaryMeasure c T =
        poissonMeasure (N.poissonRate κ hTfin t) {k} * cmeStationaryMeasure c T s := by
    intro k
    rw [lintegral_const_mul _ ((N.uniformizedPow κ hTfin k).measurable_coe hs)]
    congr 1
    rw [← Measure.bind_apply hs (N.uniformizedPow κ hTfin k).aemeasurable]
    rw [(N.uniformizedPow_invariant_cmeStationaryMeasure κ c hc hcb hTfin hT k).def]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_right]
  have hsum : (∑' k : ℕ, poissonMeasure (N.poissonRate κ hTfin t) {k}) = 1 := by
    simp_rw [poissonMeasure_singleton]
    rw [← ENNReal.ofReal_one,
      ← (hasSum_one_poissonMeasure (N.poissonRate κ hTfin t)).tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
        ((hasSum_one_poissonMeasure (N.poissonRate κ hTfin t)).summable)]
  rw [hsum, one_mul]

/-- **The semigroup preserves the Anderson–Craciun–Kurtz stationary distribution.** The
support-restricted, normalized product-Poisson probability measure of a nonempty finite closed
enabled region is invariant under every transition kernel `P_t` of the uniformized chemical-master-
equation semigroup, at a strictly positive complex-balanced concentration. This is the process-level
companion of the generator stationarity `πQ = 0`: the continuous-time semigroup `P_t = exp(tQ)`
carries the product-Poisson law to itself for all time. -/
theorem cmeSemigroup_preserves_stationarity (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c) {T : Set (S → ℕ)}
    (hTfin : T.Finite) (hT : N.ClosedEnabledRegion κ T) (t : ℝ≥0) :
    Kernel.Invariant (N.cmeSemigroup κ hTfin t)
      ((cmeStationaryMeasure c T Set.univ)⁻¹ • cmeStationaryMeasure c T) :=
  invariant_smul (N.cmeSemigroup_invariant_cmeStationaryMeasure κ c hc hcb hTfin hT t) _

end Network

end CRNT

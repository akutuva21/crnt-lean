import CRNT.Stochastic.ConservationClassRegion

/-!
# Continuous-time relaxation of the uniformized semigroup

The uniformized chemical-master-equation semigroup over a finite region is the Poisson mixture of the
powers of the uniformized region matrix, `P_t = ∑_{k} e^{−Λt}(Λt)^k/k! · U^{∘k}` (Jensen, "Markoff
chains as an aid in the study of Markoff processes"; Norris, "Markov Chains"). The discrete engine
`CRNT.Stochastic.ConservationClassRegion` carries every region probability vector to the unique
stationary law along the powers `U^{∘n} → π`. This module lifts that discrete convergence to the
continuous-time mixture: the Poisson-averaged action `∑_k Po(Λt){k} · (U^{∘k} x)` converges to the
same stationary law `π` as `t → ∞`.

The lift is an instance of a single analytic fact about the Poisson family. If a real sequence
`a_k → L`, then its Poisson average `∑_k Po(r){k} · a_k` converges to `L` as the rate `r → ∞`
(`tendsto_poissonAverage_atTop`). The Poisson weights sum to one, so the average minus `L` is the
Poisson average of `a_k − L`; bounded by `∑_k Po(r){k} · |a_k − L|`, split at a cutoff `N` past which
`|a_k − L| ≤ ε`: the tail contributes at most `ε`, and the finite head `∑_{k<N} Po(r){k} · |a_k − L|`
vanishes because each fixed-`k` Poisson weight `Po(r){k} = e^{−r}r^k/k!` tends to zero as `r → ∞`
(`tendsto_poissonPMFReal_atTop`, from `x^k e^{−x} → 0`). This is the Poisson-tail/dominated-convergence
argument that turns geometric discrete mixing into continuous-time relaxation.

Threading the rate `r = Λt`: with `Λ > 0` the rate tends to infinity with the elapsed time, so the
discrete-to-continuous lift fires by `t → ∞`.

## Main results

* `tendsto_poissonPMFReal_atTop` — each fixed-`k` Poisson weight `e^{−r}r^k/k! → 0` as the rate
  `r → ∞`.
* `summable_poissonPMFReal_mul` — the Poisson average of a bounded sequence is summable.
* `tendsto_poissonAverage_atTop` — the Poisson average of a convergent sequence converges to its
  limit as the rate `r → ∞`.
* `tendsto_poissonAverage_mulVec_atTop` — the continuous-time region vector
  `∑_k Po(r){k} · (M^k x)` converges entrywise to the discrete stationary vector `b`.
* `cmeRegionVec` — the continuous-time region vector at elapsed time `t`, the Poisson mixture of the
  discrete powers acting on a region law.
* `cmeRegionVec_tendsto_of_conservationClass` — the continuous-time relaxation `P_t x → π` as
  `t → ∞` on a jump-strongly-connected conservation-class region.
* `conservationClass_cmeRegionVec_tendsto` — the unconditional continuous-time relaxation on the
  `A ⇌ B` conservation class, the non-vacuous deliverable.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Stochastic.ConservationClassRegion`.
-/

open MeasureTheory ProbabilityTheory
open Filter Topology
open scoped ENNReal NNReal BigOperators

namespace CRNT

/-- **Each fixed-`k` Poisson weight vanishes at infinite rate.** The real singleton mass
`Po(r){k} = e^{−r} r^k / k!` tends to zero as the rate `r → ∞`: it is `(r^k e^{−r})/k!`, and
`x^k e^{−x} → 0` at `+∞` (`Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`), composed with the
coercion `ℝ≥0 → ℝ` carrying `atTop` to `atTop`. This is the per-term decay that empties the finite
head of the Poisson average. -/
theorem tendsto_poissonPMFReal_atTop (k : ℕ) :
    Tendsto (fun r : ℝ≥0 => (poissonMeasure r {k}).toReal) atTop (𝓝 0) := by
  have hg : Tendsto (fun x : ℝ => x ^ k * Real.exp (-x) / k.factorial) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
    have := h.div_const (k.factorial : ℝ)
    simpa using this
  have hcoe : Tendsto (fun r : ℝ≥0 => ((r : ℝ))) atTop atTop := by
    rw [NNReal.tendsto_coe_atTop]
    exact tendsto_id
  have := hg.comp hcoe
  refine this.congr (fun r => ?_)
  rw [Function.comp_apply, show (poissonMeasure r {k}).toReal = Po(r).real {k} from rfl,
    poissonMeasure_real_singleton]
  ring

/-- The real Poisson weights are nonnegative: the real cast of an extended-nonnegative singleton
mass. -/
theorem poissonPMFReal_nonneg' (r : ℝ≥0) (k : ℕ) : 0 ≤ (poissonMeasure r {k}).toReal :=
  ENNReal.toReal_nonneg

/-- The real Poisson weights sum to one: `∑_k Po(r){k} = 1`, the total mass of the Poisson law. -/
theorem hasSum_poissonPMFReal (r : ℝ≥0) :
    HasSum (fun k => (poissonMeasure r {k}).toReal) 1 := by
  have h := hasSum_one_poissonMeasure r
  refine h.congr_fun (fun k => ?_)
  rw [show (poissonMeasure r {k}).toReal = Po(r).real {k} from rfl, poissonMeasure_real_singleton]

/-- The real Poisson weights form a summable family. -/
theorem summable_poissonPMFReal (r : ℝ≥0) :
    Summable (fun k => (poissonMeasure r {k}).toReal) :=
  (hasSum_poissonPMFReal r).summable

/-- **The Poisson average of a bounded sequence is summable.** If `|a_k| ≤ C` for all `k`, the
weighted family `k ↦ Po(r){k} · a_k` is summable by comparison with the summable dominating family
`k ↦ Po(r){k} · C`. -/
theorem summable_poissonPMFReal_mul {a : ℕ → ℝ} {C : ℝ} (hC : ∀ k, |a k| ≤ C) (r : ℝ≥0) :
    Summable (fun k => (poissonMeasure r {k}).toReal * a k) := by
  refine Summable.of_norm_bounded
    (g := fun k => (poissonMeasure r {k}).toReal * C)
    ((summable_poissonPMFReal r).mul_right C) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonPMFReal_nonneg' r k)]
  exact mul_le_mul_of_nonneg_left (hC k) (poissonPMFReal_nonneg' r k)

/-- A finite head of the Poisson weights vanishes at infinite rate: `∑_{k < N} Po(r){k} → 0` as
`r → ∞`, the finite sum of the per-term decays `tendsto_poissonPMFReal_atTop`. -/
theorem tendsto_sum_range_poissonPMFReal_atTop (N : ℕ) :
    Tendsto (fun r : ℝ≥0 => ∑ k ∈ Finset.range N, (poissonMeasure r {k}).toReal) atTop (𝓝 0) := by
  have := tendsto_finsetSum (Finset.range N)
    (fun k _ => tendsto_poissonPMFReal_atTop k)
  simpa using this

/-- **The Poisson average of a convergent sequence relaxes to its limit.** If `a_k → L`, then the
Poisson average `∑_k Po(r){k} · a_k` tends to `L` as the rate `r → ∞`. The Poisson weights sum to
one, so the average minus `L` is the Poisson average of `a_k − L`, bounded in absolute value by
`∑_k Po(r){k} · |a_k − L|`. Past a cutoff `N` the deviations satisfy `|a_k − L| ≤ ε/2`, so this is
at most `ε/2 + (max deviation) · ∑_{k<N} Po(r){k}`; the finite head vanishes
(`tendsto_sum_range_poissonPMFReal_atTop`), giving the bound `< ε` for large rate. This is the
Poisson-tail/dominated-convergence lift of discrete mixing to continuous-time relaxation. -/
theorem tendsto_poissonAverage_atTop {a : ℕ → ℝ} {L : ℝ} (ha : Tendsto a atTop (𝓝 L)) :
    Tendsto (fun r : ℝ≥0 => ∑' k, (poissonMeasure r {k}).toReal * a k) atTop (𝓝 L) := by
  -- a uniform bound `C` on the deviations `|a_k − L|`.
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp ha) 1 one_pos
  set C : ℝ := 1 + ∑ k ∈ Finset.range N₀, |a k - L| with hCdef
  have hCnonneg : 0 ≤ C := by
    have : 0 ≤ ∑ k ∈ Finset.range N₀, |a k - L| :=
      Finset.sum_nonneg fun k _ => abs_nonneg _
    rw [hCdef]; linarith
  have hbound : ∀ k, |a k - L| ≤ C := by
    intro k
    rcases lt_or_ge k N₀ with hk | hk
    · have hmem : k ∈ Finset.range N₀ := Finset.mem_range.mpr hk
      have hle : |a k - L| ≤ ∑ j ∈ Finset.range N₀, |a j - L| :=
        Finset.single_le_sum (f := fun j => |a j - L|) (fun j _ => abs_nonneg _) hmem
      rw [hCdef]; linarith
    · have hlt := hN₀ k hk
      rw [Real.dist_eq] at hlt
      have hsnn : 0 ≤ ∑ j ∈ Finset.range N₀, |a j - L| :=
        Finset.sum_nonneg fun j _ => abs_nonneg _
      rw [hCdef]; linarith [le_of_lt hlt]
  have habs : ∀ k, |a k| ≤ C + |L| := by
    intro k
    calc |a k| = |(a k - L) + L| := by ring_nf
      _ ≤ |a k - L| + |L| := abs_add_le _ _
      _ ≤ C + |L| := by linarith [hbound k]
  -- both Poisson averages are summable.
  have hsummA : ∀ r : ℝ≥0, Summable (fun k => (poissonMeasure r {k}).toReal * a k) :=
    fun r => summable_poissonPMFReal_mul habs r
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' : ℝ := ε / 2 with hε'def
  have hε'pos : 0 < ε' := by rw [hε'def]; linarith
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ha) ε' hε'pos
  -- the finite head `∑_{k<N} Po(r){k}` shrinks, so `C · head < ε'` eventually.
  have hhead : Tendsto (fun r : ℝ≥0 =>
      C * ∑ k ∈ Finset.range N, (poissonMeasure r {k}).toReal) atTop (𝓝 0) := by
    have := (tendsto_sum_range_poissonPMFReal_atTop N).const_mul C
    simpa using this
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.mp hhead ε' hε'pos
  refine ⟨R, fun r hr => ?_⟩
  -- rewrite the deviation as the Poisson average of `a_k − L`.
  have hLsum : (∑' k, (poissonMeasure r {k}).toReal * L) = L := by
    rw [tsum_mul_right, (hasSum_poissonPMFReal r).tsum_eq, one_mul]
  have hdev : (∑' k, (poissonMeasure r {k}).toReal * a k) - L
      = ∑' k, (poissonMeasure r {k}).toReal * (a k - L) := by
    have hsplit : (∑' k, (poissonMeasure r {k}).toReal * (a k - L))
        = (∑' k, (poissonMeasure r {k}).toReal * a k)
          - ∑' k, (poissonMeasure r {k}).toReal * L := by
      rw [← Summable.tsum_sub (hsummA r) ((summable_poissonPMFReal r).mul_right L)]
      refine tsum_congr fun k => by ring
    rw [hsplit, hLsum]
  rw [Real.dist_eq, hdev]
  -- the head function, supported on `range N`.
  set head : ℕ → ℝ := fun k => if k < N then (poissonMeasure r {k}).toReal * C else 0 with hheaddef
  have hsumhead : Summable head :=
    summable_of_ne_finset_zero (s := Finset.range N) (fun k hk => by
      rw [hheaddef]; simp only; rw [if_neg (by simpa using hk)])
  -- triangle bound by the average of absolute deviations.
  have hstep1 : |∑' k, (poissonMeasure r {k}).toReal * (a k - L)|
      ≤ ∑' k, (poissonMeasure r {k}).toReal * |a k - L| := by
    have hsummN : Summable (fun k => ‖(poissonMeasure r {k}).toReal * (a k - L)‖) := by
      simp_rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonPMFReal_nonneg' r _)]
      exact summable_poissonPMFReal_mul (C := C) (fun k => by rw [abs_abs]; exact hbound k) r
    refine (norm_tsum_le_tsum_norm hsummN).trans (le_of_eq ?_)
    refine tsum_congr fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonPMFReal_nonneg' r k)]
  -- pointwise: `p · |dev| ≤ p · ε' + head k`.
  have hptwise : ∀ k, (poissonMeasure r {k}).toReal * |a k - L|
      ≤ (poissonMeasure r {k}).toReal * ε' + head k := by
    intro k
    have hp := poissonPMFReal_nonneg' r k
    rcases lt_or_ge k N with hk | hk
    · rw [hheaddef]; simp only; rw [if_pos hk]
      have : (poissonMeasure r {k}).toReal * |a k - L| ≤ (poissonMeasure r {k}).toReal * C :=
        mul_le_mul_of_nonneg_left (hbound k) hp
      nlinarith [mul_nonneg hp hε'pos.le]
    · rw [hheaddef]; simp only; rw [if_neg (by omega)]
      have hdevk : |a k - L| ≤ ε' := by
        have := hN k hk; rw [Real.dist_eq] at this; linarith [le_of_lt this]
      have : (poissonMeasure r {k}).toReal * |a k - L| ≤ (poissonMeasure r {k}).toReal * ε' :=
        mul_le_mul_of_nonneg_left hdevk hp
      linarith
  have hsumDom : Summable (fun k => (poissonMeasure r {k}).toReal * ε' + head k) :=
    ((summable_poissonPMFReal r).mul_right ε').add hsumhead
  have hsumAbs : Summable (fun k => (poissonMeasure r {k}).toReal * |a k - L|) :=
    summable_poissonPMFReal_mul (C := C) (fun k => by
      rw [abs_abs]; exact hbound k) r
  -- assemble the tsum bound.
  have hstep2 : (∑' k, (poissonMeasure r {k}).toReal * |a k - L|)
      ≤ ε' + C * ∑ k ∈ Finset.range N, (poissonMeasure r {k}).toReal := by
    refine (hsumAbs.tsum_le_tsum hptwise hsumDom).trans ?_
    rw [Summable.tsum_add ((summable_poissonPMFReal r).mul_right ε') hsumhead]
    have ht1 : (∑' k, (poissonMeasure r {k}).toReal * ε') = ε' := by
      rw [tsum_mul_right, (hasSum_poissonPMFReal r).tsum_eq, one_mul]
    have ht2 : (∑' k, head k) = ∑ k ∈ Finset.range N, (poissonMeasure r {k}).toReal * C := by
      rw [tsum_eq_sum (s := Finset.range N) (fun k hk => by
        rw [hheaddef]; simp only; rw [if_neg (by simpa using hk)])]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hheaddef]; simp only; rw [if_pos (Finset.mem_range.mp hk)]
    rw [ht1, ht2, Finset.mul_sum]
    apply le_of_eq
    congr 1
    refine Finset.sum_congr rfl fun k _ => by ring
  -- the head is small for large rate.
  have hheadsmall : C * ∑ k ∈ Finset.range N, (poissonMeasure r {k}).toReal < ε' := by
    have := hR r hr
    rw [Real.dist_eq, sub_zero] at this
    calc C * ∑ k ∈ Finset.range N, (poissonMeasure r {k}).toReal
        ≤ |C * ∑ k ∈ Finset.range N, (poissonMeasure r {k}).toReal| := le_abs_self _
      _ < ε' := this
  calc |∑' k, (poissonMeasure r {k}).toReal * (a k - L)|
      ≤ ∑' k, (poissonMeasure r {k}).toReal * |a k - L| := hstep1
    _ ≤ ε' + C * ∑ k ∈ Finset.range N, (poissonMeasure r {k}).toReal := hstep2
    _ < ε' + ε' := by linarith
    _ = ε := by rw [hε'def]; ring

/-- **The Poisson-mixed matrix action relaxes to the discrete stationary vector.** If the powers of
a matrix `M` carry a vector `x` entrywise to a limit `b i`, i.e. `(M^k x) i → b i`, then the
continuous-time Poisson mixture `∑_k Po(r){k} · (M^k x) i` converges to the same `b i` as the rate
`r → ∞`, coordinate by coordinate. This is `tendsto_poissonAverage_atTop` applied to the convergent
sequence `k ↦ (M^k x) i`, and is the matrix-level form of the continuous-time relaxation of a
column-stochastic primitive chain. -/
theorem tendsto_poissonAverage_mulVec_atTop {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (x b : ι → ℝ)
    (htend : ∀ i, Tendsto (fun k => (M ^ k).mulVec x i) atTop (𝓝 (b i))) (i : ι) :
    Tendsto (fun r : ℝ≥0 => ∑' k, (poissonMeasure r {k}).toReal * (M ^ k).mulVec x i)
      atTop (𝓝 (b i)) :=
  tendsto_poissonAverage_atTop (htend i)

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- **The continuous-time region vector.** At elapsed time `t`, the Poisson mixture of the discrete
uniformized powers acting on a region law `x`, coordinate `i`:
`P_t x i = ∑_k Po(Λt){k} · (U^{∘k} x) i`. This is the region-restricted real action of the
uniformized chemical-master-equation semigroup `cmeSemigroup` (Jensen, "Markoff chains as an aid in
the study of Markoff processes"; Norris, "Markov Chains"), with the Poisson step-count weight
`Po(Λt){k} = e^{−Λt}(Λt)^k/k!` on the `k`-step uniformized region matrix. -/
noncomputable def cmeRegionVec (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) [Fintype ↥T] (x : ↥T → ℝ) (t : ℝ≥0) (i : ↥T) : ℝ :=
  ∑' k : ℕ, (poissonMeasure (N.poissonRate κ hTfin t) {k}).toReal *
    (N.uRegionMatrix κ hTfin ^ k).mulVec x i

/-- The Poisson rate tends to infinity with the elapsed time: `Λt → ∞` as `t → ∞`. The rate is the
positive-constant scaling `t ↦ Λ.toNNReal · t`, and `Λ.toNNReal > 0` because the uniformization rate
is strictly positive. This threads `t → ∞` through the rate-`r → ∞` Poisson-average relaxation. -/
theorem tendsto_poissonRate_atTop (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) :
    Tendsto (fun t : ℝ≥0 => N.poissonRate κ hTfin t) atTop atTop := by
  have hΛ : 0 < (N.uniformizationRate κ hTfin).toNNReal :=
    Real.toNNReal_pos.mpr (N.uniformizationRate_pos κ hTfin)
  have hΛ' : 0 < ((N.uniformizationRate κ hTfin).toNNReal : ℝ) := by exact_mod_cast hΛ
  rw [← NNReal.tendsto_coe_atTop]
  have hc : Tendsto (fun t : ℝ≥0 => ((t : ℝ))) atTop atTop := by
    rw [NNReal.tendsto_coe_atTop]; exact tendsto_id
  refine (Tendsto.const_mul_atTop hΛ' hc).congr (fun t => ?_)
  rw [poissonRate]; push_cast; ring

/-- **Continuous-time relaxation of the uniformized chain on a conservation class.** On a finite
jump-strongly-connected conservation-class region, the continuous-time region vector `P_t x` of every
region probability law `x` converges entrywise to the unique stationary law `b` as `t → ∞`:
`cmeRegionVec κ hTfin x t i → b i`. The discrete powers carry `x` to `b`
(`uRegionMatrix_pow_mulVec_tendsto_of_conservationClass`), and the Poisson-mixture lift
`tendsto_poissonAverage_mulVec_atTop` turns that geometric discrete mixing into continuous-time
relaxation, threaded through `t → ∞` by the rate divergence `tendsto_poissonRate_atTop`. This is the
process-level relaxation of the Anderson–Craciun–Kurtz product-Poisson law (Anderson, Craciun &
Kurtz, "Product-form stationary distributions for deficiency zero chemical reaction networks") on a
real conservation class, with the holding-self-loop aperiodicity of Norris, "Markov Chains", §1.8. -/
theorem cmeRegionVec_tendsto_of_conservationClass (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) [Fintype ↥T] [Nonempty ↥T]
    (hT : N.ConservationClassRegion κ T) (hjsc : N.RegionJumpStronglyConnected κ T)
    (x : ↥T → ℝ) (hx : ∑ i, x i = 1) :
    ∃ b : ↥T → ℝ, (∀ i, 0 < b i) ∧ (∑ i, b i = 1) ∧
      (N.uRegionMatrix κ hTfin).mulVec b = b ∧
      ∀ i, Tendsto (fun t : ℝ≥0 => N.cmeRegionVec κ hTfin x t i) atTop (𝓝 (b i)) := by
  obtain ⟨b, hbpos, hbsum, hbfix, _, htend⟩ :=
    N.uRegionMatrix_pow_mulVec_tendsto_of_conservationClass κ hTfin hT hjsc x hx
  refine ⟨b, hbpos, hbsum, hbfix, fun i => ?_⟩
  have hr := tendsto_poissonAverage_mulVec_atTop (N.uRegionMatrix κ hTfin) x b htend i
  exact hr.comp (N.tendsto_poissonRate_atTop κ hTfin)

end Network

end CRNT

namespace CRNT.Examples.ConservationClassRegion

open CRNT CRNT.Network
open CRNT.Examples.StochasticConvergenceExample
open Filter Topology
open scoped BigOperators

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- **Unconditional continuous-time relaxation on the `A ⇌ B` conservation class.** For `1 ≤ K`, the
continuous-time region vector of the uniformized chemical-master-equation chain on the conservation
class `{n : n_A + n_B = K}` carries every region probability law `x` to the unique stationary law `b`
as `t → ∞`, entrywise. Every hypothesis is discharged: finiteness (`conservationClass_finite`), the
relaxed region structure (`conservationClassRegion`), and count-level strong connectivity
(`conservationClass_jumpStronglyConnected`); the aperiodicity self-loop is the uniformized holding
mass, available even at the simplex boundary where a closed enabled region cannot exist. This is the
non-vacuous continuous-time deliverable: a genuine `A ⇌ B` mass-action network whose uniformized
semigroup relaxes unconditionally to the Anderson–Craciun–Kurtz product-Poisson law (Anderson,
Craciun & Kurtz, "Product-form stationary distributions for deficiency zero chemical reaction
networks"), the continuous-time companion of the discrete `conservationClass_pow_mulVec_tendsto`. -/
theorem conservationClass_cmeRegionVec_tendsto (κ : RateConstants N) (K : ℕ) (hK : 1 ≤ K)
    (x : ↥(conservationClass K) → ℝ) (hx : ∑ i, x i = 1) :
    ∃ b : ↥(conservationClass K) → ℝ, (∀ i, 0 < b i) ∧ (∑ i, b i = 1) ∧
      (N.uRegionMatrix κ (conservationClass_finite K)).mulVec b = b ∧
      ∀ i, Tendsto
        (fun t : ℝ≥0 => N.cmeRegionVec κ (conservationClass_finite K) x t i) atTop (𝓝 (b i)) := by
  haveI : Nonempty ↥(conservationClass K) := ⟨⟨allA K, allA_mem K⟩⟩
  exact N.cmeRegionVec_tendsto_of_conservationClass κ (conservationClass_finite K)
    (conservationClassRegion κ K hK) (conservationClass_jumpStronglyConnected κ K hK) x hx

end CRNT.Examples.ConservationClassRegion

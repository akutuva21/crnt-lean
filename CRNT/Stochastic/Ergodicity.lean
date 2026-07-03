import CRNT.Stochastic.KernelNormalized
import CRNT.LinearAlgebra.PerronFrobenius

/-!
# Uniqueness of the stationary distribution of the embedded jump chain on a finite region

On a finite closed enabled region the embedded jump chain is a finite-state Markov chain.
General Meyn–Tweedie ergodicity (Meyn & Tweedie, "Markov Chains and Stochastic Stability") is
unavailable in this development — Mathlib's `ProbabilityTheory.Kernel.Irreducible` is a stub
carrying no uniqueness — so the uniqueness of the invariant probability measure is obtained from
finite-state Perron–Frobenius (`CRNT.LinearAlgebra.PerronFrobenius`) applied to the row-stochastic
transition matrix of the jump chain restricted to the region.

The bridge from measures to matrices runs over the finite type `↥T`. Any probability measure `μ`
that is supported on the finite region `T` is recorded by its real singleton-mass vector
`stationaryVec μ : ↥T → ℝ`, `i ↦ (μ {i}).toReal`. Invariance `μ.bind κ = μ`, read on singletons
through the discrete superposition, becomes the fixed-point equation `regionMatrix.mulVec v = v`
for the restricted transition matrix `regionMatrix κ hT i j = (jumpKernel κ j {i}).toReal`
(`stationaryVec_mulVec_fixed`). Forward-closure of the region makes that matrix column-stochastic
(`regionMatrix_colStochastic`): all of a member's exit mass stays inside `T`.

The reference fixed vector is the normalized restricted stationary measure
(`jumpKernel_isInvariant_probabilityMeasure_of_nonempty`), strictly positive on the region since
the lifted product-Poisson weight is positive there (`jumpStationaryMass_pos`). Perron–Frobenius
uniqueness (`mulVec_fixed_unique_of_stronglyConnected`) then pins every invariant fixed vector to a
scalar multiple of it, and the shared unit total mass forces that scalar to be one. The geometric
*irreducibility* of the chain — that the restricted transition digraph is strongly connected — is
stated as an explicit hypothesis `regionStronglyConnected`, the single-communicating-class property
of the region.

## Main results

* `regionMatrix` — the restricted transition matrix of the jump chain on a finite region.
* `regionMatrix_nonneg`, `regionMatrix_colStochastic` — it is entrywise nonnegative and
  column-stochastic (forward-closure keeps exit mass inside `T`).
* `stationaryVec` — the real singleton-mass vector of a region-supported measure.
* `stationaryVec_mulVec_fixed` — invariance of a region-supported probability measure is the
  matrix fixed-point equation for its mass vector.
* `stationaryVec_sum_eq_one`, `stationaryVec_nonneg` — the mass vector is a probability vector.
* `regionStronglyConnected` — the single-communicating-class hypothesis on the region.
* `invariant_probabilityMeasure_unique_on_region` — any two invariant probability measures
  supported on a finite, strongly connected closed enabled region coincide.

Depends on: `CRNT.Stochastic.KernelNormalized`,
`CRNT.LinearAlgebra.PerronFrobenius`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- The restricted transition matrix of the embedded jump chain on a finite region `T`,
indexed by the finite type `↥T`. Following the column-stochastic Perron–Frobenius convention,
the column `j` (the source) carries the transition masses out of `j`, so the entry at row `i`
(the target), column `j` is the kernel mass `jumpKernel κ j {i}` cast to a real. -/
noncomputable def regionMatrix (N : Network S) (κ : RateConstants N) (T : Set (S → ℕ)) :
    Matrix ↥T ↥T ℝ :=
  fun i j => (N.jumpKernel κ (j : S → ℕ) {(i : S → ℕ)}).toReal

/-- Each entry of the restricted transition matrix is nonnegative: it is the real cast of an
extended-nonnegative kernel mass. -/
theorem regionMatrix_nonneg (N : Network S) (κ : RateConstants N) (T : Set (S → ℕ)) :
    ∀ i j, 0 ≤ N.regionMatrix κ T i j :=
  fun _ _ => ENNReal.toReal_nonneg

/-- **Column-stochasticity.** Each column of the restricted transition matrix sums to one: the
column `j` totals the kernel mass `∑_{i ∈ T} jumpKernel κ j {i}`, and forward-closure of the
region keeps all of `j`'s outgoing mass inside `T`, so this equals the full row mass
`jumpKernel κ j Set.univ = 1` of the Markov kernel. -/
theorem regionMatrix_colStochastic (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} [Fintype ↥T] (hT : N.ClosedEnabledRegion κ T) :
    ∀ j, ∑ i, N.regionMatrix κ T i j = 1 := by
  intro j
  -- The column sum is the toReal of the kernel mass of `T`, which is the full unit row mass.
  have hsum : (∑ i : ↥T, N.jumpKernel κ (j : S → ℕ) {(i : S → ℕ)})
      = N.jumpKernel κ (j : S → ℕ) T := by
    rw [← measure_biUnion_finset]
    · congr 1
      ext x
      simp only [Set.mem_iUnion, Set.mem_singleton_iff, Finset.mem_univ,
        true_and, Subtype.exists, exists_prop]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hx; exact ⟨x, hx, rfl⟩
    · intro a _ b _ hab
      simp only [Function.onFun, Set.disjoint_singleton]
      exact fun h => hab (Subtype.ext h)
    · exact fun _ _ => MeasurableSpace.measurableSet_top
  have hjT : (j : S → ℕ) ∈ T := j.2
  haveI : IsProbabilityMeasure (N.jumpKernel κ (j : S → ℕ)) :=
    (N.instIsMarkovKernel_jumpKernel κ).isProbabilityMeasure (j : S → ℕ)
  have hcover : N.jumpKernel κ (j : S → ℕ) T = 1 := by
    -- forward-closure: from `j ∈ T`, every reaction lands in `T`, so the row mass leaving `T`
    -- vanishes. The complement carries zero mass, so `T` carries the full unit mass.
    have hcompl : N.jumpKernel κ (j : S → ℕ) Tᶜ = 0 := by
      rw [N.jumpKernel_apply_of_exitRate_pos κ (j : S → ℕ) (hT.exit_ne _ hjT)]
      refine Finset.sum_eq_zero (fun r _ => ?_)
      have hfwd : N.jumpNextCount (j : S → ℕ) r ∈ T := hT.forward _ hjT r
      rw [Set.indicator_of_notMem
        (show N.jumpNextCount (j : S → ℕ) r ∉ (Tᶜ : Set (S → ℕ)) from
          fun h => h hfwd), mul_zero]
    exact (prob_compl_eq_zero_iff (MeasurableSpace.measurableSet_top (s := T))).mp hcompl
  -- assemble
  have heq : (∑ i : ↥T, N.regionMatrix κ T i j)
      = (∑ i : ↥T, N.jumpKernel κ (j : S → ℕ) {(i : S → ℕ)}).toReal := by
    rw [ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
    rfl
  rw [heq, hsum, hcover]; rfl

/-- The real singleton-mass vector of a measure over the finite region `T`: `i ↦ (μ {i}).toReal`.
For an invariant probability measure supported on `T` this is the stationary probability vector of
the embedded jump chain on the region. -/
noncomputable def stationaryVec {T : Set (S → ℕ)} (μ : Measure (S → ℕ)) : ↥T → ℝ :=
  fun i => (μ {(i : S → ℕ)}).toReal

omit [DecidableEq S] in
/-- **Region support determines a measure by its restricted singleton masses.** Expanding the
lattice integral of a nonnegative function against a probability measure supported on the finite
region `T` (`μ Tᶜ = 0`) as a finite sum over `↥T` of the singleton masses times the integrand,
using the discrete superposition `μ = ∑ₙ μ{n} • δₙ` and dropping the off-region terms. -/
theorem lintegral_eq_sum_on_region {T : Set (S → ℕ)} [Fintype ↥T] (μ : Measure (S → ℕ))
    (hsupp : μ Tᶜ = 0) (f : (S → ℕ) → ℝ≥0∞) :
    ∫⁻ n, f n ∂μ = ∑ i : ↥T, μ {(i : S → ℕ)} * f (i : S → ℕ) := by
  conv_lhs => rw [← μ.sum_smul_dirac]
  rw [lintegral_sum_measure]
  -- each summand is the singleton-mass-weighted value, vanishing off the region.
  have hterm : ∀ n : S → ℕ, ∫⁻ a, f a ∂(μ {n} • Measure.dirac n) = μ {n} * f n := by
    intro n; rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  simp_rw [hterm]
  -- mass off the region is zero, so the lattice tsum reduces to the finite region sum.
  have hmass : ∀ n ∉ T, μ {n} = 0 := by
    intro n hn
    exact le_antisymm (hsupp ▸ measure_mono (Set.singleton_subset_iff.mpr hn)) (bot_le)
  set F : Finset (S → ℕ) := Finset.univ.image (fun i : ↥T => (i : S → ℕ)) with hF
  have hzero : ∀ n ∉ F, μ {n} * f n = 0 := by
    intro n hn
    have hnT : n ∉ T := by
      intro hnT
      exact hn (Finset.mem_image.mpr ⟨⟨n, hnT⟩, Finset.mem_univ _, rfl⟩)
    rw [hmass n hnT, zero_mul]
  rw [tsum_eq_sum hzero, hF, Finset.sum_image]
  · intro a _ b _ h; exact Subtype.ext h

/-- **Invariance is the matrix fixed-point equation.** For a probability measure `μ` supported on
the finite region `T` and invariant under the embedded jump kernel, its singleton-mass vector is a
fixed vector of the restricted transition matrix: `regionMatrix κ T · stationaryVec μ = stationaryVec μ`.
At each `m ∈ T`, invariance reads `μ {m} = ∫⁻ n, κ n {m} ∂μ`; the integral collapses to the finite
region sum `∑_{n ∈ T} μ{n} · κ n {m}` (`lintegral_eq_sum_on_region`), whose real cast is the matrix
row `∑_n regionMatrix κ T m n · stationaryVec μ n`. -/
theorem stationaryVec_mulVec_fixed (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    [Fintype ↥T] (μ : Measure (S → ℕ)) [IsProbabilityMeasure μ] (hsupp : μ Tᶜ = 0)
    (hinv : Kernel.Invariant (N.jumpKernel κ) μ) :
    (N.regionMatrix κ T).mulVec (stationaryVec (T := T) μ) = stationaryVec (T := T) μ := by
  funext m
  -- the matrix row is a finite ENNReal sum, cast to a real.
  have hrow : (N.regionMatrix κ T).mulVec (stationaryVec (T := T) μ) m
      = (∑ n : ↥T, μ {(n : S → ℕ)} * N.jumpKernel κ (n : S → ℕ) {(m : S → ℕ)}).toReal := by
    rw [Matrix.mulVec, dotProduct, ENNReal.toReal_sum (fun n _ => ?_)]
    · refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [regionMatrix, stationaryVec, ENNReal.toReal_mul, mul_comm]
    · exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [hrow]
  -- invariance read on the singleton `{m}`.
  have hbind : μ {(m : S → ℕ)} = ∫⁻ n, N.jumpKernel κ n {(m : S → ℕ)} ∂μ := by
    have hmeas := congrArg (fun ρ : Measure (S → ℕ) => ρ {(m : S → ℕ)}) hinv.def
    rw [Measure.bind_apply (MeasurableSpace.measurableSet_top (s := ({(m : S → ℕ)} : Set (S → ℕ))))
      (N.jumpKernel κ).aemeasurable] at hmeas
    exact hmeas.symm
  show _ = (μ {(m : S → ℕ)}).toReal
  rw [hbind, lintegral_eq_sum_on_region (T := T) μ hsupp
    (fun n => N.jumpKernel κ n {(m : S → ℕ)})]

omit [DecidableEq S] [Fintype S] in
/-- The singleton-mass vector of a probability measure supported on the finite region `T` sums to
one over `↥T`: the total mass `μ Set.univ = 1` is carried entirely by the region. -/
theorem stationaryVec_sum_eq_one {T : Set (S → ℕ)} [Fintype ↥T] (μ : Measure (S → ℕ))
    [IsProbabilityMeasure μ] (hsupp : μ Tᶜ = 0) :
    ∑ i : ↥T, stationaryVec (T := T) μ i = 1 := by
  have hsum : (∑ i : ↥T, μ {(i : S → ℕ)}) = 1 := by
    have hT : μ T = 1 :=
      (prob_compl_eq_zero_iff (MeasurableSpace.measurableSet_top (s := T))).mp hsupp
    have hcover : (∑ i : ↥T, μ {(i : S → ℕ)}) = μ T := by
      rw [← measure_biUnion_finset (fun a _ b _ hab => by
          simp only [Function.onFun, Set.disjoint_singleton]; exact fun h => hab (Subtype.ext h))
        (fun _ _ => MeasurableSpace.measurableSet_top)]
      congr 1
      ext x
      simp only [Set.mem_iUnion, Set.mem_singleton_iff, Finset.mem_univ, true_and, Subtype.exists,
        exists_prop]
      exact ⟨fun ⟨a, ha, h⟩ => h ▸ ha, fun hx => ⟨x, hx, rfl⟩⟩
    rw [hcover, hT]
  rw [← ENNReal.toReal_one, ← hsum, ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
  rfl

omit [DecidableEq S] [Fintype S] in
/-- The singleton-mass vector is entrywise nonnegative: it is the real cast of an
extended-nonnegative measure. -/
theorem stationaryVec_nonneg {T : Set (S → ℕ)} [Fintype ↥T] (μ : Measure (S → ℕ)) :
    ∀ i, 0 ≤ stationaryVec (T := T) μ i :=
  fun _ => ENNReal.toReal_nonneg

/-- **Single-communicating-class hypothesis on the region.** The embedded jump chain restricted to
`T` is irreducible: every state reaches every state along the support digraph of the restricted
transition matrix. This is the irreducibility that finite-state Perron–Frobenius needs and that
Mathlib's `Kernel.Irreducible` stub does not provide. -/
def regionStronglyConnected (N : Network S) (κ : RateConstants N) (T : Set (S → ℕ))
    [Fintype ↥T] : Prop :=
  ∀ i j : ↥T, supportReaches (N.regionMatrix κ T) i j

/-- The normalized restricted stationary measure of a region. -/
noncomputable def stationaryProbabilityMeasure (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (T : Set (S → ℕ)) : Measure (S → ℕ) :=
  (N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T

/-- The canonical stationary probability measure is supported on the region: it is a scalar
multiple of the `T`-restricted measure, whose mass off `T` vanishes. -/
theorem stationaryProbabilityMeasure_compl_eq_zero (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (T : Set (S → ℕ)) :
    N.stationaryProbabilityMeasure κ c T Tᶜ = 0 := by
  have hrestr : N.restrictedStationaryMeasure κ c T Tᶜ = 0 := by
    rw [restrictedStationaryMeasure,
      Measure.restrict_apply' (MeasurableSpace.measurableSet_top (s := T)),
      Set.compl_inter_self, measure_empty]
  rw [stationaryProbabilityMeasure, Measure.smul_apply, hrestr, smul_zero]

/-- The singleton-mass vector of the canonical stationary probability measure is strictly positive
on the region: at a strictly positive complex-balanced concentration the lifted product-Poisson
weight is positive on the region (`jumpStationaryMass_pos`), and the normalization scalar is a
positive finite real, so each region singleton carries positive mass. -/
theorem stationaryVec_stationaryProbabilityMeasure_pos (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Positive) {T : Set (S → ℕ)} [Fintype ↥T]
    (hT : N.ClosedEnabledRegion κ T) (hne : T.Nonempty) :
    ∀ i, 0 < stationaryVec (T := T) (N.stationaryProbabilityMeasure κ c T) i := by
  intro i
  haveI hfin : IsFiniteMeasure (N.restrictedStationaryMeasure κ c T) :=
    N.restrictedStationaryMeasure_isFiniteMeasure κ c (Set.toFinite T)
  have hmass_ne : N.restrictedStationaryMeasure κ c T Set.univ ≠ 0 :=
    N.restrictedStationaryMeasure_univ_pos κ c hc hT hne
  have hmass_lt : N.restrictedStationaryMeasure κ c T Set.univ ≠ ∞ :=
    measure_ne_top _ _
  have hval : N.stationaryProbabilityMeasure κ c T {(i : S → ℕ)}
      = (N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ *
        ENNReal.ofReal (N.jumpStationaryMass κ c (i : S → ℕ)) := by
    rw [stationaryProbabilityMeasure, Measure.smul_apply,
      N.restrictedStationaryMeasure_singleton κ c T (i : S → ℕ),
      Set.indicator_of_mem i.2, smul_eq_mul]
  have hsingle : 0 < N.stationaryProbabilityMeasure κ c T {(i : S → ℕ)} := by
    rw [hval]
    refine ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hmass_lt) ?_
    exact (ENNReal.ofReal_pos.mpr (N.jumpStationaryMass_pos κ c hc hT i.2)).ne'
  have hfin : N.stationaryProbabilityMeasure κ c T {(i : S → ℕ)} ≠ ∞ := by
    rw [hval]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hmass_ne) ENNReal.ofReal_ne_top
  exact ENNReal.toReal_pos hsingle.ne' hfin

/-- The canonical stationary probability measure is invariant under the embedded jump kernel and is
a probability measure, by `jumpKernel_isInvariant_probabilityMeasure_of_nonempty`. -/
theorem stationaryProbabilityMeasure_isInvariant_isProbability (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c) {T : Set (S → ℕ)}
    (hT : N.ClosedEnabledRegion κ T) (hTfin : T.Finite) (hne : T.Nonempty) :
    Kernel.Invariant (N.jumpKernel κ) (N.stationaryProbabilityMeasure κ c T) ∧
      IsProbabilityMeasure (N.stationaryProbabilityMeasure κ c T) :=
  N.jumpKernel_isInvariant_probabilityMeasure_of_nonempty κ c hc hcb hT hTfin hne

/-- **Uniqueness of the invariant probability measure on a finite irreducible region.** On a
finite closed enabled region `T` that is a single communicating class
(`regionStronglyConnected`), the embedded jump chain has exactly one invariant probability measure
supported on `T`: any such measure coincides with the canonical normalized stationary measure
`stationaryProbabilityMeasure`.

The jump chain on `T` is a finite-state Markov chain whose restricted transition matrix is
column-stochastic (`regionMatrix_colStochastic`) and irreducible. Both mass vectors are fixed
(`stationaryVec_mulVec_fixed`); the canonical one is strictly positive
(`stationaryVec_stationaryProbabilityMeasure_pos`), so Perron–Frobenius uniqueness
(`mulVec_fixed_unique_of_stronglyConnected`) pins the arbitrary mass vector to a scalar multiple of
it, and the shared unit total mass (`stationaryVec_sum_eq_one`) forces the scalar to be one. Equal
finite singleton masses then force the measures equal (`Measure.ext_of_singleton`), the off-region
masses both vanishing by support. This is the finite-state replacement for general Meyn–Tweedie
ergodicity (Meyn & Tweedie, "Markov Chains and Stochastic Stability"), unavailable in this
development. -/
theorem invariant_probabilityMeasure_unique_on_region (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c) {T : Set (S → ℕ)}
    [Fintype ↥T] (hT : N.ClosedEnabledRegion κ T) (hne : T.Nonempty)
    (hirr : N.regionStronglyConnected κ T)
    (μ : Measure (S → ℕ)) [IsProbabilityMeasure μ] (hμsupp : μ Tᶜ = 0)
    (hμinv : Kernel.Invariant (N.jumpKernel κ) μ) :
    μ = N.stationaryProbabilityMeasure κ c T := by
  classical
  haveI : Nonempty ↥T := hne.to_subtype
  set ρ := N.stationaryProbabilityMeasure κ c T with hρ
  haveI hρprob : IsProbabilityMeasure ρ :=
    (N.stationaryProbabilityMeasure_isInvariant_isProbability κ c hc hcb hT (Set.toFinite T) hne).2
  have hρinv : Kernel.Invariant (N.jumpKernel κ) ρ :=
    (N.stationaryProbabilityMeasure_isInvariant_isProbability κ c hc hcb hT (Set.toFinite T) hne).1
  have hρsupp : ρ Tᶜ = 0 := N.stationaryProbabilityMeasure_compl_eq_zero κ c T
  -- the two mass vectors are fixed; the canonical one is positive.
  have hPa : (N.regionMatrix κ T).mulVec (stationaryVec (T := T) ρ) = stationaryVec (T := T) ρ :=
    N.stationaryVec_mulVec_fixed κ ρ hρsupp hρinv
  have hPv : (N.regionMatrix κ T).mulVec (stationaryVec (T := T) μ) = stationaryVec (T := T) μ :=
    N.stationaryVec_mulVec_fixed κ μ hμsupp hμinv
  have hapos : ∀ i, 0 < stationaryVec (T := T) ρ i :=
    N.stationaryVec_stationaryProbabilityMeasure_pos κ c hc hT hne
  -- Perron–Frobenius: the arbitrary fixed vector is a scalar multiple of the positive one.
  obtain ⟨t, ht⟩ := mulVec_fixed_unique_of_stronglyConnected (N.regionMatrix κ T)
    (N.regionMatrix_nonneg κ T) (stationaryVec (T := T) ρ) (stationaryVec (T := T) μ)
    hapos hPa hPv hirr
  -- both vectors sum to one, forcing the scalar to be one.
  have hsumμ : ∑ i : ↥T, stationaryVec (T := T) μ i = 1 :=
    stationaryVec_sum_eq_one μ hμsupp
  have hsumρ : ∑ i : ↥T, stationaryVec (T := T) ρ i = 1 :=
    stationaryVec_sum_eq_one ρ hρsupp
  have ht1 : t = 1 := by
    have : (∑ i : ↥T, stationaryVec (T := T) μ i) = t * ∑ i : ↥T, stationaryVec (T := T) ρ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [ht]; rfl
    rw [hsumμ, hsumρ, mul_one] at this
    exact this.symm
  have hvec : stationaryVec (T := T) μ = stationaryVec (T := T) ρ := by
    rw [ht, ht1, one_smul]
  -- equal singleton masses on `T`, both zero off `T`; conclude by extensionality.
  refine Measure.ext_of_singleton (fun m => ?_)
  by_cases hm : m ∈ T
  · have : (μ {m}).toReal = (ρ {m}).toReal := congrFun hvec ⟨m, hm⟩
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp this
  · have hμ0 : μ {m} = 0 :=
      le_antisymm (hμsupp ▸ measure_mono (Set.singleton_subset_iff.mpr hm)) bot_le
    have hρ0 : ρ {m} = 0 :=
      le_antisymm (hρsupp ▸ measure_mono (Set.singleton_subset_iff.mpr hm)) bot_le
    rw [hμ0, hρ0]

end Network

end CRNT

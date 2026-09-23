import CRNT.Dynamics.ComplexBalanceCycleDecomposition
import CRNT.Dynamics.GlobalPersistence
import CRNT.Dynamics.SiphonDimensionDescent
import CRNT.Dynamics.ToricInclusion
import CRNT.Dynamics.ZeroSeparating
import CRNT.Equilibria.ComplexBalanceStructure
import CRNT.Equilibria.ComplexBalanceGeometry
import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Geometry.ToricUniformWallMargin

/-!
# The Global Attractor Theorem for complex-balanced mass-action systems

The former Global Attractor Conjecture is a theorem: every positive complex-balanced
equilibrium is the global attractor of the positive part of its stoichiometric compatibility
class.  Equivalently, every positive trajectory in that class is persistent and converges to
the unique positive complex-balanced equilibrium.

This module states the full theorem independently of single-linkage, no-critical-siphon, or
strongly-endotactic special cases.  The hard proof kernel is Craciun's toric-differential-
inclusion / zero-separating-surface construction; the surrounding CRNT consequences are
ordinary deductions from the persistence + Horn--Jackson machinery already formalized.
-/

open scoped NNReal ENNReal Topology
open Filter

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A positive equilibrium globally attracts its positive stoichiometric compatibility class for
a specified genuine mass-action flow. -/
def IsGlobalAttractorForPositiveClass (N : Network S) (κ : N.RateConstants)
    (xstar : Concentration S)
    (ϕ : Flow ℝ≥0 (Concentration S))
    (γ : Concentration S → ℝ → Concentration S) : Prop :=
  N.IsMassActionFlow κ ϕ γ ∧
  ∀ x₀ : Concentration S,
    x₀.Positive → N.StoichCompatible x₀ xstar →
      omegaLimit atTop ϕ {x₀} = {xstar}

/-- Flow-independent form of the Global Attractor property. -/
def HasGlobalAttractorProperty (N : Network S) (κ : N.RateConstants)
    (xstar : Concentration S) : Prop :=
  ∀ (ϕ : Flow ℝ≥0 (Concentration S))
    (γ : Concentration S → ℝ → Concentration S),
    N.IsMassActionFlow κ ϕ γ →
      N.IsGlobalAttractorForPositiveClass κ xstar ϕ γ

/-- **Trajectory-level standard permanence on one positive class.**  There is a single
compact subset of the open positive compatibility class that eventually absorbs every genuine
forward mass-action trajectory started in that class.  Unlike `PermanentOnPositiveClass`, this
formulation does not presuppose the existence of a global flow on the whole ambient real space. -/
def GenuinePermanentOnPositiveClass (N : Network S) (κ : N.RateConstants)
    (xref : Concentration S) : Prop :=
  ∃ K : Set (Concentration S), IsCompact K ∧
    K ⊆ N.positiveCompatibilityClass xref ∧
    ∀ x₀ : Concentration S, x₀ ∈ N.positiveCompatibilityClass xref →
      ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
        (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → Γ t ∈ K

/-- Trajectory-level standard permanence for every positive compatibility class of fixed rates. -/
def GenuinePermanentForRates (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ xref : Concentration S, xref.Positive → N.GenuinePermanentOnPositiveClass κ xref

/-- Pointwise strong persistence for fixed complex-balanced rates already implies convergence
of any genuine positive trajectory to the complex-balanced equilibrium in its class.  This isolates
the persistence input from the stronger class-uniform eventual-absorption API used below. -/
theorem trajectory_converges_of_persistentForRates
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hx₀ : x₀.Positive) (hcompat : N.StoichCompatible x₀ xstar)
    (hpersRates : N.PersistentForRates κ)
    {Γ : ℝ → Concentration S} (hΓ0 : Γ 0 = x₀)
    (hΓd : ∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) :
    Tendsto Γ atTop (𝓝 xstar) := by
  have hpers : N.PersistentFrom κ x₀ := hpersRates x₀ hx₀
  rcases hpers with ⟨K₀, hK₀cpt, hK₀pos, hgen⟩
  have hwr : N.WeaklyReversible :=
    N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  obtain ⟨ϕ, γ, hγ0, hϕγ, hsol, hω⟩ :=
    N.gac_of_persistent hwr κ hxs hcb hx₀ hcompat
      ⟨K₀, hK₀cpt, hK₀pos, hgen⟩
  have horbitK : ∀ t : ℝ≥0, ϕ t x₀ ∈ K₀ := by
    intro t
    rw [hϕγ]
    exact hgen (γ x₀) (hγ0 x₀) hsol (t : ℝ) t.coe_nonneg
  have htendNN : Tendsto (fun t : ℝ≥0 => ϕ t x₀) atTop (𝓝 xstar) := by
    apply hK₀cpt.tendsto_nhds_of_unique_mapClusterPt
    · exact Filter.Eventually.of_forall horbitK
    · intro y _hy hcluster
      have hyω : y ∈ omegaLimit atTop ϕ {x₀} :=
        (mem_omegaLimit_singleton_iff_mapClusterPt atTop ϕ x₀ y).2 hcluster
      rw [hω, Set.mem_singleton_iff] at hyω
      exact hyω
  have htendReal : Tendsto (fun t : ℝ => ϕ (Real.toNNReal t) x₀) atTop (𝓝 xstar) :=
    htendNN.comp Real.tendsto_toNNReal_atTop
  have hevent : (fun t : ℝ => ϕ (Real.toNNReal t) x₀) =ᶠ[atTop] Γ := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hϕγ, Real.coe_toNNReal t ht]
    exact (N.genuineOrbit_unique κ hxs hcb hx₀ hΓ0 (hγ0 x₀)
      hΓd hsol t ht).symm
  exact Filter.Tendsto.congr' hevent htendReal

/-- If the cutoff semiflow through a positive start has no boundary omega-limit points, then
that start has the repository's strong compact-interior persistence certificate.  This is the
omega-boundary analogue of `persistentFrom_of_omegaLimit_singleton`: singleton identification is
not needed for persistence itself. -/
theorem persistentFrom_of_omegaLimit_positive
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hωpos : ∀ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) :
    N.PersistentFrom κ x₀ := by
  set C₀ := relEntropy xstar x₀ with hC₀
  set B : ℝ := 1 + |C₀| + ∑ s, Real.exp 2 * xstar s with hBdef
  have hsumnn : 0 ≤ ∑ s, Real.exp 2 * xstar s :=
    Finset.sum_nonneg fun s _ => (mul_pos (Real.exp_pos 2) (hxs s)).le
  have hBnn : 0 ≤ B := by rw [hBdef]; have := abs_nonneg C₀; linarith
  have hBbig : ∀ s, max (Real.exp 2 * xstar s) C₀ < B := by
    intro s
    have hsum : Real.exp 2 * xstar s ≤ ∑ s', Real.exp 2 * xstar s' :=
      Finset.single_le_sum (fun s' _ => (mul_pos (Real.exp_pos 2) (hxs s')).le) (Finset.mem_univ s)
    rw [max_lt_iff, hBdef]
    exact ⟨by linarith [abs_nonneg C₀], by linarith [le_abs_self C₀]⟩
  have hγ0x0 : γ x₀ 0 = x₀ := hγ0 x₀
  have hΓ0pos : (γ x₀ 0).Positive := by rw [hγ0x0]; exact hx0
  have hpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive := N.genuineOrbit_pos κ hΓ0pos hsol
  have hrele : ∀ t, 0 ≤ t → relEntropy xstar (γ x₀ t) ≤ C₀ := by
    intro t ht
    have := N.genuineOrbit_relEntropy_le κ hxs hcb hpos hsol t ht
    rwa [hγ0x0] at this
  have hboxOf : ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      ∀ t, 0 ≤ t → ∀ s, |Γ t s| ≤ B := by
    intro Γ hΓ0 hΓd t ht s
    have hΓ0p : (Γ 0).Positive := by rw [hΓ0]; exact hx0
    have hp := N.genuineOrbit_pos κ hΓ0p hΓd t ht
    have hre : relEntropy xstar (Γ t) ≤ C₀ := by
      have := N.genuineOrbit_relEntropy_le κ hxs hcb (N.genuineOrbit_pos κ hΓ0p hΓd) hΓd t ht
      rwa [hΓ0] at this
    rw [abs_le]
    exact ⟨by linarith [hp s], le_of_lt (lt_of_le_of_lt
      (relEntropy_coord_le hxs hp.nonnegative hre s) (hBbig s))⟩
  set SC : Set (Concentration S) := {y | y.Nonnegative ∧ relEntropy xstar y ≤ C₀} with hSCdef
  have hSCcpt : IsCompact SC := isCompact_relEntropy_sublevel hxs C₀
  set O : Set (Concentration S) := γ x₀ '' Set.Ici (0 : ℝ) with hOdef
  have hOSC : O ⊆ SC := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨(hpos t ht).nonnegative, hrele t ht⟩
  have hclOSC : closure O ⊆ SC := (IsClosed.closure_subset_iff hSCcpt.isClosed).mpr hOSC
  have hclOcpt : IsCompact (closure O) := hSCcpt.of_isClosed_subset isClosed_closure hclOSC
  have hclOpos : ∀ p ∈ closure O, p.Positive := by
    intro p hp
    by_cases hpO : p ∈ O
    · obtain ⟨t, ht, rfl⟩ := hpO; exact hpos t ht
    · have htail : ∀ T' : ℝ≥0, p ∈ closure (Set.image2 ϕ (Set.Ici T') {x₀}) := by
        intro T'
        have hT0 : (0 : ℝ) ≤ (T' : ℝ) := T'.coe_nonneg
        have hcontOn : ContinuousOn (γ x₀) (Set.Icc 0 (T' : ℝ)) :=
          fun t ht => (hsol t ht.1).continuousAt.continuousWithinAt
        have hdecomp : O = γ x₀ '' Set.Icc 0 (T' : ℝ) ∪ γ x₀ '' Set.Ici (T' : ℝ) := by
          rw [hOdef, ← Set.image_union, Set.Icc_union_Ici_eq_Ici hT0]
        have hcompactInit : IsCompact (γ x₀ '' Set.Icc 0 (T' : ℝ)) :=
          isCompact_Icc.image_of_continuousOn hcontOn
        have hpInTail : p ∈ closure (γ x₀ '' Set.Ici (T' : ℝ)) := by
          have hpcl : p ∈ closure (γ x₀ '' Set.Icc 0 (T' : ℝ))
              ∪ closure (γ x₀ '' Set.Ici (T' : ℝ)) := by
            rw [← closure_union, ← hdecomp]; exact hp
          rcases hpcl with hpic | hpit
          · rw [hcompactInit.isClosed.closure_eq] at hpic
            exact absurd (Set.image_mono Set.Icc_subset_Ici_self hpic) hpO
          · exact hpit
        have hconv : γ x₀ '' Set.Ici (T' : ℝ) = Set.image2 ϕ (Set.Ici T') {x₀} := by
          rw [Set.image2_singleton_right]
          have hfeq : (fun s : ℝ≥0 => ϕ s x₀) = γ x₀ ∘ NNReal.toReal := by
            funext s; exact hϕγ x₀ s
          rw [hfeq, Set.image_comp, NNReal.image_coe_Ici]
        rwa [hconv] at hpInTail
      have hpω : p ∈ omegaLimit atTop ϕ {x₀} := by
        rw [omegaLimit_def]
        simp only [Set.mem_iInter]
        intro u hu
        obtain ⟨a, ha⟩ := Filter.mem_atTop_sets.mp hu
        exact closure_mono (Set.image2_subset (fun b hb => ha b hb) (subset_refl _)) (htail a)
      exact hωpos p hpω
  refine ⟨closure O, hclOcpt, hclOpos, ?_⟩
  intro Γ hΓ0 hΓd t ht
  have heq : Γ t = γ x₀ t :=
    N.genuineOrbit_unique_of_box κ hBnn hΓd hsol (hboxOf Γ hΓ0 hΓd)
      (hboxOf (γ x₀) hγ0x0 hsol) (by rw [hΓ0, hγ0x0]) t ht
  rw [heq]
  exact subset_closure ⟨t, ht, rfl⟩

/-- One positive omega-limit point, together with the standard complex-balanced LaSalle data,
is already enough for the strong compact-interior `PersistentFrom` certificate.  The positive
omega-point collapses the whole omega-limit set to the class equilibrium, after which
`persistentFrom_of_omegaLimit_positive` supplies the compact certificate. -/
theorem persistentFrom_of_omegaLimit_mem_positive
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    (hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t))
    (hex : ∃ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p) :
    N.PersistentFrom κ x₀ := by
  have hwr : N.WeaklyReversible :=
    N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  have hωeq : omegaLimit atTop ϕ {x₀} = {xstar} :=
    N.omegaLimit_eq_singleton_of_mem_positive hwr κ hxs hcb hx0compat hγ0 hϕγ
      hgenω hωnn hωaff hωc hposorbit hex
  apply N.persistentFrom_of_omegaLimit_positive κ hxs hcb hx0 hγ0 hϕγ hsol
  intro p hp
  rw [hωeq, Set.mem_singleton_iff] at hp
  simpa [hp] using hxs

/-- Anderson's carried-siphon comparable-growth descent is sufficient for the strong
`PersistentFrom` certificate once the standard bounded-orbit/LaSalle data are available.  This
isolates the remaining analytic content to the strictly-decreasing carried-critical-siphon step. -/
theorem persistentFrom_of_comparableGrowthDescent
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hKcl : IsClosed K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    (hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t))
    (hdesc : N.ComparableGrowthDescent ϕ x₀) :
    N.PersistentFrom κ x₀ := by
  apply N.persistentFrom_of_omegaLimit_mem_positive κ hxs hcb hx0 hx0compat
    hγ0 hϕγ hsol hgenω hωnn hωaff hωc hposorbit
  exact N.omegaLimit_positive_of_comparableGrowthDescent κ hϕγ hK hKcl hmaps
    hωnn hgenω hωaff hx0 hdesc

/-- **Weak omega-interior certificate for fixed rates.**  For every positive bounded orbit whose
omega-limit dynamics are genuine, nonnegative, and remain in the stoichiometric affine class, the
omega-limit set contains at least one strictly positive point.  This is strictly weaker than
`BoundaryOmegaExcluded`: complex-balanced LaSalle theory upgrades a single positive omega-point to
the full singleton omega-limit conclusion. -/
def PositiveOmegaPointForRates (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S},
    (∀ x (t : ℝ≥0), ϕ t x = γ x t) →
    (∃ K : Set (Concentration S), IsCompact K ∧ ∀ t : ℝ≥0, ϕ t x₀ ∈ K) →
    (∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y) →
    (∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t) →
    (∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace) →
    x₀.Positive →
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive

/-- Boundary omega-exclusion implies the weaker positive-omega-point certificate. -/
theorem positiveOmegaPointForRates_of_boundaryOmegaExcluded
    (N : Network S) (κ : N.RateConstants)
    (hboundary : N.BoundaryOmegaExcluded κ) :
    N.PositiveOmegaPointForRates κ := by
  intro ϕ γ x₀ hϕγ hbounded hωnn hgenω hωaff hx0
  obtain ⟨K, hKcpt, hmaps⟩ := hbounded
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmaps t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem, (IsClosed.closure_subset_iff hKcpt.isClosed).mpr hsubK⟩
  obtain ⟨p, hp⟩ :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hKcpt habs (Set.singleton_nonempty x₀)
  exact ⟨p, hp, hboundary hϕγ ⟨K, hKcpt, hmaps⟩ hωnn hgenω hωaff hx0 p hp⟩

/-- A uniform carried-siphon comparable-growth descent supplies the weak omega-interior certificate.
This exposes Anderson's finite siphon-cardinality descent as one concrete route to the remaining
analytic kernel. -/
def ComparableGrowthDescentForRates (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S},
    (∀ x (t : ℝ≥0), ϕ t x = γ x t) →
    (∃ K : Set (Concentration S), IsCompact K ∧ IsClosed K ∧ ∀ t : ℝ≥0, ϕ t x₀ ∈ K) →
    (∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y) →
    (∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t) →
    (∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace) →
    x₀.Positive →
    N.ComparableGrowthDescent ϕ x₀

/-- Uniform comparable-growth descent implies that every admissible bounded orbit has a positive
omega-limit point. -/
theorem positiveOmegaPointForRates_of_comparableGrowthDescentForRates
    (N : Network S) (κ : N.RateConstants)
    (hdescRates : N.ComparableGrowthDescentForRates κ) :
    N.PositiveOmegaPointForRates κ := by
  intro ϕ γ x₀ hϕγ hbounded hωnn hgenω hωaff hx0
  obtain ⟨K, hKcpt, hmaps⟩ := hbounded
  have hdesc : N.ComparableGrowthDescent ϕ x₀ :=
    hdescRates hϕγ ⟨K, hKcpt, hKcpt.isClosed, hmaps⟩ hωnn hgenω hωaff hx0
  exact N.omegaLimit_positive_of_comparableGrowthDescent κ hϕγ hKcpt hKcpt.isClosed hmaps
    hωnn hgenω hωaff hx0 hdesc

/-- The weak positive-omega-point certificate is sufficient for pointwise strong persistence of
complex-balanced fixed-rate dynamics.  The proof constructs the standard entropy-confined cutoff
flow, obtains one positive omega-point from the certificate, and then uses LaSalle plus
`omegaLimit_eq_singleton_of_mem_positive` to collapse the whole omega-limit set to the unique
complex-balanced equilibrium in the start's compatibility class. -/
theorem complexBalanced_persistentForRates_of_positiveOmegaPointForRates
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hpositiveOmega : N.PositiveOmegaPointForRates κ) :
    N.PersistentForRates κ := by
  intro x₀ hx0
  obtain ⟨xeq, hxeqclass, hxeqcb⟩ :=
    N.exists_isComplexBalanced_in_positiveClass κ hxs hcb hx0
  have hx0compat : N.StoichCompatible x₀ xeq := hxeqclass.1
  set C₀ := relEntropy xeq x₀ with hC₀
  set B : ℝ := 1 + |C₀| + ∑ s, Real.exp 2 * xeq s with hBdef
  have hsumnn : 0 ≤ ∑ s, Real.exp 2 * xeq s :=
    Finset.sum_nonneg fun s _ => (mul_pos (Real.exp_pos 2) (hxeqclass.2 s)).le
  have hBnn : 0 ≤ B := by rw [hBdef]; have := abs_nonneg C₀; linarith
  have hBbig : ∀ s, max (Real.exp 2 * xeq s) C₀ < B := by
    intro s
    have hsum : Real.exp 2 * xeq s ≤ ∑ s', Real.exp 2 * xeq s' :=
      Finset.single_le_sum
        (fun s' _ => (mul_pos (Real.exp_pos 2) (hxeqclass.2 s')).le) (Finset.mem_univ s)
    rw [max_lt_iff, hBdef]
    exact ⟨by linarith [abs_nonneg C₀], by linarith [le_abs_self C₀]⟩
  obtain ⟨L, hLnn, hbound⟩ := N.exists_field_lower_bound κ B
  obtain ⟨Klip, M, hlip, hbd⟩ := N.exists_cutoff κ hBnn
  obtain ⟨ϕ, γ, hγ0, hγd, hϕγ⟩ := ODE.exists_flow hlip hbd
  have hΓd : ∀ t, HasDerivAt (γ x₀) (N.massActionVectorField κ (clampBox B (γ x₀ t))) t :=
    fun t => hγd x₀ t
  have hΓ0pos : Concentration.Positive (γ x₀ 0) := by rw [hγ0]; exact hx0
  have hpos : ∀ t, 0 ≤ t → Concentration.Positive (γ x₀ t) :=
    orbit_pos N κ hBnn hLnn hbound hΓ0pos hΓd
  have hrele : ∀ t, 0 ≤ t → relEntropy xeq (γ x₀ t) ≤ C₀ := by
    have hB' : ∀ s, max (Real.exp 2 * xeq s) (relEntropy xeq (γ x₀ 0)) < B := by
      intro s; rw [hγ0]; exact hBbig s
    intro t ht
    have := orbit_relEntropy_le N κ hxeqclass.2 hxeqcb hpos hΓd hB' t ht
    rw [hγ0, ← hC₀] at this
    exact this
  have hclamp : ∀ t, 0 ≤ t → clampBox B (γ x₀ t) = γ x₀ t := fun t ht =>
    clampBox_eq_of_sublevel hxeqclass.2 (hpos t ht).nonnegative (hrele t ht) hBbig
  have hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t := by
    intro t ht
    have := hΓd t
    rwa [hclamp t ht] at this
  set SC : Set (Concentration S) :=
      {y : Concentration S | Concentration.Nonnegative y ∧ relEntropy xeq y ≤ C₀} with hSCdef
  have hSCcpt : IsCompact SC := isCompact_relEntropy_sublevel hxeqclass.2 C₀
  have horbit_SC : ∀ t : ℝ≥0, ϕ t x₀ ∈ SC := by
    intro t
    rw [hϕγ]
    exact ⟨(hpos t t.coe_nonneg).nonnegative, hrele t t.coe_nonneg⟩
  have hsubSC : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ SC := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact horbit_SC t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ SC :=
    ⟨Set.univ, univ_mem, (IsClosed.closure_subset_iff hSCcpt.isClosed).mpr hsubSC⟩
  have hωSC : omegaLimit atTop ϕ {x₀} ⊆ SC :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
      (u := Set.univ) univ_mem).trans
      ((IsClosed.closure_subset_iff hSCcpt.isClosed).mpr hsubSC)
  have hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y :=
    fun y hy => (hωSC hy).1
  have hSclosed : IsClosed (N.stoichSubspace : Set (Concentration S)) :=
    N.stoichSubspace.closed_of_finiteDimensional
  have haffclosed : IsClosed {z : Concentration S | z - x₀ ∈ N.stoichSubspace} :=
    IsClosed.preimage (continuous_id.sub continuous_const) hSclosed
  have horbit_aff : ∀ t : ℝ≥0, ϕ t x₀ - x₀ ∈ N.stoichSubspace := by
    intro t
    rw [hϕγ]
    have hsol' : ∀ τ ∈ Set.Icc (0 : ℝ) ↑t,
        HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ τ)) τ :=
      fun τ hτ => hsol τ hτ.1
    have := sub_mem_stoichSubspace_of_solution N κ t.coe_nonneg hsol'
    rwa [hγ0] at this
  have hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace := by
    have hsub : omegaLimit atTop ϕ {x₀} ⊆ {z | z - x₀ ∈ N.stoichSubspace} := by
      refine (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
        (u := Set.univ) univ_mem).trans ?_
      refine (IsClosed.closure_subset_iff haffclosed).mpr ?_
      rintro z ⟨t, -, x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact horbit_aff t
    exact fun z hz => hsub hz
  have hyωt_gen : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      γ y t ∈ omegaLimit atTop ϕ {x₀} := by
    intro y hy t ht
    let tNonneg : ℝ≥0 := ⟨t, ht⟩
    have hmem := (Flow.isInvariant_omegaLimit atTop ϕ {x₀}
      (fun s => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id) tNonneg) hy
    have htime : (↑tNonneg : ℝ) = t := rfl
    have hϕ' : ϕ.toFun tNonneg y = γ y t := by
      calc
        ϕ.toFun tNonneg y = γ y ↑tNonneg := hϕγ y tNonneg
        _ = γ y t := congrArg (γ y) htime
    rw [hϕ'] at hmem
    exact hmem
  have hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t := by
    intro y hy t ht
    have hmemω : γ y t ∈ omegaLimit atTop ϕ {x₀} := hyωt_gen y hy t ht
    have hclt : clampBox B (γ y t) = γ y t :=
      clampBox_eq_of_sublevel hxeqclass.2 (hωSC hmemω).1 (hωSC hmemω).2 hBbig
    rw [← hclt]
    exact hγd y t
  have hex : ∃ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p :=
    hpositiveOmega hϕγ ⟨SC, hSCcpt, horbit_SC⟩ hωnn hgenω hωaff hx0
  have hAnti : AntitoneOn (fun t => relEntropy xeq (γ x₀ t)) (Set.Ici 0) := by
    have hcont : Continuous (fun t => relEntropy xeq (γ x₀ t)) :=
      (relEntropy_continuous hxeqclass.2).comp
        (Differentiable.continuous fun t => (hΓd t).differentiableAt)
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn ?_ ?_
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      exact (relEntropy_hasDerivAt hxeqclass.2 (hpos t ht.le)
        (fun s => (hasDerivAt_pi.mp (hsol t ht.le)) s)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(relEntropy_hasDerivAt hxeqclass.2 (hpos t ht.le)
        (fun s => (hasDerivAt_pi.mp (hsol t ht.le)) s)).deriv]
      exact dissipation_nonpos N κ (hpos t ht.le) hxeqclass.2 hxeqcb
  have hmono : ∀ a b : ℝ≥0, a ≤ b →
      relEntropy xeq (ϕ b x₀) ≤ relEntropy xeq (ϕ a x₀) := by
    intro a b hab
    rw [hϕγ, hϕγ]
    exact hAnti (Set.mem_Ici.mpr a.coe_nonneg) (Set.mem_Ici.mpr b.coe_nonneg)
      (by exact_mod_cast hab)
  obtain ⟨c, _, hωinv, hωc⟩ :=
    Flow.laSalle ϕ (relEntropy_continuous hxeqclass.2) x₀ hSCcpt habs hmono
  have hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t) := by
    intro p hp hpp t ht
    have hp0 : Concentration.Positive (γ p 0) := by rw [hγ0]; exact hpp
    exact N.genuineOrbit_pos κ hp0 (hgenω p hp) t ht
  exact N.persistentFrom_of_omegaLimit_mem_positive κ hxeqclass.2 hxeqcb hx0 hx0compat
    hγ0 hϕγ hsol hgenω hωnn hωaff hωc hposorbit hex

/-- The orbit-local omega-boundary exclusion predicate is already sufficient to produce
`PersistentForRates` for complex-balanced rates.  The only flow used here is the standard globally
Lipschitz cutoff flow; entropy confinement makes the cutoff collapse on the orbit and on its
omega-limit set, so `BoundaryOmegaExcluded` applies to the genuine mass-action dynamics there. -/
theorem complexBalanced_persistentForRates_of_boundaryOmegaExcluded
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hboundary : N.BoundaryOmegaExcluded κ) :
    N.PersistentForRates κ := by
  intro x₀ hx0
  set C₀ := relEntropy xstar x₀ with hC₀
  set B : ℝ := 1 + |C₀| + ∑ s, Real.exp 2 * xstar s with hBdef
  have hsumnn : 0 ≤ ∑ s, Real.exp 2 * xstar s :=
    Finset.sum_nonneg fun s _ => (mul_pos (Real.exp_pos 2) (hxs s)).le
  have hBnn : 0 ≤ B := by rw [hBdef]; have := abs_nonneg C₀; linarith
  have hBbig : ∀ s, max (Real.exp 2 * xstar s) C₀ < B := by
    intro s
    have hsum : Real.exp 2 * xstar s ≤ ∑ s', Real.exp 2 * xstar s' :=
      Finset.single_le_sum (fun s' _ => (mul_pos (Real.exp_pos 2) (hxs s')).le) (Finset.mem_univ s)
    rw [max_lt_iff, hBdef]
    exact ⟨by linarith [abs_nonneg C₀], by linarith [le_abs_self C₀]⟩
  obtain ⟨L, hLnn, hbound⟩ := N.exists_field_lower_bound κ B
  obtain ⟨Klip, M, hlip, hbd⟩ := N.exists_cutoff κ hBnn
  obtain ⟨ϕ, γ, hγ0, hγd, hϕγ⟩ := ODE.exists_flow hlip hbd
  have hΓd : ∀ t, HasDerivAt (γ x₀) (N.massActionVectorField κ (clampBox B (γ x₀ t))) t :=
    fun t => hγd x₀ t
  have hΓ0pos : Concentration.Positive (γ x₀ 0) := by rw [hγ0]; exact hx0
  have hpos : ∀ t, 0 ≤ t → Concentration.Positive (γ x₀ t) :=
    orbit_pos N κ hBnn hLnn hbound hΓ0pos hΓd
  have hrele : ∀ t, 0 ≤ t → relEntropy xstar (γ x₀ t) ≤ C₀ := by
    have hB' : ∀ s, max (Real.exp 2 * xstar s) (relEntropy xstar (γ x₀ 0)) < B := by
      intro s; rw [hγ0]; exact hBbig s
    intro t ht
    have := orbit_relEntropy_le N κ hxs hcb hpos hΓd hB' t ht
    rw [hγ0, ← hC₀] at this
    exact this
  have hclamp : ∀ t, 0 ≤ t → clampBox B (γ x₀ t) = γ x₀ t := fun t ht =>
    clampBox_eq_of_sublevel hxs (hpos t ht).nonnegative (hrele t ht) hBbig
  have hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t := by
    intro t ht
    have := hΓd t
    rwa [hclamp t ht] at this
  set SC : Set (Concentration S) :=
      {y : Concentration S | Concentration.Nonnegative y ∧ relEntropy xstar y ≤ C₀} with hSCdef
  have hSCcpt : IsCompact SC := isCompact_relEntropy_sublevel hxs C₀
  have horbit_SC : ∀ t : ℝ≥0, ϕ t x₀ ∈ SC := by
    intro t
    rw [hϕγ]
    exact ⟨(hpos t t.coe_nonneg).nonnegative, hrele t t.coe_nonneg⟩
  have hsubSC : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ SC := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact horbit_SC t
  have hωSC : omegaLimit atTop ϕ {x₀} ⊆ SC :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
      (u := Set.univ) univ_mem).trans
      ((IsClosed.closure_subset_iff hSCcpt.isClosed).mpr hsubSC)
  have hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y :=
    fun y hy => (hωSC hy).1
  have hSclosed : IsClosed (N.stoichSubspace : Set (Concentration S)) :=
    N.stoichSubspace.closed_of_finiteDimensional
  have haffclosed : IsClosed {z : Concentration S | z - x₀ ∈ N.stoichSubspace} :=
    IsClosed.preimage (continuous_id.sub continuous_const) hSclosed
  have horbit_aff : ∀ t : ℝ≥0, ϕ t x₀ - x₀ ∈ N.stoichSubspace := by
    intro t
    rw [hϕγ]
    have hsol' : ∀ τ ∈ Set.Icc (0 : ℝ) ↑t,
        HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ τ)) τ :=
      fun τ hτ => hsol τ hτ.1
    have := sub_mem_stoichSubspace_of_solution N κ t.coe_nonneg hsol'
    rwa [hγ0] at this
  have hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace := by
    have hsub : omegaLimit atTop ϕ {x₀} ⊆ {z | z - x₀ ∈ N.stoichSubspace} := by
      refine (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
        (u := Set.univ) univ_mem).trans ?_
      refine (IsClosed.closure_subset_iff haffclosed).mpr ?_
      rintro z ⟨t, -, x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact horbit_aff t
    exact fun z hz => hsub hz
  have hyωt_gen : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      γ y t ∈ omegaLimit atTop ϕ {x₀} := by
    intro y hy t ht
    let tNonneg : ℝ≥0 := ⟨t, ht⟩
    have hmem := (Flow.isInvariant_omegaLimit atTop ϕ {x₀}
      (fun s => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id) tNonneg) hy
    have htime : (↑tNonneg : ℝ) = t := rfl
    have hϕ' : ϕ.toFun tNonneg y = γ y t := by
      calc
        ϕ.toFun tNonneg y = γ y ↑tNonneg := hϕγ y tNonneg
        _ = γ y t := congrArg (γ y) htime
    rw [hϕ'] at hmem
    exact hmem
  have hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t := by
    intro y hy t ht
    have hmemω : γ y t ∈ omegaLimit atTop ϕ {x₀} := hyωt_gen y hy t ht
    have hclt : clampBox B (γ y t) = γ y t :=
      clampBox_eq_of_sublevel hxs (hωSC hmemω).1 (hωSC hmemω).2 hBbig
    rw [← hclt]
    exact hγd y t
  have hωpos : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive y := by
    intro y hy
    exact hboundary hϕγ ⟨SC, hSCcpt, horbit_SC⟩ hωnn hgenω hωaff hx0 y hy
  exact N.persistentFrom_of_omegaLimit_positive κ hxs hcb hx0 hγ0 hϕγ hsol hωpos

/-- For complex-balanced fixed rates, the repository's pointwise compact persistence certificate
already upgrades to the class-uniform eventual compactness formulation used by
`GenuinePermanentForRates`.  Consequently the genuinely new kernel needed below can be reduced to
`PersistentForRates κ`. -/
theorem complexBalanced_genuinePermanent_of_persistentForRates
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hpersRates : N.PersistentForRates κ) :
    N.GenuinePermanentForRates κ := by
  intro xref hxref
  obtain ⟨xeq, hxeqclass, hxeqcb⟩ :=
    N.exists_isComplexBalanced_in_positiveClass κ hxs hcb hxref
  have hopenPos : IsOpen ({y : Concentration S | y.Positive} : Set (Concentration S)) := by
    have heq : ({y : Concentration S | y.Positive} : Set (Concentration S)) =
        ⋂ s : S, {y : Concentration S | 0 < y s} := by
      ext y
      simp [Concentration.Positive]
    rw [heq]
    exact isOpen_iInter_of_finite fun s => isOpen_lt continuous_const (continuous_apply s)
  obtain ⟨ε, hεpos, hball⟩ := (Metric.isOpen_iff.mp hopenPos) xeq hxeqclass.2
  let r : ℝ := ε / 2
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < ε := by dsimp [r]; linarith
  let K : Set (Concentration S) := Metric.closedBall xeq r ∩ N.compatibilityClass xref
  refine ⟨K, ?_, ?_, ?_⟩
  · have hSclosed : IsClosed (N.stoichSubspace : Set (Concentration S)) :=
      N.stoichSubspace.closed_of_finiteDimensional
    have hclassClosed : IsClosed (N.compatibilityClass xref) :=
      IsClosed.preimage (continuous_id.sub continuous_const) hSclosed
    exact (isCompact_closedBall xeq r).inter_right hclassClosed
  · intro y hy
    refine ⟨hy.2, ?_⟩
    apply hball
    exact Metric.closedBall_subset_ball hrlt hy.1
  · intro x₀ hx₀class Γ hΓ0 hΓd
    have hx₀xeq : N.StoichCompatible x₀ xeq := hx₀class.1.symm.trans hxeqclass.1
    have htend : Tendsto Γ atTop (𝓝 xeq) :=
      N.trajectory_converges_of_persistentForRates κ hxeqclass.2 hxeqcb
        hx₀class.2 hx₀xeq hpersRates hΓ0 hΓd
    have hev : ∀ᶠ t : ℝ in atTop, Γ t ∈ Metric.ball xeq r :=
      htend (Metric.ball_mem_nhds xeq hrpos)
    obtain ⟨T₀, hT₀⟩ := (Filter.mem_atTop_sets.mp hev)
    let T : ℝ := max 0 T₀
    refine ⟨T, le_max_left 0 T₀, ?_⟩
    intro t ht
    have htT₀ : T₀ ≤ t := (le_max_right 0 T₀).trans ht
    have hΓball : Γ t ∈ Metric.ball xeq r := hT₀ t htT₀
    have ht0 : 0 ≤ t := (le_max_left 0 T₀).trans ht
    have hdisp : Γ t - Γ 0 ∈ N.stoichSubspace :=
      N.sub_mem_stoichSubspace_of_solution κ ht0 (fun u hu => hΓd u hu.1)
    have hx₀Γ : N.StoichCompatible x₀ (Γ t) := by
      rw [Network.StoichCompatible, ← hΓ0]
      exact hdisp
    refine ⟨Metric.ball_subset_closedBall hΓball, ?_⟩
    exact hx₀class.1.trans hx₀Γ

/-- The weak omega-interior certificate is sufficient for the exact class-uniform genuine
permanence API consumed by the Global Attractor Theorem. -/
theorem complexBalanced_genuinePermanent_of_positiveOmegaPointForRates
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hpositiveOmega : N.PositiveOmegaPointForRates κ) :
    N.GenuinePermanentForRates κ :=
  N.complexBalanced_genuinePermanent_of_persistentForRates κ hxs hcb
    (N.complexBalanced_persistentForRates_of_positiveOmegaPointForRates κ hxs hcb hpositiveOmega)

/-- Uniform Anderson-style carried-siphon descent is a sufficient analytic certificate for
the full class-uniform complex-balanced permanence conclusion. -/
theorem complexBalanced_genuinePermanent_of_comparableGrowthDescentForRates
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hdescRates : N.ComparableGrowthDescentForRates κ) :
    N.GenuinePermanentForRates κ :=
  N.complexBalanced_genuinePermanent_of_positiveOmegaPointForRates κ hxs hcb
    (N.positiveOmegaPointForRates_of_comparableGrowthDescentForRates κ hdescRates)

/-- The no-critical-siphon structural regime closes the exact trajectory-level permanence API as a
special case of the general omega-boundary interface. -/
theorem complexBalanced_genuinePermanent_of_hasNoCriticalSiphon
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hncs : N.HasNoCriticalSiphon) :
    N.GenuinePermanentForRates κ :=
  N.complexBalanced_genuinePermanent_of_positiveOmegaPointForRates κ hxs hcb
    (N.positiveOmegaPointForRates_of_boundaryOmegaExcluded κ
      (N.boundaryOmegaExcluded_of_hasNoCriticalSiphon κ hncs))

/-- For complex-balanced rates, omega-boundary exclusion is enough for the exact class-uniform
permanence API consumed by the Global Attractor Theorem. -/
theorem complexBalanced_genuinePermanent_of_boundaryOmegaExcluded
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hboundary : N.BoundaryOmegaExcluded κ) :
    N.GenuinePermanentForRates κ :=
  N.complexBalanced_genuinePermanent_of_persistentForRates κ hxs hcb
    (N.complexBalanced_persistentForRates_of_boundaryOmegaExcluded κ hxs hcb hboundary)

/-- **Deep permanence kernel for the Global Attractor Theorem.**  Every positive
complex-balanced mass-action system is class-uniformly permanent for genuine forward
trajectories.  This is the toric-differential-inclusion / zero-separating-surface content of
Craciun's theorem, stated without the potentially vacuous assumption of a global ambient flow. -/
theorem complexBalanced_genuinePermanent
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.GenuinePermanentForRates κ := by
  apply N.complexBalanced_genuinePermanent_of_positiveOmegaPointForRates κ hxs hcb
  -- Remaining deep kernel, now in its weakest orbit form used by the proof: every positive bounded
  -- orbit whose omega-limit dynamics are genuine/nonnegative/stoichiometrically compatible has
  -- at least one strictly positive omega-limit point.  Complex-balanced LaSalle theory above then
  -- upgrades that single interior omega-point to the full singleton omega-limit and permanence.
  sorry

/-- The trajectory-level permanence theorem implies the older flow-quantified standard
permanence API whenever a genuine global mass-action flow is supplied. -/
theorem complexBalanced_permanent
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.PermanentForRates κ := by
  intro ϕ γ hflow xref hxref
  obtain ⟨K, hKcpt, hKclass, habs⟩ :=
    N.complexBalanced_genuinePermanent κ hxs hcb xref hxref
  refine ⟨K, hKcpt, hKclass, ?_⟩
  intro x₀ hxclass
  rcases hflow with ⟨hγ0, hϕγ, hγd⟩
  obtain ⟨T, hT0, htail⟩ := habs x₀ hxclass (γ x₀) (hγ0 x₀) (hγd x₀)
  let a : ℝ≥0 := ⟨T, hT0⟩
  refine ⟨Set.Ici a, Filter.Ici_mem_atTop a, ?_⟩
  rw [IsClosed.closure_subset_iff hKcpt.isClosed]
  rintro y ⟨t, ht, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at hx
  subst x
  rw [hϕγ]
  apply htail (t : ℝ)
  change T ≤ (t : ℝ)
  exact_mod_cast ht

/-- Eventual class-uniform genuine permanence plus genuine-orbit uniqueness upgrades one
specified genuine trajectory to the all-time compact persistence certificate consumed by the
cutoff-flow GAC machinery. -/
theorem GenuinePermanentOnPositiveClass.persistentFrom_of_trajectory
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hperm : N.GenuinePermanentOnPositiveClass κ xstar)
    (hxclass : x₀ ∈ N.positiveCompatibilityClass xstar)
    {Γ : ℝ → Concentration S} (hΓ0 : Γ 0 = x₀)
    (hΓd : ∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) :
    N.PersistentFrom κ x₀ := by
  obtain ⟨K, hKcpt, hKclass, habs⟩ := hperm
  obtain ⟨T, hT0, htail⟩ := habs x₀ hxclass Γ hΓ0 hΓd
  have hx₀ : x₀.Positive := hxclass.2
  have hΓpos : ∀ t, 0 ≤ t → (Γ t).Positive := by
    apply N.genuineOrbit_pos κ
    · simpa [hΓ0] using hx₀
    · exact hΓd
  have hcont : ContinuousOn Γ (Set.Icc (0 : ℝ) T) :=
    fun t ht => (hΓd t ht.1).continuousAt.continuousWithinAt
  have hIcpt : IsCompact (Γ '' Set.Icc (0 : ℝ) T) :=
    isCompact_Icc.image_of_continuousOn hcont
  let K₀ : Set (Concentration S) := Γ '' Set.Icc (0 : ℝ) T ∪ K
  refine ⟨K₀, hIcpt.union hKcpt, ?_, ?_⟩
  · intro y hy
    rcases hy with hy | hy
    · rcases hy with ⟨t, ht, rfl⟩
      exact hΓpos t ht.1
    · exact (hKclass hy).2
  · intro Ψ hΨ0 hΨd t ht
    have heq : Ψ t = Γ t :=
      N.genuineOrbit_unique κ hxs hcb hx₀ hΨ0 hΓ0 hΨd hΓd t ht
    rw [heq]
    by_cases htT : t ≤ T
    · exact Set.mem_union_left K ⟨t, ⟨ht, htT⟩, rfl⟩
    · exact Set.mem_union_right _ (htail t (le_of_lt (lt_of_not_ge htT)))

/-- **Global Attractor Theorem.** A positive complex-balanced equilibrium globally attracts
its entire positive stoichiometric compatibility class. -/
theorem complexBalanced_globalAttractor
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.HasGlobalAttractorProperty κ xstar := by
  intro ϕ γ hflow
  refine ⟨hflow, ?_⟩
  intro x₀ hx₀ hcompat
  have hpermClass : N.PermanentOnPositiveClass ϕ xstar :=
    N.complexBalanced_permanent κ hxs hcb ϕ γ hflow xstar hxs
  have hx₀class : x₀ ∈ N.positiveCompatibilityClass xstar :=
    ⟨hcompat.symm, hx₀⟩
  have hpermOrbit : Permanent ϕ x₀ := hpermClass.permanent hx₀class
  rcases hflow with ⟨hγ0, hϕγ, hγd⟩
  have hwr : N.WeaklyReversible :=
    N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  have hpos : ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ x₀ t) :=
    N.genuineOrbit_pos κ (by simpa [hγ0] using hx₀) (hγd x₀)
  have hcontOn : ContinuousOn (fun t : ℝ => relEntropy xstar (γ x₀ t)) (Set.Ici 0) := by
    intro t ht
    exact (relEntropy_continuous hxs).continuousAt.comp_continuousWithinAt
      ((hγd x₀ t ht).continuousAt.continuousWithinAt)
  have hAnti : AntitoneOn (fun t : ℝ => relEntropy xstar (γ x₀ t)) (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcontOn ?_ ?_
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      exact (relEntropy_hasDerivAt hxs (hpos t ht.le)
        (fun s => (hasDerivAt_pi.mp (hγd x₀ t ht.le)) s)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(relEntropy_hasDerivAt hxs (hpos t ht.le)
        (fun s => (hasDerivAt_pi.mp (hγd x₀ t ht.le)) s)).deriv]
      exact dissipation_nonpos N κ (hpos t ht.le) hxs hcb
  have hmono : ∀ a b : ℝ≥0, a ≤ b →
      relEntropy xstar (ϕ b x₀) ≤ relEntropy xstar (ϕ a x₀) := by
    intro a b hab
    rw [hϕγ, hϕγ]
    exact hAnti (Set.mem_Ici.mpr a.coe_nonneg) (Set.mem_Ici.mpr b.coe_nonneg)
      (by exact_mod_cast hab)
  rcases hpermOrbit with ⟨K, hKcpt, hKpos, v, hv, hvK⟩
  obtain ⟨c, _, _hωinv, hωc⟩ :=
    Flow.laSalle ϕ (relEntropy_continuous hxs) x₀ hKcpt ⟨v, hv, hvK⟩ hmono
  have hωK : omegaLimit atTop ϕ {x₀} ⊆ K := by
    exact (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) hv).trans hvK
  have hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y := by
    intro y hy
    exact (hKpos y (hωK hy)).nonnegative
  have hSclosed : IsClosed (N.stoichSubspace : Set (Concentration S)) :=
    N.stoichSubspace.closed_of_finiteDimensional
  have haffclosed : IsClosed {z : Concentration S | z - x₀ ∈ N.stoichSubspace} :=
    IsClosed.preimage (continuous_id.sub continuous_const) hSclosed
  have horbit_aff : ∀ t : ℝ≥0, ϕ t x₀ - x₀ ∈ N.stoichSubspace := by
    intro t
    rw [hϕγ]
    have hsol' : ∀ τ ∈ Set.Icc (0:ℝ) ↑t,
        HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ τ)) τ :=
      fun τ hτ => hγd x₀ τ hτ.1
    have hs := sub_mem_stoichSubspace_of_solution N κ t.coe_nonneg hsol'
    rwa [hγ0] at hs
  have hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace := by
    have hsub : omegaLimit atTop ϕ {x₀} ⊆ {z | z - x₀ ∈ N.stoichSubspace} := by
      refine (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ)
        univ_mem).trans ?_
      refine (IsClosed.closure_subset_iff haffclosed).mpr ?_
      rintro z ⟨t, -, x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact horbit_aff t
    exact fun z hz => hsub hz
  have hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t := by
    intro y _ t ht
    exact hγd y t ht
  have hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t) := by
    intro p _ hp
    apply N.genuineOrbit_pos κ
    · simpa [hγ0] using hp
    · exact hγd p
  apply N.gac_of_permanent hwr κ hxs hcb hcompat hγ0 hϕγ hgenω hωnn hωaff hωc hposorbit
  exact ⟨K, hKcpt, hKpos, v, hv, hvK⟩

/-- The theorem does not need weak reversibility as a separate hypothesis: existence of a
positive complex-balanced equilibrium already implies weak reversibility. -/
theorem globalAttractor_implies_weaklyReversible
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) : N.WeaklyReversible := by
  exact N.weaklyReversible_of_positive_complexBalanced κ hxs hcb

/-- Trajectory-level convergence formulation of the Global Attractor Theorem. -/
def PositiveClassTrajectoryConverges (N : Network S) (κ : N.RateConstants)
    (xstar : Concentration S) : Prop :=
  ∀ γ : ℝ → Concentration S,
    γ 0 |>.Positive →
    N.StoichCompatible (γ 0) xstar →
    (∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) →
    Tendsto γ atTop (𝓝 xstar)

/-- Equivalent convergence form: every genuine positive trajectory in the class tends to the
complex-balanced equilibrium. -/
theorem complexBalanced_trajectory_converges
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.PositiveClassTrajectoryConverges κ xstar := by
  intro Γ hΓ0pos hcompat hΓd
  have hxclass : Γ 0 ∈ N.positiveCompatibilityClass xstar :=
    ⟨hcompat.symm, hΓ0pos⟩
  have hpermClass : N.GenuinePermanentOnPositiveClass κ xstar :=
    N.complexBalanced_genuinePermanent κ hxs hcb xstar hxs
  have hpers : N.PersistentFrom κ (Γ 0) :=
    GenuinePermanentOnPositiveClass.persistentFrom_of_trajectory
      (N := N) κ hxs hcb hpermClass hxclass rfl hΓd
  rcases hpers with ⟨K₀, hK₀cpt, hK₀pos, hgen⟩
  have hwr : N.WeaklyReversible :=
    N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  obtain ⟨ϕ, γ, hγ0, hϕγ, hsol, hω⟩ :=
    N.gac_of_persistent hwr κ hxs hcb hΓ0pos hcompat
      ⟨K₀, hK₀cpt, hK₀pos, hgen⟩
  have horbitK : ∀ t : ℝ≥0, ϕ t (Γ 0) ∈ K₀ := by
    intro t
    rw [hϕγ]
    exact hgen (γ (Γ 0)) (hγ0 (Γ 0)) hsol (t : ℝ) t.coe_nonneg
  have htendNN : Tendsto (fun t : ℝ≥0 => ϕ t (Γ 0)) atTop (𝓝 xstar) := by
    apply hK₀cpt.tendsto_nhds_of_unique_mapClusterPt
    · exact Filter.Eventually.of_forall horbitK
    · intro y _hy hcluster
      have hyω : y ∈ omegaLimit atTop ϕ {Γ 0} :=
        (mem_omegaLimit_singleton_iff_mapClusterPt atTop ϕ (Γ 0) y).2 hcluster
      rw [hω, Set.mem_singleton_iff] at hyω
      exact hyω
  have htendReal : Tendsto (fun t : ℝ => ϕ (Real.toNNReal t) (Γ 0)) atTop (𝓝 xstar) :=
    htendNN.comp Real.tendsto_toNNReal_atTop
  have hevent : (fun t : ℝ => ϕ (Real.toNNReal t) (Γ 0)) =ᶠ[atTop] Γ := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hϕγ, Real.coe_toNNReal t ht]
    exact (N.genuineOrbit_unique κ hxs hcb hΓ0pos rfl (hγ0 (Γ 0))
      hΓd hsol t ht).symm
  exact Filter.Tendsto.congr' hevent htendReal

/-- Every positive class of a complex-balanced system has exactly one positive equilibrium and
that equilibrium is globally asymptotically stable relative to the class. -/
theorem complexBalanced_uniqueGlobalEquilibrium_in_class
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hx₀ : x₀.Positive) :
    ∃! x : Concentration S,
      N.StoichCompatible x₀ x ∧ x.Positive ∧ N.IsMassActionSteadyState κ x := by
  have hwr : N.WeaklyReversible :=
    N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  obtain ⟨x, hxclass, hxcb⟩ :=
    N.exists_isComplexBalanced_in_positiveClass κ hxs hcb hx₀
  refine ⟨x, ⟨hxclass.1, hxclass.2, hxcb.isMassActionSteadyState N κ⟩, ?_⟩
  intro y hy
  have hycb : N.IsComplexBalanced κ y := by
    apply N.complexBalanced_of_dissipation_eq_zero κ hy.2.1 hxs hcb
    apply Finset.sum_eq_zero
    intro s _
    rw [hy.2.2 s, mul_zero]
  exact N.isComplexBalanced_unique_in_positiveClass
    (x₀ := x₀) (x := x) (y := y) hwr κ
    hxclass ⟨hy.1, hy.2.1⟩ hxcb hycb |>.symm

end Network
end CRNT

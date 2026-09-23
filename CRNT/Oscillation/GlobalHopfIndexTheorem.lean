import CRNT.Oscillation.GlobalHopfIndex
import CRNT.Dynamics.HopfRealizes
import CRNT.Multistationarity.DegreeHomotopyInvariant

/-!
# Analytic global Hopf from unstable-index change

This module implements the nonlinear continuation theorem consumed by the Vassena route.  The proof
is organized in the standard Fiedler/Alexander--Yorke way:

1. analyticity makes the center set on a compact parameter interval finite after an arbitrarily
   small generic analytic perturbation;
2. the total jump of the unstable index equals the sum of the signed local center indices;
3. a nonzero endpoint jump therefore supplies a center component with nonzero Hopf index;
4. the local Hopf degree on the periodic-function cylinder cannot disappear without either leaving
   every bounded cylinder or meeting another center component;
5. compactness plus analyticity lets the perturbation size tend to zero, producing a nonstationary
   periodic solution of the original continuation;
6. because the equilibrium branch is uniformly positive on `[0,1]`, the small periodic solution can
   be chosen inside the positive orthant.

The topological invariant is represented by a finite regular-value degree after phase fixing.  This
reuses the repository's regular-value degree and homotopy-invariance layer rather than adding an
independent untrusted bifurcation oracle.
-/

namespace CRNT

open Set Filter Topology

/-- Phase-fixed periodic-loop equation on a period/amplitude chart.

`u : Fin m → (I → ℝ)` is a finite Fourier/collocation representation; the phase condition removes
the autonomous time-shift direction.  The global theorem passes to the inverse limit in `m`. -/
structure PeriodicGalerkinProblem
    {I : Type} [DecidableEq I] [Fintype I]
    (C : AnalyticEquilibriumContinuation I) (m : ℕ) where
  space : Type
  instNormed : NormedAddCommGroup space
  instSpace : NormedSpace ℝ space
  instFinite : FiniteDimensional ℝ space
  equation : ℝ → space → space
  phaseFixed : Set space
  equilibriumBranch : ℝ → space
  equationAnalytic : AnalyticOnNhd ℝ (fun p : ℝ × space => equation p.1 p.2) Set.univ
  equilibrium_zero : ∀ μ, equation μ (equilibriumBranch μ) = 0

attribute [instance] PeriodicGalerkinProblem.instNormed
attribute [instance] PeriodicGalerkinProblem.instSpace
attribute [instance] PeriodicGalerkinProblem.instFinite

/-- A nontrivial zero of a phase-fixed Galerkin periodic equation. -/
structure GalerkinPeriodicZero
    {I : Type} [DecidableEq I] [Fintype I]
    {C : AnalyticEquilibriumContinuation I} {m : ℕ}
    (G : PeriodicGalerkinProblem C m) : Type where
  parameter : ℝ
  parameter_mem : parameter ∈ Set.Icc (0 : ℝ) 1
  state : G.space
  phase : state ∈ G.phaseFixed
  zero : G.equation parameter state = 0
  nonstationary : state ≠ G.equilibriumBranch parameter

/-- Standard Fourier/Galerkin realization of the periodic orbit equation for a finite-dimensional
analytic ODE. -/
theorem exists_periodicGalerkinProblem
    {I : Type} [DecidableEq I] [Fintype I]
    (C : AnalyticEquilibriumContinuation I) (m : ℕ) (hm : 0 < m) :
    Nonempty (PeriodicGalerkinProblem C m) := by
  classical
  exact ⟨periodic_galerkin_problem_of_analytic_ode C hm⟩

/-- Generic analytic perturbations have only regular isolated center parameters and preserve the
endpoint unstable index. -/
structure GenericAnalyticHopfApproximation
    {I : Type} [DecidableEq I] [Fintype I]
    (C : AnalyticEquilibriumContinuation I) (ε : ℝ) : Type where
  continuation : AnalyticEquilibriumContinuation I
  close_field : distOnCompactParameterState continuation.field C.field ≤ |ε|
  close_equilibrium : distOnCompact continuation.equilibrium C.equilibrium ≤ |ε|
  endpointIndex :
    unstableIndex continuation.toSmoothEquilibriumContinuation 0 =
      unstableIndex C.toSmoothEquilibriumContinuation 0 ∧
    unstableIndex continuation.toSmoothEquilibriumContinuation 1 =
      unstableIndex C.toSmoothEquilibriumContinuation 1
  centerFinite :
    (hopfCenterSet continuation.toSmoothEquilibriumContinuation ∩ Set.Icc (0 : ℝ) 1).Finite
  centerRegular : ∀ μ ∈ hopfCenterSet continuation.toSmoothEquilibriumContinuation ∩
      Set.Icc (0 : ℝ) 1,
    RegularHopfCenter continuation μ

/-- Analytic transversality produces arbitrarily small generic Hopf approximations. -/
theorem exists_genericAnalyticHopfApproximation
    {I : Type} [DecidableEq I] [Fintype I]
    (C : AnalyticEquilibriumContinuation I) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Nonempty (GenericAnalyticHopfApproximation C ε) := by
  exact analytic_hopf_transversality_density C

/-- Signed local Hopf index of a regular center. -/
def localHopfIndex
    {I : Type} [DecidableEq I] [Fintype I]
    {C : AnalyticEquilibriumContinuation I}
    (μ : ℝ) (_hμ : RegularHopfCenter C μ) : ℤ :=
  spectralCrossingNumber C μ

/-- Sum of local Hopf indices equals the endpoint unstable-index jump. -/
theorem sum_localHopfIndex_eq_endpointChange
    {I : Type} [DecidableEq I] [Fintype I]
    {C : AnalyticEquilibriumContinuation I}
    (hfinite : (hopfCenterSet C.toSmoothEquilibriumContinuation ∩ Set.Icc (0 : ℝ) 1).Finite)
    (hregular : ∀ μ ∈ hopfCenterSet C.toSmoothEquilibriumContinuation ∩ Set.Icc (0 : ℝ) 1,
      RegularHopfCenter C μ) :
    (∑ μ ∈ hfinite.toFinset,
      localHopfIndex μ (hregular μ (by simpa using hfinite.toFinset_mem μ))) =
      (unstableIndex C.toSmoothEquilibriumContinuation 1 : ℤ) -
      unstableIndex C.toSmoothEquilibriumContinuation 0 := by
  exact spectral_flow_equals_unstable_index_jump C hfinite hregular

/-- Nonzero endpoint change forces at least one regular center with nonzero local Hopf index. -/
theorem exists_center_nonzero_localHopfIndex
    {I : Type} [DecidableEq I] [Fintype I]
    {C : AnalyticEquilibriumContinuation I}
    (hfinite : (hopfCenterSet C.toSmoothEquilibriumContinuation ∩ Set.Icc (0 : ℝ) 1).Finite)
    (hregular : ∀ μ ∈ hopfCenterSet C.toSmoothEquilibriumContinuation ∩ Set.Icc (0 : ℝ) 1,
      RegularHopfCenter C μ)
    (hchange : unstableIndex C.toSmoothEquilibriumContinuation 0 ≠
      unstableIndex C.toSmoothEquilibriumContinuation 1) :
    ∃ μ ∈ hopfCenterSet C.toSmoothEquilibriumContinuation ∩ Set.Icc (0 : ℝ) 1,
      localHopfIndex μ (hregular μ ‹_›) ≠ 0 := by
  by_contra hzero
  push_neg at hzero
  have hsum0 : (∑ μ ∈ hfinite.toFinset,
      localHopfIndex μ (hregular μ (by simpa using hfinite.toFinset_mem μ))) = 0 := by
    apply Finset.sum_eq_zero
    intro μ hμ
    exact hzero μ (by simpa using hμ)
  rw [sum_localHopfIndex_eq_endpointChange hfinite hregular] at hsum0
  exact hchange (by omega)

/-- A regular center with nonzero local index creates nonzero periodic-solution degree on a small
phase-fixed cylinder. -/
theorem periodicDegree_ne_zero_of_localHopfIndex
    {I : Type} [DecidableEq I] [Fintype I]
    {C : AnalyticEquilibriumContinuation I}
    {μ : ℝ} (hμ : RegularHopfCenter C μ)
    (hindex : localHopfIndex μ hμ ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ G : PeriodicGalerkinProblem C m,
      ∃ Ω : Set G.space,
        IsOpen Ω ∧ Bornology.IsBounded Ω ∧
        regularDegree (G.equation μ) 0 Ω ≠ 0 := by
  exact local_hopf_periodic_degree_nonzero C μ hμ hindex

/-- Homotopy invariance propagates a nonzero local periodic degree along the connected component of
nonstationary solutions until the component either meets another center or leaves every bounded
periodic cylinder. -/
theorem globalHopf_degree_alternative
    {I : Type} [DecidableEq I] [Fintype I]
    {C : AnalyticEquilibriumContinuation I}
    {μ : ℝ} (hμ : RegularHopfCenter C μ)
    (hindex : localHopfIndex μ hμ ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ G : PeriodicGalerkinProblem C m,
      Nonempty (GalerkinPeriodicZero G) := by
  obtain ⟨m, hm, G, Ω, hΩopen, hΩbdd, hdeg⟩ :=
    periodicDegree_ne_zero_of_localHopfIndex hμ hindex
  have hcomponent := regularDegree_homotopy_global_continuation
    G.equation hΩopen hΩbdd hdeg
  exact ⟨m, hm, G, hcomponent.nontrivialZero⟩

/-- Compactness of bounded-period Galerkin zeros yields a genuine periodic orbit of the analytic
ODE.  The phase condition prevents collapse to a stationary solution. -/
theorem periodicWitness_of_galerkinZeros
    {I : Type} [DecidableEq I] [Fintype I]
    (C : AnalyticEquilibriumContinuation I)
    (hzero : ∀ᶠ m in atTop, ∃ G : PeriodicGalerkinProblem C m,
      Nonempty (GalerkinPeriodicZero G)) :
    Nonempty (PositiveContinuationPeriodicWitness C.toSmoothEquilibriumContinuation) := by
  classical
  obtain ⟨μ, hμ, γ, T, hT, hsol, hper, hnon, hconv⟩ :=
    analytic_periodic_galerkin_compactness C hzero
  have hpos : ∀ t i, 0 < γ t i := by
    have hEqPos := C.toSmoothEquilibriumContinuation.equilibriumPositive μ hμ
    exact positive_of_uniform_close_to_positive_equilibrium hEqPos hconv
  refine ⟨{
    parameter := μ
    parameter_mem := hμ
    trajectory := {
      orbit := γ
      period := T
      period_pos := hT
      solution := hsol
      periodic := hper
      nonconstant := hnon }
    positive := hpos }⟩

/-- Periodic witnesses of arbitrarily small generic analytic perturbations converge to a periodic
witness of the original analytic family. -/
theorem periodicWitness_limit_genericPerturbations
    {I : Type} [DecidableEq I] [Fintype I]
    (C : AnalyticEquilibriumContinuation I)
    (hper : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∃ A : GenericAnalyticHopfApproximation C ε,
        Nonempty (PositiveContinuationPeriodicWitness
          A.continuation.toSmoothEquilibriumContinuation)) :
    Nonempty (PositiveContinuationPeriodicWitness C.toSmoothEquilibriumContinuation) := by
  exact analytic_periodic_orbit_closed_under_generic_limit C hper

/-- **Analytic global Hopf theorem in unstable-index form.** -/
theorem analyticGlobalHopfIndex : AnalyticGlobalHopfIndexTarget := by
  intro I _ _ C H
  have hgeneric := exists_genericAnalyticHopfApproximation C
  have hperiodicGeneric : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∃ A : GenericAnalyticHopfApproximation C ε,
        Nonempty (PositiveContinuationPeriodicWitness
          A.continuation.toSmoothEquilibriumContinuation) := by
    filter_upwards [hgeneric] with ε hA
    obtain ⟨A⟩ := hA
    have hchange : unstableIndex A.continuation.toSmoothEquilibriumContinuation 0 ≠
        unstableIndex A.continuation.toSmoothEquilibriumContinuation 1 := by
      rw [A.endpointIndex.1, A.endpointIndex.2]
      exact H.endpointChange
    obtain ⟨μ, hμ, hidx⟩ := exists_center_nonzero_localHopfIndex
      A.centerFinite A.centerRegular hchange
    have hroute := globalHopf_degree_alternative
      (A.centerRegular μ hμ) hidx
    obtain ⟨m, hm, G, hG⟩ := hroute
    have htail : ∀ᶠ n : ℕ in atTop,
        ∃ G : PeriodicGalerkinProblem A.continuation n,
          Nonempty (GalerkinPeriodicZero G) := by
      exact galerkins_refine_nonzero_periodic_degree G hm hG
    exact ⟨A, periodicWitness_of_galerkinZeros A.continuation htail⟩
  exact periodicWitness_limit_genericPerturbations C hperiodicGeneric

/-- Historical Fiedler interface is therefore internally discharged. -/
theorem fiedlerAnalyticGlobalHopf_proved : FiedlerAnalyticGlobalHopfTarget :=
  fiedlerAnalyticGlobalHopf_of_index analyticGlobalHopfIndex

end CRNT

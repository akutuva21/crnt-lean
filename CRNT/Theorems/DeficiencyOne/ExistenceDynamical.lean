import CRNT.Theorems.DeficiencyOne.Existence
import CRNT.Theorems.DeficiencyZero.AsymptoticStability

/-!
# A degree-free dynamical existence route, and the complex-balanced deficiency-one corollary

The classical proof that every positive stoichiometric compatibility class of a weakly
reversible deficiency-one network carries a positive mass-action steady state is
degree-theoretic (Feinberg). Mathlib carries no Brouwer fixed point, topological degree,
Poincaré–Miranda, or Sperner lemma, so that route is unavailable. This module records what a
purely dynamical/compactness argument *does* deliver on the proven semiflow + LaSalle +
relative-entropy stack, and routes the unconditional complex-balanced existence engine into
the deficiency-one existence statement.

* `omegaLimit_relEntropy_const_of_absorbed` — the degree-free compactness brick. For the
  mass-action semiflow built from the bounded-Lipschitz cutoff, a positive complex-balanced
  reference `x*`, and a positive start `x₀`, the genuine orbit is confined by relative-entropy
  dissipation to a *compact* relative-entropy sublevel set, so `Flow.laSalle` yields a
  **nonempty** ω-limit set, invariant under the semiflow, on which `relEntropy x* ·` is
  **constant**. No persistence, closeness, or boundary hypothesis is needed: the Lyapunov
  descent supplies the absorbing compact set directly. This is the genuine dynamical payoff —
  a nonempty ω-limit of a confined mass-action orbit — without any degree theory.

* `deficiencyOneExistence_of_complexBalancedExistence` — the integration. A deficiency-one
  network meeting Feinberg's hypotheses whose every rate-constant choice admits a positive
  complex-balanced concentration satisfies `DeficiencyOneExistence`. The complex-balanced
  reference is transported into the positive class of any start, where complex balancing makes
  it a mass-action steady state, and the proven deficiency-one uniqueness closes the `∃!`.

The general (non-complex-balanced) deficiency-one existence half remains open: a generic
positive steady state of a deficiency-one network is not complex-balanced, so `relEntropy x* ·`
is not a Lyapunov function adapted to it and LaSalle gives no handle; and turning a nonempty
ω-limit into an equilibrium still requires positivity of the ω-limit (the persistence/boundary
obstruction). Closing it needs degree theory, which is absent from Mathlib v4.31.

Depends on:
`CRNT.Theorems.DeficiencyOne.Existence`, `CRNT.Theorems.DeficiencyZero.AsymptoticStability`.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Degree-free compactness brick.** For a positive complex-balanced reference `x*` and a
positive start `x₀`, the mass-action semiflow built from the bounded-Lipschitz cutoff has the
genuine dynamics as its orbit through `x₀`, and that orbit's ω-limit set is **nonempty**,
invariant under the semiflow, with `relEntropy x* ·` **constant** on it.

The relative-entropy dissipation (`dissipation_nonpos`) makes the initial relative-entropy
sublevel set forward-invariant; that set is compact (`isCompact_relEntropy_sublevel`) and
absorbs the orbit, so `Flow.laSalle` applies. No persistence, closeness, or boundary
hypothesis enters: this is the dynamical compactness payoff of a confined mass-action orbit,
obtained without any topological-degree input. -/
theorem omegaLimit_relEntropy_const_of_absorbed
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S) (c : ℝ),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      (omegaLimit atTop ϕ {x₀}).Nonempty ∧
      IsInvariant ϕ (omegaLimit atTop ϕ {x₀}) ∧
      (∀ y ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar y = c) := by
  set C₀ := relEntropy xstar x₀ with hC₀
  -- choose `B` past the coercivity bound of the initial relative-entropy sublevel set
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
  -- the field's linear lower bound, the cutoff, and the resulting semiflow
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
    rw [hγ0, ← hC₀] at this; exact this
  have hclamp : ∀ t, 0 ≤ t → clampBox B (γ x₀ t) = γ x₀ t := fun t ht =>
    clampBox_eq_of_sublevel hxs (hpos t ht).nonnegative (hrele t ht) hBbig
  have hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t := by
    intro t ht; have := hΓd t; rwa [hclamp t ht] at this
  -- the compact relative-entropy sublevel set absorbing the orbit (supplied by dissipation)
  set K : Set (Concentration S) := {y | y.Nonnegative ∧ relEntropy xstar y ≤ C₀} with hK
  have hKcpt : IsCompact K := isCompact_relEntropy_sublevel hxs C₀
  have horbitK : ∀ t : ℝ≥0, ϕ t x₀ ∈ K := by
    intro t; rw [hϕγ]
    exact ⟨(hpos t t.coe_nonneg).nonnegative, hrele t t.coe_nonneg⟩
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩; rw [Set.mem_singleton_iff] at hx; subst hx; exact horbitK t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem, (IsClosed.closure_subset_iff hKcpt.isClosed).mpr hsubK⟩
  -- Lyapunov descent along the orbit (monotonicity for LaSalle)
  have hAnti : AntitoneOn (fun t => relEntropy xstar (γ x₀ t)) (Set.Ici 0) := by
    have hcont : Continuous (fun t => relEntropy xstar (γ x₀ t)) :=
      (relEntropy_continuous hxs).comp (Differentiable.continuous fun t => (hΓd t).differentiableAt)
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn ?_ ?_
    · intro t ht; rw [interior_Ici, Set.mem_Ioi] at ht
      exact (relEntropy_hasDerivAt hxs (hpos t ht.le)
        (fun s => (hasDerivAt_pi.mp (hsol t ht.le)) s)).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(relEntropy_hasDerivAt hxs (hpos t ht.le)
        (fun s => (hasDerivAt_pi.mp (hsol t ht.le)) s)).deriv]
      exact dissipation_nonpos N κ (hpos t ht.le) hxs hcb
  have hmono : ∀ a b : ℝ≥0, a ≤ b →
      relEntropy xstar (ϕ b x₀) ≤ relEntropy xstar (ϕ a x₀) := by
    intro a b hab
    rw [hϕγ, hϕγ]
    exact hAnti (Set.mem_Ici.mpr a.coe_nonneg) (Set.mem_Ici.mpr b.coe_nonneg) (by exact_mod_cast hab)
  obtain ⟨c, hωne, hωinv, hωc⟩ :=
    Flow.laSalle ϕ (relEntropy_continuous hxs) x₀ hKcpt habs hmono
  exact ⟨ϕ, γ, c, hγ0, hϕγ, hsol, hωne, hωinv, hωc⟩

/-- **Deficiency-one existence in the complex-balanced case.** A deficiency-one network meeting
Feinberg's hypotheses whose every rate-constant choice admits a positive complex-balanced
concentration satisfies `DeficiencyOneExistence`: every positive compatibility class contains
a unique positive mass-action steady state.

The complex-balanced reference is transported into the positive class of any start via
`exists_isComplexBalanced_in_positiveClass`, where complex balancing makes it a mass-action
steady state, and `deficiencyOneUniqueness` closes the `∃!`. This is the half of the
deficiency-one existence theorem that is reachable without topological degree. -/
theorem deficiencyOneExistence_of_complexBalancedExistence (N : Network S)
    (h : N.DeficiencyOneHypotheses) (hδ : N.DeficiencyOne)
    (hCB : ∀ (κ : RateConstants N), ∃ x : Concentration S,
      x.Positive ∧ N.IsComplexBalanced κ x) :
    N.DeficiencyOneExistence :=
  N.deficiencyOneExistence_of_complexBalanced h hδ hCB

end Network

end CRNT

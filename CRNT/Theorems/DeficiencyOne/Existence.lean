import CRNT.Theorems.DeficiencyOne.Uniqueness
import CRNT.Theorems.DeficiencyOne.Statement
import CRNT.Dynamics.MassActionAlgebra
import CRNT.Theorems.DeficiencyZero.Existence

/-!
# Deficiency-one existence: reduction to a per-class steady state

The weakly reversible deficiency-one theorem asserts that each positive stoichiometric
compatibility class contains *exactly one* positive mass-action steady state. Its uniqueness
half is the theorem `Network.deficiencyOneUniqueness`. This module records the sound reduction
that, modulo that uniqueness, the existence-and-uniqueness statement
`Network.DeficiencyOneExistence` is equivalent to a bare per-class *existence* obligation, and
discharges that obligation in the complex-balanced special case.

* `deficiencyOneExistence_iff_exists_steadyState` — for a deficiency-one network meeting
  Feinberg's hypotheses, `DeficiencyOneExistence` holds iff every positive class contains at
  least one mass-action steady state. The `∃!` collapses to `∃` because uniqueness is a theorem.
* `deficiencyOneExistence_of_existsSteadyState` — the constructive direction on its own: a
  per-class existence proof yields `DeficiencyOneExistence`. This is the plug-in point for an
  existence engine.
* `deficiencyOneExistence_of_complexBalanced` — the genuinely provable special case. If a
  positive complex-balanced concentration exists for every rate-constant choice, then
  `DeficiencyOneExistence` holds, by landing such an equilibrium in the positive class and
  invoking uniqueness.

The weakly reversible existence half is reduced here to a per-class positive-steady-state
obligation; that obligation is discharged only under the complex-balanced hypothesis. The
unconditional statement `∀ N, N.WeaklyReversible → N.DeficiencyOneHypotheses →
N.DeficiencyOneExistence` is not asserted: a generic deficiency-one positive steady state is
not complex-balanced, and no degree-theoretic or global-persistence brick is available to
produce one.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Theorems.DeficiencyOne.Uniqueness`, `CRNT.Theorems.DeficiencyOne.Statement`,
`CRNT.Dynamics.MassActionAlgebra`, `CRNT.Theorems.DeficiencyZero.Existence`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Existence reduces to a single positive steady state per class.** Under the deficiency-one
hypotheses, `DeficiencyOneExistence` is equivalent to the bare obligation that every positive
compatibility class contains at least one mass-action steady state. The reverse direction uses
`deficiencyOneUniqueness` to upgrade the `∃` to the `∃!` in `DeficiencyOneExistence`. -/
theorem deficiencyOneExistence_iff_exists_steadyState (N : Network S)
    (h : N.DeficiencyOneHypotheses) (hδ : N.DeficiencyOne) :
    N.DeficiencyOneExistence ↔
      ∀ (κ : RateConstants N) (x₀ : Concentration S), x₀.Positive →
        ∃ x : Concentration S,
          x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x := by
  constructor
  · intro hE κ x₀ hx0
    obtain ⟨x, ⟨hmem, hss⟩, _⟩ := hE κ x₀ hx0
    exact ⟨x, hmem, hss⟩
  · intro hExists κ x₀ hx0
    obtain ⟨x, hmem, hss⟩ := hExists κ x₀ hx0
    refine ⟨x, ⟨hmem, hss⟩, ?_⟩
    rintro y ⟨hymem, hyss⟩
    exact N.deficiencyOneUniqueness h hδ κ x₀ hx0 hymem hyss hmem hss

/-- **The constructive direction, standalone.** A proof that every positive compatibility class
of a deficiency-one network contains a mass-action steady state yields `DeficiencyOneExistence`.
This is the plug-in point for any future existence argument. -/
theorem deficiencyOneExistence_of_existsSteadyState (N : Network S)
    (h : N.DeficiencyOneHypotheses) (hδ : N.DeficiencyOne)
    (hExists : ∀ (κ : RateConstants N) (x₀ : Concentration S), x₀.Positive →
      ∃ x : Concentration S,
        x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x) :
    N.DeficiencyOneExistence :=
  (N.deficiencyOneExistence_iff_exists_steadyState h hδ).mpr hExists

/-- **The complex-balanced special case.** If, for every choice of rate constants, the network
admits a positive complex-balanced concentration, then `DeficiencyOneExistence` holds. The
reference complex-balanced point is transported into the positive class of any start via
`exists_isComplexBalanced_in_positiveClass`, where complex balancing makes it a mass-action
steady state, and uniqueness closes the `∃!`. -/
theorem deficiencyOneExistence_of_complexBalanced (N : Network S)
    (h : N.DeficiencyOneHypotheses) (hδ : N.DeficiencyOne)
    (hCB : ∀ (κ : RateConstants N), ∃ x : Concentration S,
      x.Positive ∧ N.IsComplexBalanced κ x) :
    N.DeficiencyOneExistence := by
  refine N.deficiencyOneExistence_of_existsSteadyState h hδ ?_
  intro κ x₀ hx0
  obtain ⟨xstar, hpos, hcb⟩ := hCB κ
  obtain ⟨x, hmem, hxcb⟩ := N.exists_isComplexBalanced_in_positiveClass κ hpos hcb hx0
  exact ⟨x, hmem, hxcb.isMassActionSteadyState N κ⟩

end Network

end CRNT

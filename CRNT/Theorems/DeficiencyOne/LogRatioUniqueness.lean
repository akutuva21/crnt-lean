import CRNT.Theorems.DeficiencyOne.Statement
import CRNT.Kinetics.Generalized

/-!
# Deficiency-one uniqueness from the log-ratio characterization

Feinberg's deficiency-one uniqueness proof splits into two parts. The hard part (the
*log-ratio characterization*) shows that any two positive mass-action steady states `x`, `y`
in a common stoichiometric compatibility class have `log x − log y` in the orthogonal
complement `orthSum N.stoichSubspace` of the stoichiometric subspace — the steady states are
*toric*, exactly as in the deficiency-zero case. The remaining part deduces uniqueness, and
it is precisely the deficiency-zero sign argument: two positive vectors of a common
`S`-coset whose log-ratio is `S`-orthogonal coincide (`birch_uniqueness_of_self`, the
classical Birch step driven by `signCompatible_self`).

This module records that second part as `deficiencyOneUniqueness_of_logRatio`, reducing the
full uniqueness theorem to the log-ratio characterization `LogRatioCharacterization`. No
deficiency-one hypotheses enter here: the reduction is unconditional, isolating the
characterization as the single remaining obligation.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Theorems.DeficiencyOne.Statement`, `CRNT.Kinetics.Generalized`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The log-ratio (toric) characterization of positive steady states.** For every positive
rate constants and starting point, any two positive mass-action steady states in the same
compatibility class have their log-ratio orthogonal to the stoichiometric subspace. This is
the toric form `steady states ⊆ x* ∘ e^(Sᗮ)` and is the substantive content of the
deficiency-one theorem; here it is a hypothesis. -/
def LogRatioCharacterization (N : Network S) : Prop :=
  ∀ (κ : RateConstants N) (x₀ : Concentration S), x₀.Positive →
    ∀ ⦃x y : Concentration S⦄,
      x ∈ N.positiveCompatibilityClass x₀ → N.IsMassActionSteadyState κ x →
      y ∈ N.positiveCompatibilityClass x₀ → N.IsMassActionSteadyState κ y →
      (fun s => Real.log (x s) - Real.log (y s)) ∈ orthSum N.stoichSubspace

/-- **Uniqueness reduces to the log-ratio characterization.** If positive steady states of a
common class are toric — their log-ratio lies in `orthSum N.stoichSubspace` — then a positive
compatibility class contains at most one mass-action steady state. The deduction is the
classical Birch sign argument: `x − y ∈ S` (same class) and `log x − log y ∈ Sᗮ` force
`x = y`, since the difference and the log-ratio share signs coordinatewise. -/
theorem deficiencyOneUniqueness_of_logRatio (N : Network S)
    (hchar : N.LogRatioCharacterization) : N.DeficiencyOneUniqueness := by
  intro κ x₀ hx0 x y hxmem hxss hymem hyss
  have hxy : x - y ∈ N.stoichSubspace := by
    rw [← sub_sub_sub_cancel_right x y x₀]
    exact N.stoichSubspace.sub_mem hxmem.1 hymem.1
  exact birch_uniqueness_of_self N.stoichSubspace hxmem.2 hymem.2 hxy
    (hchar κ x₀ hx0 hxmem hxss hymem hyss)

end Network

end CRNT

import CRNT.Theorems.DeficiencyOne.LogRatioUniqueness
import CRNT.Deficiency.ComplexBalancedRatio

/-!
# Reducing deficiency-one uniqueness to the deficient linkage class

Assembling the pieces of the deficiency-one uniqueness argument:

* uniqueness reduces to the log-ratio characterization (`deficiencyOneUniqueness_of_logRatio`);
* the characterization is constancy of the log-monomial ratio `Φ` along every reaction
  (`logRatio_mem_orthSum_iff`);
* on a deficiency-zero linkage class `Φ` is automatically constant
  (`logMonomialRatio_const_of_deficiencyZeroClass`).

Under the deficiency-one conditions every linkage class has deficiency `0` or `1`, so the
only reactions where constancy of `Φ` is not already established are those of the single
deficient class. This module records `DeficientClassRatioConst` — `Φ`-constancy along the
deficient class's reactions — and proves it is the **sole remaining obligation** for
deficiency-one uniqueness (`deficiencyOneUniqueness_of_deficientClassRatioConst`). The
deficient-class constancy is the substantive sign-counting core of Feinberg's theorem.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Theorems.DeficiencyOne.LogRatioUniqueness`, `CRNT.Deficiency.ComplexBalancedRatio`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The deficient-class constancy obligation.** For any two positive mass-action steady
states in a common compatibility class, the log-monomial ratio `Φ` is constant along every
reaction whose linkage class has deficiency one. This is the residual content of the
log-ratio characterization once the deficiency-zero classes are handled. -/
def DeficientClassRatioConst (N : Network S) : Prop :=
  ∀ (κ : RateConstants N) (x₀ : Concentration S), x₀.Positive →
    ∀ ⦃x y : Concentration S⦄,
      x ∈ N.positiveCompatibilityClass x₀ → N.IsMassActionSteadyState κ x →
      y ∈ N.positiveCompatibilityClass x₀ → N.IsMassActionSteadyState κ y →
      ∀ r : N.R, N.linkageDeficiency (N.classOf (N.sourceIdx r)) = 1 →
        N.logMonomialRatio x y (N.targetIdx r) = N.logMonomialRatio x y (N.sourceIdx r)

/-- **Deficiency-one uniqueness reduces to the deficient linkage class.** Given the
deficiency-one hypotheses, if the log-monomial ratio is constant along the reactions of the
single deficient class, then a positive compatibility class contains at most one mass-action
steady state. The deficiency-zero classes are discharged automatically, leaving only the
deficient class — Feinberg's sign-counting core — as the obligation. -/
theorem deficiencyOneUniqueness_of_deficientClassRatioConst (N : Network S)
    (h : N.DeficiencyOneHypotheses) (hdef : N.DeficientClassRatioConst) :
    N.DeficiencyOneUniqueness := by
  apply N.deficiencyOneUniqueness_of_logRatio
  intro κ x₀ hx0 x y hxmem hxss hymem hyss
  rw [logRatio_mem_orthSum_iff N hxmem.2 hymem.2]
  intro r
  rcases N.linkageDeficiency_eq_zero_or_one h.conditions (N.classOf (N.sourceIdx r)) with hz | ho
  · exact N.logMonomialRatio_const_of_deficiencyZeroClass h κ hxmem.2 hymem.2 hxss hyss hz
      (N.classOf_sourceIdx_eq_targetIdx r).symm rfl
  · exact hdef κ x₀ hx0 hxmem hxss hymem hyss r ho

end Network

end CRNT

import CRNT.Translation.SourceCoefficientEquivalence
import CRNT.Algebra.SteadyStateIdeal
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Completeness of source-coefficient certificates

Source-coefficient equality is already known to imply equality of mass-action vector fields.
This module proves the converse.  For finite-species mass-action systems, the grouped source
monomials are distinct multivariate monomials, so equality of the polynomial vector fields forces
equality of every source coefficient.  Thus the finite coefficient certificate is complete as
well as sound.
-/

namespace CRNT
namespace Network

open MvPolynomial

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The coefficient of the monomial for `y` in the species polynomial is precisely the
corresponding source coefficient. -/
theorem steadyStatePolynomial_coeff_sourceCoefficient
    (N : Network S) (κ : N.RateConstants) (y : Complex S) (s : S) :
    (N.steadyStatePolynomial κ s).coeff (complexExponent y) =
      N.sourceCoefficient κ y s := by
  classical
  have hexp (z : Complex S) : complexExponent z = complexExponent y ↔ z = y := by
    constructor
    · intro h
      have h' := congrArg Finsupp.equivFunOnFinite h
      simpa [complexExponent] using h'
    · rintro rfl
      rfl
  rw [steadyStatePolynomial, coeff_sum]
  simp_rw [coeff_C_mul]
  simp [reactionRatePolynomial, complexMonomialPolynomial, sourceCoefficient,
    coeff_monomial, hexp]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> ring

/-- Equality of mass-action vector fields forces equality of every source coefficient vector. -/
theorem sourceCoefficientEquivalent_of_massActionDynamicallyEquivalent
    {N M : Network S} {κN : N.RateConstants} {κM : M.RateConstants}
    (h : N.MassActionDynamicallyEquivalent M κN κM) :
    N.SourceCoefficientEquivalent M κN κM := by
  intro y
  funext s
  have hpoly : N.steadyStatePolynomial κN s = M.steadyStatePolynomial κM s := by
    apply MvPolynomial.funext
    intro x
    rw [N.eval_steadyStatePolynomial, M.eval_steadyStatePolynomial]
    exact congrFun (h x) s
  rw [← N.steadyStatePolynomial_coeff_sourceCoefficient,
    ← M.steadyStatePolynomial_coeff_sourceCoefficient, hpoly]

/-- Equality on the positive orthant alone already determines every source coefficient.  The
positive orthant is a product of infinite subsets of `ℝ`, so multivariate polynomial function
extensionality applies without requiring equality at boundary concentrations. -/
theorem sourceCoefficientEquivalent_of_vectorField_eq_on_positive
    {N M : Network S} {κN : N.RateConstants} {κM : M.RateConstants}
    (h : ∀ x : Concentration S, Concentration.Positive x →
      N.massActionVectorField κN x = M.massActionVectorField κM x) :
    N.SourceCoefficientEquivalent M κN κM := by
  intro y
  funext s
  have hpoly : N.steadyStatePolynomial κN s = M.steadyStatePolynomial κM s := by
    apply MvPolynomial.funext_set (s := fun _ : S => Set.Ioi (0 : ℝ))
      (hs := fun _ => Set.Ioi_infinite 0)
    intro x hx
    have hxpos : Concentration.Positive x := by
      intro i
      exact (Set.mem_pi.mp hx) i (Set.mem_univ i)
    rw [N.eval_steadyStatePolynomial, M.eval_steadyStatePolynomial]
    exact congrFun (h x hxpos) s
  rw [← N.steadyStatePolynomial_coeff_sourceCoefficient,
    ← M.steadyStatePolynomial_coeff_sourceCoefficient, hpoly]

/-- For mass-action networks on finitely many species, equality of all source coefficients is
equivalent to equality of the induced vector fields. -/
theorem massActionDynamicallyEquivalent_iff_sourceCoefficientEquivalent
    (N M : Network S) (κN : N.RateConstants) (κM : M.RateConstants) :
    N.MassActionDynamicallyEquivalent M κN κM ↔
      N.SourceCoefficientEquivalent M κN κM := by
  constructor
  · exact sourceCoefficientEquivalent_of_massActionDynamicallyEquivalent
  · exact massActionDynamicallyEquivalent_of_sourceCoefficientEquivalent

/-- The complete coefficient certificate is finite: it suffices to check the union of the two
networks' source-complex sets. -/
theorem massActionDynamicallyEquivalent_iff_sourceCoefficientEquivalent_on_union
    (N M : Network S) (κN : N.RateConstants) (κM : M.RateConstants) :
    N.MassActionDynamicallyEquivalent M κN κM ↔
      ∀ y ∈ N.sourceComplexes ∪ M.sourceComplexes,
        N.sourceCoefficient κN y = M.sourceCoefficient κM y := by
  rw [massActionDynamicallyEquivalent_iff_sourceCoefficientEquivalent]
  exact N.sourceCoefficientEquivalent_iff_on_union M κN κM

/-- Failure of dynamical equivalence has a finite source/species coefficient witness. -/
theorem exists_sourceCoefficientMismatch_on_union_iff_not_massActionDynamicallyEquivalent
    (N M : Network S) (κN : N.RateConstants) (κM : M.RateConstants) :
    (∃ y ∈ N.sourceComplexes ∪ M.sourceComplexes, ∃ s : S,
      N.sourceCoefficient κN y s ≠ M.sourceCoefficient κM y s) ↔
      ¬ N.MassActionDynamicallyEquivalent M κN κM := by
  rw [massActionDynamicallyEquivalent_iff_sourceCoefficientEquivalent_on_union]
  simp only [not_forall]
  have hvec {f g : S → ℝ} : f ≠ g ↔ ∃ s, f s ≠ g s := by
    constructor
    · intro hne
      by_contra h
      push_neg at h
      exact hne (funext h)
    · rintro ⟨s, hs⟩ hEq
      exact hs (congrFun hEq s)
  constructor
  · rintro ⟨y, hy, s, hs⟩
    exact ⟨y, hy, fun hEq => hs (congrFun hEq s)⟩
  · rintro ⟨y, hy, hne⟩
    obtain ⟨s, hs⟩ := hvec.mp hne
    exact ⟨y, hy, s, hs⟩

end Network
end CRNT

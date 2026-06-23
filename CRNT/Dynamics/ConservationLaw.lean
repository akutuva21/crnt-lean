import CRNT.Theorems.DeficiencyZero.AsymptoticStability
import CRNT.Dynamics.SiphonConservation

/-!
# Conservation laws are constants of motion; non-critical siphons resist depletion

A *conservation law* is a species vector `w` orthogonal to every reaction vector — equivalently, by
`conservationLaw_iff_mem_orthSum`, a member of `orthSum N.stoichSubspace`. This module proves the
dynamical counterpart of that algebra: along any mass-action solution the weighted total
`∑ s, w s · γ(t) s` is **constant in time** (`conservationLaw_const_along_solution`). The mass-action
velocity lies in the stoichiometric subspace, so the displacement `γ(t) − γ(0)` does too, and a
conservation law annihilates it.

This is the analytic mechanism behind persistence at non-critical siphons. A non-critical (nonempty)
siphon `P` carries, by definition, a conservation law `v` that is nonnegative and *strictly positive
exactly on `P`* (`exists_pos_conservationLaw_of_not_critical`). The conserved total
`∑ s, v s · γ(t) s = ∑ s, v s · γ(0) s` then pins a strictly positive combination of the `P`-species
to its initial value for all time (`not_critical_conserved_along_solution`): the species of a
non-critical siphon cannot all be driven to extinction together, since their `v`-weighted sum is a
constant of motion. This is the conserved-quantity half of the siphon persistence criterion of
Angeli, De Leenheer & Sontag (_A Petri-net approach to persistence analysis_, 2007); the converse
boundary-repelling (Butler & Waltman) analysis is not constructed here.

## Main results

* `conservationLaw_const_along_solution` — a vector in `orthSum N.stoichSubspace` has constant
  weighted total along every mass-action solution.
* `exists_pos_conservationLaw_of_not_critical` — a non-critical nonempty siphon admits a conservation
  law positive exactly on it.
* `not_critical_conserved_along_solution` — that conserved total resists total depletion of the siphon.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Theorems.DeficiencyZero.AsymptoticStability`, `CRNT.Dynamics.SiphonConservation`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Conservation laws are constants of motion.** If `w` is orthogonal to the stoichiometric
subspace, then along any mass-action solution `γ` on `[0, t]` the weighted total `∑ s, w s · γ(τ) s`
is unchanged from time `0` to time `t`. The velocity `f(γ)` lies in the stoichiometric subspace, so
the displacement `γ(t) − γ(0)` does, and `w` annihilates it. -/
theorem conservationLaw_const_along_solution (N : Network S) (κ : RateConstants N)
    {w : S → ℝ} (hw : w ∈ orthSum N.stoichSubspace)
    {γ : ℝ → Concentration S} {t : ℝ} (ht : 0 ≤ t)
    (hsol : ∀ τ ∈ Set.Icc (0 : ℝ) t, HasDerivAt γ (N.massActionVectorField κ (γ τ)) τ) :
    ∑ s, w s * γ t s = ∑ s, w s * γ 0 s := by
  have hdiff : (γ t : S → ℝ) - γ 0 ∈ N.stoichSubspace :=
    sub_mem_stoichSubspace_of_solution N κ ht hsol
  have h0 : ∑ i, w i * ((γ t : S → ℝ) - γ 0) i = 0 := (mem_orthSum.mp hw) _ hdiff
  have key : (∑ s, w s * γ t s) - (∑ s, w s * γ 0 s) = 0 := by
    rw [← Finset.sum_sub_distrib]
    rw [show (∑ s, (w s * γ t s - w s * γ 0 s)) = ∑ i, w i * ((γ t : S → ℝ) - γ 0) i from
      Finset.sum_congr rfl fun s _ => by rw [Pi.sub_apply]; ring]
    exact h0
  linarith

/-- **A non-critical nonempty siphon carries a conservation law positive exactly on it.** Unfolding
the definition of criticality, a nonempty siphon that is *not* critical is precisely one admitting a
nonnegative species vector that is strictly positive exactly on `P` and orthogonal to the
stoichiometric subspace. -/
theorem exists_pos_conservationLaw_of_not_critical (N : Network S)
    {P : Finset S} (hP : N.IsSiphon P) (hPne : P.Nonempty) (hnc : ¬ N.IsCriticalSiphon P) :
    ∃ v : S → ℝ, (∀ s, 0 ≤ v s) ∧ (∀ s, 0 < v s ↔ s ∈ P) ∧ v ∈ orthSum N.stoichSubspace := by
  unfold IsCriticalSiphon at hnc
  push Not at hnc
  obtain ⟨v, hv0, hvP, hvcons⟩ := hnc hPne hP
  exact ⟨v, hv0, hvP, (N.conservationLaw_iff_mem_orthSum v).mp hvcons⟩

/-- **Non-critical siphons resist total depletion.** A non-critical nonempty siphon `P` admits a
conservation law `v`, nonnegative and strictly positive exactly on `P`, whose weighted total along
any mass-action solution is a constant of motion. The strictly-positive-on-`P` combination
`∑ s, v s · γ(t) s` therefore stays equal to its initial value for all time — the species of `P`
cannot all be driven to zero together. -/
theorem not_critical_conserved_along_solution (N : Network S) (κ : RateConstants N)
    {P : Finset S} (hP : N.IsSiphon P) (hPne : P.Nonempty) (hnc : ¬ N.IsCriticalSiphon P) :
    ∃ v : S → ℝ, (∀ s, 0 ≤ v s) ∧ (∀ s, 0 < v s ↔ s ∈ P) ∧
      ∀ {γ : ℝ → Concentration S} {t : ℝ}, 0 ≤ t →
        (∀ τ ∈ Set.Icc (0 : ℝ) t, HasDerivAt γ (N.massActionVectorField κ (γ τ)) τ) →
        ∑ s, v s * γ t s = ∑ s, v s * γ 0 s := by
  obtain ⟨v, hv0, hvP, hw⟩ := N.exists_pos_conservationLaw_of_not_critical hP hPne hnc
  exact ⟨v, hv0, hvP, fun ht hsol => N.conservationLaw_const_along_solution κ hw ht hsol⟩

end Network

end CRNT

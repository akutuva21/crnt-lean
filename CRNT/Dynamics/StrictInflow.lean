import CRNT.Dynamics.Persistence

/-!
# Strict inflow at a non-siphon zero set

A *siphon* is a species set `P` such that every reaction producing a `P`-species also consumes
one. The persistence analysis needs the contrapositive engine: at a nonnegative concentration `w`
whose zero set `Z(w) = {s | w s = 0}` is **not** a siphon, the mass-action field points strictly
*inward* at the offending species.

Concretely, if `Z(w)` is not a siphon there is a reaction `r` producing some `s ∈ Z(w)` while
consuming no `Z(w)`-species. Every reactant of `r` is then outside `Z(w)`, hence at positive
concentration, so `r` fires at a strictly positive rate; and since `r` does not consume `s`, its
reaction-vector entry there is strictly positive. Every other reaction contributes nonnegatively
to the `s`-rate (the summand argument of `massActionVectorField_nonneg_of_zero`), so the total is
strictly positive: `0 < ẋ_s(w)`.

This is the dynamical opposite of `massActionVectorField_eq_zero_on_siphonFace` (the field is
tangent to a *siphon* face). Combined with negative invariance of the ω-limit set, it forces the
zero set of a boundary ω-point to be a siphon.

Depends on: `CRNT.Dynamics.Persistence`.
-/

open scoped BigOperators

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Strict inflow at a non-siphon zero set.** Let `w` be a nonnegative concentration and `P`
its zero set (`s ∈ P ↔ w s = 0`). If `P` is not a siphon, then some `s ∈ P` has strictly
positive `s`-component of the mass-action field: `0 < N.massActionVectorField κ w s`. -/
theorem massActionVectorField_pos_of_not_isSiphon (N : Network S) (κ : N.RateConstants)
    {w : Concentration S} (hwnn : w.Nonnegative) {P : Finset S}
    (hP : ∀ s, s ∈ P ↔ w s = 0) (hns : ¬ N.IsSiphon P) :
    ∃ s ∈ P, 0 < N.massActionVectorField κ w s := by
  rw [IsSiphon] at hns
  push Not at hns
  obtain ⟨r, ⟨s, hsP, hprod⟩, hno⟩ := hns
  refine ⟨s, hsP, ?_⟩
  rw [massActionVectorField_apply]
  refine Finset.sum_pos' (fun r' _ => ?_) ⟨r, Finset.mem_univ r, ?_⟩
  · -- every summand is nonnegative at the empty species `s` (with `w s = 0`)
    by_cases hle : (N.reaction r').source s ≤ (N.reaction r').target s
    · refine mul_nonneg (N.massActionRate_nonneg κ r' hwnn) ?_
      rw [reactionVector_apply]
      have : ((N.reaction r').source s : ℝ) ≤ ((N.reaction r').target s : ℝ) := by exact_mod_cast hle
      linarith
    · have hsrc : (N.reaction r').source s ≠ 0 := by omega
      have hrate := N.massActionRate_eq_zero_of_reactant_zero κ ((hP s).mp hsP) hsrc
      simp [hrate]
  · -- the offending reaction `r` fires at positive rate with a strictly positive entry at `s`
    have hsrc0 : (N.reaction r).source s = 0 := not_not.mp (hno s hsP)
    have hvec : 0 < N.reactionVector r s := by
      rw [reactionVector_apply, hsrc0, Nat.cast_zero, sub_zero]
      exact_mod_cast Nat.pos_of_ne_zero hprod
    have hrate : 0 < N.massActionRate κ r w := by
      show 0 < κ.k r * (N.reaction r).source.massActionMonomial w
      refine mul_pos (κ.positive r) ?_
      show 0 < ∏ s' : S, w s' ^ (N.reaction r).source s'
      refine Finset.prod_pos fun s' _ => ?_
      by_cases hs' : (N.reaction r).source s' = 0
      · rw [hs', pow_zero]; exact one_pos
      · have hnotP : s' ∉ P := fun h => hno s' h hs'
        have hne : w s' ≠ 0 := fun h => hnotP ((hP s').mpr h)
        exact pow_pos (lt_of_le_of_ne (hwnn s') (Ne.symm hne)) _
    exact mul_pos hrate hvec

end Network

end CRNT

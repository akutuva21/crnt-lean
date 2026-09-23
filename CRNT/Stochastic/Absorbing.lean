import CRNT.Stochastic.IntegerLattice

/-!
# Absorbing states and structural boundary traps

A count state is absorbing exactly when no reaction source is dominated by the state.
This is the elementary boundary obstruction underlying stochastic irreducibility tests.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- No reaction can fire from the count state. -/
def IsAbsorbingCount (N : Network S) (n : S → ℕ) : Prop :=
  ∀ r : N.R, ¬ N.Enabled n r

/-- Equivalent source-deficiency characterization of absorbing states. -/
theorem isAbsorbingCount_iff (N : Network S) (n : S → ℕ) :
    N.IsAbsorbingCount n ↔
      ∀ r : N.R, ∃ s : S, n s < (N.reaction r).source s := by
  unfold IsAbsorbingCount Enabled
  simp only [not_forall, not_le]

/-- The stochastic exit rate vanishes at every absorbing state. -/
theorem exitRate_eq_zero_of_absorbing (N : Network S) (κ : N.RateConstants)
    {n : S → ℕ} (h : N.IsAbsorbingCount n) : N.exitRate κ n = 0 := by
  unfold exitRate
  apply Finset.sum_eq_zero
  intro r _
  exact N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r (h r)

/-- Conversely, under strictly positive rate constants, zero exit rate forces every
reaction to be disabled. -/
theorem absorbing_of_exitRate_eq_zero (N : Network S) (κ : N.RateConstants)
    {n : S → ℕ} (hκ : ∀ r, 0 < κ.k r) (hzero : N.exitRate κ n = 0) :
    N.IsAbsorbingCount n := by
  intro r hen
  have hpos : 0 < N.stochasticMassActionRate κ n r := by
    unfold stochasticMassActionRate
    apply mul_pos (hκ r)
    apply Finset.prod_pos
    intro s _
    exact_mod_cast Nat.descFactorial_pos.mpr (hen s)
  have hle : N.stochasticMassActionRate κ n r ≤ N.exitRate κ n := by
    unfold exitRate
    exact Finset.single_le_sum
      (fun r _ => N.stochasticMassActionRate_nonneg κ n r) (Finset.mem_univ r)
  rw [hzero] at hle
  linarith

/-- Absorbing states are terminal for count reachability. -/
theorem reachable_eq_of_absorbing (N : Network S) {n m : S → ℕ}
    (habs : N.IsAbsorbingCount n) (hreach : N.CountReachable n m) : m = n := by
  induction hreach with
  | refl => rfl
  | tail hreach hstep ih =>
      subst ih
      rcases hstep with ⟨r, hen, rfl⟩
      exact False.elim (habs r hen)

/-- The zero count is absorbing exactly when every reaction has a nonzero source complex. -/
theorem zero_absorbing_iff_no_zero_source (N : Network S) :
    N.IsAbsorbingCount (fun _ => 0) ↔
      ∀ r : N.R, (N.reaction r).source ≠ 0 := by
  rw [N.isAbsorbingCount_iff]
  constructor
  · intro h r hzero
    obtain ⟨s, hs⟩ := h r
    rw [hzero] at hs
    simp at hs
  · intro h r
    by_contra hnone
    push_neg at hnone
    apply h r
    funext s
    specialize hnone s
    simp only [Pi.zero_apply]
    omega

/-- A zero-source reaction rules out absorption at the origin. -/
theorem zero_not_absorbing_of_zeroSourceReaction (N : Network S)
    {r : N.R} (hr : (N.reaction r).source = 0) :
    ¬ N.IsAbsorbingCount (fun _ => 0) := by
  rw [N.zero_absorbing_iff_no_zero_source]
  push_neg
  exact ⟨r, hr⟩

end Network
end CRNT

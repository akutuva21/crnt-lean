/-
No non-constant positive periodic orbit for weakly reversible, deficiency-zero
mass-action networks.

The relative entropy `relEntropy xstar` is a strict Lyapunov function: it is nonincreasing
along every positive trajectory and its dissipation vanishes only at complex-balanced points.
A positive periodic orbit returns the relative entropy to its starting value each period, so
along the orbit the relative entropy is both nonincreasing and periodic, hence constant; its
derivative, the dissipation, is therefore identically zero, so every point of the orbit is
complex-balanced. Deficiency-zero per-class uniqueness then forces the orbit to be a single
point. Consequently a weakly reversible deficiency-zero network sustains no oscillation, for
every choice of rate constants.
-/
import CRNT.Theorems.DeficiencyZero.AsymptoticStability
import CRNT.Theorems.DeficiencyZero.Existence

open scoped BigOperators

namespace CRNT

/-- A real function that is antitone and periodic with a positive period is constant. -/
theorem eq_of_antitone_periodic {g : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hanti : Antitone g) (hper : Function.Periodic g T) : ∀ x y, g x = g y := by
  have hiter : ∀ (n : ℕ) (x : ℝ), g (x + n * T) = g x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        have hstep : g (x + ((k : ℝ) + 1) * T) = g x := by
          have harg : x + ((k : ℝ) + 1) * T = (x + (k : ℝ) * T) + T := by ring
          rw [harg, hper, ih x]
        simpa [Nat.cast_succ] using hstep
  have key : ∀ x y : ℝ, g x ≤ g y := by
    intro x y
    obtain ⟨n, hn⟩ := Archimedean.arch (y - x) hT
    have hnn : y - x ≤ (n : ℝ) * T := by simpa [nsmul_eq_mul] using hn
    have hle : y ≤ x + (n : ℝ) * T := by linarith
    calc g x = g (x + (n : ℝ) * T) := (hiter n x).symm
      _ ≤ g y := hanti hle
  intro x y
  exact le_antisymm (key x y) (key y x)

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **No non-constant positive periodic orbit.** For a weakly reversible, deficiency-zero
mass-action network, every positive periodic solution of the mass-action ODE is constant, for
every choice of rate constants. This is the exclusion of sustained oscillation from the
deficiency-zero class. -/
theorem eq_of_periodic_solution
    (N : Network S) (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) (κ : N.RateConstants)
    {γ : ℝ → Concentration S} {T : ℝ} (hT : 0 < T)
    (hpos : ∀ t, (γ t).Positive)
    (hsol : ∀ t s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t)
    (hper : Function.Periodic γ T) :
    ∀ t, γ t = γ 0 := by
  -- A positive complex-balanced reference exists from weak reversibility and δ = 0.
  obtain ⟨xstar, hxs, hcb⟩ := N.exists_isComplexBalanced hwr hδ κ
  -- The relative entropy along the orbit is antitone (Lyapunov descent) and periodic, hence
  -- constant.
  have hanti : Antitone (fun t => relEntropy xstar (γ t)) :=
    N.relEntropy_antitone_along_solution κ hxs hcb hpos hsol
  have hgper : Function.Periodic (fun t => relEntropy xstar (γ t)) T := by
    intro t
    show relEntropy xstar (γ (t + T)) = relEntropy xstar (γ t)
    rw [hper t]
  have hgconst : ∀ a b, relEntropy xstar (γ a) = relEntropy xstar (γ b) :=
    eq_of_antitone_periodic hT hanti hgper
  -- Whole-vector form of the solution, for the compatibility-class lemma.
  have hsolwv : ∀ τ, HasDerivAt γ (N.massActionVectorField κ (γ τ)) τ :=
    fun τ => hasDerivAt_pi.mpr (fun s => hsol τ s)
  -- Every point of the orbit is complex-balanced: the relative entropy is locally constant, so
  -- its derivative (the dissipation) vanishes, and vanishing dissipation is complex balance.
  have hcbt : ∀ t, N.IsComplexBalanced κ (γ t) := by
    intro t₀
    have hchain := relEntropy_hasDerivAt hxs (hpos t₀) (fun s => hsol t₀ s)
    have hd0 : HasDerivAt (fun τ => relEntropy xstar (γ τ)) 0 t₀ := by
      have heq : (fun τ => relEntropy xstar (γ τ)) = fun _ => relEntropy xstar (γ t₀) := by
        funext u; exact hgconst u t₀
      rw [heq]; exact hasDerivAt_const t₀ _
    have hdiss : (∑ s, (Real.log (γ t₀ s) - Real.log (xstar s))
        * N.massActionVectorField κ (γ t₀) s) = 0 := hchain.unique hd0
    exact N.complexBalanced_of_dissipation_eq_zero κ (hpos t₀) hxs hcb hdiss
  -- Every point of the orbit lies in γ 0's positive compatibility class.
  have hmem : ∀ t, γ t ∈ N.positiveCompatibilityClass (γ 0) := by
    intro t
    refine ⟨?_, hpos t⟩
    show γ t - γ 0 ∈ N.stoichSubspace
    rcases le_total 0 t with h | h
    · have hsol0t : ∀ τ ∈ Set.Icc (0 : ℝ) t,
          HasDerivAt γ (N.massActionVectorField κ (γ τ)) τ := fun τ _ => hsolwv τ
      exact N.sub_mem_stoichSubspace_of_solution κ h hsol0t
    · have hsolt0 : ∀ τ ∈ Set.Icc t (0 : ℝ),
          HasDerivAt γ (N.massActionVectorField κ (γ τ)) τ := fun τ _ => hsolwv τ
      have h2 := N.sub_mem_stoichSubspace_of_solution κ h hsolt0
      simpa [neg_sub] using N.stoichSubspace.neg_mem h2
  -- Two complex-balanced points of one positive class are equal (deficiency-zero uniqueness).
  intro t
  exact N.isComplexBalanced_unique_in_positiveClass hwr κ (hmem t) (hmem 0) (hcbt t) (hcbt 0)

end Network
end CRNT

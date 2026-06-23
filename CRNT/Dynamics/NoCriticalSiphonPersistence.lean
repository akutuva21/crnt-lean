import CRNT.Dynamics.CriticalSiphonOmega

/-!
# No critical siphon ⇒ every ω-limit point is positive

The Angeli–De Leenheer–Sontag persistence criterion at the ω-limit level: if a network has **no
critical siphon**, then no ω-limit point of a positive mass-action trajectory lies on the
boundary — every ω-limit point is strictly positive.

The proof is the contrapositive of `isCriticalSiphon_zeroSet_of_mem_omegaLimit`. An ω-limit point
`w` is nonnegative; were some coordinate zero, its zero set `Z(w)` would be a nonempty critical
siphon, contradicting the hypothesis. Hence every coordinate is positive.

This is persistence stated at the ω-limit set: combined with the relative-entropy Lyapunov stack
(which converges once boundary ω-points are excluded), it is the bridge from the decidable
structural condition `HasNoCriticalSiphon` to the global attractor conjecture for the no-critical-
siphon class.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.CriticalSiphonOmega`.
-/

open Filter Topology
open scoped NNReal

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **No critical siphon ⇒ ω-limit points are positive.** Under the genuine-field / nonnegativity
/ boundedness / affine-invariance data of the mass-action semiflow, a positive start `x₀`, and
`HasNoCriticalSiphon`, every ω-limit point `w` of the trajectory through `x₀` is strictly
positive. -/
theorem omegaLimit_positive_of_hasNoCriticalSiphon (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) (hncs : N.HasNoCriticalSiphon)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀}) :
    w.Positive := by
  classical
  intro s₁
  -- `w` is nonnegative; show every coordinate is strictly positive
  have hwnn : w.Nonnegative := hωnn w hw
  by_contra hns₁
  -- the zero set of `w` is nonempty (it contains `s₁`)
  have hs₁0 : w s₁ = 0 := le_antisymm (not_lt.mp hns₁) (hwnn s₁)
  set P : Finset S := Finset.univ.filter (fun s => w s = 0) with hPdef
  have hP : ∀ s, s ∈ P ↔ w s = 0 := fun s => by
    rw [hPdef, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ s, h⟩⟩
  have hPne : P.Nonempty := ⟨s₁, (hP s₁).mpr hs₁0⟩
  -- but then it is a critical siphon, contradicting the hypothesis
  exact hncs P (N.isCriticalSiphon_zeroSet_of_mem_omegaLimit κ hϕγ hK hmaps hωnn hgenω hωaff
    hx0pos hw hP hPne)

end Network

end CRNT

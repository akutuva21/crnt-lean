import CRNT.Multistationarity.SRCycleInjectivity

/-!
# Mass-action injectivity on a compatibility class from a consistent signed SR-cover

This module closes the species–reaction graph injectivity chain to its monostationarity
verdict. The full mass-action Jacobian is a P-matrix at a positive concentration when every
reaction-choice cover over every restricted species set carries a nonnegative signed-incidence
weight and every Jacobian diagonal entry is positive
(`isPMatrix_massActionJacobian_of_consistentSRSign`). For a network whose stoichiometric chart
is a coordinate selection the reduced (`s × s`) Jacobian is a principal submatrix of the full
Jacobian, so it inherits the P-matrix property (`reducedJacobian_isPMatrix_of_submatrix`).
Feeding that into the box Gale–Nikaido reduction
(`massActionInjectiveOnClass_of_jacobian_pmatrix`) makes the mass-action vector field injective
on the positive compatibility class, whence the class carries at most one positive mass-action
steady state.

This is the ∀-side injectivity verdict of Craciun and Feinberg ("Multiple equilibria in complex
chemical reaction networks: I. The injectivity property" and "II. The species–reaction graph"),
resting on the global-univalence theorem of Gale and Nikaido ("The Jacobian matrix and global
univalence of mappings").

* `massActionInjectiveOnClass_of_consistentSRSign` — from the consistent signed SR-cover weight
  and positive Jacobian diagonal, holding at every concentration whose chart coordinate lies in
  an enclosing box that covers the positive compatibility class, together with a coordinate
  selection presenting the reduced Jacobian as a principal submatrix of the full Jacobian, the
  mass-action kinetics is injective on the class.
* `subsingleton_steadyState_of_consistentSRSign` — the monostationarity payoff: at most one
  positive mass-action steady state per compatibility class.

Carrying the full-Jacobian P-matrix property to the reduced Jacobian for a general
stoichiometric chart is a genuine Schur-style oblique compression `stoichProj ∘ J ∘ stoichChart`,
not a principal submatrix, so its P-matrix property is not inherited by submatrix selection; it
needs the signed SR-cover sign condition recast on the reduced covers and is not developed here.

Depends on:
`CRNT.Multistationarity.SRCycleInjectivity`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Matrix
open Equiv Finset

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Mass-action injectivity on a compatibility class from a consistent signed SR-cover.**
Suppose the chart coordinates of every point of the positive compatibility class of `x₀` lie in
a box `Icc lo hi`, and that at every concentration `affineChart x₀ y` with `y` in that box:

* the concentration is positive (`hpos`),
* every reaction-choice cover over every restricted species set carries a nonnegative
  signed-incidence weight `(coverCoeff σ) · ∏ a, signedEdge (σ a) (ρ a)` (`hweight`),
* every Jacobian diagonal entry is positive (`hdiag`).

Suppose moreover a coordinate selection `f : Fin (stoichRank N) → S` presents the reduced
Jacobian as a principal submatrix of the full Jacobian at every box coordinate (`hsub`). Then
the full Jacobian is a P-matrix on the box (Craciun–Feinberg signed-SR-cover criterion), the
reduced Jacobian inherits the P-matrix property by submatrix selection, and the box Gale–Nikaido
reduction makes the mass-action vector field injective on the class. -/
theorem massActionInjectiveOnClass_of_consistentSRSign (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    {f : Fin N.stoichRank → S} (hf : Function.Injective f)
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hpos : ∀ y ∈ Set.Icc lo hi, Concentration.Positive (N.affineChart x₀ y))
    (hweight : ∀ y ∈ Set.Icc lo hi, ∀ (s : Finset S) (σ : Perm s) (ρ : s → N.R),
      0 ≤ ((coverCoeff σ : ℤ) : ℝ) *
        ((∏ a : s, N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℝ))
    (hdiag : ∀ y ∈ Set.Icc lo hi, ∀ i : S,
      0 < (N.massActionJacobian κ (N.affineChart x₀ y)) i i)
    (hsub : ∀ y ∈ Set.Icc lo hi, N.reducedJacobian κ x₀ y
      = (N.massActionJacobian κ (N.affineChart x₀ y)).submatrix f f) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ := by
  refine N.massActionInjectiveOnClass_of_jacobian_pmatrix κ x₀ hbox (fun y hy => ?_)
  have hP : (N.massActionJacobian κ (N.affineChart x₀ y)).IsPMatrix :=
    N.isPMatrix_massActionJacobian_of_consistentSRSign κ (hpos y hy)
      (hweight y hy) (hdiag y hy)
  exact N.reducedJacobian_isPMatrix_of_submatrix κ x₀ y hf hP (hsub y hy)

/-- **Monostationarity from a consistent signed SR-cover.** Under the hypotheses of
`massActionInjectiveOnClass_of_consistentSRSign`, the positive compatibility class of `x₀`
carries at most one positive mass-action steady state. This is the Craciun–Feinberg injectivity
verdict in its monostationarity form. -/
theorem subsingleton_steadyState_of_consistentSRSign (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    {f : Fin N.stoichRank → S} (hf : Function.Injective f)
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hpos : ∀ y ∈ Set.Icc lo hi, Concentration.Positive (N.affineChart x₀ y))
    (hweight : ∀ y ∈ Set.Icc lo hi, ∀ (s : Finset S) (σ : Perm s) (ρ : s → N.R),
      0 ≤ ((coverCoeff σ : ℤ) : ℝ) *
        ((∏ a : s, N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℝ))
    (hdiag : ∀ y ∈ Set.Icc lo hi, ∀ i : S,
      0 < (N.massActionJacobian κ (N.affineChart x₀ y)) i i)
    (hsub : ∀ y ∈ Set.Icc lo hi, N.reducedJacobian κ x₀ y
      = (N.massActionJacobian κ (N.affineChart x₀ y)).submatrix f f)
    {x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsMassActionSteadyState κ x) (hsy : N.IsMassActionSteadyState κ y) : x = y :=
  (N.massActionInjectiveOnClass_of_consistentSRSign κ x₀ hf hbox hpos hweight hdiag
    hsub).subsingleton_steadyState hx hy
    ((N.isMassActionSteadyState_iff_kinetic κ x).mp hsx)
    ((N.isMassActionSteadyState_iff_kinetic κ y).mp hsy)

end Network

end CRNT

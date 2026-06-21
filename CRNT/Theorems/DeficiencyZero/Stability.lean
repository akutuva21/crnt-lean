import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Theorems.DeficiencyZero.Lyapunov
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Lyapunov descent along mass-action solutions

The relative entropy `relEntropy x* ·` decreases along every positive mass-action
trajectory. Concretely, for a positive solution `γ` of `ẋ = f(x)`:

* `relEntropy_hasDerivAt`: `d/dt relEntropy x* (γ t) = ∑_s (log γ_s − log x*_s) · γ'_s`
  (the chain rule, with `∇relEntropy = log(·/x*)`);
* `relEntropy_antitone_along_solution`: relative to a complex-balanced reference,
  `t ↦ relEntropy x* (γ t)` is nonincreasing.

This is the Lyapunov-descent half of Horn–Jackson stability. It is stated for an arbitrary
differentiable positive solution `γ`, so it needs no flow construction. Turning descent
into convergence (`γ t → x*`) additionally requires LaSalle's invariance principle
(`Flow.laSalle`) applied to the mass-action *semiflow* — whose construction from
Picard–Lindelöf (global forward existence and continuous dependence on initial conditions)
is beyond the current Mathlib ODE library.

This module is **stable** and `sorry`-free.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

omit [DecidableEq S] in
/-- **Chain rule for the Lyapunov function.** Along a positive path `γ` with coordinatewise
derivatives `γ'`, the relative entropy has derivative `∑_s (log γ_s − log x*_s) γ'_s`. -/
theorem relEntropy_hasDerivAt {xstar : Concentration S} (hxs : xstar.Positive)
    {γ : ℝ → Concentration S} {γ' : S → ℝ} {t : ℝ} (hpos : (γ t).Positive)
    (hγ : ∀ s, HasDerivAt (fun τ => γ τ s) (γ' s) t) :
    HasDerivAt (fun τ => relEntropy xstar (γ τ))
      (∑ s, (Real.log (γ t s) - Real.log (xstar s)) * γ' s) t := by
  unfold relEntropy
  rw [show (fun τ => ∑ i, (γ τ i * Real.log (γ τ i / xstar i) - γ τ i + xstar i))
      = ∑ i, fun τ => γ τ i * Real.log (γ τ i / xstar i) - γ τ i + xstar i from by
        funext τ; simp only [Finset.sum_apply]]
  apply HasDerivAt.sum
  intro s _
  have hc : 0 < xstar s := hxs s
  have hu : 0 < γ t s := hpos s
  -- derivative of the scalar term `u ↦ u·log(u/x*ₛ) − u + x*ₛ` at `u = γ t s`
  have hterm : HasDerivAt (fun u => u * Real.log (u / xstar s) - u + xstar s)
      (Real.log (γ t s) - Real.log (xstar s)) (γ t s) := by
    have heq : (fun u => u * Real.log (u / xstar s) - u + xstar s)
        =ᶠ[nhds (γ t s)] (fun u => u * Real.log u - u * Real.log (xstar s) - u + xstar s) := by
      filter_upwards [Ioi_mem_nhds hu] with u hu'
      rw [Real.log_div (ne_of_gt hu') hc.ne']; ring
    refine HasDerivAt.congr_of_eventuallyEq ?_ heq
    have h1 : HasDerivAt (fun u => u * Real.log u) (Real.log (γ t s) + 1) (γ t s) :=
      Real.hasDerivAt_mul_log hu.ne'
    have h2 : HasDerivAt (fun u : ℝ => u * Real.log (xstar s)) (Real.log (xstar s)) (γ t s) := by
      simpa using (hasDerivAt_id (γ t s)).mul_const (Real.log (xstar s))
    have h3 := ((h1.sub h2).sub (hasDerivAt_id (γ t s))).add_const (xstar s)
    have hval : Real.log (γ t s) + 1 - Real.log (xstar s) - 1
        = Real.log (γ t s) - Real.log (xstar s) := by ring
    rwa [hval] at h3
  exact hterm.comp t (hγ s)

/-- **Lyapunov descent.** Relative to a positive complex-balanced reference, the relative
entropy is nonincreasing along every positive mass-action solution. -/
theorem relEntropy_antitone_along_solution (N : Network S) (κ : RateConstants N)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} (hpos : ∀ t, (γ t).Positive)
    (hsol : ∀ t s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t) :
    Antitone (fun t => relEntropy xstar (γ t)) := by
  have hchain : ∀ t, HasDerivAt (fun τ => relEntropy xstar (γ τ))
      (∑ s, (Real.log (γ t s) - Real.log (xstar s)) * N.massActionVectorField κ (γ t) s) t :=
    fun t => relEntropy_hasDerivAt hxs (hpos t) (fun s => hsol t s)
  refine antitone_of_deriv_nonpos (fun t => (hchain t).differentiableAt) fun t => ?_
  rw [(hchain t).deriv]
  exact dissipation_nonpos N κ (hpos t) hxs hcb

end Network

end CRNT

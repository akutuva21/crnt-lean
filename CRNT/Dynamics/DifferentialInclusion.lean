import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Differential inclusions

A *differential inclusion* replaces the single right-hand side of an ODE `ẋ = f(x)` by a
set-valued field `F : E → Set E`. A curve solves the inclusion when its derivative lies in
the field evaluated at the current point, `deriv γ t ∈ F (γ t)`. This is the definitional
substrate for toric differential inclusions: a genuine mass-action flow is a *selection* of
the inclusion, so any region that traps every solution of the inclusion in particular traps
the flow.

The interval-relative solution predicate `IsInclusionSolutionOn F γ s` asks for
`HasDerivWithinAt γ (deriv γ t) s t` together with `deriv γ t ∈ F (γ t)` at every point of
`s`; the unrestricted predicate `IsInclusionSolution F γ` is the same with `HasDerivAt`.

**Selection.** If `γ` solves the ODE `ẋ = f(x)` and `f x ∈ F x` pointwise, then `γ` solves
the inclusion `F`. This is the easy, central direction: it embeds a mass-action flow
into a toric differential inclusion.

**Monotonicity.** A field can only acquire more solutions as it grows: if `F x ⊆ G x`
pointwise then every `F`-solution is a `G`-solution.

**Forward invariance.** A region `R : Set E` is forward invariant for `F` on `Set.Ici 0`
when every inclusion solution that starts in `R` at time `0` stays in `R` for all `t ≥ 0`.
The whole space is invariant, and an arbitrary intersection of invariant regions is invariant.

The deep theory — Filippov existence, viability, measurable selection — is **absent** from
Mathlib and is not attempted here.

This module is **stable** and `sorry`-free. Depends on:
`Mathlib.Analysis.Calculus.Deriv.Basic`, `Mathlib.Topology.MetricSpace.Basic`.
-/

namespace CRNT

namespace DifferentialInclusion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A set-valued field on `E`: at each point it prescribes the admissible velocities. -/
abbrev Field (E : Type*) := E → Set E

/-- A curve `γ : ℝ → E` solves the differential inclusion `F` on the set `s` when, at every
time `t ∈ s`, it is differentiable within `s` and its velocity is an admissible velocity of
the field at the current point. -/
def IsInclusionSolutionOn (F : Field E) (γ : ℝ → E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt γ (derivWithin γ s t) s t ∧ derivWithin γ s t ∈ F (γ t)

/-- A curve `γ : ℝ → E` solves the differential inclusion `F` (on all of `ℝ`) when it is
everywhere differentiable with velocity an admissible velocity of the field. -/
def IsInclusionSolution (F : Field E) (γ : ℝ → E) : Prop :=
  ∀ t, HasDerivAt γ (deriv γ t) t ∧ deriv γ t ∈ F (γ t)

/-- A solution of an ODE `ẋ = f(x)` whose velocities are admissible (`f x ∈ F x`) is a
solution of the inclusion `F`. The selection direction: a mass-action flow embeds into any
inclusion that contains its field. -/
theorem IsInclusionSolution.of_ode {F : Field E} {f : E → E} {γ : ℝ → E}
    (hderiv : ∀ t, HasDerivAt γ (f (γ t)) t) (hsel : ∀ x, f x ∈ F x) :
    IsInclusionSolution F γ := by
  intro t
  have hd : deriv γ t = f (γ t) := (hderiv t).deriv
  refine ⟨?_, ?_⟩
  · rw [hd]; exact hderiv t
  · rw [hd]; exact hsel (γ t)

/-- The interval version of selection: an ODE solution on `s` with admissible velocities
solves the inclusion on `s`, provided `s` is uniquely differentiable at each of its points
(so that the within-derivative agrees with the genuine derivative). -/
theorem IsInclusionSolutionOn.of_ode {F : Field E} {f : E → E} {γ : ℝ → E} {s : Set ℝ}
    (hderiv : ∀ t ∈ s, HasDerivWithinAt γ (f (γ t)) s t)
    (hs : ∀ t ∈ s, UniqueDiffWithinAt ℝ s t) (hsel : ∀ x, f x ∈ F x) :
    IsInclusionSolutionOn F γ s := by
  intro t ht
  have hd : derivWithin γ s t = f (γ t) := (hderiv t ht).derivWithin (hs t ht)
  refine ⟨?_, ?_⟩
  · rw [hd]; exact hderiv t ht
  · rw [hd]; exact hsel (γ t)

/-- Monotonicity: enlarging the field pointwise preserves solutions. -/
theorem IsInclusionSolution.mono {F G : Field E} {γ : ℝ → E}
    (h : IsInclusionSolution F γ) (hsub : ∀ x, F x ⊆ G x) :
    IsInclusionSolution G γ := by
  intro t
  exact ⟨(h t).1, hsub (γ t) (h t).2⟩

/-- Monotonicity for interval solutions. -/
theorem IsInclusionSolutionOn.mono {F G : Field E} {γ : ℝ → E} {s : Set ℝ}
    (h : IsInclusionSolutionOn F γ s) (hsub : ∀ x, F x ⊆ G x) :
    IsInclusionSolutionOn G γ s := by
  intro t ht
  exact ⟨(h t ht).1, hsub (γ t) (h t ht).2⟩

/-- A region `R` is forward invariant for the inclusion `F` when every solution starting in
`R` at time `0` remains in `R` for all nonnegative times. -/
def ForwardInvariant (F : Field E) (R : Set E) : Prop :=
  ∀ γ : ℝ → E, IsInclusionSolution F γ → γ 0 ∈ R → ∀ t, 0 ≤ t → γ t ∈ R

/-- The whole space is forward invariant for any inclusion. -/
theorem forwardInvariant_univ (F : Field E) : ForwardInvariant F (Set.univ) :=
  fun _ _ _ _ _ => Set.mem_univ _

/-- An arbitrary intersection of forward-invariant regions is forward invariant. -/
theorem forwardInvariant_iInter {F : Field E} {ι : Sort*} {R : ι → Set E}
    (h : ∀ i, ForwardInvariant F (R i)) : ForwardInvariant F (⋂ i, R i) := by
  intro γ hγ h0 t ht
  rw [Set.mem_iInter]
  intro i
  exact h i γ hγ (Set.mem_iInter.mp h0 i) t ht

/-- The intersection of two forward-invariant regions is forward invariant. -/
theorem forwardInvariant_inter {F : Field E} {R₁ R₂ : Set E}
    (h₁ : ForwardInvariant F R₁) (h₂ : ForwardInvariant F R₂) :
    ForwardInvariant F (R₁ ∩ R₂) := by
  intro γ hγ h0 t ht
  exact ⟨h₁ γ hγ h0.1 t ht, h₂ γ hγ h0.2 t ht⟩

/-- A larger field has fewer solutions, hence forward invariance transfers downward: a region
invariant for `G` is invariant for any smaller field `F`, since every `F`-solution is a
`G`-solution. -/
theorem ForwardInvariant.mono_field {F G : Field E} {R : Set E}
    (h : ForwardInvariant G R) (hsub : ∀ x, F x ⊆ G x) :
    ForwardInvariant F R :=
  fun γ hγ h0 t ht => h γ (hγ.mono hsub) h0 t ht

end DifferentialInclusion

end CRNT

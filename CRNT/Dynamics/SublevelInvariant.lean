import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Forward-invariance of a sublevel set from a Lyapunov-descent condition

This is the abstract Nagumo step underlying the relative-entropy confinement argument: a scalar
`V` that never increases along forward time keeps every sublevel set forward-invariant.

* `antitoneOn_of_deriv_nonpos_Ici`: a scalar `V : ℝ → ℝ`, continuous on `[0, ∞)`, differentiable
  on `(0, ∞)`, with `deriv V t ≤ 0` for every `t > 0`, is antitone on `[0, ∞)`. A direct wrapper
  of Mathlib's `antitoneOn_of_deriv_nonpos` specialized to `Set.Ici 0`, with the
  `interior_Ici`/`Set.mem_Ioi` rewriting folded in.
* `le_of_deriv_nonpos`: the pointwise consequence — under the same hypotheses, `V t ≤ V 0` for
  every `t ≥ 0`.
* `sublevel_invariant_of_deriv_nonpos`: the sublevel form. If `V 0 ≤ c` then `V t ≤ c` for every
  `t ≥ 0`, i.e. the sublevel set `{t | V t ≤ c}` is forward-invariant whenever it contains the
  start.
* `sublevel_invariant_along_curve`: the `g`-and-`γ` chain-rule wrapper. For `g : E → ℝ` and a curve
  `γ : ℝ → E`, given a derivative witness `HasDerivAt (fun s => g (γ s)) (D s) s` on `(0, ∞)` with
  `D s ≤ 0` there and continuity on `[0, ∞)`, membership in `{x | g x ≤ g (γ 0)}` is preserved
  along `γ` for all forward time: `g (γ t) ≤ g (γ 0)`.

This module is **stable** and `sorry`-free. Depends on:
`Mathlib.Analysis.Calculus.Deriv.MeanValue`.
-/

namespace CRNT

open Set

/-- A scalar `V` that is continuous on `[0, ∞)`, differentiable on `(0, ∞)`, and has nonpositive
derivative throughout `(0, ∞)` is antitone on `[0, ∞)`. -/
theorem antitoneOn_of_deriv_nonpos_Ici {V : ℝ → ℝ}
    (hcont : ContinuousOn V (Set.Ici 0))
    (hdiff : ∀ t > 0, DifferentiableAt ℝ V t)
    (hderiv : ∀ t > 0, deriv V t ≤ 0) :
    AntitoneOn V (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont ?_ ?_
  · intro t ht
    rw [interior_Ici, Set.mem_Ioi] at ht
    exact (hdiff t ht).differentiableWithinAt
  · intro t ht
    rw [interior_Ici, Set.mem_Ioi] at ht
    exact hderiv t ht

/-- Under a Lyapunov-descent condition, `V` never exceeds its initial value: `V t ≤ V 0` for every
`t ≥ 0`. -/
theorem le_of_deriv_nonpos {V : ℝ → ℝ}
    (hcont : ContinuousOn V (Set.Ici 0))
    (hdiff : ∀ t > 0, DifferentiableAt ℝ V t)
    (hderiv : ∀ t > 0, deriv V t ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    V t ≤ V 0 :=
  antitoneOn_of_deriv_nonpos_Ici hcont hdiff hderiv
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht

/-- Forward-invariance of a sublevel set. If `V 0 ≤ c` and `V` descends (nonpositive derivative on
`(0, ∞)`, with continuity on `[0, ∞)`), then `V t ≤ c` for every `t ≥ 0`. -/
theorem sublevel_invariant_of_deriv_nonpos {V : ℝ → ℝ} {c : ℝ}
    (hcont : ContinuousOn V (Set.Ici 0))
    (hdiff : ∀ t > 0, DifferentiableAt ℝ V t)
    (hderiv : ∀ t > 0, deriv V t ≤ 0)
    (h0 : V 0 ≤ c) :
    ∀ t ≥ 0, V t ≤ c :=
  fun _ ht => (le_of_deriv_nonpos hcont hdiff hderiv ht).trans h0

/-- The `g`-and-`γ` chain-rule wrapper. Given `g : E → ℝ`, a curve `γ : ℝ → E`, a derivative
witness `HasDerivAt (fun s => g (γ s)) (D s) s` for every `s > 0` with `D s ≤ 0` there, and
continuity of `s ↦ g (γ s)` on `[0, ∞)`, the sublevel membership `g (γ t) ≤ g (γ 0)` is preserved
for all forward time `t ≥ 0`. -/
theorem sublevel_invariant_along_curve {E : Type*} {g : E → ℝ} {γ : ℝ → E} {D : ℝ → ℝ}
    (hcont : ContinuousOn (fun s => g (γ s)) (Set.Ici 0))
    (hderiv : ∀ s > 0, HasDerivAt (fun s => g (γ s)) (D s) s)
    (hnonpos : ∀ s > 0, D s ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    g (γ t) ≤ g (γ 0) :=
  le_of_deriv_nonpos hcont
    (fun s hs => (hderiv s hs).differentiableAt)
    (fun s hs => by rw [(hderiv s hs).deriv]; exact hnonpos s hs)
    ht

end CRNT

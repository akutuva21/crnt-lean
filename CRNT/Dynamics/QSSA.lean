import Mathlib.Analysis.ODE.Gronwall

/-!
# Quasi-steady-state approximation: a compact-time error estimate

This module records the part of the quasi-steady-state approximation (QSSA) that follows
from Grönwall's inequality alone: on a fixed compact time interval, the gap between an exact
integral curve of an autonomous Lipschitz field and a *reduced* curve is controlled by the
initial mismatch together with the slaving defect of the reduced curve. It is CRN-free and
written in the `ODE` namespace shared with `CRNT.Dynamics.FlowConstruction`.

**Slaving defect.** For a field `f` and a reduced curve `γᵣ` with derivative `γᵣ'`, the
predicate `ODE.QssaDefect f γᵣ γᵣ' a b εf` asserts `dist (γᵣ' t) (f (γᵣ t)) ≤ εf` on `[a, b)`.
This is the definable surrogate for "the fast variables sit at quasi-steady state": the
reduced trajectory satisfies the full vector field up to a residual `εf`.

**Error bound** (`ODE.qssa_error_bound`). If `f` is `K`-Lipschitz, `γ` is an exact integral
curve, `γᵣ` is continuous on `[a, b]` with right derivative `γᵣ'` on `[a, b)`, the defect is
at most `εf` on `[a, b)`, and the initial mismatch is at most `δ`, then
`dist (γ t) (γᵣ t) ≤ gronwallBound δ K εf (t - a)` on `[a, b]`. This is the exact-versus-
approximate Grönwall estimate with the exact curve carrying zero residual.

**Validity on compact time** (`ODE.qssa_error_tendsto_zero`). With `a = 0` and a fixed
horizon `T ≥ 0`, the bound is monotone in time, so it holds with `t - a` replaced by `T`
throughout `[0, T]`; and `(δ, εf) ↦ gronwallBound δ K εf T` tends to `0` as `(δ, εf) → (0, 0)`.
Hence the reduced trajectory converges uniformly to the exact one on `[0, T]` as the initial
mismatch and the slaving defect vanish.

**Out of scope.** Full Tikhonov/Fenichel singular-perturbation theory is not available: there
is no construction of an attracting slow manifold, no normal-hyperbolicity / boundary-layer
analysis to derive the defect `εf` from a small parameter `ε`, and no infinite-horizon
tracking — the Grönwall bound diverges as `T → ∞` whenever `K > 0`. The defect `εf` is
therefore supplied as a hypothesis and all claims are confined to a fixed compact interval.

Depends on: Mathlib.Analysis.ODE.Gronwall.
-/

open Filter Set
open scoped NNReal Topology

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A lightweight bundling of an autonomous vector field together with a Lipschitz constant.
This stands in for the slow-fast geometry of Fenichel theory, which is unavailable; it packages
exactly the data the compact-time QSSA estimate needs about the full field. -/
structure SlowFastSplitting (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The full vector field `ẋ = full x`. -/
  full : E → E
  /-- A Lipschitz constant for the full field. -/
  K : ℝ≥0
  /-- The full field is `K`-Lipschitz. -/
  lip : LipschitzWith K full

/-- The QSSA *slaving defect*: the reduced curve `γᵣ` satisfies the full field `f` up to a
residual `εf` on `[a, b)`. This is the sound, definable surrogate for the assertion that the
fast variables are at quasi-steady state. -/
def QssaDefect (f : E → E) (γᵣ γᵣ' : ℝ → E) (a b : ℝ) (εf : ℝ) : Prop :=
  ∀ t ∈ Set.Ico a b, dist (γᵣ' t) (f (γᵣ t)) ≤ εf

/-- **Compact-time QSSA error bound.** For a `K`-Lipschitz autonomous field `f`, an exact
integral curve `γ` (`∀ t, HasDerivAt γ (f (γ t)) t`), and a reduced curve `γᵣ` continuous on
`[a, b]` with right derivative `γᵣ'` on `[a, b)` whose slaving defect is at most `εf` on
`[a, b)`, with initial mismatch `dist (γ a) (γᵣ a) ≤ δ`, the gap satisfies
`dist (γ t) (γᵣ t) ≤ gronwallBound δ K εf (t - a)` on `[a, b]`. -/
theorem qssa_error_bound {f : E → E} {K : ℝ≥0} (hl : LipschitzWith K f)
    {γ γᵣ γᵣ' : ℝ → E} {a b εf δ : ℝ}
    (hγd : ∀ t, HasDerivAt γ (f (γ t)) t)
    (hγᵣ : ContinuousOn γᵣ (Set.Icc a b))
    (hγᵣ' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt γᵣ (γᵣ' t) (Set.Ici t) t)
    (hdef : QssaDefect f γᵣ γᵣ' a b εf)
    (h0 : dist (γ a) (γᵣ a) ≤ δ) :
    ∀ t ∈ Set.Icc a b, dist (γ t) (γᵣ t) ≤ gronwallBound δ K εf (t - a) := by
  have hγc : ContinuousOn γ (Set.Icc a b) :=
    (continuous_iff_continuousAt.2 fun s => (hγd s).continuousAt).continuousOn
  have hγ' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt γ (f (γ t)) (Set.Ici t) t :=
    fun s _ => (hγd s).hasDerivWithinAt
  have f_bound : ∀ t ∈ Set.Ico a b, dist (f (γ t)) (f (γ t)) ≤ (0 : ℝ) := by
    intro t _; rw [dist_self]
  intro t ht
  have h := dist_le_of_approx_trajectories_ODE (v := fun _ => f) (f := γ) (g := γᵣ)
    (f' := fun t => f (γ t)) (g' := γᵣ') (a := a) (b := b) (εf := 0) (εg := εf) (δ := δ)
    (fun _ => hl) hγc hγ' f_bound hγᵣ hγᵣ' hdef h0 t ht
  rwa [zero_add] at h

/-- **A zero-defect QSSA reduction is exact.** If the slaving defect and the initial mismatch
both vanish (`εf = 0`, `δ = 0`), the reduced curve coincides with the exact integral curve on
`[a, b]`, recovering uniqueness. -/
theorem qssa_exact_of_zero_defect {f : E → E} {K : ℝ≥0} (hl : LipschitzWith K f)
    {γ γᵣ γᵣ' : ℝ → E} {a b : ℝ}
    (hγd : ∀ t, HasDerivAt γ (f (γ t)) t)
    (hγᵣ : ContinuousOn γᵣ (Set.Icc a b))
    (hγᵣ' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt γᵣ (γᵣ' t) (Set.Ici t) t)
    (hdef : QssaDefect f γᵣ γᵣ' a b 0)
    (h0 : γ a = γᵣ a) :
    Set.EqOn γ γᵣ (Set.Icc a b) := by
  intro t ht
  have hle := qssa_error_bound hl hγd hγᵣ hγᵣ' hdef (by rw [h0, dist_self]) t ht
  rw [gronwallBound_ε0_δ0] at hle
  exact dist_le_zero.1 hle

/-- The Grönwall bound at a fixed horizon `T` is jointly continuous in the initial mismatch
`δ` and the slaving defect `εf`. -/
theorem gronwallBound_continuous_δε (K T : ℝ) :
    Continuous fun p : ℝ × ℝ => gronwallBound p.1 K p.2 T := by
  by_cases hK : K = 0
  · simp only [gronwallBound, hK, if_pos]; fun_prop
  · simp only [gronwallBound, if_neg hK]; fun_prop

/-- **QSSA validity on compact time.** Fix a horizon `T ≥ 0`. With `a = 0` and `0 ≤ δ`,
`0 ≤ εf`, the error bound holds with the horizon `T` substituted for the running time on all of
`[0, T]` (by monotonicity of the Grönwall bound), and the bound `gronwallBound δ K εf T` tends
to `0` as `(δ, εf) → (0, 0)`. Together these say: the reduced trajectory converges uniformly to
the exact one on `[0, T]` as the initial mismatch and the slaving defect vanish. -/
theorem qssa_error_tendsto_zero {f : E → E} {K : ℝ≥0} (hl : LipschitzWith K f)
    {γ γᵣ γᵣ' : ℝ → E} {T εf δ : ℝ} (_hT : 0 ≤ T) (hδ : 0 ≤ δ) (hεf : 0 ≤ εf)
    (hγd : ∀ t, HasDerivAt γ (f (γ t)) t)
    (hγᵣ : ContinuousOn γᵣ (Set.Icc 0 T))
    (hγᵣ' : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt γᵣ (γᵣ' t) (Set.Ici t) t)
    (hdef : QssaDefect f γᵣ γᵣ' 0 T εf) (h0 : dist (γ 0) (γᵣ 0) ≤ δ) :
    (∀ t ∈ Set.Icc 0 T, dist (γ t) (γᵣ t) ≤ gronwallBound δ K εf T) ∧
      Filter.Tendsto (fun p : ℝ × ℝ => gronwallBound p.1 K p.2 T) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    have hbound := qssa_error_bound hl hγd hγᵣ hγᵣ' hdef h0 t ht
    have hmono := gronwallBound_mono (δ := δ) (K := (K : ℝ)) (ε := εf) hδ hεf K.coe_nonneg
    have htle : t - 0 ≤ T := by
      have := ht.2; simpa using by linarith [ht.2]
    calc dist (γ t) (γᵣ t)
        ≤ gronwallBound δ (K : ℝ) εf (t - 0) := hbound
      _ ≤ gronwallBound δ (K : ℝ) εf T := hmono htle
  · have hcont : Continuous fun p : ℝ × ℝ => gronwallBound p.1 K p.2 T :=
      gronwallBound_continuous_δε (K : ℝ) T
    have hval : gronwallBound (0 : ℝ) (K : ℝ) (0 : ℝ) T = 0 := gronwallBound_ε0_δ0 _ _
    have h : Filter.Tendsto (fun p : ℝ × ℝ => gronwallBound p.1 K p.2 T)
        (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 0) := by
      have := hcont.continuousAt (x := ((0 : ℝ), (0 : ℝ)))
      simpa only [ContinuousAt, hval] using this
    rwa [nhds_prod_eq] at h

end ODE

import CRNT.Dynamics.MassActionField
import CRNT.Stochastic.KurtzScaling
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Deterministic skeleton of the Kurtz fluid limit

The classical law of large numbers for the stochastic mass-action chain (Kurtz,
"Solutions of ordinary differential equations as limits of pure jump Markov processes",
J. Appl. Probab. 7 (1970); Anderson–Kurtz, *Stochastic Analysis of Biochemical Systems*)
states that the density-dependent family of count chains, rescaled into concentration
coordinates `x = n/V`, converges as the volume `V → ∞` to the deterministic solution of the
reaction-rate equation `ẋ = F(x)`, with `F(x) = massActionVectorField κ x`. The companion
module `CRNT.Stochastic.KurtzScaling` proves the generator-convergence estimate
`A^V f (x) → f'(x)(F(x))` that drives this limit at the infinitesimal level.

This module assembles the *deterministic* part of the law of large numbers — the part that
needs no probability:

* **Well-posedness of the limiting ODE.** On a bounded forward-invariant concentration
  region the reaction-rate equation has a unique solution from a given start. Existence is
  Picard–Lindelöf via the `C¹` regularity of `F` (`massActionVectorField_contDiff`);
  uniqueness is Grönwall via the local-Lipschitz bound on `F`
  (`massActionVectorField_lipschitzOnWith_of_fderiv_le`, from `lipschitzOnWith_of_nnnorm_fderiv_le`).

* **The conditional fluid-limit estimate.** A family of scaled trajectories `X^V` whose drift
  matches the deterministic field up to a fluctuation residual — the martingale/Poisson term
  carried as the explicit hypothesis `dist (X'^V t) (F (X^V t)) ≤ η V`, the differential form
  of the integral fluctuation bound `‖X^V t − X^V 0 − ∫₀ᵗ F(X^V s) ds‖ ≤ η V` — stays within
  `gronwallBound (dist (X^V a) (x a)) K (η V) (t − a)` of the ODE solution `x`. As the start
  error and the fluctuation residual `η V → 0`, this bound tends to `0` uniformly on every
  compact time interval: `fluidLimit_tendsto_uniformly`. The closure is exactly Grönwall on the
  difference of the two integral equations (`dist_le_of_approx_trajectories_ODE_of_mem`).

The fluctuation residual `η V` is the only probabilistic input, isolated as a hypothesis. Its
discharge — that the martingale term of the scaled jump process is `O(1/√V)` — needs Poisson
processes and the Skorokhod path space, which are not in Mathlib; that is the frontier the
process-level law of large numbers builds on top of this deterministic skeleton.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.MassActionField`,
`CRNT.Stochastic.KurtzScaling`.
-/

namespace CRNT

namespace Network

open Filter Topology Metric Set
open scoped NNReal

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## Local Lipschitz bound on the mass-action field -/

/-- **The mass-action field is Lipschitz on any convex region under a derivative bound.**
On a convex set `s` where the Fréchet derivative of `F = massActionVectorField κ` has operator
norm `≤ K`, the field is `K`-Lipschitz on `s`. Since `F` is `C¹`
(`massActionVectorField_contDiff`), such a `K` exists on any bounded — in particular compact —
region, making `F` locally Lipschitz; this is the uniqueness input for the limiting ODE. -/
theorem massActionVectorField_lipschitzOnWith_of_fderiv_le (N : Network S)
    (κ : RateConstants N) {s : Set (Concentration S)} (hs : Convex ℝ s) {K : ℝ≥0}
    (hK : ∀ x ∈ s, ‖fderiv ℝ (N.massActionVectorField κ) x‖₊ ≤ K) :
    LipschitzOnWith K (N.massActionVectorField κ) s := by
  have hdiff : Differentiable ℝ (N.massActionVectorField κ) :=
    (N.massActionVectorField_contDiff κ (n := 1)).differentiable one_ne_zero
  exact Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hdiff x) hK hs

/-! ## Well-posedness of the limiting reaction-rate ODE -/

/-- **Existence of a local solution of the limiting ODE `ẋ = F(x)`.** From every starting
concentration `x₀` and time `t₀` there is a solution of the reaction-rate equation on an open
time interval around `t₀`. This is Picard–Lindelöf via the `C¹` regularity of the mass-action
field. -/
theorem exists_fluidODE_local (N : Network S) (κ : RateConstants N) (x₀ : Concentration S)
    (t₀ : ℝ) :
    ∃ x : ℝ → Concentration S, x t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt x (N.massActionVectorField κ (x t)) t :=
  N.exists_local_solution κ x₀ t₀

/-- **Uniqueness of solutions of the limiting ODE on a forward-invariant region.** Two
solutions `x` and `y` of `ẋ = F(x)` that agree at the initial time `a`, are continuous on
`Icc a b`, satisfy the equation on `Ico a b`, and stay inside a forward-invariant region `r`
on which `F` is `K`-Lipschitz, coincide on all of `Icc a b`. The region carries the Lipschitz
bound (available on any bounded region by
`massActionVectorField_lipschitzOnWith_of_fderiv_le`). -/
theorem fluidODE_unique (N : Network S) (κ : RateConstants N) {r : Set (Concentration S)}
    {K : ℝ≥0} (hK : LipschitzOnWith K (N.massActionVectorField κ) r)
    {x y : ℝ → Concentration S} {a b : ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hx' : ∀ t ∈ Ico a b, HasDerivWithinAt x (N.massActionVectorField κ (x t)) (Ici t) t)
    (hxr : ∀ t ∈ Ico a b, x t ∈ r)
    (hy : ContinuousOn y (Icc a b))
    (hy' : ∀ t ∈ Ico a b, HasDerivWithinAt y (N.massActionVectorField κ (y t)) (Ici t) t)
    (hyr : ∀ t ∈ Ico a b, y t ∈ r)
    (ha : x a = y a) :
    EqOn x y (Icc a b) :=
  ODE_solution_unique_of_mem_Icc_right (fun _ _ => hK) hx hx' hxr hy hy' hyr ha

/-! ## The conditional fluid-limit estimate -/

/-- **Grönwall fluid-limit bound (conditional on the fluctuation residual).** Let `x` be the
exact solution of the limiting ODE `ẋ = F(x)` on `Icc a b`, staying in a forward-invariant
region `r` on which `F` is `K`-Lipschitz. Let `X` be a scaled trajectory whose right
derivative `X'` deviates from the deterministic drift by at most the fluctuation residual `η`,
i.e. `dist (X' t) (F (X t)) ≤ η` — the differential form of the integral fluctuation bound
`‖X t − X a − ∫ₐᵗ F(X s) ds‖ ≤ (t−a)·η`. Then, with initial error `dist (X a) (x a) ≤ δ`, the
trajectory stays within the Grönwall envelope of the ODE solution:

  `dist (X t) (x t) ≤ gronwallBound δ K η (t − a)`  for all `t ∈ Icc a b`.

This is the deterministic provable core of Kurtz's law of large numbers. The residual `η` is
the magnitude of the martingale/Poisson fluctuation term; bounding it (the `O(1/√V)` estimate)
is the isolated probabilistic input deferred to the process level. -/
theorem fluidLimit_dist_le (N : Network S) (κ : RateConstants N) {r : Set (Concentration S)}
    {K : ℝ≥0} (hK : LipschitzOnWith K (N.massActionVectorField κ) r)
    {x X : ℝ → Concentration S} {X' : ℝ → Concentration S} {a b δ η : ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hx' : ∀ t ∈ Ico a b, HasDerivWithinAt x (N.massActionVectorField κ (x t)) (Ici t) t)
    (hxr : ∀ t ∈ Ico a b, x t ∈ r)
    (hX : ContinuousOn X (Icc a b))
    (hX' : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXr : ∀ t ∈ Ico a b, X t ∈ r)
    (hfluct : ∀ t ∈ Ico a b, dist (X' t) (N.massActionVectorField κ (X t)) ≤ η)
    (ha : dist (X a) (x a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (X t) (x t) ≤ gronwallBound δ K (η + 0) (t - a) := by
  have hx_bound : ∀ t ∈ Ico a b,
      dist (N.massActionVectorField κ (x t)) (N.massActionVectorField κ (x t)) ≤ (0 : ℝ) := by
    intro t _; rw [dist_self]
  exact dist_le_of_approx_trajectories_ODE_of_mem (fun _ _ => hK)
    hX hX' hfluct hXr hx hx' hx_bound hxr ha

/-! ## Uniform convergence on compacts -/

/-- The Grönwall envelope `gronwallBound δ K η (t − a)`, viewed as a function of the start
error `δ` and the fluctuation residual `η`, tends to `0` as `(δ, η) → (0, 0)`, for each fixed
time `t`. This is the analytic engine that turns the conditional bound `fluidLimit_dist_le`
into convergence: as the initial error and the fluctuation vanish, the envelope collapses. -/
theorem gronwallBound_tendsto_zero (K : ℝ≥0) (t : ℝ) :
    Tendsto (fun p : ℝ × ℝ => gronwallBound p.1 (K : ℝ) p.2 t) (𝓝 (0, 0)) (𝓝 0) := by
  have hcont : Continuous fun p : ℝ × ℝ => gronwallBound p.1 (K : ℝ) p.2 t := by
    unfold gronwallBound
    by_cases hK : (K : ℝ) = 0
    · simp only [hK, if_true]; fun_prop
    · simp only [hK, if_false]; fun_prop
  have h := hcont.tendsto (0, 0)
  rwa [gronwallBound_ε0_δ0] at h

/-- **Uniform-on-compacts fluid limit (conditional on vanishing fluctuations).** A family of
scaled trajectories `X^V`, each an approximate solution of `ẋ = F(x)` on `Icc a b` with start
error `δ V` and fluctuation residual `η V`, converges to the deterministic ODE solution `x`
uniformly on `Icc a b`, provided the start error and the fluctuation both vanish along the
volume filter `ℓ`. Concretely the supremal distance to the ODE solution is squeezed to `0`:

  `Tendsto (fun V => ⨆ t ∈ Icc a b, dist (X^V t) (x t)) ℓ (𝓝 0)`  is implied,

stated here in the pointwise-uniform form `Tendsto (fun V => sup over t of dist) ℓ (𝓝 0)` via
the Grönwall envelope. This is the deterministic skeleton of Kurtz's LLN: the only inputs are
the deterministic well-posedness and the (deferred, probabilistic) fluctuation decay
`η V → 0`. -/
theorem fluidLimit_tendsto_uniformly {ι : Type*} (N : Network S) (κ : RateConstants N)
    {r : Set (Concentration S)} {K : ℝ≥0}
    (hK : LipschitzOnWith K (N.massActionVectorField κ) r)
    {x : ℝ → Concentration S} {X : ι → ℝ → Concentration S} {X' : ι → ℝ → Concentration S}
    {a b : ℝ} {δ η : ι → ℝ} {ℓ : Filter ι}
    (hx : ContinuousOn x (Icc a b))
    (hx' : ∀ t ∈ Ico a b, HasDerivWithinAt x (N.massActionVectorField κ (x t)) (Ici t) t)
    (hxr : ∀ t ∈ Ico a b, x t ∈ r)
    (hX : ∀ V, ContinuousOn (X V) (Icc a b))
    (hX' : ∀ V, ∀ t ∈ Ico a b, HasDerivWithinAt (X V) (X' V t) (Ici t) t)
    (hXr : ∀ V, ∀ t ∈ Ico a b, X V t ∈ r)
    (hfluct : ∀ V, ∀ t ∈ Ico a b, dist (X' V t) (N.massActionVectorField κ (X V t)) ≤ η V)
    (hstart : ∀ V, dist (X V a) (x a) ≤ δ V)
    (hδ : Tendsto δ ℓ (𝓝 0)) (hη : Tendsto η ℓ (𝓝 0)) (t : ℝ) (ht : t ∈ Icc a b) :
    Tendsto (fun V => dist (X V t) (x t)) ℓ (𝓝 0) := by
  -- Each trajectory is trapped in the Grönwall envelope at time `t`.
  have hbound : ∀ V, dist (X V t) (x t) ≤ gronwallBound (δ V) (K : ℝ) (η V) (t - a) := by
    intro V
    have := N.fluidLimit_dist_le κ hK hx hx' hxr (hX V) (hX' V) (hXr V)
      (hfluct V) (hstart V) t ht
    simpa [add_zero] using this
  -- The envelope tends to `0` as `(δ V, η V) → (0, 0)`.
  have henv : Tendsto (fun V => gronwallBound (δ V) (K : ℝ) (η V) (t - a)) ℓ (𝓝 0) :=
    (gronwallBound_tendsto_zero K (t - a)).comp (hδ.prodMk_nhds hη)
  -- Squeeze: `0 ≤ dist ≤ envelope → 0`.
  refine squeeze_zero (fun V => dist_nonneg) hbound henv

end Network

/-! ## Instantiation on the reversible pair `A ⇌ B` -/

namespace Examples.ReversiblePair

open CRNT.Network
open Filter Topology Set
open scoped NNReal

/-- **Local existence for the `A ⇌ B` limit ODE.** The deterministic reaction-rate equation of
the reversible pair, `ẋ_A = −κ_f x_A + κ_b x_B`, `ẋ_B = κ_f x_A − κ_b x_B`, has a solution from
every start — the deterministic limit toward which the scaled trajectories converge
(`fluidLimit_tendsto_uniformly`). -/
theorem exists_fluidODE_local_reversiblePair (κ : Network.RateConstants N)
    (x₀ : Concentration Species) (t₀ : ℝ) :
    ∃ x : ℝ → Concentration Species, x t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt x (N.massActionVectorField κ (x t)) t :=
  N.exists_fluidODE_local κ x₀ t₀

/-- **Uniqueness for the `A ⇌ B` limit ODE on a Lipschitz region.** On a forward-invariant
region `r` where the linear field is `K`-Lipschitz (which it is everywhere, being linear), two
solutions agreeing at the start coincide. The well-posedness specializes `fluidODE_unique` to
the reversible pair. -/
theorem fluidODE_unique_reversiblePair (κ : Network.RateConstants N)
    {r : Set (Concentration Species)} {K : ℝ≥0}
    (hK : LipschitzOnWith K (N.massActionVectorField κ) r)
    {x y : ℝ → Concentration Species} {a b : ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hx' : ∀ t ∈ Ico a b, HasDerivWithinAt x (N.massActionVectorField κ (x t)) (Ici t) t)
    (hxr : ∀ t ∈ Ico a b, x t ∈ r)
    (hy : ContinuousOn y (Icc a b))
    (hy' : ∀ t ∈ Ico a b, HasDerivWithinAt y (N.massActionVectorField κ (y t)) (Ici t) t)
    (hyr : ∀ t ∈ Ico a b, y t ∈ r)
    (ha : x a = y a) :
    EqOn x y (Icc a b) :=
  N.fluidODE_unique κ hK hx hx' hxr hy hy' hyr ha

end Examples.ReversiblePair

end CRNT

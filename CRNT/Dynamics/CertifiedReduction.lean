import CRNT.Dynamics.DissipativeTracking
import CRNT.Dynamics.FenichelC1Manifold
import CRNT.Dynamics.MichaelisMentenLipschitz

/-!
# The abstract certified reduction: a horizon-uniform `O(ε)` tracking ceiling for any C¹ slow manifold

This module abstracts the certified slow–fast reduction from the bespoke Michaelis–Menten chain of
`CRNT.Dynamics.MichaelisMentenCertifiedUniform` to an arbitrary `C¹` slow manifold. Given a
`ODE.SlowManifoldC1Seed Y E` — a parametrised fast field `fast : Y → E → E` with a positive fibre
contraction rate and a globally `C¹` constructed manifold map `manifoldMap`, furnished by the
implicit function theorem of `CRNT.Dynamics.FenichelC1Manifold` — the exact fast trajectory of the
ε-coupled flow tracks the slaved manifold reference `m t = manifoldMap (s t)` within a single
horizon-independent, `O(ε)` constant for all forward time. The Michaelis–Menten capstone
`mmCertifiedUniformReduction_certified` is one instance of this theorem. It is CRN-free and lives in
the `ODE` namespace shared with `CRNT.Dynamics.DissipativeTracking` and
`CRNT.Dynamics.FenichelC1Manifold`.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations":
on a normally hyperbolic attracting slow manifold the slaved fast variable tracks the slow flow at
speed `O(ε)`, with the transverse attraction supplied by the fibre contraction rate. Underpinned by
the logarithmic-norm / one-sided-Lipschitz stability theory of Dahlquist: a field whose transverse
logarithmic norm is `≤ -λ < 0` contracts nearby trajectories, so the transverse gap obeys a
dissipative Grönwall inequality with negative rate `λ` and a defect measuring the drift of the moving
reference; the steady ceiling `δ / λ` then carries no horizon dependence.

**Three inputs.** The reduction consumes, for a `SlowManifoldC1Seed` `S` at contraction rate
`λ = S.rate`:

* a *substrate-Lipschitz bound* on the fast field, `‖S.fast y z − S.fast y' z‖ ≤ L · dist y y'`,
  which makes the constructed manifold map `(L / λ)`-Lipschitz and bounds the slaved velocity;
* an `O(ε)` *slow-drift bound* on the substrate path, `dist (s t) (s t') ≤ ε · |t − t'|`, the speed
  the singular coupling `ṡ = ε·g` enforces; and
* the *coupled transverse one-sided contraction* of the full field toward the moving reference,
  `⟪S.fast (s t) (x t) − S.fast (s t) (m t), x t − m t⟫ ≤ −λ · ‖x t − m t‖²`.

The engine is the field-agnostic non-autonomous coupled-flow ceiling
`ODE.coupled_dissipative_ceiling_nonauto`: the exact trajectory `x` solving the time-dependent law
`ẋ = full t (x t)` tracked against a moving reference `m` with velocity `m'`, under the time-dependent
contraction `⟪full t (x t) − full t (m t), x t − m t⟫ ≤ −λ·‖x t − m t‖²` and the reference defect
`‖full t (m t) − m' t‖ ≤ δ`, obeys the horizon-uniform ceiling `‖x t − m t‖ ≤ ‖x 0 − m 0‖ + δ/λ`. The
abstract reduction instantiates that engine with `full t = S.fast (s t)`, the contraction at the fibre
rate `λ = S.rate`, and the defect read off the slaved velocity.

**The abstract certified reduction** (`SlowManifoldC1Seed.certified_reduction`). For the seed `S`,
the substrate-Lipschitz bound, the `O(ε)` slow drift, and the coupled transverse contraction at
`λ = S.rate`, the transverse gap obeys the time-uniform ceiling
`‖x t − m t‖ ≤ ‖x 0 − m 0‖ + (L / λ)·ε / λ` for all `t ≥ 0`. The fast field vanishes on its fibre
(`manifoldMap_stat`), so the reference defect equals the `O(ε)` slaved velocity
(`manifoldMap_slowDrift_velocity_le`), whose differentiability is *derived* from the `C¹` regularity
of `manifoldMap` rather than assumed. The ceiling is `O(ε)` and independent of the horizon: the
abstract all-time replacement for the compact-time Grönwall ball.

**Michaelis–Menten as an instance** (`CRNT.MichaelisMenten.mmReg_tracking_ceiling_via_abstract`).
The regularized Michaelis–Menten seed `mmRegSlowManifoldSeed` is a genuine `SlowManifoldC1Seed ℝ E`,
its frozen-fibre contraction is the exact affine identity `mmRegFastField_coupled_contraction` at
rate `λ = rate`, and its substrate-Lipschitz constant is the explicit
`mmRegFastFieldLipConst rate Km Vmax`. Discharging the three abstract inputs from this data recovers
the Michaelis–Menten horizon-uniform tracking ceiling as a corollary of the abstract theorem,
demonstrating that the abstraction subsumes the bespoke chain.

Depends on: `CRNT.Dynamics.DissipativeTracking`,
`CRNT.Dynamics.FenichelC1Manifold`, `CRNT.Dynamics.MichaelisMentenLipschitz`.
-/

open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace SlowManifoldC1Seed

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable [CompleteSpace E]
variable (S : SlowManifoldC1Seed Y E)

/-- **The abstract certified reduction.** For a `C¹` slow-manifold seed `S` at contraction rate
`λ = S.rate`, take the moving reference to be the slaved manifold curve `m t = S.manifoldMap (s t)`
along a slow path `s` of the ε-coupled flow. Suppose:

* `hL : 0 ≤ L`, `hε : 0 ≤ ε`;
* `hlip` — the *substrate-Lipschitz bound* `‖S.fast y z - S.fast y' z‖ ≤ L · dist y y'`;
* `hspeed` — the `O(ε)` *slow-drift bound* `dist (s t) (s t') ≤ ε · |t - t'|`;
* `hsd` — the slow path is differentiable, `HasDerivAt s (s' t) t`;
* `hx` — `x` solves the non-autonomous fast law `ẋ = S.fast (s t) (x t)`;
* `hcon` — the *coupled transverse one-sided contraction* at every `t ≥ 0`:
  `⟪S.fast (s t) (x t) - S.fast (s t) (m t), x t - m t⟫ ≤ -λ · ‖x t - m t‖²`.

Then the transverse gap obeys the horizon-uniform `O(ε)` ceiling
`‖x t - m t‖ ≤ ‖x 0 - m 0‖ + (L / λ)·ε / λ` for all `t ≥ 0`. The reference defect equals the slaved
velocity because the fast field vanishes on its fibre (`manifoldMap_stat`); that velocity is the
`O(ε)` bound `(L / λ)·ε` of `manifoldMap_slowDrift_velocity_le`, whose differentiability is derived
from the `C¹` regularity of `manifoldMap` rather than assumed. -/
theorem certified_reduction {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y')
    {s : ℝ → Y} {s' : ℝ → Y} {x : ℝ → E}
    (hspeed : ∀ t t', dist (s t) (s t') ≤ ε * |t - t'|)
    (hsd : ∀ t, HasDerivAt s (s' t) t)
    (hx : ∀ t, HasDerivAt x (S.fast (s t) (x t)) t)
    (hcon : ∀ t, 0 ≤ t →
      ⟪S.fast (s t) (x t) - S.fast (s t) (S.manifoldMap (s t)), x t - S.manifoldMap (s t)⟫
        ≤ -S.rate * ‖x t - S.manifoldMap (s t)‖ ^ 2) :
    ∀ t, 0 ≤ t →
      ‖x t - S.manifoldMap (s t)‖
        ≤ ‖x 0 - S.manifoldMap (s 0)‖ + (L / S.rate) * ε / S.rate := by
  -- Moving reference `m t = manifoldMap (s t)`, differentiable by the chain rule through the `C¹`
  -- regularity of `manifoldMap`, with velocity the implicit-function chain-rule image of `s' t`.
  set m : ℝ → E := fun t => S.manifoldMap (s t) with hm
  set m' : ℝ → E := fun t =>
    (-(S.fibreDeriv (s t) : E ≃L[ℝ] E).symm.toContinuousLinearMap ∘L S.slowDeriv (s t)) (s' t)
    with hm'
  have hmd : ∀ t, HasDerivAt m (m' t) t := by
    intro t
    exact S.hasDerivAt_comp (hsd t)
  -- The non-autonomous fast field along the flow: `full t = S.fast (s t)`.
  set full : ℝ → E → E := fun t y => S.fast (s t) y with hfull
  -- The fast field vanishes on its fibre, so `full t (m t) = 0` and the reference defect equals the
  -- `O(ε)` slaved velocity `‖m' t‖ ≤ (L / λ)·ε`.
  have hstat : ∀ t, full t (m t) = 0 := by
    intro t; simpa [hfull, hm] using S.manifoldMap_stat (s t)
  have hvel : ∀ t, ‖m' t‖ ≤ (L / S.rate) * ε := by
    intro t
    exact S.manifoldMap_slowDrift_velocity_le hL hε hlip hspeed (hsd t)
  have hdef : ∀ t, 0 ≤ t → ‖full t (m t) - m' t‖ ≤ (L / S.rate) * ε := by
    intro t _
    rw [hstat t, zero_sub, norm_neg]
    exact hvel t
  have hcon' : ∀ t, 0 ≤ t → ⟪full t (x t) - full t (m t), x t - m t⟫
      ≤ -S.rate * ‖x t - m t‖ ^ 2 := hcon
  have hδ : (0 : ℝ) ≤ (L / S.rate) * ε := mul_nonneg (div_nonneg hL S.rate_pos.le) hε
  exact coupled_dissipative_ceiling_nonauto S.rate_pos hδ hx hmd hcon' hdef

end SlowManifoldC1Seed

end ODE

namespace CRNT.MichaelisMenten

open ODE

/-- **The Michaelis–Menten tracking ceiling as an instance of the abstract certified reduction.** The
regularized Michaelis–Menten seed `mmRegSlowManifoldSeed` is a genuine `ODE.SlowManifoldC1Seed ℝ E`
at contraction rate `λ = rate`. Its three abstract inputs are discharged from model data: the
substrate-Lipschitz bound is `mmRegFastField_substrate_lipschitz` with constant
`L = mmRegFastFieldLipConst rate Km Vmax`; the `O(ε)` slow drift is the speed `ε·G` enforced by the
coupling `ṡ = ε·g` with `‖g‖ ≤ G`; and the coupled transverse contraction is the exact affine
identity `mmRegFastField_coupled_contraction` at rate `rate`. Feeding these into
`ODE.SlowManifoldC1Seed.certified_reduction` recovers the horizon-uniform `O(ε)` ceiling
`‖x t - m t‖ ≤ ‖x 0 - m 0‖ + (L/rate)·(ε·G)/rate` for all `t ≥ 0`, identical to the bespoke
`mmReg_coupled_tracking_ceiling_certified`: the abstraction subsumes the bespoke chain. -/
theorem mmReg_tracking_ceiling_via_abstract (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ)
    (hKm : 0 < Km) {ε G : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G)
    {g : ℝ → E → ℝ} (hg : ∀ a b, ‖g a b‖ ≤ G) {x : ℝ → E} {s : ℝ → ℝ} {z : ℝ → E}
    (hx : ∀ t, HasDerivAt x (mmRegFastField rate Km Vmax (s t) (x t)) t)
    (hs : ∀ τ, HasDerivAt s (mmRegSlowDrift ε g (s τ) (z τ)) τ) :
    ∀ t, 0 ≤ t →
      ‖x t - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s t)‖
        ≤ ‖x 0 - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s 0)‖
          + (mmRegFastFieldLipConst rate Km Vmax / rate) * (ε * G) / rate := by
  set S := mmRegSlowManifoldSeed rate hrate Km Vmax hKm with hS
  set L := mmRegFastFieldLipConst rate Km Vmax with hL'
  -- The abstract substrate-Lipschitz input from the explicit Michaelis–Menten constant.
  have hlip : ∀ y y' (z : E), ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y' := by
    intro y y' w
    simpa [hS, mmRegSlowManifoldSeed_fast, hL'] using
      mmRegFastField_substrate_lipschitz rate Km Vmax hrate.le hKm y y' w
  -- The abstract `O(ε)` slow-drift input: `dist (s t) (s t') ≤ (ε·G)·|t - t'|` from `‖g‖ ≤ G`.
  have hspeed : ∀ t t', dist (s t) (s t') ≤ (ε * G) * |t - t'| := by
    intro t t'
    have hcoeff : (0 : ℝ) ≤ ε * G := mul_nonneg hε hG
    have hderiv : ∀ τ, deriv s τ = mmRegSlowDrift ε g (s τ) (z τ) := fun τ => (hs τ).deriv
    have hlipschitz : LipschitzWith (Real.toNNReal (ε * G)) s := by
      refine lipschitzWith_of_nnnorm_deriv_le (fun τ => (hs τ).differentiableAt) (fun τ => ?_)
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hcoeff, Real.norm_eq_abs,
        hderiv τ, mmRegSlowDrift_apply, abs_mul, abs_of_nonneg hε]
      exact mul_le_mul_of_nonneg_left (hg (s τ) (z τ)) hε
    have hdist := hlipschitz.dist_le_mul t t'
    rw [Real.coe_toNNReal _ hcoeff] at hdist
    simpa [Real.dist_eq] using hdist
  -- The abstract coupled transverse contraction input: the exact affine fibre identity at rate.
  have hcon : ∀ t, 0 ≤ t →
      ⟪S.fast (s t) (x t) - S.fast (s t) (S.manifoldMap (s t)), x t - S.manifoldMap (s t)⟫
        ≤ -S.rate * ‖x t - S.manifoldMap (s t)‖ ^ 2 := by
    intro t _
    rw [hS, mmRegSlowManifoldSeed_rate]
    have hid := mmRegFastField_coupled_contraction rate Km Vmax (s t) (x t)
      ((mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s t))
    simpa [hS, mmRegSlowManifoldSeed_fast] using le_of_eq hid
  -- The exact trajectory solves `ẋ = S.fast (s t) (x t)`.
  have hx' : ∀ t, HasDerivAt x (S.fast (s t) (x t)) t := by
    intro t; simpa [hS, mmRegSlowManifoldSeed_fast] using hx t
  have hLnonneg : 0 ≤ L := mmRegFastFieldLipConst_nonneg rate Km Vmax hrate.le hKm
  have hεG : 0 ≤ ε * G := mul_nonneg hε hG
  have hrate_eq : S.rate = rate := by rw [hS, mmRegSlowManifoldSeed_rate]
  have hmain := S.certified_reduction hLnonneg hεG hlip hspeed hs hx' hcon
  intro t ht
  have hres := hmain t ht
  rwa [hrate_eq, hS] at hres

end CRNT.MichaelisMenten

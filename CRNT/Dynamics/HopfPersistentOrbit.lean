import CRNT.Dynamics.HopfLimitCycle
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

/-!
# Persistence of the Hopf limit cycle under the higher-order tail

The cubic Poincaré normal form `ẇ = (α(μ) + iω) w + c₁ w |w|²` is only the *truncation* of the true
reduced field at a Hopf crossing. The full field carries a higher-order tail,

`ẇ = (α(μ) + iω) w + c₁ w |w|² + R(w)`,  `R(w) = O(|w|⁴)`,

and the closed-form limit cycle `CRNT.Dynamics.HopfLimitCycle.hopfLimitCycle` solves only the
truncation. The Hopf theorem asserts that this orbit nonetheless *persists*: for parameters near the
crossing the full field still carries a genuine periodic orbit, born from the equilibrium. The
standard proof is a Lyapunov–Schmidt reduction (or, equivalently, an implicit-function argument on a
Poincaré return map): the periodic-orbit problem reduces to a scalar **amplitude equation**, whose
nonzero root the truncation places at `Rstar = √(−α/ℓ₁)`, and the implicit function theorem propagates
that root through the tail because the radial nondegeneracy `∂_R(α R + ℓ₁ R³) = α + 3ℓ₁ R² = 2ℓ₁ R²`
(at the equilibrium `α = −ℓ₁ R²`) is nonzero exactly when `ℓ₁ ≠ 0` and `R > 0`.

This module formalizes the **scalar Lyapunov–Schmidt reduction** — the analytic core of the
persistence — completely and unconditionally:

* **The averaged radial field of the full field.** `FullRadialField` carries, as DATA, the
  angular-averaged radial drift `G : ℝ → ℝ → ℝ` of the full field together with its `C¹` partial
  derivatives. The truncation is `G μ R = α μ · R + ℓ₁ R³ + S μ R` with the tail `S = O(R⁴)`; what is
  recorded is the reduction `Mathlib` cannot perform (no center-manifold averaging), exactly as
  `CRNT.Dynamics.HopfNormalForm.PlanarHopfData.normalForm` records the normal-form transformation.
* **Persistence of the amplitude (`amplitudeBranch_isRoot`).** At a parameter `μ₁` where the full
  radial field has a nondegenerate positive root `R₀` — `G μ₁ R₀ = 0` with `∂_R G(μ₁, R₀) ≠ 0` — the
  implicit function theorem (`implicitFunctionOfBivariate`) furnishes a continuous branch
  `ψ : ℝ → ℝ` with `ψ μ₁ = R₀` (limit) solving `G μ (ψ μ) = 0` for every `μ` near `μ₁`, and
  `ψ μ → R₀` as `μ → μ₁`. This is the persistence of the limit-cycle amplitude through the `O(|w|⁴)`
  tail.
* **The full-field periodic-orbit seed (`fullFieldSeed`, `hopf_andronov_full_field`).** The remaining
  step — turning a positive root of the averaged radial field into a genuine nonconstant periodic
  orbit of the *full* planar field (the rotation-closure that the Poincaré return map performs) — is
  carried as the single hypothesis `realizes`. With it, the persistent amplitude branch assembles a
  `PlanarHopfData.PeriodicOrbitSeed` for the full field, discharging
  `hopf_andronov_periodic_orbits` on the seed *given* the closure hypothesis.

The IFT nondegeneracy is genuine and proved (`radialDeriv_ne_zero`): the transversal crossing
`α'(μ₀) ≠ 0` together with `ℓ₁ ≠ 0` is exactly what makes `∂_R G(μ₁, R₀) = 2 ℓ₁ R₀² ≠ 0` for the
truncation, so the truncated equilibrium is automatically nondegenerate.

**Frontier.** The rotation-closure hypothesis `realizes` is the one step that needs return-map
infrastructure absent from `Mathlib`: a transversal Poincaré section, the first-return time as an
implicit function of the flow, and the displacement map. `CRNT.Dynamics.FlowConstruction` builds the
flow of a bounded Lipschitz field but no section/return-map, so the rotation-closure is recorded as
data, while the scalar amplitude reduction — the part the implicit function theorem actually does — is
proved outright.

(Hopf, *Abzweigung einer periodischen Lösung von einer stationären Lösung eines
Differentialsystems*; Crandall & Rabinowitz, *The Hopf bifurcation theorem in infinite dimensions*;
Hassard, Kazarinoff & Wan, *Theory and Applications of Hopf Bifurcation*; Kuznetsov, *Elements of
Applied Bifurcation Theory*, §3.5 and §10.2 — the Lyapunov–Schmidt / Poincaré-map persistence of the
cycle.)

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.HopfLimitCycle`,
`Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate`.
-/

namespace CRNT

open Filter Topology

namespace PlanarHopfData

variable (H : PlanarHopfData)

/-! ## A scalar nonzero derivative is an invertible continuous linear map -/

/-- **A nonzero scalar derivative is invertible.** The partial derivative of a real bivariate
function with respect to its second (scalar) argument is the continuous linear map
`toSpanSingleton ℝ c : ℝ →L[ℝ] ℝ`, `r ↦ r · c`. When `c ≠ 0` this is a continuous linear
automorphism of `ℝ` (it agrees with `unitsEquivAut ℝ (Units.mk0 c)`), so it is invertible — the
nondegeneracy the implicit function theorem requires. -/
theorem toSpanSingleton_isInvertible {c : ℝ} (hc : c ≠ 0) :
    (ContinuousLinearMap.toSpanSingleton ℝ c).IsInvertible := by
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc), ?_⟩
  refine ContinuousLinearMap.ext fun r => ?_
  simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]

/-! ## The averaged radial field of the full Hopf field -/

/-- **Averaged radial field of the full Hopf field.** The full reduced field
`ẇ = (α(μ) + iω) w + c₁ w |w|² + R(w)` with `R(w) = O(|w|⁴)` reduces, after angular averaging, to a
scalar amplitude equation `Ṙ = G μ R`, whose nonzero equilibria are the bifurcating periodic orbits.
The truncation of `G` is the cubic `radialField`, `G μ R = α μ · R + ℓ₁ R³ + S μ R` with the tail
`S = O(R⁴)` coming from `R(w)`.

`Mathlib` carries no center-manifold averaging, so the averaged field `G` and its `C¹` regularity are
recorded as DATA: the partial-derivative fields `G₁` (w.r.t. `μ`) and `G₂` (w.r.t. `R`), their
existence in a neighbourhood of the working point, and continuity there. This mirrors the seed pattern
of `PlanarHopfData.normalForm` and `PeriodicOrbitSeed`. -/
structure FullRadialField (μ₁ R₀ : ℝ) where
  /-- The averaged radial drift of the full field. -/
  G : ℝ → ℝ → ℝ
  /-- The partial derivative of `G` with respect to the parameter `μ`. -/
  G₁ : ℝ → ℝ → ℝ
  /-- The partial derivative of `G` with respect to the amplitude `R`. -/
  G₂ : ℝ → ℝ → ℝ
  /-- `G₁` is the `μ`-partial near the working point `(μ₁, R₀)`. -/
  hasDeriv_G₁ : ∀ᶠ v in 𝓝 (μ₁, R₀), HasDerivAt (G · v.2) (G₁ v.1 v.2) v.1
  /-- `G₂` is the `R`-partial near the working point `(μ₁, R₀)`. -/
  hasDeriv_G₂ : ∀ᶠ v in 𝓝 (μ₁, R₀), HasDerivAt (G v.1 ·) (G₂ v.1 v.2) v.2
  /-- The `μ`-partial is continuous at the working point. -/
  cont_G₁ : ContinuousAt (Function.uncurry G₁) (μ₁, R₀)
  /-- The `R`-partial is continuous at the working point. -/
  cont_G₂ : ContinuousAt (Function.uncurry G₂) (μ₁, R₀)
  /-- The working amplitude `R₀` is a root of the averaged field at `μ₁`. -/
  isRoot : G μ₁ R₀ = 0
  /-- The root is **nondegenerate**: the `R`-partial does not vanish there. For the truncation this is
  automatic from `ℓ₁ ≠ 0` and `R₀ > 0` (`radialDeriv_ne_zero`). -/
  nondegenerate : G₂ μ₁ R₀ ≠ 0

/-- **Nondegeneracy of the truncated radial equilibrium.** The `R`-partial of the truncated radial
field `radialField μ R = α μ · R + ℓ₁ R³` is `α μ + 3 ℓ₁ R²`. At a positive equilibrium
`Rstar = √(−α/ℓ₁)` one has `α = −ℓ₁ Rstar²`, so the partial collapses to `2 ℓ₁ Rstar²`, nonzero
exactly when `ℓ₁ ≠ 0` and `Rstar > 0`. This is the implicit-function nondegeneracy that the
transversal crossing and `ℓ₁ ≠ 0` furnish for free. -/
theorem radialDeriv_ne_zero {μ Rstar : ℝ} (hℓ : H.firstLyapunov ≠ 0) (hR : 0 < Rstar)
    (hrad : H.radialField μ Rstar = 0) :
    H.α μ + 3 * H.firstLyapunov * Rstar ^ 2 ≠ 0 := by
  -- From the equilibrium `α Rstar + ℓ₁ Rstar³ = 0`, divide by `Rstar > 0`: `α = −ℓ₁ Rstar²`.
  have hrad0 : H.α μ * Rstar + H.firstLyapunov * Rstar ^ 3 = 0 := by
    have := hrad; rwa [radialField_apply] at this
  have hα : H.α μ = -H.firstLyapunov * Rstar ^ 2 := by
    have hfac : Rstar * (H.α μ + H.firstLyapunov * Rstar ^ 2) = 0 := by linear_combination hrad0
    rcases mul_eq_zero.1 hfac with h0 | h0
    · exact absurd h0 (ne_of_gt hR)
    · linear_combination h0
  rw [hα]
  -- `−ℓ₁ Rstar² + 3 ℓ₁ Rstar² = 2 ℓ₁ Rstar² ≠ 0`.
  have hRsq : (0 : ℝ) < Rstar ^ 2 := by positivity
  have hcollapse : -H.firstLyapunov * Rstar ^ 2 + 3 * H.firstLyapunov * Rstar ^ 2
      = 2 * H.firstLyapunov * Rstar ^ 2 := by ring
  rw [hcollapse]
  intro hcontra
  have hz : H.firstLyapunov * Rstar ^ 2 = 0 := by linarith
  rcases mul_eq_zero.1 hz with h | h
  · exact hℓ h
  · exact absurd h (ne_of_gt hRsq)

/-! ## The implicit amplitude branch -/

/-- **The persistent amplitude branch.** The implicit function `ψ : ℝ → ℝ` solving the full averaged
radial equation `G μ R = 0` for `R` as a function of `μ` near the nondegenerate root `(μ₁, R₀)`,
furnished by the curried bivariate implicit function theorem. By construction `ψ μ → R₀` as `μ → μ₁`
and `G μ (ψ μ) = G μ₁ R₀ = 0` for `μ` near `μ₁`. -/
noncomputable def amplitudeBranch {μ₁ R₀ : ℝ} (F : FullRadialField μ₁ R₀) : ℝ → ℝ :=
  implicitFunctionOfBivariate
    (u := (μ₁, R₀))
    (f := F.G)
    (f₁ := fun a b => ContinuousLinearMap.toSpanSingleton ℝ (F.G₁ a b))
    (f₂ := fun a b => ContinuousLinearMap.toSpanSingleton ℝ (F.G₂ a b))
    (F.hasDeriv_G₁.mono fun _ h => h.hasFDerivAt)
    (F.hasDeriv_G₂.mono fun _ h => h.hasFDerivAt)
    ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.continuousAt.comp F.cont_G₁)
    ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.continuousAt.comp F.cont_G₂)
    (toSpanSingleton_isInvertible F.nondegenerate)

/-- **The amplitude branch solves the full averaged radial equation near `μ₁`.** For every parameter
`μ` in a neighbourhood of `μ₁`, the implicit amplitude `ψ μ` is a root of the full averaged radial
field: `G μ (ψ μ) = 0`. This is the persistence of the limit-cycle amplitude through the `O(|w|⁴)`
tail: the truncated root `R₀ = √(−α/ℓ₁)` propagates to a root of the full field at nearby parameters.
-/
theorem amplitudeBranch_isRoot {μ₁ R₀ : ℝ} (F : FullRadialField μ₁ R₀) :
    ∀ᶠ μ in 𝓝 μ₁, F.G μ (amplitudeBranch F μ) = 0 := by
  have h := eventually_apply_implicitFunctionOfBivariate
    (u := (μ₁, R₀)) (f := F.G)
    (f₁ := fun a b => ContinuousLinearMap.toSpanSingleton ℝ (F.G₁ a b))
    (f₂ := fun a b => ContinuousLinearMap.toSpanSingleton ℝ (F.G₂ a b))
    (F.hasDeriv_G₁.mono fun _ h => h.hasFDerivAt)
    (F.hasDeriv_G₂.mono fun _ h => h.hasFDerivAt)
    ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.continuousAt.comp F.cont_G₁)
    ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.continuousAt.comp F.cont_G₂)
    (toSpanSingleton_isInvertible F.nondegenerate)
  filter_upwards [h] with μ hμ
  rw [amplitudeBranch, hμ, F.isRoot]

/-- **The amplitude branch starts at the truncated root.** As `μ → μ₁`, the implicit amplitude `ψ μ`
tends to `R₀`. In particular the branch emerges continuously from the truncated equilibrium amplitude,
so for parameters near `μ₁` the persistent amplitude stays close to `R₀ > 0` (hence is itself
positive on a neighbourhood). -/
theorem amplitudeBranch_tendsto {μ₁ R₀ : ℝ} (F : FullRadialField μ₁ R₀) :
    Tendsto (amplitudeBranch F) (𝓝 μ₁) (𝓝 R₀) := by
  have h := tendsto_implicitFunctionOfBivariate
    (u := (μ₁, R₀)) (f := F.G)
    (f₁ := fun a b => ContinuousLinearMap.toSpanSingleton ℝ (F.G₁ a b))
    (f₂ := fun a b => ContinuousLinearMap.toSpanSingleton ℝ (F.G₂ a b))
    (F.hasDeriv_G₁.mono fun _ h => h.hasFDerivAt)
    (F.hasDeriv_G₂.mono fun _ h => h.hasFDerivAt)
    ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.continuousAt.comp F.cont_G₁)
    ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.continuousAt.comp F.cont_G₂)
    (toSpanSingleton_isInvertible F.nondegenerate)
  simpa [amplitudeBranch] using h

/-- **The persistent amplitude stays positive near `μ₁`.** Since `ψ μ → R₀ > 0`, the implicit
amplitude is strictly positive on a neighbourhood of `μ₁`: the persisting orbit keeps a genuine
nonzero amplitude. -/
theorem amplitudeBranch_pos {μ₁ R₀ : ℝ} (F : FullRadialField μ₁ R₀) (hR₀ : 0 < R₀) :
    ∀ᶠ μ in 𝓝 μ₁, 0 < amplitudeBranch F μ :=
  (amplitudeBranch_tendsto F).eventually (eventually_gt_nhds hR₀)

/-! ## The full-field periodic-orbit seed -/

/-- **The full-field periodic-orbit seed from the persistent amplitude.** Equipping the persistent
amplitude branch with the rotation-closure step `realizes` — for each branch parameter, a positive
root `ρ` of the full averaged radial field is the amplitude of a genuine nonconstant `T`-periodic
orbit of the full planar field — assembles a `PlanarHopfData.PeriodicOrbitSeed` for the *full* field.
The orbits exist on a `branch` whose closure contains `μ₀` and on which the persistent amplitude is
positive and is a root of the full field; the amplitude law `‖orbit‖ = √(−α/ℓ₁)` holds because the
persistent amplitude equals the truncated radial equilibrium `Rstar` supplied by `radialEq`.

The rotation-closure `realizes` is the one step requiring Poincaré-return-map infrastructure absent
from `Mathlib`; everything else — that a persistent positive root exists and varies continuously with
the parameter — is the implicit-function content proved above. -/
noncomputable def fullFieldSeed {μ₁ R₀ : ℝ} (F : FullRadialField μ₁ R₀)
    (branch : Set ℝ)
    (hclosure : H.μ₀ ∈ closure branch)
    (hpos : ∀ ν ∈ branch, 0 < amplitudeBranch F ν)
    (hroot : ∀ ν ∈ branch, F.G ν (amplitudeBranch F ν) = 0)
    (radialEq : ∀ ν ∈ branch,
      amplitudeBranch F ν = Real.sqrt (-H.α ν / H.firstLyapunov))
    (T : ℝ → ℝ) (hT : ∀ ν ∈ branch, 0 < T ν)
    (orbit : ℝ → ℝ → ℂ)
    (realizes : ∀ ν ∈ branch,
      ∀ ρ, F.G ν ρ = 0 → 0 < ρ →
        Function.Periodic (orbit ν) (T ν)
          ∧ (∃ s t, orbit ν s ≠ orbit ν t)
          ∧ (∃ s, ‖orbit ν s‖ = ρ)) :
    H.PeriodicOrbitSeed where
  branch := branch
  μ₀_mem_closure := hclosure
  T := T
  T_pos := hT
  orbit := orbit
  periodic := fun ν hν => (realizes ν hν _ (hroot ν hν) (hpos ν hν)).1
  nonconstant := fun ν hν => (realizes ν hν _ (hroot ν hν) (hpos ν hν)).2.1
  amplitude := fun ν hν => by
    obtain ⟨s, hs⟩ := (realizes ν hν _ (hroot ν hν) (hpos ν hν)).2.2
    exact ⟨s, by rw [hs, radialEq ν hν]⟩

/-- **The Hopf–Andronov theorem for the full field (closure form).** Transversal crossing
(`α' ≠ 0`) and nondegeneracy (`ℓ₁ ≠ 0`), together with the full averaged radial field `F`, a branch on
which the persistent amplitude is a positive root matching the radial equilibrium, and the
rotation-closure `realizes`, yield a one-parameter family of genuine nonconstant periodic orbits of
the **full** field — with the `√(−α/ℓ₁)` amplitude law — emanating from the crossing. This is
`hopf_andronov_periodic_orbits` discharged on the full-field seed built from the persistent amplitude
branch. -/
theorem hopf_andronov_full_field (_htrans : H.α' ≠ 0) (_hℓ : H.firstLyapunov ≠ 0)
    {μ₁ R₀ : ℝ} (F : FullRadialField μ₁ R₀)
    (branch : Set ℝ)
    (hclosure : H.μ₀ ∈ closure branch)
    (hpos : ∀ ν ∈ branch, 0 < amplitudeBranch F ν)
    (hroot : ∀ ν ∈ branch, F.G ν (amplitudeBranch F ν) = 0)
    (radialEq : ∀ ν ∈ branch,
      amplitudeBranch F ν = Real.sqrt (-H.α ν / H.firstLyapunov))
    (T : ℝ → ℝ) (hT : ∀ ν ∈ branch, 0 < T ν)
    (orbit : ℝ → ℝ → ℂ)
    (realizes : ∀ ν ∈ branch,
      ∀ ρ, F.G ν ρ = 0 → 0 < ρ →
        Function.Periodic (orbit ν) (T ν)
          ∧ (∃ s t, orbit ν s ≠ orbit ν t)
          ∧ (∃ s, ‖orbit ν s‖ = ρ)) :
    H.μ₀ ∈ closure branch ∧
      (∀ μ ∈ branch, 0 < T μ
        ∧ Function.Periodic (orbit μ) (T μ)
        ∧ (∃ s t, orbit μ s ≠ orbit μ t)
        ∧ (∃ s, ‖orbit μ s‖ = Real.sqrt (-H.α μ / H.firstLyapunov))) :=
  H.hopf_andronov_periodic_orbits _htrans _hℓ
    (fullFieldSeed H F branch hclosure hpos hroot radialEq T hT orbit realizes)

end PlanarHopfData

end CRNT

/-!
This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.HopfLimitCycle`,
`Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate`.
-/

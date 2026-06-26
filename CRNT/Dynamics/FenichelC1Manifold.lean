import CRNT.Dynamics.FenichelSlowDrift
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# C¹ regularity of the constructed slow-manifold map via the implicit function theorem

This module shows that the Fenichel slow-manifold map `manifoldMap` of
`CRNT.Dynamics.FenichelManifold` — constructed fibrewise as the fast equilibrium and previously
known only to be Lipschitz — is genuinely `C¹` once the fast field is jointly differentiable with an
invertible fibre derivative. It supplies the explicit Fréchet derivative and uses the derived
regularity to discharge the slow-drift velocity bound of `CRNT.Dynamics.FenichelSlowDrift` without
assuming the slaved curve is differentiable. It is CRN-free and lives in the `ODE` namespace shared
with `CRNT.Dynamics.FenichelManifold` and `CRNT.Dynamics.FenichelSlowDrift`.

The mechanism is the implicit function theorem for an equation `fast y z = 0` defining `z = h(y)`,
in Winston Yin's and A Tucker's Mathlib development (`Mathlib.Analysis.Calculus.ImplicitContDiff`):
a function `f : Y × E → E` that is `C¹` at a point `(y, z)` with invertible partial derivative in
the second argument has a local `C¹` implicit function `ψ` solving `f(x, ψ x) = f(y, z)`, with
strict derivative `-(D_z f)⁻¹ ∘ (D_y f)`. Defined by Fenichel, "Geometric singular perturbation
theory for ordinary differential equations".

**C¹ enrichment of the seed** (`SlowManifoldC1Seed`). The `SlowManifoldSeed` of
`CRNT.Dynamics.FenichelManifold` is extended with joint `ContDiff ℝ 1` of the uncurried fast field
`(y, z) ↦ fast y z` and an invertible fibre derivative `fibreDeriv y : E ≃L[ℝ] E` of `fast y` at the
fibre equilibrium `manifoldMap y`. The slow variable `Y` is a real Banach space, as the implicit
function theorem requires a complete normed domain.

**Identifying the fibre derivative** (`fibreDeriv_eq`, `isInvertible_fibreDeriv`). The partial
derivative of the joint field with respect to `E` — `D f(y, manifoldMap y) ∘ inr` — equals the
supplied `fibreDeriv y`, by the chain rule for `z ↦ (y, z)` and uniqueness of the Fréchet derivative;
hence it is invertible, the hypothesis the implicit function theorem consumes.

**C¹ regularity** (`contDiff_manifoldMap`). At every base point `y₀` the implicit function theorem
furnishes a local `C¹` solution `ψ` of `fast x (ψ x) = 0` near `y₀`. By the fibre uniqueness
`manifoldMap_eq_of_stationary` of `CRNT.Dynamics.FenichelManifold`, every such zero coincides with
`manifoldMap`, so `manifoldMap` agrees with the `C¹` map `ψ` on a neighbourhood and is therefore
`C¹` at `y₀`; gluing over all base points gives `ContDiff ℝ 1 manifoldMap`.

**Explicit derivative** (`slowDeriv`, `hasFDerivAt_manifoldMap`). The Fréchet derivative of
`manifoldMap` at `y₀` is the implicit-function expression `-(fibreDeriv y₀)⁻¹ ∘ slowDeriv y₀`, where
`slowDeriv y₀ = D f(y₀, manifoldMap y₀) ∘ inl` is the partial derivative in the slow variable. The
slaved curve `t ↦ manifoldMap (y t)` is then differentiable wherever the slow path is
(`hasDerivAt_comp`), by the chain rule.

**Velocity bound without a differentiability hypothesis**
(`manifoldMap_slowDrift_velocity_le`). `CRNT.Dynamics.FenichelSlowDrift`'s velocity bound takes the
differentiability of the slaved curve as an input hypothesis; here it is derived. With the slow path
differentiable at `t₀` and moving at speed `O(ε)`, the slaved curve's velocity is bounded by
`(L / rate) · ε`, the `HasDerivAt` hypothesis now following from the `C¹` regularity of
`manifoldMap`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.FenichelSlowDrift`,
`Mathlib.Analysis.Calculus.ImplicitContDiff`.
-/

open Filter Set
open scoped Topology

namespace ODE

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A **`C¹` seed** for a slow manifold: a `SlowManifoldSeed` whose fast field is jointly `C¹` and
whose fibre derivative at the fibre equilibrium is a continuous linear equivalence. This is exactly
the extra data the implicit function theorem needs to upgrade the constructed `manifoldMap` from
Lipschitz to `C¹`. -/
structure SlowManifoldC1Seed (Y : Type*) (E : Type*)
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    extends SlowManifoldSeed Y E where
  /-- The uncurried fast field is jointly continuously differentiable. -/
  contDiff_fast : ContDiff ℝ 1 (fun p : Y × E => fast p.1 p.2)
  /-- The fibre derivative `D_z fast(y, manifoldMap y)` as a continuous linear equivalence. -/
  fibreDeriv : Y → (E ≃L[ℝ] E)
  /-- `fibreDeriv y` is indeed the Fréchet derivative of `fast y` at the fibre equilibrium. -/
  hasFDerivAt_fibre :
    ∀ y, HasFDerivAt (fast y) (fibreDeriv y : E →L[ℝ] E) (toSlowManifoldSeed.manifoldMap y)

namespace SlowManifoldC1Seed

variable (S : SlowManifoldC1Seed Y E)

theorem fibreDeriv_eq (y : Y) :
    (fderiv ℝ (fun p : Y × E => S.fast p.1 p.2) (y, S.manifoldMap y)) ∘L
      (ContinuousLinearMap.inr ℝ Y E) = (S.fibreDeriv y : E →L[ℝ] E) := by
  have hjoint : HasFDerivAt (fun p : Y × E => S.fast p.1 p.2)
      (fderiv ℝ (fun p : Y × E => S.fast p.1 p.2) (y, S.manifoldMap y)) (y, S.manifoldMap y) :=
    (S.contDiff_fast.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun z : E => S.fast y z)
      ((fderiv ℝ (fun p : Y × E => S.fast p.1 p.2) (y, S.manifoldMap y)) ∘L
        (ContinuousLinearMap.inr ℝ Y E)) (S.manifoldMap y) :=
    hjoint.comp (S.manifoldMap y) (hasFDerivAt_prodMk_right (𝕜 := ℝ) y (S.manifoldMap y))
  exact hcomp.unique (S.hasFDerivAt_fibre y)

theorem isInvertible_fibreDeriv (y : Y) :
    (fderiv ℝ (fun p : Y × E => S.fast p.1 p.2) (y, S.manifoldMap y) ∘L
      ContinuousLinearMap.inr ℝ Y E).IsInvertible := by
  rw [S.fibreDeriv_eq y]
  exact ContinuousLinearMap.isInvertible_equiv

theorem contDiffAt_fast (y : Y) :
    ContDiffAt ℝ 1 (fun p : Y × E => S.fast p.1 p.2) (y, S.manifoldMap y) :=
  S.contDiff_fast.contDiffAt

/-- C¹ regularity of the slaved manifold curve. -/
theorem contDiff_manifoldMap : ContDiff ℝ 1 S.manifoldMap := by
  rw [contDiff_iff_contDiffAt]
  intro y₀
  set u : Y × E := (y₀, S.manifoldMap y₀) with hu
  have cdf : ContDiffAt ℝ 1 (fun p : Y × E => S.fast p.1 p.2) u := S.contDiffAt_fast y₀
  have if₂ : (fderiv ℝ (fun p : Y × E => S.fast p.1 p.2) u ∘L
      ContinuousLinearMap.inr ℝ Y E).IsInvertible := S.isInvertible_fibreDeriv y₀
  set ψ := cdf.implicitFunction (by norm_num) if₂ with hψ
  have hψ_cd : ContDiffAt ℝ 1 ψ u.1 := cdf.contDiffAt_implicitFunction (by norm_num) if₂
  -- f u = fast y₀ (manifoldMap y₀) = 0.
  have hfu : (fun p : Y × E => S.fast p.1 p.2) u = 0 := S.manifoldMap_stat y₀
  -- Near y₀, ψ agrees with manifoldMap by fibre uniqueness.
  have heq : S.manifoldMap =ᶠ[𝓝 y₀] ψ := by
    have hev := cdf.eventually_apply_implicitFunction (by norm_num) if₂
    filter_upwards [hev] with x hx
    -- hx : fast x (ψ x) = fast y₀ (manifoldMap y₀) = 0, so ψ x = manifoldMap x by uniqueness.
    have hzero : S.fast x (ψ x) = 0 := by rw [hx]; exact hfu
    exact (S.manifoldMap_eq_of_stationary hzero).symm
  exact hψ_cd.congr_of_eventuallyEq heq

/-- The slow (parameter) partial derivative of the fast field at the fibre equilibrium:
`D_y fast(y, manifoldMap y)`, obtained by restricting the joint derivative along `Y`. -/
noncomputable def slowDeriv (y : Y) : Y →L[ℝ] E :=
  fderiv ℝ (fun p : Y × E => S.fast p.1 p.2) (y, S.manifoldMap y) ∘L ContinuousLinearMap.inl ℝ Y E

/-- **Implicit derivative formula.** The constructed manifold map is Fréchet differentiable, with
derivative the implicit-function expression `-(D_z fast)⁻¹ ∘ (D_y fast)` evaluated at the fibre
equilibrium: `D manifoldMap y = -(fibreDeriv y)⁻¹ ∘ slowDeriv y`. -/
theorem hasFDerivAt_manifoldMap (y₀ : Y) :
    HasFDerivAt S.manifoldMap
      (-(S.fibreDeriv y₀ : E ≃L[ℝ] E).symm.toContinuousLinearMap ∘L S.slowDeriv y₀) y₀ := by
  set u : Y × E := (y₀, S.manifoldMap y₀) with hu
  have cdf : ContDiffAt ℝ 1 (fun p : Y × E => S.fast p.1 p.2) u := S.contDiffAt_fast y₀
  have if₂ : (fderiv ℝ (fun p : Y × E => S.fast p.1 p.2) u ∘L
      ContinuousLinearMap.inr ℝ Y E).IsInvertible := S.isInvertible_fibreDeriv y₀
  set ψ := cdf.implicitFunction (by norm_num) if₂ with hψ
  -- ψ has the implicit-function strict derivative; manifoldMap agrees with ψ near y₀.
  have hsd := cdf.hasStrictFDerivAt_implicitFunction (by norm_num) if₂
  have heq : S.manifoldMap =ᶠ[𝓝 y₀] ψ := by
    have hfu : (fun p : Y × E => S.fast p.1 p.2) u = 0 := S.manifoldMap_stat y₀
    have hev := cdf.eventually_apply_implicitFunction (by norm_num) if₂
    filter_upwards [hev] with x hx
    have hzero : S.fast x (ψ x) = 0 := by rw [hx]; exact hfu
    exact (S.manifoldMap_eq_of_stationary hzero).symm
  -- Rewrite the implicit inverse `(D_z fast)⁻¹` as `(fibreDeriv y₀).symm`.
  have hinv : (fderiv ℝ (fun p : Y × E => S.fast p.1 p.2) u ∘L
      ContinuousLinearMap.inr ℝ Y E).inverse =
      (S.fibreDeriv y₀ : E ≃L[ℝ] E).symm.toContinuousLinearMap := by
    rw [S.fibreDeriv_eq y₀, ContinuousLinearMap.inverse_equiv]
  have hfd : HasFDerivAt ψ
      (-(S.fibreDeriv y₀ : E ≃L[ℝ] E).symm.toContinuousLinearMap ∘L S.slowDeriv y₀) u.1 := by
    have := hsd.hasFDerivAt
    rw [hinv] at this
    exact this
  exact hfd.congr_of_eventuallyEq heq

/-- The slaved manifold curve `t ↦ manifoldMap (y t)` is differentiable wherever the slow path is,
with derivative the chain-rule composite of the implicit derivative and the path velocity. -/
theorem hasDerivAt_comp {y : ℝ → Y} {y' : ℝ → Y} {t₀ : ℝ} (hy : HasDerivAt y (y' t₀) t₀) :
    HasDerivAt (fun t => S.manifoldMap (y t))
      ((-(S.fibreDeriv (y t₀) : E ≃L[ℝ] E).symm.toContinuousLinearMap ∘L
        S.slowDeriv (y t₀)) (y' t₀)) t₀ :=
  (S.hasFDerivAt_manifoldMap (y t₀)).comp_hasDerivAt t₀ hy

/-- **The slaved slow-manifold curve's velocity is `O(ε)`, with differentiability derived.** When the
fast field is jointly `C¹` with invertible fibre derivative (so `manifoldMap` is `C¹`) and the slow
path `y` is differentiable at `t₀`, the slaved curve `t ↦ manifoldMap (y t)` is differentiable by the
chain rule, and the converse mean-value inequality bounds its velocity by `(L / rate) · ε`. Unlike
`SlowManifoldSeed.manifoldMap_slowDrift_velocity_le`, the `HasDerivAt` hypothesis is no longer
required: it follows from the implicit-function regularity of `manifoldMap`. -/
theorem manifoldMap_slowDrift_velocity_le {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y')
    {y : ℝ → Y} (hy : ∀ t t', dist (y t) (y t') ≤ ε * |t - t'|)
    {y' : ℝ → Y} {t₀ : ℝ} (hyd : HasDerivAt y (y' t₀) t₀) :
    ‖(-(S.fibreDeriv (y t₀) : E ≃L[ℝ] E).symm.toContinuousLinearMap ∘L
        S.slowDeriv (y t₀)) (y' t₀)‖ ≤ (L / S.rate) * ε :=
  S.toSlowManifoldSeed.manifoldMap_slowDrift_velocity_le hL hε hlip hy
    (γᵣ' := fun _ => (-(S.fibreDeriv (y t₀) : E ≃L[ℝ] E).symm.toContinuousLinearMap ∘L
      S.slowDeriv (y t₀)) (y' t₀)) t₀ (S.hasDerivAt_comp hyd)

end SlowManifoldC1Seed

end ODE

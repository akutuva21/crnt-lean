import CRNT.Dynamics.Fenichel

/-!
# Constructing the slow-manifold map from a parametrised contracting fast field

This module upgrades `CRNT.Dynamics.Fenichel`'s `ODE.SlowManifold` from a structure carrying the
graph map `h : Y → E` as *free hypothesised data* to one whose `h` is **constructed** from the
fast field itself. The input is a `SlowManifoldSeed`: a parametrised fast field `fast : Y → E → E`,
a positive contraction rate, a per-fibre existence-of-equilibrium hypothesis, and the per-fibre
one-sided contraction. From the seed the manifold map is built fibrewise as the chosen fast
equilibrium, pinned to a canonical value by the contraction-driven uniqueness already proved as
`SlowManifold.eq_of_stationary`. It is CRN-free and lives in the `ODE` namespace shared with
`CRNT.Dynamics.Tikhonov` and `CRNT.Dynamics.Fenichel`.

**Constructed manifold map** (`SlowManifoldSeed.manifoldMap`). `manifoldMap y` is the equilibrium
furnished by `exists_stat y`, so `fast y (manifoldMap y) = 0` (`manifoldMap_stat`). Bundling this
with the seed's rate and contraction data yields a genuine `ODE.SlowManifold`
(`SlowManifoldSeed.toSlowManifold`) whose `h` field is `manifoldMap` — no longer free data.

**Canonicity** (`SlowManifoldSeed.manifoldMap_eq_of_stationary`,
`SlowManifoldSeed.manifoldMap_unique`). Through the constructed `SlowManifold` the uniqueness
result applies: any stationary point of `fast y` equals `manifoldMap y`, and the fibre
equilibrium set is exactly `{manifoldMap y}`. So the construction is independent of which
equilibrium `exists_stat` happens to select.

**Lipschitz regularity** (`SlowManifoldSeed.manifoldMap_dist_le`,
`SlowManifoldSeed.manifoldMap_lipschitzWith`, `SlowManifoldSeed.continuous_manifoldMap`). Under a
uniform Lipschitz-in-parameter bound `‖fast y z - fast y' z‖ ≤ L · dist y y'` on the fast field,
the manifold map is Lipschitz with constant `L / rate`, hence continuous. The heart is a purely
algebraic estimate from the contraction inequality and Cauchy–Schwarz: writing `p = manifoldMap y`,
`q = manifoldMap y'`, the contraction at `p` gives `rate · ‖q - p‖² ≤ ⟪fast y q, q - p⟫`, while
`fast y q = fast y q - fast y' q` (since `fast y' q = 0`) and Cauchy–Schwarz bound the right side
by `‖fast y q - fast y' q‖ · ‖q - p‖`; dividing by `‖q - p‖` and applying the Lipschitz bound
yields `‖q - p‖ ≤ (L / rate) · dist y y'`.

**Scope.** Two results lie beyond the one-sided contraction. (1) *C¹
regularity of `h`*: differentiability of `manifoldMap` is not reachable from the one-sided
contraction alone — it needs an invertible fibre-derivative hypothesis
(`D_z fast y (manifoldMap y)` invertible) together with joint `C¹` dependence of `fast` on
`(y, z)`, fed to Mathlib's implicit function theorem
(`HasStrictFDerivAt.localInverse` / `ImplicitFunctionData`), which is strictly more input data. The
one-sided contraction yields only Lipschitz/continuous `h`. (2)
*ε-positive Fenichel persistence*: perturbing the exact `ε = 0` invariant graph `{(y, h y)}` to a
nearby invariant manifold for `ε > 0` requires a uniform-in-`ε` normally-hyperbolic
invariant-manifold construction, absent from Mathlib v4.31; the contraction supplies only the
layer (`ε = 0`) invariance.

Depends on: CRNT.Dynamics.Fenichel.
-/

open Filter Set Classical
open scoped Topology RealInnerProductSpace

namespace ODE

variable {Y : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A **seed** for a slow manifold: the data from which the manifold map is *constructed* rather
than hypothesised. A parametrised fast field `fast : Y → E → E`, a positive contraction `rate`,
the existence of a fibre equilibrium for every slow point, and the per-fibre one-sided contraction
toward any such equilibrium. The manifold map is then the (uniquely pinned) fibre equilibrium. -/
structure SlowManifoldSeed (Y : Type*) (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The parametrised fast vector field; freezing `y` gives the layer subsystem `ż = fast y z`. -/
  fast : Y → E → E
  /-- The uniform contraction rate of every fibre. -/
  rate : ℝ
  /-- The contraction rate is strictly positive. -/
  rate_pos : 0 < rate
  /-- Every fibre has a fast equilibrium. -/
  exists_stat : ∀ y, ∃ z, fast y z = 0
  /-- Every fibre is one-sided contracting toward each of its equilibria at `rate`. -/
  contraction : ∀ y zstar, fast y zstar = 0 → OneSidedContraction (fast y) zstar rate

namespace SlowManifoldSeed

variable (S : SlowManifoldSeed Y E)

/-- The **constructed manifold map**: `manifoldMap y` is a fast equilibrium of `fast y`, chosen by
`exists_stat`. Its value is pinned canonically by `manifoldMap_eq_of_stationary`. -/
noncomputable def manifoldMap (y : Y) : E := (S.exists_stat y).choose

/-- The constructed manifold map lands on a fast equilibrium: `fast y (manifoldMap y) = 0`. -/
theorem manifoldMap_stat (y : Y) : S.fast y (S.manifoldMap y) = 0 :=
  (S.exists_stat y).choose_spec

/-- The genuine `ODE.SlowManifold` built from the seed, with `h` field the **constructed**
`manifoldMap` rather than free data. It consumes the `SlowManifold` structure. -/
noncomputable def toSlowManifold : SlowManifold Y E where
  fast := S.fast
  h := S.manifoldMap
  rate := S.rate
  rate_pos := S.rate_pos
  equil_stat := S.manifoldMap_stat
  contraction := fun y => S.contraction y _ (S.manifoldMap_stat y)

@[simp] theorem toSlowManifold_fast : S.toSlowManifold.fast = S.fast := rfl
@[simp] theorem toSlowManifold_h : S.toSlowManifold.h = S.manifoldMap := rfl
@[simp] theorem toSlowManifold_rate : S.toSlowManifold.rate = S.rate := rfl

/-- **Canonicity.** Any stationary point of the fibre `fast y` equals the constructed
`manifoldMap y`: the construction does not depend on which equilibrium `exists_stat` selects. -/
theorem manifoldMap_eq_of_stationary {y : Y} {w : E} (hw : S.fast y w = 0) :
    w = S.manifoldMap y :=
  S.toSlowManifold.eq_of_stationary hw

/-- The fibre equilibrium set is exactly the singleton of the constructed manifold map. -/
theorem manifoldMap_unique (y : Y) : {w : E | S.fast y w = 0} = {S.manifoldMap y} :=
  S.toSlowManifold.fiber_eq_singleton y

section Regularity

variable [PseudoMetricSpace Y]

/-- **Core distance estimate.** Under a uniform Lipschitz-in-parameter bound on the fast field,
the constructed manifold map satisfies `‖manifoldMap y' - manifoldMap y‖ ≤ (L / rate) · dist y y'`.
The proof runs the contraction inequality at `p = manifoldMap y` evaluated on `q = manifoldMap y'`,
uses `fast y' q = 0` to rewrite `fast y q` as `fast y q - fast y' q`, bounds the inner product by
Cauchy–Schwarz, and divides by `‖q - p‖`. -/
theorem manifoldMap_dist_le {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y') :
    ∀ y y', ‖S.manifoldMap y' - S.manifoldMap y‖ ≤ (L / S.rate) * dist y y' := by
  intro y y'
  set p := S.manifoldMap y with hp_def
  set q := S.manifoldMap y' with hq_def
  have hp : S.fast y p = 0 := S.manifoldMap_stat y
  have hq : S.fast y' q = 0 := S.manifoldMap_stat y'
  -- Contraction at the equilibrium `p`, evaluated at `q`.
  have hcon : ⟪S.fast y q - S.fast y p, q - p⟫ ≤ -S.rate * ‖q - p‖ ^ 2 :=
    S.contraction y p hp q
  rw [hp, sub_zero] at hcon
  -- Replace `fast y q` by `fast y q - fast y' q` (legal since `fast y' q = 0`).
  rw [show S.fast y q = S.fast y q - S.fast y' q by rw [hq, sub_zero]] at hcon
  -- Cauchy–Schwarz lower bound on the inner product.
  have hcs : -(‖S.fast y q - S.fast y' q‖ * ‖q - p‖) ≤
      ⟪S.fast y q - S.fast y' q, q - p⟫ :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  -- Combine: `rate · ‖q - p‖² ≤ ‖fast y q - fast y' q‖ · ‖q - p‖`.
  have hkey : S.rate * ‖q - p‖ ^ 2 ≤ ‖S.fast y q - S.fast y' q‖ * ‖q - p‖ := by
    nlinarith [hcon, hcs]
  -- Lipschitz bound on the field defect.
  have hbnd : ‖S.fast y q - S.fast y' q‖ ≤ L * dist y y' := hlip y y' q
  rcases eq_or_lt_of_le (norm_nonneg (q - p)) with h0 | h0
  · -- Degenerate fibre: `q = p`, so the deviation is zero and the bound holds.
    rw [← h0]
    exact mul_nonneg (div_nonneg hL S.rate_pos.le) dist_nonneg
  · -- Positive deviation: cancel one factor of `‖q - p‖`.
    have hmul : S.rate * ‖q - p‖ * ‖q - p‖ ≤ (L * dist y y') * ‖q - p‖ := by
      nlinarith [hkey, hbnd, norm_nonneg (q - p)]
    have hle : S.rate * ‖q - p‖ ≤ L * dist y y' := le_of_mul_le_mul_right hmul h0
    rw [div_mul_eq_mul_div, le_div_iff₀ S.rate_pos]
    linarith [hle]

/-- **Lipschitz regularity.** Under the uniform Lipschitz-in-parameter bound the constructed
manifold map is Lipschitz with constant `L / rate`. -/
theorem manifoldMap_lipschitzWith {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y') :
    LipschitzWith ⟨L / S.rate, div_nonneg hL S.rate_pos.le⟩ S.manifoldMap := by
  apply LipschitzWith.of_dist_le_mul
  intro y' y
  show dist (S.manifoldMap y') (S.manifoldMap y) ≤ L / S.rate * dist y' y
  rw [dist_eq_norm, dist_comm y' y]
  exact S.manifoldMap_dist_le hL hlip y y'

/-- **Continuity** of the constructed manifold map, under the uniform Lipschitz-in-parameter
bound on the fast field. -/
theorem continuous_manifoldMap {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y') :
    Continuous S.manifoldMap :=
  (S.manifoldMap_lipschitzWith hL hlip).continuous

end Regularity

end SlowManifoldSeed

end ODE

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# The variational equation: linearized dependence of an ODE flow on initial data

For an autonomous `C¹` vector field `f : E → E` on a finite-dimensional real normed space,
the flow `x₀ ↦ Φ x₀ t` depends differentiably on the initial point `x₀`. The derivative in a
fixed direction `v` is governed by the *linear variational equation*
`Ẇ = (Df (x t)) · W`, `W 0 = v`, where `Df := fderiv ℝ f` and `x` is the base solution.
This module proves the analytic heart of that statement: along `[0, T]` the difference between
the genuine flow separation `y t - x t` and its linear prediction `h • W t` is controlled by
Grönwall's inequality and is governed by the modulus of continuity of `Df`.

`Mathlib`'s ODE library furnishes flow existence and *Lipschitz* dependence on initial
conditions (`ODE_solution_unique`, the Grönwall lemmas
`norm_le_gronwallBound_of_norm_deriv_right_le`, `dist_le_of_trajectories_ODE`), but no
Fréchet-derivative / variational result. This development supplies that missing analytic step,
filling the variational datum (`spaceDeriv` and the difference-quotient limit) that smooth
dependence on initial conditions — and through it the Andronov–Hopf transversal first-return
map — requires.

## Main results

* `norm_variational_error_le`: the abstract Grönwall estimate. Given the base solution `x`, a
  comparison solution `y`, and a solution `W` of the linear variational ODE, with the
  first-order remainder of `f` bounded by `r` and `‖Df (x t)‖ ≤ K`, the variational error
  `(y t - x t) - h • W t` is bounded by `gronwallBound 0 K r t` on `[0, T]`.

* `norm_flow_variational_error_le`: the headline. Feeding in the mean-value bound on the
  remainder (`ρ` = a uniform modulus for `Df` along the joined segment) together with the
  Lipschitz separation `‖y t - x t‖ ≤ |h| · ‖v‖ · exp (K t)`, the variational error obeys
  `‖(y t - x t) - h • W t‖ ≤ gronwallBound 0 K (ρ · |h| · ‖v‖ · exp (K T)) t`, in which the
  driving term is `O(ρ · |h|)`: linear in `|h|` and vanishing as the `Df`-modulus `ρ → 0`.
-/

open Set Filter
open scoped Topology

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Abstract variational Grönwall estimate.**

Let `x` solve `ẋ = f (x t)` and `y` solve `ẏ = f (y t)` on a neighbourhood of `[0, T]`, and let
`W` solve the linear variational ODE `Ẇ = Df (x t) · W` for a continuous family of operators
`Df : ℝ → (E →L[ℝ] E)`. Suppose the first-order remainder of `f` along the two solutions is
bounded, `‖f (y t) - f (x t) - Df t (y t - x t)‖ ≤ r`, that `‖Df t‖ ≤ K`, and that the
variational error vanishes initially, `(y 0 - x 0) - h • W 0 = 0`. Then the variational error
is bounded by Grönwall's growth function on `[0, T]`:
`‖(y t - x t) - h • W t‖ ≤ gronwallBound 0 K r t`. -/
theorem norm_variational_error_le {f : E → E} {Df : ℝ → (E →L[ℝ] E)}
    {x y W : ℝ → E} {h K r T : ℝ}
    (hx : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt x (f (x t)) t)
    (hy : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (f (y t)) t)
    (hW : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt W (Df t (W t)) t)
    (hxc : ContinuousOn x (Icc 0 T)) (hyc : ContinuousOn y (Icc 0 T))
    (hWc : ContinuousOn W (Icc 0 T))
    (hDfK : ∀ t ∈ Ico (0 : ℝ) T, ‖Df t‖ ≤ K)
    (hrem : ∀ t ∈ Ico (0 : ℝ) T, ‖f (y t) - f (x t) - Df t (y t - x t)‖ ≤ r)
    (h0 : (y 0 - x 0) - h • W 0 = 0) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖(y t - x t) - h • W t‖ ≤ gronwallBound 0 K r t := by
  -- The variational error `u` and its derivative `u'`.
  set u : ℝ → E := fun t => (y t - x t) - h • W t with hu
  set u' : ℝ → E := fun t => (f (y t) - f (x t) - h • Df t (W t)) with hu'
  have hcont : ContinuousOn u (Icc 0 T) := (hyc.sub hxc).sub (hWc.const_smul h)
  -- `u` differentiates to `u'` from the three ODEs.
  have hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt u (u' t) (Ici t) t := by
    intro t ht
    have hd : HasDerivAt u (u' t) t :=
      ((hy t ht).sub (hx t ht)).sub ((hW t ht).const_smul h)
    exact hd.hasDerivWithinAt
  -- The Grönwall differential inequality `‖u' t‖ ≤ K * ‖u t‖ + r`.
  have hbound : ∀ t ∈ Ico (0 : ℝ) T, ‖u' t‖ ≤ K * ‖u t‖ + r := by
    intro t ht
    -- Split the velocity into the linearized part `Df t (u t)` and the remainder.
    have hsplit : u' t = Df t (u t) + (f (y t) - f (x t) - Df t (y t - x t)) := by
      have hlin : Df t (u t) = Df t (y t - x t) - h • Df t (W t) := by
        simp only [hu, map_sub, map_smul]
      simp only [hu', hlin]; abel
    rw [hsplit]
    calc ‖Df t (u t) + (f (y t) - f (x t) - Df t (y t - x t))‖
        ≤ ‖Df t (u t)‖ + ‖f (y t) - f (x t) - Df t (y t - x t)‖ := norm_add_le _ _
      _ ≤ K * ‖u t‖ + r := by
          gcongr
          · exact (Df t).le_opNorm (u t) |>.trans (by gcongr; exact hDfK t ht)
          · exact hrem t ht
  -- Feed into Grönwall.
  have h0' : ‖u 0‖ ≤ 0 := by rw [show u 0 = 0 from h0]; simp
  intro t ht
  have := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv h0' hbound t ht
  simpa using this

/-- **Headline variational error bound.**

For a `C¹` field `f` with derivative `Df := fderiv ℝ f` bounded in operator norm by `K` along
the base solution `x`, let `y` be the comparison solution started at `y 0 = x 0 + h • v` and
`W` the solution of the linear variational ODE `Ẇ = Df (x t) · W`, `W 0 = v`. Suppose:

* the first-order remainder of `f` along the two solutions is controlled by a uniform modulus
  `ρ` for `Df` on the joined segment, `‖f (y t) - f (x t) - Df (x t) (y t - x t)‖ ≤ ρ · ‖y t - x t‖`
  (the mean-value bound `norm_image_sub_le_of_norm_fderiv_le'`), and
* the genuine flow separation grows at most as the Lipschitz/Grönwall estimate predicts,
  `‖y t - x t‖ ≤ |h| · ‖v‖ · exp (K t)` (Mathlib's continuous dependence on initial data).

Then on `[0, T]` the variational error obeys
`‖(y t - x t) - h • W t‖ ≤ gronwallBound 0 K (ρ · |h| · ‖v‖ · exp (K T)) t`.

The driving term `ρ · |h| · ‖v‖ · exp (K T)` is linear in `|h|` and vanishes as the
`Df`-modulus `ρ → 0` (continuity of `Df` as `h → 0`), so the variational error is higher-order:
the difference quotient `(y t - x t) / h` converges to `W t`. -/
theorem norm_flow_variational_error_le {f : E → E}
    {x y W : ℝ → E} {v : E} {h K ρ T : ℝ} (hK : 0 ≤ K) (hρ : 0 ≤ ρ)
    (hx : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt x (f (x t)) t)
    (hy : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (f (y t)) t)
    (hW : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt W ((fderiv ℝ f (x t)) (W t)) t)
    (hxc : ContinuousOn x (Icc 0 T)) (hyc : ContinuousOn y (Icc 0 T))
    (hWc : ContinuousOn W (Icc 0 T))
    (hDfK : ∀ t ∈ Ico (0 : ℝ) T, ‖fderiv ℝ f (x t)‖ ≤ K)
    (hmod : ∀ t ∈ Ico (0 : ℝ) T,
      ‖f (y t) - f (x t) - (fderiv ℝ f (x t)) (y t - x t)‖ ≤ ρ * ‖y t - x t‖)
    (hsep : ∀ t ∈ Ico (0 : ℝ) T, ‖y t - x t‖ ≤ |h| * ‖v‖ * Real.exp (K * t))
    (h0 : (y 0 - x 0) - h • W 0 = 0) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖(y t - x t) - h • W t‖ ≤ gronwallBound 0 K (ρ * (|h| * ‖v‖ * Real.exp (K * T))) t := by
  -- The uniform first-order remainder bound, with the separation absorbed at `t = T`.
  have hrem : ∀ t ∈ Ico (0 : ℝ) T,
      ‖f (y t) - f (x t) - (fderiv ℝ f (x t)) (y t - x t)‖
        ≤ ρ * (|h| * ‖v‖ * Real.exp (K * T)) := by
    intro t ht
    refine (hmod t ht).trans ?_
    have hKtT : K * t ≤ K * T := by
      apply mul_le_mul_of_nonneg_left ht.2.le hK
    have hmono : |h| * ‖v‖ * Real.exp (K * t) ≤ |h| * ‖v‖ * Real.exp (K * T) := by
      gcongr
    exact mul_le_mul_of_nonneg_left ((hsep t ht).trans hmono) hρ
  exact norm_variational_error_le hx hy hW hxc hyc hWc hDfK hrem h0

import CRNT.Kinetics.MassAction
import CRNT.Examples.ReversiblePair
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# Density-dependent scaling and generator convergence (Kurtz fluid limit)

The classical law of large numbers for the stochastic mass-action chain (Kurtz,
"Solutions of ordinary differential equations as limits of pure jump Markov processes",
J. Appl. Probab. 7 (1970); Anderson–Kurtz, *Stochastic Analysis of Biochemical Systems*)
links the continuous-time Markov chain on the count lattice `ℕ^S` to the deterministic
reaction-rate equation `ẋ = F(x)`. The bridge is the *density-dependent family*: at a
system volume `V > 0` the chain is rescaled into concentration coordinates `x = n/V`, with
each reaction firing at the scaled propensity

  `λ^V_r(x) = V · κ_r · ∏_s x_s ^ {source_r s} = V · massActionRate κ r x`

and changing the concentration by the scaled reaction vector `v_r / V`, where
`v_r = target_r − source_r`. The generator of this rescaled process, acting on a smooth
observable `f` of the concentration, is

  `A^V f (x) = ∑_r λ^V_r(x) · (f(x + v_r/V) − f(x))`.

The analytic heart of Kurtz's theorem is the *generator-convergence estimate*: for a
differentiable observable `f` with Fréchet derivative `f'(x)`,

  `A^V f (x) → f'(x)(F(x)) = ∇f(x) · F(x)`  as  `V → ∞`,

where `F(x) = ∑_r κ_r x^{source_r} (target_r − source_r) = massActionVectorField κ x` is
the deterministic mass-action field. The mechanism is a first-order expansion of each jump,
`V · (f(x + v_r/V) − f(x)) → f'(x)(v_r)`, combined with the algebraic identity
`λ^V_r(x)/V = massActionRate κ r x`; the sum over reactions and the linearity of `f'(x)`
then collapse the limit onto `f'(x)(F(x))`.

The single-jump expansion is `volume_smul_sub_tendsto_fderiv`: it is exactly the directional
(line) derivative read at `V → ∞` along the scaled increment `v/V`, obtained from
`HasFDerivAt.hasLineDerivAt` and `HasLineDerivAt.tendsto_slope_zero_right` after the change
of variable `t = V⁻¹`.

The scope here is the generator-convergence estimate itself — the pointwise limit of `A^V f`
on a differentiable observable. The process-level law of large numbers (Skorokhod-path
convergence of the rescaled trajectories to the solution of `ẋ = F(x)`) is separate and
builds on this estimate together with a martingale/Gronwall argument.

Depends on: `CRNT.Kinetics.MassAction`,
`CRNT.Examples.ReversiblePair`.
-/

namespace CRNT

open Filter Topology

open scoped BigOperators

/-- **Single-jump first-order expansion.** For a function `f` with Fréchet derivative `L`
at `x`, the volume-scaled increment along the direction `v/V` converges to the directional
derivative `L v` as the volume `V → ∞`:

  `V · (f(x + V⁻¹ • v) − f(x)) → L v`.

This is the directional derivative `lim_{t→0⁺} t⁻¹ (f(x + t•v) − f(x))` read through the
change of variable `t = V⁻¹`, and is the analytic engine of the generator-convergence
estimate: a single reaction's contribution to `A^V f` expands to first order to a directional
derivative of the observable. -/
theorem volume_smul_sub_tendsto_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {x : E} {L : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f L x) (v : E) :
    Tendsto (fun V : ℝ => V • (f (x + V⁻¹ • v) - f x)) atTop (𝓝 (L v)) := by
  have hline : HasLineDerivAt ℝ f (L v) x v := hf.hasLineDerivAt v
  -- The line derivative as a right-hand slope limit at `t = 0`.
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (f (x + t • v) - f x)) (𝓝[>] 0) (𝓝 (L v)) :=
    hline.tendsto_slope_zero_right
  -- Pull back along `V ↦ V⁻¹ : atTop → 𝓝[>] 0`.
  have hcomp := hslope.comp tendsto_inv_atTop_nhdsGT_zero
  -- On `atTop` the composite agrees with `V ↦ V • (f (x + V⁻¹ • v) - f x)`.
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with V hV
  simp only [Function.comp_apply, inv_inv]

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Density-dependent (volume-scaled) propensity.** At volume `V`, reaction `r` fires at
`λ^V_r(x) = V · κ_r · ∏_s x_s ^ {source_r s}`, the mass-action propensity expressed in the
concentration coordinate `x = n/V` and rescaled by the volume. -/
noncomputable def densityScaledRate (N : Network S) (κ : RateConstants N) (V : ℝ)
    (r : N.R) (x : Concentration S) : ℝ :=
  V * N.massActionRate κ r x

/-- The density-dependent propensity is the volume times the deterministic mass-action
rate; equivalently `λ^V_r(x) / V = massActionRate κ r x`. -/
@[simp] theorem densityScaledRate_apply (N : Network S) (κ : RateConstants N) (V : ℝ)
    (r : N.R) (x : Concentration S) :
    N.densityScaledRate κ V r x = V * N.massActionRate κ r x :=
  rfl

/-- **The volume-scaled generator** acting on an observable `f` of the concentration. At
volume `V` and concentration `x`, summing over reactions the scaled propensity times the
finite difference of `f` across the scaled reaction increment `v_r / V`:

  `A^V f (x) = ∑_r λ^V_r(x) · (f(x + v_r/V) − f(x))`.

The scaled increment is written `V⁻¹ • reactionVector r` so that the limit `V → ∞` shrinks
the jump while `λ^V_r` grows linearly in `V`. -/
noncomputable def scaledGenerator (N : Network S) (κ : RateConstants N) (V : ℝ)
    (f : Concentration S → ℝ) (x : Concentration S) : ℝ :=
  ∑ r : N.R, N.densityScaledRate κ V r x *
    (f (x + V⁻¹ • N.reactionVector r) - f x)

/-- **Per-reaction generator-convergence estimate.** For a differentiable observable `f`,
the volume-scaled contribution of a single reaction `r` to `A^V f` converges to the
mass-action rate times the directional derivative of `f` along that reaction's vector:

  `λ^V_r(x) · (f(x + v_r/V) − f(x)) → massActionRate κ r x · L(v_r)`.

This is the single-jump expansion `volume_smul_sub_tendsto_fderiv` scaled by the constant
`massActionRate κ r x`, using `λ^V_r(x) = V · massActionRate κ r x`. -/
theorem tendsto_densityScaledRate_smul_sub (N : Network S) (κ : RateConstants N)
    {f : Concentration S → ℝ} {x : Concentration S} {L : Concentration S →L[ℝ] ℝ}
    (hf : HasFDerivAt f L x) (r : N.R) :
    Tendsto (fun V : ℝ => N.densityScaledRate κ V r x *
        (f (x + V⁻¹ • N.reactionVector r) - f x)) atTop
      (𝓝 (N.massActionRate κ r x * L (N.reactionVector r))) := by
  have hbase := volume_smul_sub_tendsto_fderiv hf (N.reactionVector r)
  have := hbase.const_mul (N.massActionRate κ r x)
  refine this.congr fun V => ?_
  simp only [densityScaledRate_apply, smul_eq_mul]
  ring

/-- **Generator-convergence estimate (the analytic core of Kurtz's theorem).** For a
differentiable observable `f` with Fréchet derivative `L = f'(x)`, the volume-scaled
generator converges, as `V → ∞`, to the derivative of `f` evaluated on the deterministic
mass-action field:

  `A^V f (x) → f'(x)(F(x)) = ∇f(x) · F(x)`,

with `F(x) = massActionVectorField κ x`. The proof sums the per-reaction estimates and uses
linearity of `f'(x)` to identify the reaction-indexed limit
`∑_r massActionRate κ r x · L(v_r)` with `L(∑_r massActionRate κ r x · v_r) = L(F(x))`. -/
theorem tendsto_scaledGenerator (N : Network S) (κ : RateConstants N)
    {f : Concentration S → ℝ} {x : Concentration S} {L : Concentration S →L[ℝ] ℝ}
    (hf : HasFDerivAt f L x) :
    Tendsto (fun V : ℝ => N.scaledGenerator κ V f x) atTop
      (𝓝 (L (N.massActionVectorField κ x))) := by
  -- The limit value, expanded reaction-by-reaction via linearity of the derivative `L`.
  have hLF : L (N.massActionVectorField κ x) =
      ∑ r : N.R, N.massActionRate κ r x * L (N.reactionVector r) := by
    have hsum : N.massActionVectorField κ x =
        ∑ r : N.R, N.massActionRate κ r x • N.reactionVector r := by
      funext s
      simp [massActionVectorField, Finset.sum_apply, smul_eq_mul]
    rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, smul_eq_mul]
  rw [hLF]
  simp only [scaledGenerator]
  exact tendsto_finsetSum _ fun r _ => N.tendsto_densityScaledRate_smul_sub κ hf r

end Network

namespace Examples.ReversiblePair

open CRNT.Network

/-- The deterministic mass-action field of the reversible pair `A ⇌ B` is the linear field
`ẋ_A = −κ_f x_A + κ_b x_B`, `ẋ_B = κ_f x_A − κ_b x_B`: the limit toward which the
volume-scaled generator drives observables (`tendsto_scaledGenerator`). The `A`-component is
recorded here; the `B`-component is its negative on the conservation line. -/
theorem massActionVectorField_A (κ : Network.RateConstants N) (x : Concentration Species) :
    N.massActionVectorField κ x Species.A =
      -(κ.k Rxn.fwd * x Species.A) + κ.k Rxn.bwd * x Species.B := by
  rw [massActionVectorField_apply,
    show (∑ r, N.massActionRate κ r x * N.reactionVector r Species.A)
        = N.massActionRate κ Rxn.fwd x * N.reactionVector Rxn.fwd Species.A
          + N.massActionRate κ Rxn.bwd x * N.reactionVector Rxn.bwd Species.A from
      Fintype.sum_eq_add Rxn.fwd Rxn.bwd (by decide)
        (fun r _ => by rcases r with _ | _ <;> simp_all)]
  have hmonA : cA.massActionMonomial x = x Species.A := by
    rw [Complex.massActionMonomial,
      Fintype.prod_eq_mul Species.A Species.B (by decide)
        (by rintro s ⟨hA, hB⟩; cases s <;> simp_all)]
    simp [cA]
  have hmonB : cB.massActionMonomial x = x Species.B := by
    rw [Complex.massActionMonomial,
      Fintype.prod_eq_mul Species.A Species.B (by decide)
        (by rintro s ⟨hA, hB⟩; cases s <;> simp_all)]
    simp [cB]
  simp only [massActionRate, reactionVector_apply, N, rxn, cA, cB, hmonA, hmonB]
  push_cast
  ring

/-- **Generator convergence on `A ⇌ B`.** For any differentiable observable `f`, the
volume-scaled generator of the reversible pair converges to the derivative of `f` along the
linear mass-action field `F(x)`, whose `A`-component is `−κ_f x_A + κ_b x_B`. The instance
specializes `tendsto_scaledGenerator` to the reversible pair. -/
theorem tendsto_scaledGenerator_reversiblePair (κ : Network.RateConstants N)
    {f : Concentration Species → ℝ} {x : Concentration Species}
    {L : Concentration Species →L[ℝ] ℝ} (hf : HasFDerivAt f L x) :
    Tendsto (fun V : ℝ => N.scaledGenerator κ V f x) atTop
      (𝓝 (L (N.massActionVectorField κ x))) :=
  N.tendsto_scaledGenerator κ hf

end Examples.ReversiblePair

end CRNT

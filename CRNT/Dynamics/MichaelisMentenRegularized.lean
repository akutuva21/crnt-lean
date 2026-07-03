import CRNT.Dynamics.MichaelisMentenC1
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A globally `C¹` regularized Michaelis–Menten fast field and its slow-manifold seed

The genuine Michaelis–Menten fast field of `CRNT.Dynamics.MichaelisMentenManifold` is jointly `C¹`
only off the unphysical pole `s = -Km` of its rate law `Vmax·s/(Km+s)`, so it has no *global*
`ODE.SlowManifoldC1Seed` instance over the whole substrate line. This module builds a faithful
**globally `C¹` regularized** Michaelis–Menten fast field — one that coincides with the true field
on the physical substrate ray `s ≥ 0` yet keeps its effective denominator bounded away from zero
for all `s` — and assembles a genuine `ODE.SlowManifoldC1Seed` from it, obtaining the certified
`C¹` Michaelis–Menten reduction through the abstract implicit-function API of
`CRNT.Dynamics.FenichelC1Manifold` rather than the bespoke domain-localized route of
`CRNT.Dynamics.MichaelisMentenC1`. Defined by Fenichel, "Geometric singular perturbation theory for
ordinary differential equations"; the rate law is the Michaelis–Menten/Briggs–Haldane
quasi-steady-state level.

**The smooth retraction of the denominator** (`mmRegDen`, `mmRegDen_of_nonneg`,
`mmRegDen_ge_half`, `mmRegDen_contDiff`). The denominator `Km + s` is replaced by `mmRegDen Km s`,
equal to `Km + s` on `s ≥ 0` and to `Km/2 + (Km/2)·exp(2s/Km)` on `s < 0`. The two pieces meet `C¹`
at `s = 0` (shared value `Km` and shared slope `1`), so `mmRegDen Km` is globally `ContDiff ℝ 1`,
proved through `contDiff_one_iff_deriv` from the everywhere-`HasDerivAt` law `mmRegDen_hasDerivAt`
with continuous derivative `mmRegDeriv`. On `s < 0` the exponential tail keeps the denominator in
`(Km/2, Km)`, so `mmRegDen Km s ≥ Km/2 > 0` for all `s` — the global lower bound the regularization
secures.

**The regularized rate law and fast field** (`mmRegEquil`, `mmRegFastField`,
`mmRegEquil_eq_of_nonneg`, `mmRegFastField_eq_of_nonneg`). With the denominator bounded away from
zero, the regularized quasi-equilibrium level `mmRegEquil Km Vmax s = Vmax·s/mmRegDen Km s` is
globally `C¹` (`mmRegEquil_contDiff`), and the regularized fast field
`mmRegFastField rate Km Vmax s z = -rate·(z - mmRegEquil Km Vmax s · e0)` is jointly `ContDiff ℝ 1`
in `(s, z)` (`mmRegFastField_contDiff`). On the physical ray `s ≥ 0` the regularized denominator,
rate law, and fast field equal the true Michaelis–Menten ones, so the model is unchanged on the
substrate.

**The invertible fibre derivative and the genuine seed** (`mmRegFibreDeriv`,
`mmRegFastField_hasFDerivAt_fibre`, `mmRegSlowManifoldSeed`). The fast field is, in the complex
variable `z`, the same affine relaxation as the true field, so its fibre Jacobian is the continuous
linear equivalence `-rate·id` reused from `CRNT.Dynamics.MichaelisMentenC1`'s `mmFibreDeriv`.
Bundling the joint `C¹` field, the per-fibre equilibrium, the one-sided contraction, and this
invertible fibre derivative gives a genuine `ODE.SlowManifoldC1Seed ℝ E`.

**The certified global `C¹` reduction** (`mmRegManifoldMap_contDiff`, `mmRegManifoldMap_eq`,
`mmRegManifoldMap_eq_mm`). The abstract `contDiff_manifoldMap` of `CRNT.Dynamics.FenichelC1Manifold`
now yields, with no domain restriction, that the seed's constructed `manifoldMap` is globally
`ContDiff ℝ 1`. Its value is the regularized complex-equilibrium curve everywhere
(`mmRegManifoldMap_eq`), and on the substrate ray `s ≥ 0` it agrees with the true Michaelis–Menten
complex-equilibrium curve `Vmax·s/(Km+s) · e0` (`mmRegManifoldMap_eq_mm`). This is the certified
`C¹` Michaelis–Menten reduction obtained through the abstract implicit-function API.

Depends on: CRNT.Dynamics.MichaelisMentenC1,
Mathlib.Analysis.SpecialFunctions.ExpDeriv.
-/

open Set
open scoped Topology RealInnerProductSpace NNReal

namespace CRNT.MichaelisMenten

/-- The **smooth retraction of the Michaelis–Menten denominator**: equal to `Km + s` on the
physical ray `s ≥ 0`, and to `Km/2 + (Km/2)·exp(2s/Km)` on `s < 0`. The negative-substrate branch
is the unique exponential meeting `Km + s` to first order at `s = 0` while staying in `(Km/2, Km)`,
so the denominator never falls to zero. -/
noncomputable def mmRegDen (Km s : ℝ) : ℝ :=
  if 0 ≤ s then Km + s else Km / 2 + (Km / 2) * Real.exp (2 * s / Km)

/-- The candidate everywhere-derivative of `mmRegDen Km`: `1` on `s ≥ 0` and `exp(2s/Km)` on
`s < 0`. The two branches share the value `1` at `s = 0`, so it is continuous. -/
noncomputable def mmRegDeriv (Km s : ℝ) : ℝ :=
  if 0 ≤ s then 1 else Real.exp (2 * s / Km)

/-- On the physical ray the regularized denominator is the true Michaelis–Menten denominator. -/
lemma mmRegDen_of_nonneg (Km : ℝ) {s : ℝ} (hs : 0 ≤ s) : mmRegDen Km s = Km + s := by
  simp only [mmRegDen, if_pos hs]

/-- The negative-substrate branch of the regularized denominator, written out. -/
lemma mmRegDen_of_neg (Km : ℝ) {s : ℝ} (hs : s < 0) :
    mmRegDen Km s = Km / 2 + (Km / 2) * Real.exp (2 * s / Km) := by
  simp only [mmRegDen, if_neg (not_le.mpr hs)]

/-- **Global positive lower bound.** For `0 < Km` the regularized denominator is at least `Km/2`
everywhere: on `s ≥ 0` it is `Km + s ≥ Km > Km/2`, and on `s < 0` the exponential term is positive,
keeping it above `Km/2`. -/
lemma mmRegDen_ge_half (Km : ℝ) (hKm : 0 < Km) (s : ℝ) : Km / 2 ≤ mmRegDen Km s := by
  rw [mmRegDen]
  split_ifs with hs
  · linarith
  · have hexp : 0 < Real.exp (2 * s / Km) := Real.exp_pos _
    nlinarith

/-- The regularized denominator is strictly positive for `0 < Km`. -/
lemma mmRegDen_pos (Km : ℝ) (hKm : 0 < Km) (s : ℝ) : 0 < mmRegDen Km s :=
  lt_of_lt_of_le (by linarith) (mmRegDen_ge_half Km hKm s)

/-- The regularized denominator is nonzero for `0 < Km`. -/
lemma mmRegDen_ne_zero (Km : ℝ) (hKm : 0 < Km) (s : ℝ) : mmRegDen Km s ≠ 0 :=
  (mmRegDen_pos Km hKm s).ne'

/-- **Everywhere `HasDerivAt` law for the regularized denominator.** On either physical side the
derivative is read off the elementary formula; at the junction `s = 0` the two one-sided derivatives
agree at the shared value `1`, so the global derivative exists and equals `mmRegDeriv Km`. -/
lemma mmRegDen_hasDerivAt (Km : ℝ) (hKm : 0 < Km) (s : ℝ) :
    HasDerivAt (mmRegDen Km) (mmRegDeriv Km s) s := by
  rcases lt_trichotomy s 0 with hneg | hzero | hpos
  · -- Strictly negative: the function is the exponential branch on a neighbourhood.
    have hbranch : mmRegDen Km =ᶠ[𝓝 s] fun u => Km / 2 + (Km / 2) * Real.exp (2 * u / Km) := by
      filter_upwards [Iio_mem_nhds hneg] with u hu
      exact mmRegDen_of_neg Km hu
    have hd : HasDerivAt (fun u => Km / 2 + (Km / 2) * Real.exp (2 * u / Km))
        (Real.exp (2 * s / Km)) s := by
      have he : HasDerivAt (fun u => Real.exp (2 * u / Km))
          (Real.exp (2 * s / Km) * (2 / Km)) s := by
        have hlin : HasDerivAt (fun u : ℝ => 2 * u / Km) (2 / Km) s := by
          simpa [mul_comm, mul_div_assoc] using
            ((hasDerivAt_id s).const_mul (2 : ℝ)).div_const Km
        simpa [Function.comp_def] using (Real.hasDerivAt_exp (2 * s / Km)).comp s hlin
      have := (he.const_mul (Km / 2)).const_add (Km / 2)
      have hcoef : Km / 2 * (Real.exp (2 * s / Km) * (2 / Km)) = Real.exp (2 * s / Km) := by
        field_simp
      rwa [hcoef] at this
    rw [mmRegDeriv, if_neg (not_le.mpr hneg)]
    exact hd.congr_of_eventuallyEq hbranch
  · -- Junction `s = 0`: glue the two one-sided derivatives (both equal `1`).
    subst hzero
    -- Right side on `Ici 0`: the function is `Km + s`, derivative `1`.
    have hright : HasDerivWithinAt (mmRegDen Km) 1 (Ici 0) 0 := by
      have hbase : HasDerivWithinAt (fun u => Km + u) 1 (Ici 0) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_add Km).hasDerivWithinAt
      apply hbase.congr _ (by rw [mmRegDen_of_nonneg Km le_rfl])
      intro u hu
      exact mmRegDen_of_nonneg Km hu
    -- Left side on `Iic 0`: the function is the exponential branch, derivative `exp 0 = 1`.
    have hleft : HasDerivWithinAt (mmRegDen Km) 1 (Iic 0) 0 := by
      have hd : HasDerivAt (fun u => Km / 2 + (Km / 2) * Real.exp (2 * u / Km))
          (Real.exp (2 * (0 : ℝ) / Km)) 0 := by
        have he : HasDerivAt (fun u => Real.exp (2 * u / Km))
            (Real.exp (2 * (0 : ℝ) / Km) * (2 / Km)) 0 := by
          have hlin : HasDerivAt (fun u : ℝ => 2 * u / Km) (2 / Km) 0 := by
            simpa [mul_comm, mul_div_assoc] using
              ((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).div_const Km
          simpa [Function.comp_def] using (Real.hasDerivAt_exp (2 * (0 : ℝ) / Km)).comp 0 hlin
        have := (he.const_mul (Km / 2)).const_add (Km / 2)
        have hcoef : Km / 2 * (Real.exp (2 * (0 : ℝ) / Km) * (2 / Km))
            = Real.exp (2 * (0 : ℝ) / Km) := by field_simp
        rwa [hcoef] at this
      have hd1 : HasDerivWithinAt (fun u => Km / 2 + (Km / 2) * Real.exp (2 * u / Km))
          1 (Iic 0) 0 := by
        have : Real.exp (2 * (0 : ℝ) / Km) = 1 := by simp
        rw [this] at hd
        exact hd.hasDerivWithinAt
      refine hd1.congr (fun u hu => ?_) (by rw [mmRegDen_of_nonneg Km le_rfl]; norm_num)
      rcases eq_or_lt_of_le (mem_Iic.mp hu) with heq | hlt
      · subst heq; rw [mmRegDen_of_nonneg Km le_rfl]; norm_num
      · exact mmRegDen_of_neg Km hlt
    rw [mmRegDeriv, if_pos le_rfl]
    have huniv : HasDerivWithinAt (mmRegDen Km) 1 univ 0 := by
      rw [← Iic_union_Ici]; exact hleft.union hright
    rwa [hasDerivWithinAt_univ] at huniv
  · -- Strictly positive: the function is `Km + s` on a neighbourhood.
    have hbranch : mmRegDen Km =ᶠ[𝓝 s] fun u => Km + u := by
      filter_upwards [Ioi_mem_nhds hpos] with u hu
      exact mmRegDen_of_nonneg Km hu.le
    have hd : HasDerivAt (fun u => Km + u) 1 s := by
      simpa using (hasDerivAt_id s).const_add Km
    rw [mmRegDeriv, if_pos hpos.le]
    exact hd.congr_of_eventuallyEq hbranch

/-- The candidate derivative `mmRegDeriv Km` is continuous: both branches are continuous and agree
at the junction `s = 0` (shared value `1`). -/
lemma mmRegDeriv_continuous (Km : ℝ) (_hKm : 0 < Km) : Continuous (mmRegDeriv Km) := by
  have hexp : Continuous fun u : ℝ => Real.exp (2 * u / Km) :=
    Real.continuous_exp.comp (by fun_prop)
  refine Continuous.if_le continuous_const hexp continuous_const continuous_id ?_
  intro u hu
  -- At the junction `0 = u`, the constant `1` matches `exp(2u/Km) = exp 0 = 1`.
  rw [← hu]; simp

/-- **The regularized denominator is globally `ContDiff ℝ 1`.** Differentiable everywhere with
continuous derivative (`mmRegDen_hasDerivAt`, `mmRegDeriv_continuous`), it is `C¹` over the whole
substrate line — the global smoothness the true denominator `Km + s` lacks only at the pole. -/
lemma mmRegDen_contDiff (Km : ℝ) (hKm : 0 < Km) : ContDiff ℝ 1 (mmRegDen Km) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (mmRegDen_hasDerivAt Km hKm s).differentiableAt, ?_⟩
  have hderiv : deriv (mmRegDen Km) = mmRegDeriv Km :=
    funext fun s => (mmRegDen_hasDerivAt Km hKm s).deriv
  rw [hderiv]; exact mmRegDeriv_continuous Km hKm

/-- The **regularized Michaelis–Menten quasi-equilibrium level** `Vmax·s/mmRegDen Km s`, equal to the
true level `Vmax·s/(Km+s)` on the physical ray and `C¹` everywhere because the denominator is bounded
away from zero. -/
noncomputable def mmRegEquil (Km Vmax s : ℝ) : ℝ := Vmax * s / mmRegDen Km s

/-- On the physical ray the regularized rate law is the true Michaelis–Menten rate law. -/
lemma mmRegEquil_eq_of_nonneg (Km Vmax : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    mmRegEquil Km Vmax s = mmComplexEquil Km Vmax s := by
  rw [mmRegEquil, mmComplexEquil, mmRegDen_of_nonneg Km hs]

/-- **The regularized rate law is globally `ContDiff ℝ 1`.** A ratio of the affine numerator
`Vmax·s` and the globally-`C¹`, nonvanishing denominator `mmRegDen Km`. -/
lemma mmRegEquil_contDiff (Km Vmax : ℝ) (hKm : 0 < Km) :
    ContDiff ℝ 1 (mmRegEquil Km Vmax) := by
  have hnum : ContDiff ℝ 1 (fun s => Vmax * s) := contDiff_const.mul contDiff_id
  exact hnum.div (mmRegDen_contDiff Km hKm) (mmRegDen_ne_zero Km hKm)

/-- The **regularized Michaelis–Menten fast field**:
`mmRegFastField rate Km Vmax s z = -rate · (z - mmRegEquil Km Vmax s · e0)`. It is the same affine
relaxation in `z` as the true fast field, with the substrate-dependent target taken from the
globally-`C¹` regularized rate law. -/
noncomputable def mmRegFastField (rate Km Vmax : ℝ) : ℝ → E → E :=
  fun s z => -rate • (z - mmRegEquil Km Vmax s • e0)

/-- On the physical ray the regularized fast field equals the true Michaelis–Menten fast field. -/
lemma mmRegFastField_eq_of_nonneg (rate Km Vmax : ℝ) {s : ℝ} (hs : 0 ≤ s) (z : E) :
    mmRegFastField rate Km Vmax s z = mmFastField rate Km Vmax s z := by
  rw [mmRegFastField, mmFastField, mmRegEquil_eq_of_nonneg Km Vmax hs]

/-- The regularized fast field is stationary at the regularized equilibrium fibre. -/
lemma mmRegFastField_stat (rate Km Vmax s : ℝ) :
    mmRegFastField rate Km Vmax s (mmRegEquil Km Vmax s • e0) = 0 := by
  simp [mmRegFastField]

/-- The regularized fast field is one-sided contracting toward its equilibrium fibre at `rate ≥ 0`,
identically to the true field (the contraction depends only on the affine `z`-relaxation). -/
lemma mmRegFastField_oneSidedContraction (rate Km Vmax s : ℝ) (_h : 0 ≤ rate) :
    ODE.OneSidedContraction (mmRegFastField rate Km Vmax s) (mmRegEquil Km Vmax s • e0) rate := by
  intro z
  set q : E := mmRegEquil Km Vmax s • e0 with hq
  have hstat : mmRegFastField rate Km Vmax s q = 0 := mmRegFastField_stat rate Km Vmax s
  show ⟪mmRegFastField rate Km Vmax s z - mmRegFastField rate Km Vmax s q, z - q⟫
      ≤ -rate * ‖z - q‖ ^ 2
  rw [hstat, sub_zero]
  show ⟪-rate • (z - q), z - q⟫ ≤ -rate * ‖z - q‖ ^ 2
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- **The regularized fast field is jointly `ContDiff ℝ 1`.** The map `(s, z) ↦ -rate·(z - h_reg(s)·e0)`
is built from the globally-`C¹` regularized rate law `h_reg = mmRegEquil`, the constant direction `e0`,
and the linear coordinate `z`, all combined by `C¹`-preserving operations — the joint regularity the
abstract `ODE.SlowManifoldC1Seed` consumes, now available over the whole slow space. -/
lemma mmRegFastField_contDiff (rate Km Vmax : ℝ) (hKm : 0 < Km) :
    ContDiff ℝ 1 (fun p : ℝ × E => mmRegFastField rate Km Vmax p.1 p.2) := by
  have hz : ContDiff ℝ 1 (fun p : ℝ × E => p.2) := contDiff_snd
  have hequil : ContDiff ℝ 1 (fun p : ℝ × E => mmRegEquil Km Vmax p.1) :=
    (mmRegEquil_contDiff Km Vmax hKm).comp contDiff_fst
  have htarget : ContDiff ℝ 1 (fun p : ℝ × E => mmRegEquil Km Vmax p.1 • e0) :=
    hequil.smul contDiff_const
  have hsub : ContDiff ℝ 1 (fun p : ℝ × E => p.2 - mmRegEquil Km Vmax p.1 • e0) := hz.sub htarget
  exact hsub.const_smul (-rate)

/-- **The invertible fibre derivative of the regularized fast field at any fibre equilibrium.** In
the complex variable `z` the regularized field is the same affine relaxation `-rate·(z - target)` as
the true field, so its Fréchet derivative at the regularized equilibrium is the continuous linear
equivalence `mmFibreDeriv rate = -rate·id` of `CRNT.Dynamics.MichaelisMentenC1`. -/
lemma mmRegFastField_hasFDerivAt_fibre (rate : ℝ) (hrate : 0 < rate) (Km Vmax s : ℝ) :
    HasFDerivAt (mmRegFastField rate Km Vmax s) (mmFibreDeriv rate hrate : E →L[ℝ] E)
      (mmRegEquil Km Vmax s • e0) := by
  rw [mmFibreDeriv_coe]
  show HasFDerivAt (fun z : E => -rate • (z - mmRegEquil Km Vmax s • e0))
    (-rate • ContinuousLinearMap.id ℝ E) (mmRegEquil Km Vmax s • e0)
  have h1 : HasFDerivAt (fun z : E => z - mmRegEquil Km Vmax s • e0)
      (ContinuousLinearMap.id ℝ E) (mmRegEquil Km Vmax s • e0) :=
    (hasFDerivAt_id (mmRegEquil Km Vmax s • e0)).sub_const (mmRegEquil Km Vmax s • e0)
  exact h1.const_smul (-rate)

/-- The underlying (pre-`C¹`) slow-manifold seed of the regularized fast field: the parametrised
field, its positive contraction rate, per-fibre equilibrium, and per-fibre one-sided contraction.
Its constructed `manifoldMap` is pinned to the regularized complex curve by
`mmRegManifoldMap_eq`. -/
noncomputable def mmRegBaseSeed (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) :
    ODE.SlowManifoldSeed ℝ E where
  fast := mmRegFastField rate Km Vmax
  rate := rate
  rate_pos := hrate
  exists_stat := fun s => ⟨mmRegEquil Km Vmax s • e0, mmRegFastField_stat rate Km Vmax s⟩
  contraction := by
    intro s zstar hzs
    have hzeq : zstar = mmRegEquil Km Vmax s • e0 := by
      have h : -rate • (zstar - mmRegEquil Km Vmax s • e0) = 0 := hzs
      rcases smul_eq_zero.1 h with hr | hd
      · exact absurd (neg_eq_zero.1 hr) hrate.ne'
      · exact sub_eq_zero.1 hd
    rw [hzeq]
    exact mmRegFastField_oneSidedContraction rate Km Vmax s hrate.le

@[simp] lemma mmRegBaseSeed_fast (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) :
    (mmRegBaseSeed rate hrate Km Vmax).fast = mmRegFastField rate Km Vmax := rfl

@[simp] lemma mmRegBaseSeed_rate (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) :
    (mmRegBaseSeed rate hrate Km Vmax).rate = rate := rfl

/-- **Canonicity of the regularized reduction.** The constructed `manifoldMap` of the regularized
base seed equals the regularized complex-equilibrium curve `mmRegEquil Km Vmax s • e0`, pinning the
abstract `Classical.choose`-constructed graph to the regularized rate law. -/
theorem mmRegBaseManifoldMap_eq (rate : ℝ) (hrate : 0 < rate) (Km Vmax s : ℝ) :
    (mmRegBaseSeed rate hrate Km Vmax).manifoldMap s = mmRegEquil Km Vmax s • e0 :=
  ((mmRegBaseSeed rate hrate Km Vmax).manifoldMap_eq_of_stationary
    (mmRegFastField_stat rate Km Vmax s)).symm

/-- **The genuine `C¹` slow-manifold seed of the regularized Michaelis–Menten fast field.** Enriching
the base seed with the joint `ContDiff ℝ 1` field (`mmRegFastField_contDiff`) and the invertible
fibre derivative (`mmFibreDeriv`, identified by `mmRegFastField_hasFDerivAt_fibre` at the
canonical fibre equilibrium `mmRegManifoldMap_eq`) yields a real, globally-defined
`ODE.SlowManifoldC1Seed ℝ E` — the global instance the true Michaelis–Menten field cannot supply. -/
noncomputable def mmRegSlowManifoldSeed (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km) :
    ODE.SlowManifoldC1Seed ℝ E where
  toSlowManifoldSeed := mmRegBaseSeed rate hrate Km Vmax
  contDiff_fast := mmRegFastField_contDiff rate Km Vmax hKm
  fibreDeriv := fun _ => mmFibreDeriv rate hrate
  hasFDerivAt_fibre := by
    intro s
    show HasFDerivAt (mmRegFastField rate Km Vmax s) (mmFibreDeriv rate hrate : E →L[ℝ] E)
      ((mmRegBaseSeed rate hrate Km Vmax).manifoldMap s)
    rw [mmRegBaseManifoldMap_eq rate hrate Km Vmax s]
    exact mmRegFastField_hasFDerivAt_fibre rate hrate Km Vmax s

@[simp] lemma mmRegSlowManifoldSeed_fast (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km) :
    (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).fast = mmRegFastField rate Km Vmax := rfl

@[simp] lemma mmRegSlowManifoldSeed_rate (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km) :
    (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).rate = rate := rfl

/-- The constructed `manifoldMap` of the `C¹` regularized seed is the regularized complex curve. -/
theorem mmRegManifoldMap_eq (rate : ℝ) (hrate : 0 < rate) (Km Vmax s : ℝ) (hKm : 0 < Km) :
    (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap s = mmRegEquil Km Vmax s • e0 :=
  mmRegBaseManifoldMap_eq rate hrate Km Vmax s

/-- **The certified global `C¹` Michaelis–Menten reduction.** The abstract implicit-function
regularity `ODE.SlowManifoldC1Seed.contDiff_manifoldMap` of `CRNT.Dynamics.FenichelC1Manifold`,
applied to the genuine regularized seed, gives that the constructed `manifoldMap` is `ContDiff ℝ 1`
over the *whole* substrate line — no domain restriction — through the abstract API rather than the
bespoke closed-form route. -/
theorem mmRegManifoldMap_contDiff (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km) :
    ContDiff ℝ 1 (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap :=
  (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).contDiff_manifoldMap

/-- **The certified `C¹` reduction is faithful on the substrate ray.** On `s ≥ 0` the regularized
constructed slow manifold equals the true Michaelis–Menten complex-equilibrium curve
`Vmax·s/(Km+s) · e0`, so the global `C¹` reduction coincides with the genuine Michaelis–Menten
quasi-steady-state manifold on the physical domain. -/
theorem mmRegManifoldMap_eq_mm (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km)
    {s : ℝ} (hs : 0 ≤ s) :
    (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap s
      = mmComplexEquil Km Vmax s • e0 := by
  rw [mmRegManifoldMap_eq, mmRegEquil_eq_of_nonneg Km Vmax hs]

end CRNT.MichaelisMenten

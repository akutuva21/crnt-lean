import CRNT.Dynamics.MichaelisMentenCertifiedUniform
import CRNT.Dynamics.MichaelisMentenSlowDriftSpeed

/-!
# The coupled transverse one-sided contraction of the regularized Michaelis–Menten fast field

This module discharges the coupled transverse one-sided contraction hypothesis `hcon` of
`CRNT.Dynamics.MichaelisMentenCertifiedUniform`, turning the horizon-uniform tracking ceiling there
from a conditional statement into a theorem about the genuine ε-coupled Michaelis–Menten flow.

The regularized fast field `mmRegFastField rate Km Vmax s z = -rate · (z - mmRegEquil Km Vmax s · e0)`
is affine in the complex variable `z` with the constant slope `-rate · id`: the substrate `s` enters
only through the additive target `mmRegEquil Km Vmax s · e0`. At a fixed substrate value the target
cancels in any difference of two field values, so for every pair of complex states `z, w` the field
satisfies the exact identity `⟪field s z - field s w, z - w⟫ = -rate · ‖z - w‖²`. The transverse
spectrum of the frozen fibre is therefore exactly `-rate`, and the one-sided contraction holds with no
cross terms and no smallness condition. This is the negative logarithmic-norm bound of Dahlquist's
one-sided-Lipschitz stability theory, here an equality rather than an estimate because the fibre
Jacobian is the constant `mmFibreDeriv = -rate · id`.

Along the ε-coupled flow the complex variable solves the non-autonomous fast law
`ẋ = mmRegFastField rate Km Vmax (s t) (x t)`, where the substrate `s` solves the slow law
`ṡ = ε·g(s, z)`. Tracking the exact complex trajectory against the slaved manifold reference
`m t = manifoldMap (s t)` at a frozen substrate at each instant, the contraction supplies the negative
rate `-rate` cleanly, and the only motion of the reference is its `O(ε)` slaved velocity. The
abstract dissipative ceiling of `CRNT.Dynamics.MichaelisMentenCertifiedUniform`, restated here for a
time-dependent field (`ODE.coupled_dissipative_ceiling_nonauto`), then yields the all-time `O(ε)`
tracking bound with no contraction hypothesis assumed.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations":
on an attracting slow manifold the slaved fast variable tracks the slow flow at speed `O(ε)`, with the
transverse attraction supplied by the fibre contraction rate; and by the logarithmic-norm /
one-sided-Lipschitz theory of Dahlquist, under which a field whose transverse logarithmic norm is
`≤ -rate` contracts nearby trajectories, so the transverse gap obeys a dissipative Grönwall inequality
with negative rate `rate` and a defect measuring the drift of the moving reference.

**The non-autonomous dissipative ceiling** (`ODE.coupled_dissipative_ceiling_nonauto`). The exact
trajectory `x` solving the time-dependent law `ẋ = full t (x t)` tracked against a moving reference
`m` with velocity `m'`, under the time-dependent contraction
`⟪full t (x t) - full t (m t), x t - m t⟫ ≤ -λ·‖x t - m t‖²` and the reference defect
`‖full t (m t) - m' t‖ ≤ δ`, obeys the horizon-uniform ceiling `‖x t - m t‖ ≤ ‖x 0 - m 0‖ + δ/λ`.

**The frozen-fibre exact contraction** (`mmRegFastField_coupled_contraction`). At every fixed
substrate `s`, for every pair `z, w`,
`⟪mmRegFastField rate Km Vmax s z - mmRegFastField rate Km Vmax s w, z - w⟫ = -rate·‖z - w‖²`.

**The hypothesis-free coupled tracking ceiling** (`mmReg_coupled_tracking_ceiling_unconditional`).
For the exact complex trajectory `x` solving the non-autonomous fast law along the substrate path `s`
of the ε-coupled slow flow `ṡ = ε·g(s, z)` with uniform drift bound `‖g‖ ≤ G` and fast-field substrate
Lipschitz constant `L`, the transverse gap obeys `‖x t - m t‖ ≤ ‖x 0 - m 0‖ + (L/rate)·(ε·G)/rate` for
all `t ≥ 0`, with the coupled transverse contraction discharged from the field's affine structure: a
genuinely horizon-uniform `O(ε)` tracking bound with no assumed contraction.

**The hypothesis-free certified reduction** (`mmCertifiedUniformReduction_unconditional`). The
all-time confinements together with the hypothesis-free horizon-uniform `O(ε)` tracking field, with
the coupled transverse contraction discharged.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Dynamics.MichaelisMentenCertifiedUniform`, `CRNT.Dynamics.MichaelisMentenSlowDriftSpeed`.
-/

open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Non-autonomous coupled-flow dissipative tracking ceiling.** Let `x : ℝ → E` be an integral
curve of a time-dependent field `full` (`ẋ = full t (x t)`) and `m : ℝ → E` a moving reference with
velocity `m'` (`ṁ = m' t`). Suppose:

* `hlam : 0 < λ`, `hδ : 0 ≤ δ`;
* `hcon` — the *coupled transverse one-sided contraction* at every `t ≥ 0`:
  `⟪full t (x t) - full t (m t), x t - m t⟫ ≤ -λ · ‖x t - m t‖²`;
* `hdef` — the *reference defect bound* at every `t ≥ 0`: `‖full t (m t) - m' t‖ ≤ δ`.

Then the transverse gap is bounded by the horizon-uniform ceiling
`‖x t - m t‖ ≤ ‖x 0 - m 0‖ + δ / λ` for every `t ≥ 0`. The proof is the autonomous
`coupled_dissipative_ceiling` with the field evaluated along the trajectory at each instant: the
differential inequality on the Lyapunov square `V t = ‖x t - m t‖²` only ever uses the field at the
current time, so the time dependence is inert. -/
theorem coupled_dissipative_ceiling_nonauto {full : ℝ → E → E} {x m m' : ℝ → E} {lam δ : ℝ}
    (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hx : ∀ t, HasDerivAt x (full t (x t)) t) (hm : ∀ t, HasDerivAt m (m' t) t)
    (hcon : ∀ t, 0 ≤ t → ⟪full t (x t) - full t (m t), x t - m t⟫ ≤ -lam * ‖x t - m t‖ ^ 2)
    (hdef : ∀ t, 0 ≤ t → ‖full t (m t) - m' t‖ ≤ δ) :
    ∀ t, 0 ≤ t → ‖x t - m t‖ ≤ ‖x 0 - m 0‖ + δ / lam := by
  -- Error curve `e t = x t - m t` with derivative `full t (x t) - m' t`.
  set e : ℝ → E := fun t => x t - m t with he
  have hed : ∀ t, HasDerivAt e (full t (x t) - m' t) t := fun t => (hx t).sub (hm t)
  -- Lyapunov square `V t = ⟪e t, e t⟫ = ‖e t‖²` with derivative `2⟪full t (x t) - m' t, e t⟫`.
  set V : ℝ → ℝ := fun t => ⟪e t, e t⟫ with hV
  have hVd : ∀ t, HasDerivAt V (2 * ⟪full t (x t) - m' t, e t⟫) t := by
    intro t
    have h := (hed t).inner ℝ (hed t)
    have hsym : ⟪e t, full t (x t) - m' t⟫ + ⟪full t (x t) - m' t, e t⟫
        = 2 * ⟪full t (x t) - m' t, e t⟫ := by
      rw [real_inner_comm (e t) (full t (x t) - m' t)]; ring
    simpa [hV, hsym] using h
  -- The dissipative differential inequality on `V`: `V' t ≤ -2λ·V t + 2δ·‖e t‖`.
  have hVbound : ∀ t, 0 ≤ t → 2 * ⟪full t (x t) - m' t, e t⟫ ≤ -2 * lam * V t + 2 * δ * ‖e t‖ := by
    intro t ht
    have hsplit : full t (x t) - m' t = (full t (x t) - full t (m t)) + (full t (m t) - m' t) := by
      abel
    have hVe : V t = ‖e t‖ ^ 2 := by simp only [hV]; rw [real_inner_self_eq_norm_sq]
    have hc : ⟪full t (x t) - full t (m t), e t⟫ ≤ -lam * ‖e t‖ ^ 2 := hcon t ht
    have hd : ⟪full t (m t) - m' t, e t⟫ ≤ δ * ‖e t‖ := by
      calc ⟪full t (m t) - m' t, e t⟫
          ≤ ‖full t (m t) - m' t‖ * ‖e t‖ := real_inner_le_norm _ _
        _ ≤ δ * ‖e t‖ := mul_le_mul_of_nonneg_right (hdef t ht) (norm_nonneg _)
    have hinner : ⟪full t (x t) - m' t, e t⟫
        = ⟪full t (x t) - full t (m t), e t⟫ + ⟪full t (m t) - m' t, e t⟫ := by
      rw [hsplit, inner_add_left]
    rw [hVe]
    nlinarith [hc, hd, hinner]
  -- Fence `V` below the ceiling `(gap 0 + δ/λ)²` via strictly-larger comparison constants.
  set gap0 : ℝ := ‖x 0 - m 0‖ with hgap0
  have hgap0_nonneg : 0 ≤ gap0 := norm_nonneg _
  have hVη : ∀ {η : ℝ}, 0 < η → ∀ t, 0 ≤ t → V t ≤ (gap0 + (δ + η) / lam) ^ 2 := by
    intro η hη t ht
    set C : ℝ := gap0 + (δ + η) / lam with hC
    have hCpos : 0 < C := by
      have : 0 < (δ + η) / lam := by positivity
      linarith
    have hVcont : ContinuousOn V (Icc 0 t) :=
      (continuous_iff_continuousAt.2 fun s => (hVd s).continuousAt).continuousOn
    have ha : V 0 ≤ C ^ 2 := by
      have hV0 : V 0 = gap0 ^ 2 := by
        simp only [hV, he, hgap0]; rw [real_inner_self_eq_norm_sq]
      rw [hV0]
      have hle : gap0 ≤ C := by
        rw [hC]
        have hdη : 0 ≤ (δ + η) / lam := by positivity
        linarith
      exact pow_le_pow_left₀ hgap0_nonneg hle 2
    have hbound : ∀ s ∈ Ico 0 t, V s = C ^ 2 →
        2 * ⟪full s (x s) - m' s, e s⟫ < (0 : ℝ) := by
      intro s hs hVs
      have hs0 : 0 ≤ s := hs.1
      have hVe : V s = ‖e s‖ ^ 2 := by simp only [hV]; rw [real_inner_self_eq_norm_sq]
      have hnormC : ‖e s‖ = C := by
        have h1 : ‖e s‖ ^ 2 = C ^ 2 := by rw [← hVe, hVs]
        nlinarith [norm_nonneg (e s), hCpos.le, sq_nonneg (‖e s‖ - C), h1]
      have hb := hVbound s hs0
      rw [hVs] at hb
      have hcalc : -2 * lam * C ^ 2 + 2 * δ * ‖e s‖ < 0 := by
        rw [hnormC]
        have hexpand : -2 * lam * C ^ 2 + 2 * δ * C = 2 * C * (δ - lam * C) := by ring
        have hlamC : lam * C = lam * gap0 + (δ + η) := by
          rw [hC, mul_add]
          field_simp
        have hfac : δ - lam * C = -(lam * gap0) - η := by rw [hlamC]; ring
        rw [hexpand, hfac]
        have hneg : -(lam * gap0) - η < 0 := by
          have : 0 ≤ lam * gap0 := mul_nonneg hlam.le hgap0_nonneg
          linarith
        have : 2 * C > 0 := by linarith
        exact mul_neg_of_pos_of_neg this hneg
      linarith [hb, hcalc]
    have hkey := image_le_of_deriv_right_lt_deriv_boundary
      (f := V) (f' := fun s => 2 * ⟪full s (x s) - m' s, e s⟫) (a := 0) (b := t)
      hVcont (fun s _ => (hVd s).hasDerivWithinAt)
      (B := fun _ => C ^ 2) (B' := fun _ => 0) ha (fun _ => hasDerivAt_const _ (C ^ 2))
      (fun s hs hVs => hbound s hs hVs)
    exact hkey (right_mem_Icc.2 ht)
  intro t ht
  have hVlim : V t ≤ (gap0 + δ / lam) ^ 2 := by
    have hcont : ContinuousWithinAt (fun η : ℝ => (gap0 + (δ + η) / lam) ^ 2) (Ioi 0) 0 := by
      fun_prop
    have htend : Tendsto (fun η : ℝ => (gap0 + (δ + η) / lam) ^ 2) (𝓝[>] 0)
        (𝓝 ((gap0 + δ / lam) ^ 2)) := by
      have h := hcont.tendsto
      simpa [add_zero] using h
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hVη hη t ht
  set C0 : ℝ := gap0 + δ / lam with hC0
  have hC0_nonneg : 0 ≤ C0 := by
    rw [hC0]
    have hdl : 0 ≤ δ / lam := by positivity
    linarith
  have hVe : V t = ‖e t‖ ^ 2 := by simp only [hV]; rw [real_inner_self_eq_norm_sq]
  rw [hVe] at hVlim
  have : ‖e t‖ ≤ C0 := by nlinarith [norm_nonneg (e t), hC0_nonneg, sq_nonneg (‖e t‖ - C0)]
  simpa [he, hC0] using this

end ODE

namespace CRNT.MichaelisMenten

open ODE

/-- **The frozen-fibre exact transverse contraction of the regularized fast field.** At every fixed
substrate `s`, for every pair of complex states `z, w`,
`⟪mmRegFastField rate Km Vmax s z - mmRegFastField rate Km Vmax s w, z - w⟫ = -rate · ‖z - w‖²`. The
substrate-dependent target `mmRegEquil Km Vmax s · e0` cancels in the difference because the field is
affine in `z` with the constant slope `mmFibreDeriv = -rate · id`, so the transverse rate is exactly
`-rate` between any two points, an equality rather than the one-sided estimate of
`mmRegFastField_oneSidedContraction`. -/
theorem mmRegFastField_coupled_contraction (rate Km Vmax s : ℝ) (z w : E) :
    ⟪mmRegFastField rate Km Vmax s z - mmRegFastField rate Km Vmax s w, z - w⟫
      = -rate * ‖z - w‖ ^ 2 := by
  -- The target cancels: `field s z - field s w = -rate • (z - w)`.
  have hdiff : mmRegFastField rate Km Vmax s z - mmRegFastField rate Km Vmax s w
      = -rate • (z - w) := by
    simp only [mmRegFastField, smul_sub]
    abel
  rw [hdiff, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- **The hypothesis-free horizon-uniform Michaelis–Menten tracking ceiling.** The exact complex
trajectory `x` solves the genuine non-autonomous fast law `ẋ = mmRegFastField rate Km Vmax (s t) (x t)`
along the substrate path `s` of the ε-coupled slow flow `ṡ = ε·g(s, z)` with uniform drift bound
`‖g‖ ≤ G` and fast-field substrate Lipschitz constant `L`. Tracking against the slaved manifold
reference `m t = manifoldMap (s t)`, the transverse gap obeys the time-uniform ceiling
`‖x t - m t‖ ≤ ‖x 0 - m 0‖ + (L/rate)·(ε·G)/rate` for all `t ≥ 0`. The coupled transverse one-sided
contraction is discharged from the field's affine structure (`mmRegFastField_coupled_contraction`) and
the reference defect from the `O(ε)` slaved velocity (`mmRegSlavedVelocity_le_of_drift`): no contraction
hypothesis and no ε-smallness condition is assumed, and the ceiling is `O(ε)` and horizon-uniform. -/
theorem mmReg_coupled_tracking_ceiling_unconditional (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ)
    (hKm : 0 < Km) {L ε G : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hlip : ∀ s s' z, ‖mmRegFastField rate Km Vmax s z - mmRegFastField rate Km Vmax s' z‖
      ≤ L * dist s s')
    {g : ℝ → E → ℝ} (hg : ∀ a b, ‖g a b‖ ≤ G) {x : ℝ → E} {s : ℝ → ℝ} {z : ℝ → E}
    (hx : ∀ t, HasDerivAt x (mmRegFastField rate Km Vmax (s t) (x t)) t)
    (hs : ∀ τ, HasDerivAt s (mmRegSlowDrift ε g (s τ) (z τ)) τ) :
    ∀ t, 0 ≤ t →
      ‖x t - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s t)‖
        ≤ ‖x 0 - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s 0)‖
          + (L / rate) * (ε * G) / rate := by
  -- The slaved reference `m t = manifoldMap (s t)` has velocity `mmRegSlavedVelocity` by the chain
  -- rule through the global `C¹` regularity of the manifold map.
  set m : ℝ → E := fun t => (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s t) with hm
  have hmd : ∀ t, HasDerivAt m
      (mmRegSlavedVelocity rate hrate Km Vmax hKm (s t) (mmRegSlowDrift ε g (s t) (z t))) t := by
    intro t
    exact mmRegHasDerivAt_slavedCurve rate hrate Km Vmax hKm
      (s' := fun τ => mmRegSlowDrift ε g (s τ) (z τ)) (hs t)
  -- The non-autonomous field along the flow: `full t = mmRegFastField rate Km Vmax (s t)`.
  set full : ℝ → E → E := fun t y => mmRegFastField rate Km Vmax (s t) y with hfull
  -- The coupled transverse contraction is the frozen-fibre exact identity at the current substrate.
  have hcon : ∀ t, 0 ≤ t → ⟪full t (x t) - full t (m t), x t - m t⟫
      ≤ -rate * ‖x t - m t‖ ^ 2 := by
    intro t _
    rw [hfull]
    exact le_of_eq (mmRegFastField_coupled_contraction rate Km Vmax (s t) (x t) (m t))
  -- The fast field vanishes on its manifold fibre, so `full t (m t) = 0` and the reference defect
  -- equals the `O(ε)` slaved velocity.
  have hstat : ∀ t, full t (m t) = 0 := by
    intro t
    simp only [hfull, hm]
    rw [mmRegManifoldMap_eq rate hrate Km Vmax (s t) hKm]
    exact mmRegFastField_stat rate Km Vmax (s t)
  have hdef : ∀ t, 0 ≤ t →
      ‖full t (m t)
        - mmRegSlavedVelocity rate hrate Km Vmax hKm (s t) (mmRegSlowDrift ε g (s t) (z t))‖
      ≤ (L / rate) * (ε * G) := by
    intro t _
    rw [hstat t, zero_sub, norm_neg]
    exact mmRegSlavedVelocity_le_of_drift rate hrate Km Vmax hKm hL hε hG hlip hg hs
  have hδ : (0 : ℝ) ≤ (L / rate) * (ε * G) := by
    have : 0 ≤ L / rate := by positivity
    exact mul_nonneg this (mul_nonneg hε hG)
  exact coupled_dissipative_ceiling_nonauto hrate hδ hx hmd hcon hdef

/-- **The hypothesis-free time-uniform certified Michaelis–Menten reduction.** The all-time
confinements of `mmCertifiedUniformReduction` together with the horizon-uniform `O(ε)` tracking field,
with the coupled transverse one-sided contraction discharged from the regularized fast field's affine
structure rather than assumed. The exact complex trajectory `x` solves the genuine non-autonomous fast
law along the substrate path `mmSubstrate Km Vmax hKm hV s₀`, which solves the ε-coupled slow law with
uniform drift bound `‖g‖ ≤ G`; the tracking ceiling
`C = ‖x 0 - m 0‖ + (L/rate)·(ε·G)/rate` is `O(ε)` and independent of the horizon. -/
theorem mmCertifiedUniformReduction_unconditional (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ)
    (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ} (hs0 : 0 ≤ s₀)
    {L ε G : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hlip : ∀ s s' z, ‖mmRegFastField rate Km Vmax s z - mmRegFastField rate Km Vmax s' z‖
      ≤ L * dist s s')
    {g : ℝ → E → ℝ} (hg : ∀ a b, ‖g a b‖ ≤ G) {x : ℝ → E} {z : ℝ → E}
    (hx : ∀ t, HasDerivAt x
      (mmRegFastField rate Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t) (x t)) t)
    (hs : ∀ τ, HasDerivAt (mmSubstrate Km Vmax hKm hV s₀)
      (mmRegSlowDrift ε g (mmSubstrate Km Vmax hKm hV s₀ τ) (z τ)) τ) :
    mmCertifiedUniformReduction rate hrate Km Vmax hKm hV s₀ ε G L x
      (mmSubstrate Km Vmax hKm hV s₀) where
  confined ht := mmSubstrate_mem_Icc Km Vmax hKm hV hs0 ht
  level_confined ht := mmReducedComplexLevel_mem_Icc Km Vmax hKm hV hs0 ht
  tracking_uniform :=
    mmReg_coupled_tracking_ceiling_unconditional rate hrate Km Vmax hKm hL hε hG hlip hg hx hs

end CRNT.MichaelisMenten

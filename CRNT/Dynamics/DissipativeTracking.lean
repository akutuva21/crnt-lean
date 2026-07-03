import CRNT.Dynamics.Fenichel

/-!
# Horizon-uniform dissipative tracking: the logarithmic-norm Grönwall estimate

This module supplies the transverse-dissipativity estimate that upgrades the compact-time
Grönwall tracking of `CRNT.Dynamics.MichaelisMentenCertified` to a bound that is *uniform in the
time horizon*. The compact-time estimate `gronwallBound δ K εf T` grows like `e^{K·T}` because the
full field is only assumed `K`-Lipschitz; nothing pulls trajectories back toward the slow manifold.
Replacing the symmetric Lipschitz bound by a *negative one-sided* (dissipative) bound transverse to
the manifold removes the exponential blow-up: the gap decays at rate `λ` toward a steady ceiling
`δ/λ`. It is CRN-free and lives in the `ODE` namespace shared with `CRNT.Dynamics.Tikhonov`,
`CRNT.Dynamics.Fenichel`, `CRNT.Dynamics.QSSA`, and `CRNT.Dynamics.FlowConstruction`.

This is the logarithmic-norm / one-sided-Lipschitz stability theory of Dahlquist: a vector field
whose logarithmic norm transverse to a reference curve is `≤ -λ < 0` contracts nearby trajectories,
so the inter-trajectory distance obeys a *dissipative* Grönwall inequality with a negative rate
constant. On an attracting slow manifold the transverse rate is exactly the Fenichel fibre
contraction rate (`SlowManifold.rate`, `ODE.OneSidedContraction`), so the same `λ` that governs the
boundary-layer collapse governs the all-time tracking ceiling.

**Abstract dissipative Grönwall** (`ODE.le_dissipative_of_deriv_le`). For a scalar comparison
function `u : ℝ → ℝ` (read: the transverse gap `‖x − m‖`) that is continuous on `[0, T]`, has a
right derivative `u' x` on `[0, T)`, and satisfies the dissipative differential inequality
`u' x ≤ -λ · u x + δ` with `λ > 0` and defect `δ ≥ 0`, the gap obeys
`u t ≤ u 0 · Real.exp (-λ · t) + δ / λ` for every `t ∈ [0, T]`. The transient `u 0 · e^{-λt}` decays
to zero and the steady term `δ / λ` is *independent of the horizon* `T`: no `e^{K·T}` growth. The
proof instantiates Mathlib's `le_gronwallBound_of_liminf_deriv_right_le` with the negative rate
`K := -λ` and reads off the closed form `gronwallBound (u 0) (-λ) δ t = u 0 · e^{-λt}
+ (δ/λ)(1 - e^{-λt}) ≤ u 0 · e^{-λt} + δ/λ`.

**Steady tracking ceiling** (`ODE.dissipative_tracking_ceiling`). Specialising to a transverse gap
`gap : ℝ → ℝ` (the distance `‖x − m‖` between a trajectory and the slow manifold reference) with the
dissipative bound at rate `λ` and defect `δ`, the gap is uniformly bounded by `gap 0 + δ / λ` for all
`t ∈ [0, T]` — one constant, no horizon dependence.

**Asymptotic ceiling** (`ODE.dissipative_gap_le_ceiling`). For the same data taken over `[0, ∞)`, the
transient `gap 0 · e^{-λt}` tends to `0`, so `limsup` of the gap is at most `δ / λ`: when the defect
`δ` is `O(ε)` the asymptotic tracking error is `O(ε)`, vanishing as `ε → 0`.

**Out of scope.** The dissipative differential inequality `u' ≤ -λ u + δ` is supplied as a
hypothesis; deriving it for a concrete enzyme field from a uniform negative one-sided Lipschitz bound
transverse to the Michaelis–Menten graph `h(s)` requires differentiating `t ↦ ‖x t − h(s t)‖²` along
the *coupled* slow–fast flow and absorbing the slow drift of `h(s t)` into the defect `δ`. That
coupled-flow differentiation needs the parametrised slow ODE for the substrate together with a
transverse contraction bound for the full field, neither of which the repository currently exposes in
the form this estimate consumes; the Michaelis–Menten instantiation is therefore left to a
downstream module. What is delivered here is the complete, field-agnostic dissipative-Grönwall engine
that such an instantiation plugs into, replacing the horizon-dependent `gronwallBound δ K εf T` by the
uniform ceiling `δ / λ`.

Depends on: CRNT.Dynamics.Fenichel.
-/

open Filter Set
open scoped Topology

namespace ODE

/-- **Abstract dissipative (logarithmic-norm) Grönwall estimate.** Let `u : ℝ → ℝ` be continuous on
`[0, T]`, have a right derivative `u' x` at every `x ∈ [0, T)`, and satisfy the *dissipative*
differential inequality `u' x ≤ -λ · u x + δ` with a strictly positive transverse rate `λ` and a
nonnegative defect `δ`. Then for every `t ∈ [0, T]`,
`u t ≤ u 0 · Real.exp (-λ · t) + δ / λ`.

The transient `u 0 · e^{-λt}` decays to `0` and the steady term `δ / λ` is independent of the time
horizon `T`: unlike the symmetric `K`-Lipschitz Grönwall bound `gronwallBound δ K εf T`, which grows
like `e^{K·T}`, the negative rate `-λ` produces no horizon-dependent blow-up. This is the
one-sided-Lipschitz (Dahlquist) stability estimate underlying horizon-uniform Fenichel tracking. -/
theorem le_dissipative_of_deriv_le {u u' : ℝ → ℝ} {lam δ T : ℝ} (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hu : ContinuousOn u (Icc 0 T)) (hu' : ∀ x ∈ Ico 0 T, HasDerivWithinAt u (u' x) (Ici x) x)
    (hbound : ∀ x ∈ Ico 0 T, u' x ≤ -lam * u x + δ) :
    ∀ t ∈ Icc 0 T, u t ≤ u 0 * Real.exp (-lam * t) + δ / lam := by
  -- Instantiate Mathlib's Grönwall inequality with the negative rate `K := -lam` and `ε := δ`.
  have hK : (-lam : ℝ) ≠ 0 := neg_ne_zero.2 hlam.ne'
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (f := u) (f' := u') (δ := u 0)
    (K := -lam) (ε := δ) (a := 0) (b := T) hu
    (fun x hx _r hr => (hu' x hx).liminf_right_slope_le hr) le_rfl
    (by intro x hx; have := hbound x hx; simpa [neg_mul] using this)
  intro t ht
  have hgt := hgron t ht
  rw [sub_zero] at hgt
  -- Closed form: `gronwallBound (u 0) (-lam) δ t = u 0 · e^{-λt} + (δ/λ)(1 - e^{-λt})`.
  rw [gronwallBound_of_K_ne_0 hK] at hgt
  -- Bound the steady term: `(δ/λ)(1 - e^{-λt}) ≤ δ/λ` since `0 ≤ e^{-λt}`.
  have hexp_nonneg : (0 : ℝ) ≤ Real.exp (-lam * t) := (Real.exp_pos _).le
  have hclose : u 0 * Real.exp (-lam * t)
      + δ / (-lam) * (Real.exp (-lam * t) - 1) ≤ u 0 * Real.exp (-lam * t) + δ / lam := by
    have : δ / (-lam) * (Real.exp (-lam * t) - 1) ≤ δ / lam := by
      rw [div_neg, neg_mul]
      have hle : δ / lam * (1 - Real.exp (-lam * t)) ≤ δ / lam := by
        have hdl : 0 ≤ δ / lam := by positivity
        have : δ / lam * (1 - Real.exp (-lam * t)) ≤ δ / lam * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hdl
        simpa using this
      have heq : -(δ / lam * (Real.exp (-lam * t) - 1)) = δ / lam * (1 - Real.exp (-lam * t)) := by
        ring
      linarith [heq ▸ hle]
    linarith
  linarith [hgt, hclose]

/-- **Horizon-uniform tracking ceiling.** Let `gap : ℝ → ℝ` measure the transverse gap between a
trajectory and a slow-manifold reference (read: `gap t = ‖x t − m t‖`). If `gap` is continuous on
`[0, T]`, has a right derivative `gap' x` on `[0, T)`, and satisfies the dissipative inequality
`gap' x ≤ -λ · gap x + δ` (a uniform negative one-sided Lipschitz / logarithmic-norm bound transverse
to the manifold, with defect `δ`), and additionally `gap 0 ≥ 0`, then the gap is uniformly bounded:
`gap t ≤ gap 0 + δ / λ` for every `t ∈ [0, T]`. The bound has *no* `T`-dependence — the hallmark of
dissipative Fenichel tracking. -/
theorem dissipative_tracking_ceiling {gap gap' : ℝ → ℝ} {lam δ T : ℝ} (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hg0 : 0 ≤ gap 0) (hg : ContinuousOn gap (Icc 0 T))
    (hg' : ∀ x ∈ Ico 0 T, HasDerivWithinAt gap (gap' x) (Ici x) x)
    (hbound : ∀ x ∈ Ico 0 T, gap' x ≤ -lam * gap x + δ) :
    ∀ t ∈ Icc 0 T, gap t ≤ gap 0 + δ / lam := by
  intro t ht
  have hmain := le_dissipative_of_deriv_le hlam hδ hg hg' hbound t ht
  -- `e^{-λt} ≤ 1` on `t ≥ 0`, so the transient is at most `gap 0`.
  have ht0 : 0 ≤ t := ht.1
  have hexp_le_one : Real.exp (-lam * t) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    have : 0 ≤ lam * t := mul_nonneg hlam.le ht0
    linarith
  have htrans : gap 0 * Real.exp (-lam * t) ≤ gap 0 :=
    by simpa using mul_le_mul_of_nonneg_left hexp_le_one hg0
  linarith [hmain, htrans]

/-- **Asymptotic tracking ceiling.** Taking the dissipative bound over all of `[0, ∞)`, the transient
`gap 0 · e^{-λt}` tends to `0`, so the gap is eventually within any margin above the steady ceiling
`δ / λ`: for every `η > 0` there is a time beyond which `gap t ≤ δ / λ + η`. When the defect `δ` is
`O(ε)` (the slaving defect of the reduced flow), the all-time tracking error is `O(ε)` and vanishes
as `ε → 0` — the horizon-uniform replacement for the compact-time Grönwall ball. -/
theorem dissipative_gap_le_ceiling {gap gap' : ℝ → ℝ} {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hg : ∀ T, ContinuousOn gap (Icc 0 T))
    (hg' : ∀ x, 0 ≤ x → HasDerivWithinAt gap (gap' x) (Ici x) x)
    (hbound : ∀ x, 0 ≤ x → gap' x ≤ -lam * gap x + δ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in atTop, gap t ≤ δ / lam + η := by
  -- The transient envelope `gap 0 · e^{-λt} + δ/λ` tends to `δ/λ`.
  have henv : Tendsto (fun t : ℝ => gap 0 * Real.exp (-lam * t) + δ / lam) atTop (𝓝 (δ / lam)) := by
    have hexp : Tendsto (fun t : ℝ => Real.exp (-lam * t)) atTop (𝓝 0) := by
      have hmul : Tendsto (fun t : ℝ => lam * t) atTop atTop :=
        Tendsto.const_mul_atTop hlam (tendsto_id (α := ℝ))
      have hcomp : Tendsto (fun t : ℝ => -lam * t) atTop atBot := by
        have h := tendsto_neg_atTop_atBot.comp hmul
        have hfun : (Neg.neg ∘ fun t : ℝ => lam * t) = fun t : ℝ => -lam * t := by
          funext s; simp [Function.comp, neg_mul]
        rwa [hfun] at h
      exact Real.tendsto_exp_atBot.comp hcomp
    have htrans : Tendsto (fun t : ℝ => gap 0 * Real.exp (-lam * t)) atTop (𝓝 0) := by
      simpa using hexp.const_mul (gap 0)
    simpa using htrans.add_const (δ / lam)
  -- Eventually the envelope is within `η` of the ceiling.
  have henvη : ∀ᶠ t in atTop, gap 0 * Real.exp (-lam * t) + δ / lam < δ / lam + η :=
    henv.eventually_lt_const (show δ / lam < δ / lam + η by linarith)
  -- Eventually `t ≥ 0`, so the dissipative bound applies; chain through the envelope.
  filter_upwards [henvη, eventually_ge_atTop (0 : ℝ)] with t htη ht0
  have hmain := le_dissipative_of_deriv_le hlam hδ (hg t)
    (fun x hx => hg' x hx.1) (fun x hx => hbound x hx.1) t (right_mem_Icc.2 ht0)
  linarith [hmain, htη]

end ODE

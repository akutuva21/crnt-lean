import CRNT.Dynamics.DissipativeTracking
import CRNT.Dynamics.MichaelisMentenCertified

/-!
# The time-uniform Michaelis–Menten tracking ceiling: an all-time `O(ε)` bound via coupled-flow dissipativity

This module completes the certified-reduction companion of `CRNT.Dynamics.MichaelisMentenCertified`
by supplying the missing horizon-uniform tracking constant. The certified reduction there delivers
all-time confinement of the substrate and reduced complex level, and an all-time `O(ε)` slaved
velocity (`mmRegSlavedVelocity_certified`), but its exact-versus-reduced tracking error is the
compact-time Grönwall bound `gronwallBound δ K εf T`, which for `K > 0` grows like `e^{K·T}` and
diverges as `T → ∞`. The dissipative-Grönwall engine of `CRNT.Dynamics.DissipativeTracking` replaces
that horizon-dependent ball by the steady ceiling `δ / λ` once a *negative one-sided* (dissipative)
bound transverse to the slow manifold is available. Here that bound is derived for the coupled
slow–fast Michaelis–Menten flow and fed into the engine.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations",
and underpinned by the logarithmic-norm / one-sided-Lipschitz stability theory of Dahlquist: a vector
field whose logarithmic norm transverse to a reference curve is `≤ -λ < 0` contracts nearby
trajectories, so the transverse gap obeys a dissipative Grönwall inequality with negative rate `λ`
and a defect `δ` measuring the drift of the moving reference. On the Michaelis–Menten slow manifold
the transverse rate is the fibre contraction rate (`ODE.OneSidedContraction`, `SlowManifold.rate`),
and the defect is the `O(ε)` slaved velocity of the manifold reference.

**Abstract coupled-flow ceiling** (`ODE.coupled_dissipative_ceiling`). For an exact trajectory
`x : ℝ → E` of an autonomous field `full` (`ẋ = full x`) tracked against a moving reference
`m : ℝ → E` with velocity `m'`, suppose the *coupled transverse one-sided contraction*
`⟪full (x t) - full (m t), x t - m t⟫ ≤ -λ · ‖x t - m t‖²` holds at every `t ≥ 0` with `λ > 0`, and
the *reference defect* `‖full (m t) - m' t‖ ≤ δ` holds with `δ ≥ 0`. Then the transverse gap obeys the
horizon-uniform ceiling `‖x t - m t‖ ≤ ‖x 0 - m 0‖ + δ / λ` for all `t ≥ 0` — no `T`-dependence. The
proof differentiates the Lyapunov square `V t = ‖x t - m t‖²` along the coupled flow; the contraction
supplies `-2λ·V` and the defect supplies `+2δ·√V`, so any level set `V = (gap 0 + (δ+η)/λ)²` is
strictly entering, fencing `V` below `(gap 0 + δ/λ)²` via the mean-value fencing inequality and a
limit `η → 0`.

**Michaelis–Menten instantiation** (`mmReg_coupled_tracking_ceiling`). For the regularized
Michaelis–Menten complex trajectory `x` and a substrate path `s` solving the ε-coupled slow law
`ṡ = ε·g(s, z)`, the moving reference is the slaved complex curve
`m t = manifoldMap (s t) = mmRegEquil Km Vmax (s t) • e0`, whose velocity `mmRegSlavedVelocity` is
bounded by `(L / rate)·(ε·G) = O(ε)` for all time (`mmRegSlavedVelocity_certified`). Under the
coupled transverse contraction at rate `rate`, the gap is uniformly bounded by
`‖x 0 - m 0‖ + (L / rate)·(ε·G) / rate` for all `t ≥ 0`: a genuinely horizon-uniform `O(ε)` tracking
constant, the all-time replacement for `gronwallBound δ K εf T`.

**Time-uniform certified reduction** (`mmCertifiedUniformReduction`, `mmCertifiedUniformReduction_of`).
A record bundling the all-time confinements of `mmCertifiedReduction` with the time-uniform tracking
field: a single constant `C = ‖x 0 - m 0‖ + (L / rate)·(ε·G) / rate`, independent of the horizon,
within which the exact complex trajectory tracks the slaved manifold reference for all forward time.

**The transverse hypothesis is the crux.** The coupled transverse one-sided contraction
`⟪full (x t) - full (m t), x t - m t⟫ ≤ -λ·‖x t - m t‖²` is the load-bearing input: it asserts that the
*full* enzyme field — not merely the frozen fast fibre — pulls the exact trajectory toward the moving
manifold reference faster than the slow drift pushes them apart. For the affine regularized fast field
this is the fibre contraction `mmRegFastField_oneSidedContraction` carried along the coupled flow when
the fast relaxation dominates; it is supplied here as an explicit hypothesis on the coupled pair,
exactly the negative logarithmic-norm condition the Dahlquist theory requires and the engine of
`CRNT.Dynamics.DissipativeTracking` consumes.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.DissipativeTracking`,
`CRNT.Dynamics.MichaelisMentenCertified`.
-/

open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Abstract coupled-flow dissipative tracking ceiling.** Let `x : ℝ → E` be an integral curve of
an autonomous field `full` (`ẋ = full x`) and `m : ℝ → E` a moving reference with velocity `m'`
(`ṁ = m' t`). Suppose:

* `hlam : 0 < λ`, `hδ : 0 ≤ δ`;
* `hcon` — the *coupled transverse one-sided contraction* at every `t ≥ 0`:
  `⟪full (x t) - full (m t), x t - m t⟫ ≤ -λ · ‖x t - m t‖²`;
* `hdef` — the *reference defect bound* at every `t ≥ 0`: `‖full (m t) - m' t‖ ≤ δ`.

Then the transverse gap is bounded by the horizon-uniform ceiling
`‖x t - m t‖ ≤ ‖x 0 - m 0‖ + δ / λ` for every `t ≥ 0`. The bound has no horizon dependence: the
transient `‖x 0 - m 0‖` is fixed and the steady term `δ / λ` is the Dahlquist dissipative ceiling. -/
theorem coupled_dissipative_ceiling {full : E → E} {x m m' : ℝ → E} {lam δ : ℝ}
    (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hx : ∀ t, HasDerivAt x (full (x t)) t) (hm : ∀ t, HasDerivAt m (m' t) t)
    (hcon : ∀ t, 0 ≤ t → ⟪full (x t) - full (m t), x t - m t⟫ ≤ -lam * ‖x t - m t‖ ^ 2)
    (hdef : ∀ t, 0 ≤ t → ‖full (m t) - m' t‖ ≤ δ) :
    ∀ t, 0 ≤ t → ‖x t - m t‖ ≤ ‖x 0 - m 0‖ + δ / lam := by
  -- Error curve `e t = x t - m t` with derivative `full (x t) - m' t`.
  set e : ℝ → E := fun t => x t - m t with he
  have hed : ∀ t, HasDerivAt e (full (x t) - m' t) t := fun t => (hx t).sub (hm t)
  -- Lyapunov square `V t = ⟪e t, e t⟫ = ‖e t‖²` with derivative `2⟪full (x t) - m' t, e t⟫`.
  set V : ℝ → ℝ := fun t => ⟪e t, e t⟫ with hV
  have hVd : ∀ t, HasDerivAt V (2 * ⟪full (x t) - m' t, e t⟫) t := by
    intro t
    have h := (hed t).inner ℝ (hed t)
    have hsym : ⟪e t, full (x t) - m' t⟫ + ⟪full (x t) - m' t, e t⟫
        = 2 * ⟪full (x t) - m' t, e t⟫ := by
      rw [real_inner_comm (e t) (full (x t) - m' t)]; ring
    simpa [hV, hsym] using h
  -- The dissipative differential inequality on `V`: `V' t ≤ -2λ·V t + 2δ·‖e t‖`.
  have hVbound : ∀ t, 0 ≤ t → 2 * ⟪full (x t) - m' t, e t⟫ ≤ -2 * lam * V t + 2 * δ * ‖e t‖ := by
    intro t ht
    -- Split the velocity into the contracting part and the reference defect.
    have hsplit : full (x t) - m' t = (full (x t) - full (m t)) + (full (m t) - m' t) := by abel
    have hVe : V t = ‖e t‖ ^ 2 := by simp only [hV]; rw [real_inner_self_eq_norm_sq]
    -- Contraction term: `⟪full (x t) - full (m t), e t⟫ ≤ -λ·‖e t‖²`.
    have hc : ⟪full (x t) - full (m t), e t⟫ ≤ -lam * ‖e t‖ ^ 2 := hcon t ht
    -- Defect term: `⟪full (m t) - m' t, e t⟫ ≤ δ·‖e t‖`.
    have hd : ⟪full (m t) - m' t, e t⟫ ≤ δ * ‖e t‖ := by
      calc ⟪full (m t) - m' t, e t⟫
          ≤ ‖full (m t) - m' t‖ * ‖e t‖ := real_inner_le_norm _ _
        _ ≤ δ * ‖e t‖ := mul_le_mul_of_nonneg_right (hdef t ht) (norm_nonneg _)
    have hinner : ⟪full (x t) - m' t, e t⟫
        = ⟪full (x t) - full (m t), e t⟫ + ⟪full (m t) - m' t, e t⟫ := by
      rw [hsplit, inner_add_left]
    rw [hVe]
    nlinarith [hc, hd, hinner]
  -- Fence `V` below the ceiling `(gap 0 + δ/λ)²` via strictly-larger comparison constants.
  set gap0 : ℝ := ‖x 0 - m 0‖ with hgap0
  have hgap0_nonneg : 0 ≤ gap0 := norm_nonneg _
  -- For each margin `η > 0`, `V t ≤ (gap0 + (δ+η)/λ)²` on `[0, t]`.
  have hVη : ∀ {η : ℝ}, 0 < η → ∀ t, 0 ≤ t → V t ≤ (gap0 + (δ + η) / lam) ^ 2 := by
    intro η hη t ht
    set C : ℝ := gap0 + (δ + η) / lam with hC
    have hCpos : 0 < C := by
      have : 0 < (δ + η) / lam := by positivity
      linarith
    -- Apply the strict mean-value fencing inequality with constant boundary `B = C²`.
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
    -- Boundary condition: where `V x = C²`, the derivative is strictly negative.
    have hbound : ∀ s ∈ Ico 0 t, V s = C ^ 2 →
        2 * ⟪full (x s) - m' s, e s⟫ < (0 : ℝ) := by
      intro s hs hVs
      have hs0 : 0 ≤ s := hs.1
      -- At the boundary `‖e s‖ = C` since `V s = ‖e s‖² = C²` and both nonnegative.
      have hVe : V s = ‖e s‖ ^ 2 := by simp only [hV]; rw [real_inner_self_eq_norm_sq]
      have hnormC : ‖e s‖ = C := by
        have h1 : ‖e s‖ ^ 2 = C ^ 2 := by rw [← hVe, hVs]
        nlinarith [norm_nonneg (e s), hCpos.le, sq_nonneg (‖e s‖ - C), h1]
      have hb := hVbound s hs0
      rw [hVs] at hb
      -- `V' ≤ -2λ·C² + 2δ·C`, and `2δC - 2λC² = -2C(λC - δ) ≤ -2C·(η/λ)·λ`... compute strictly.
      have hcalc : -2 * lam * C ^ 2 + 2 * δ * ‖e s‖ < 0 := by
        rw [hnormC]
        -- `-2λC² + 2δC = 2C(δ - λC) = 2C(δ - λgap0 - (δ+η)) = 2C(-λgap0 - η) < 0`.
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
    -- The fencing inequality `image_le_of_deriv_right_lt_deriv_boundary`.
    have hkey := image_le_of_deriv_right_lt_deriv_boundary
      (f := V) (f' := fun s => 2 * ⟪full (x s) - m' s, e s⟫) (a := 0) (b := t)
      hVcont (fun s _ => (hVd s).hasDerivWithinAt)
      (B := fun _ => C ^ 2) (B' := fun _ => 0) ha (fun _ => hasDerivAt_const _ (C ^ 2))
      (fun s hs hVs => hbound s hs hVs)
    exact hkey (right_mem_Icc.2 ht)
  -- Take `η → 0`: `V t ≤ (gap0 + δ/λ)²`, then square roots give the gap ceiling.
  intro t ht
  have hVlim : V t ≤ (gap0 + δ / lam) ^ 2 := by
    -- The envelope `η ↦ (gap0 + (δ+η)/λ)²` is continuous at `0` with value `(gap0 + δ/λ)²`.
    have hcont : ContinuousWithinAt (fun η : ℝ => (gap0 + (δ + η) / lam) ^ 2) (Ioi 0) 0 := by
      fun_prop
    have htend : Tendsto (fun η : ℝ => (gap0 + (δ + η) / lam) ^ 2) (𝓝[>] 0)
        (𝓝 ((gap0 + δ / lam) ^ 2)) := by
      have h := hcont.tendsto
      simpa [add_zero] using h
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hVη hη t ht
  -- `‖e t‖ = √(V t) ≤ √((gap0+δ/λ)²) = gap0 + δ/λ`.
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

/-- **The horizon-uniform Michaelis–Menten tracking ceiling.** For the regularized complex trajectory
`x : ℝ → E` solving `ẋ = full (x t)` and a substrate path `s` solving the ε-coupled slow law
`ṡ = ε·g(s, z)` under the uniform drift bound `‖g‖ ≤ G`, take the moving reference to be the slaved
complex curve `m t = manifoldMap (s t)`, whose velocity is the `O(ε)` slaved velocity
`mmRegSlavedVelocity` (bounded by `(L / rate)·(ε·G)` for all time via `mmRegSlavedVelocity_certified`).
Under the *coupled transverse one-sided contraction* of the full field toward the moving reference at
the fibre rate `rate`, the transverse gap obeys the time-uniform ceiling
`‖x t - m t‖ ≤ ‖x 0 - m 0‖ + (L / rate)·(ε·G) / rate` for all `t ≥ 0`. The ceiling is `O(ε)` in the
defect and independent of the horizon: the all-time replacement for the compact-time Grönwall bound. -/
theorem mmReg_coupled_tracking_ceiling (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km)
    {L ε G : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hG : 0 ≤ G)
    {g : ℝ → E → ℝ}
    {full : E → E} {x : ℝ → E} {s : ℝ → ℝ} {z : ℝ → E}
    (hx : ∀ t, HasDerivAt x (full (x t)) t)
    (hs : ∀ τ, HasDerivAt s (mmRegSlowDrift ε g (s τ) (z τ)) τ)
    (hcon : ∀ t, 0 ≤ t →
      ⟪full (x t) - full ((mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s t)),
        x t - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s t)⟫
      ≤ -rate * ‖x t - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s t)‖ ^ 2)
    (hdef : ∀ t, 0 ≤ t →
      ‖full ((mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s t))
        - mmRegSlavedVelocity rate hrate Km Vmax hKm (s t)
            (mmRegSlowDrift ε g (s t) (z t))‖ ≤ (L / rate) * (ε * G)) :
    ∀ t, 0 ≤ t →
      ‖x t - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s t)‖
        ≤ ‖x 0 - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s 0)‖
          + (L / rate) * (ε * G) / rate := by
  -- The slaved reference `m t = manifoldMap (s t)` has velocity `mmRegSlavedVelocity` by the chain
  -- rule through the global `C¹` regularity of the manifold map (`mmRegHasDerivAt_slavedCurve`).
  set m : ℝ → E := fun t => (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s t) with hm
  have hmd : ∀ t, HasDerivAt m
      (mmRegSlavedVelocity rate hrate Km Vmax hKm (s t) (mmRegSlowDrift ε g (s t) (z t))) t := by
    intro t
    exact mmRegHasDerivAt_slavedCurve rate hrate Km Vmax hKm
      (s' := fun τ => mmRegSlowDrift ε g (s τ) (z τ)) (hs t)
  have hδ : (0 : ℝ) ≤ (L / rate) * (ε * G) := by
    have : 0 ≤ L / rate := by positivity
    exact mul_nonneg this (mul_nonneg hε hG)
  exact coupled_dissipative_ceiling hrate hδ hx hmd hcon hdef

/-- **The time-uniform certified Michaelis–Menten reduction.** A record bundling the all-time
confinements of `mmCertifiedReduction` with a genuine horizon-uniform tracking field: the exact
regularized complex trajectory `x` stays within a single horizon-independent constant
`C = ‖x 0 - m 0‖ + (L / rate)·(ε·G) / rate` of the slaved manifold reference
`m t = manifoldMap (s t)` for all forward time. Unlike `mmCertifiedReduction`, whose tracking field is
the compact-time Grönwall bound `gronwallBound δ K εf T`, this field is uniform in the horizon `T` and
`O(ε)` in the defect. -/
structure mmCertifiedUniformReduction (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km)
    (hV : 0 ≤ Vmax) (s₀ : ℝ) (ε G L : ℝ) (x : ℝ → E) (s : ℝ → ℝ) : Prop where
  /-- The substrate stays in the compact set `[0, s₀]` for all forward time. -/
  confined : ∀ {t : ℝ}, 0 ≤ t → mmSubstrate Km Vmax hKm hV s₀ t ∈ Icc (0 : ℝ) s₀
  /-- The reduced complex level stays in `[0, mmComplexEquil Km Vmax s₀]` for all forward time. -/
  level_confined : ∀ {t : ℝ}, 0 ≤ t →
    mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t) ∈
      Icc (0 : ℝ) (mmComplexEquil Km Vmax s₀)
  /-- The exact complex trajectory tracks the slaved manifold reference within a single
  horizon-independent, `O(ε)` constant for all forward time. -/
  tracking_uniform : ∀ t, 0 ≤ t →
    ‖x t - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s t)‖
      ≤ ‖x 0 - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s 0)‖
        + (L / rate) * (ε * G) / rate

/-- **Assembly of the time-uniform certified reduction.** Given the regularized complex trajectory
`x` of the full field, a substrate path `s` solving the ε-coupled slow law with drift bound `‖g‖ ≤ G`,
the coupled transverse one-sided contraction at rate `rate`, and the `O(ε)` reference defect bound,
the all-time confinements and the horizon-uniform `O(ε)` tracking ceiling hold simultaneously. -/
theorem mmCertifiedUniformReduction_of (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ)
    (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ} (hs0 : 0 ≤ s₀)
    {L ε G : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hG : 0 ≤ G)
    {g : ℝ → E → ℝ}
    {full : E → E} {x : ℝ → E} {z : ℝ → E}
    (hx : ∀ t, HasDerivAt x (full (x t)) t)
    (hs : ∀ τ, HasDerivAt (mmSubstrate Km Vmax hKm hV s₀)
      (mmRegSlowDrift ε g (mmSubstrate Km Vmax hKm hV s₀ τ) (z τ)) τ)
    (hcon : ∀ t, 0 ≤ t →
      ⟪full (x t) - full ((mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap
            (mmSubstrate Km Vmax hKm hV s₀ t)),
        x t - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap
            (mmSubstrate Km Vmax hKm hV s₀ t)⟫
      ≤ -rate * ‖x t - (mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap
            (mmSubstrate Km Vmax hKm hV s₀ t)‖ ^ 2)
    (hdef : ∀ t, 0 ≤ t →
      ‖full ((mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap
            (mmSubstrate Km Vmax hKm hV s₀ t))
        - mmRegSlavedVelocity rate hrate Km Vmax hKm (mmSubstrate Km Vmax hKm hV s₀ t)
            (mmRegSlowDrift ε g (mmSubstrate Km Vmax hKm hV s₀ t) (z t))‖
      ≤ (L / rate) * (ε * G)) :
    mmCertifiedUniformReduction rate hrate Km Vmax hKm hV s₀ ε G L x
      (mmSubstrate Km Vmax hKm hV s₀) where
  confined ht := mmSubstrate_mem_Icc Km Vmax hKm hV hs0 ht
  level_confined ht := mmReducedComplexLevel_mem_Icc Km Vmax hKm hV hs0 ht
  tracking_uniform :=
    mmReg_coupled_tracking_ceiling rate hrate Km Vmax hKm hL hε hG hx hs hcon hdef

end CRNT.MichaelisMenten

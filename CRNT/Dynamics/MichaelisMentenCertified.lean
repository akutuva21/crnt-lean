import CRNT.Dynamics.MichaelisMentenDepletion
import CRNT.Dynamics.MichaelisMentenSlowDriftSpeed

/-!
# The certified Michaelis–Menten reduction: confinement, an all-time `O(ε)` slaved velocity, and a horizon-uniform tracking constant

This module assembles the certified-reduction companion of the constructed Michaelis–Menten
slow flow: the reduced scalar model `mmSubstrate` together with the qualitative facts that hold
for **all** forward time, packaged for external consumption. It combines the monotone depletion of
`CRNT.Dynamics.MichaelisMentenDepletion`, the derived `O(ε)` slaved velocity of
`CRNT.Dynamics.MichaelisMentenSlowDriftSpeed`, and the compact-time Grönwall tracking of
`CRNT.Dynamics.MichaelisMentenReduced`.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations",
and Tikhonov: on an attracting slow manifold the slaved fast variable tracks the slow flow at speed
`O(ε)`, and the slow variable evolves on the reduced flow. Here the slow variable is the
Michaelis–Menten substrate, which depletes monotonically and is therefore confined to the compact
set `[0, s₀]` for all forward time.

**Forward confinement to a compact set** (`mmSubstrate_mem_Icc`). From a nonnegative initial
substrate `s₀`, the constructed substrate curve `σ := mmSubstrate Km Vmax hKm hV s₀` satisfies
`σ t ∈ [0, s₀]` for every `t ≥ 0`: it is antitone (`mmSubstrate_antitone`) and bounded below by `0`
(`mmSubstrate_nonneg`). This confinement is genuinely all-time — it does not degrade with the
horizon — because it rests on the depletion structure, not on a Grönwall expansion.

**Reduced complex level confinement** (`mmComplexEquil_mono_of_nonneg`, `mmReducedComplexLevel_mem_Icc`).
The Michaelis–Menten complex level `mmComplexEquil Km Vmax s = Vmax·s/(Km+s)` is monotone in `s` on
the physical ray, so the confinement of the substrate lifts to a confinement of the reduced complex
level: `mmComplexEquil Km Vmax (σ t) ∈ [0, mmComplexEquil Km Vmax s₀]` for all `t ≥ 0`. The reduced
complex trajectory `t ↦ mmComplexEquil Km Vmax (σ t) • e0` therefore stays in a fixed compact ball
for all forward time, with bound independent of the horizon.

**All-time `O(ε)` slaved velocity** (`mmRegSlavedVelocity_certified`). The slaved complex velocity
bound `‖mmRegSlavedVelocity …‖ ≤ (L/rate)·(ε·G)` of `mmRegSlavedVelocity_le_of_drift` is pointwise in
time and so holds at **every** `t₀ ≥ 0` with one constant `(L/rate)·G·ε` proportional to `ε` and
independent of the horizon: the slaved fast variable tracks the slow substrate at speed `O(ε)` for
all forward time.

**Horizon-uniform tracking constant** (`mmCertifiedReduction`, `mmCertified_tracking_const_eq`). The
exact-versus-reduced tracking error is the compact-time Grönwall estimate
`michaelisMenten_reduced_qssa_error`: on `[0, T]` the exact trajectory stays within
`gronwallBound δ K εf T` of the reduced complex curve. The certified-reduction record
`mmCertifiedReduction` bundles the reduced model, the all-time confinements, the all-time slaved
velocity, and this tracking estimate into one structure for external use.

**The all-time tracking ceiling, stated precisely.** A tracking constant `C` independent of the
horizon `T` is **not** delivered here, and the depletion structure alone does not supply one: the
tracking error is governed by `gronwallBound δ K εf T`, which for `K > 0` grows like `e^{K·T}` and
diverges as `T → ∞`. Substrate confinement bounds the reduced curve in a fixed compact ball but does
not bound the Grönwall expansion of the gap, because the full enzyme field `full` is only assumed
`K`-Lipschitz, not dissipative toward the slow manifold. A genuinely time-uniform constant requires
a contraction/dissipativity estimate — `full` pulling trajectories back toward the invariant graph
faster than the `K`-Lipschitz expansion pushes them apart, i.e. a uniform negative one-sided
Lipschitz (logarithmic-norm) bound transverse to the manifold — which is absent from the repository.
What the depletion confinement does give is recorded above in full: all-time confinement of both the
substrate and the reduced complex level, and an all-time `O(ε)` slaved velocity.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.MichaelisMentenDepletion`,
`CRNT.Dynamics.MichaelisMentenSlowDriftSpeed`.
-/

open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace CRNT.MichaelisMenten

/-- **Forward confinement of the substrate to a compact set.** From a nonnegative initial substrate
`s₀`, the constructed Michaelis–Menten substrate curve stays in `[0, s₀]` for every `t ≥ 0`: it is
nonnegative (depletion stays above the equilibrium `s = 0`) and antitone (it never increases above
`s₀`). This bound is uniform in time — it rests on the depletion structure, not on a horizon. -/
theorem mmSubstrate_mem_Icc (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ} (hs0 : 0 ≤ s₀)
    {t : ℝ} (ht : 0 ≤ t) : mmSubstrate Km Vmax hKm hV s₀ t ∈ Icc (0 : ℝ) s₀ :=
  ⟨mmSubstrate_nonneg Km Vmax hKm hV hs0 ht, mmSubstrate_le_init Km Vmax hKm hV s₀ ht⟩

/-- **Monotonicity of the Michaelis–Menten complex level on the physical ray.** For `0 < Km`,
`0 ≤ Vmax`, the level `mmComplexEquil Km Vmax s = Vmax·s/(Km+s)` is monotone in `s` on `s ≥ 0`:
larger substrate gives a larger quasi-steady complex level. -/
theorem mmComplexEquil_mono_of_nonneg (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax)
    {s s' : ℝ} (hs : 0 ≤ s) (hss' : s ≤ s') :
    mmComplexEquil Km Vmax s ≤ mmComplexEquil Km Vmax s' := by
  have hs' : 0 ≤ s' := le_trans hs hss'
  have hKs : 0 < Km + s := by linarith
  have hKs' : 0 < Km + s' := by linarith
  rw [mmComplexEquil, mmComplexEquil, div_le_div_iff₀ hKs hKs']
  nlinarith [mul_nonneg hV hs, mul_nonneg hV hs', mul_le_mul_of_nonneg_left hss' hV]

/-- The Michaelis–Menten complex level is nonnegative on the physical ray. -/
theorem mmComplexEquil_nonneg (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ mmComplexEquil Km Vmax s := by
  rw [mmComplexEquil]; positivity

/-- **Forward confinement of the reduced complex level.** Lifting the substrate confinement
`mmSubstrate_mem_Icc` through the monotone level `mmComplexEquil`, the reduced complex level along
the constructed flow stays in `[0, mmComplexEquil Km Vmax s₀]` for every `t ≥ 0`. The reduced complex
trajectory `t ↦ mmComplexEquil Km Vmax (σ t) • e0` is therefore confined to a fixed compact ball for
all forward time, with bound independent of the horizon. -/
theorem mmReducedComplexLevel_mem_Icc (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ}
    (hs0 : 0 ≤ s₀) {t : ℝ} (ht : 0 ≤ t) :
    mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t) ∈
      Icc (0 : ℝ) (mmComplexEquil Km Vmax s₀) := by
  obtain ⟨hlo, hhi⟩ := mmSubstrate_mem_Icc Km Vmax hKm hV hs0 ht
  exact ⟨mmComplexEquil_nonneg Km Vmax hKm hV hlo,
    mmComplexEquil_mono_of_nonneg Km Vmax hKm hV hlo hhi⟩

/-- **All-time `O(ε)` slaved velocity of the certified reduction.** Along the constructed
ε-coupled flow, with the regularized fast field uniformly `L`-Lipschitz in the substrate and the
substrate path solving `ṡ = ε·g(s, z)` under the uniform drift bound `‖g‖ ≤ G`, the slaved complex
velocity is bounded by `(L/rate)·(ε·G)` at **every** time `t₀` — one constant proportional to `ε`,
independent of the horizon. This is `mmRegSlavedVelocity_le_of_drift` exposed as the all-time slaving
estimate of the certified reduction: the slaved fast variable tracks the slow substrate at speed
`O(ε)` for all forward time. -/
theorem mmRegSlavedVelocity_certified (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km)
    {L ε G : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hlip : ∀ s s' z, ‖mmRegFastField rate Km Vmax s z - mmRegFastField rate Km Vmax s' z‖
      ≤ L * dist s s')
    {g : ℝ → E → ℝ} (hg : ∀ a b, ‖g a b‖ ≤ G) {s : ℝ → ℝ} {z : ℝ → E}
    (hs : ∀ τ, HasDerivAt s (mmRegSlowDrift ε g (s τ) (z τ)) τ) :
    ∀ t₀ : ℝ, ‖mmRegSlavedVelocity rate hrate Km Vmax hKm (s t₀)
        (mmRegSlowDrift ε g (s t₀) (z t₀))‖ ≤ (L / rate) * (ε * G) :=
  fun _ => mmRegSlavedVelocity_le_of_drift rate hrate Km Vmax hKm hL hε hG hlip hg hs

/-- **The certified Michaelis–Menten reduction.** A record bundling, for a `K`-Lipschitz full enzyme
field `full` with exact integral curve `γ` over a nonnegative initial substrate `s₀`:

* `reduced` — the constructed reduced scalar Michaelis–Menten flow `σ := mmSubstrate Km Vmax hKm hV s₀`;
* `confined` — the all-time substrate confinement `σ t ∈ [0, s₀]` for `t ≥ 0`;
* `level_confined` — the all-time reduced complex-level confinement
  `mmComplexEquil Km Vmax (σ t) ∈ [0, mmComplexEquil Km Vmax s₀]` for `t ≥ 0`;
* `tracking` — the compact-time Grönwall tracking estimate
  `dist (γ t) (mmComplexEquil Km Vmax (σ t) • e0) ≤ gronwallBound δ K εf T` on `[0, T]`, together with
  its joint vanishing as the initial mismatch `δ` and slaving defect `εf` vanish.

The confinements hold for all forward time; the tracking constant `gronwallBound δ K εf T` is
horizon-dependent (it grows with `T` for `K > 0`), as documented in the module header. -/
structure mmCertifiedReduction (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km)
    (hV : 0 ≤ Vmax) (s₀ : ℝ) (full : E → E) (K : ℝ≥0) (γ : ℝ → E) (T εf δ : ℝ) : Prop where
  /-- The substrate stays in the compact set `[0, s₀]` for all forward time. -/
  confined : ∀ {t : ℝ}, 0 ≤ t → mmSubstrate Km Vmax hKm hV s₀ t ∈ Icc (0 : ℝ) s₀
  /-- The reduced complex level stays in `[0, mmComplexEquil Km Vmax s₀]` for all forward time. -/
  level_confined : ∀ {t : ℝ}, 0 ≤ t →
    mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t) ∈
      Icc (0 : ℝ) (mmComplexEquil Km Vmax s₀)
  /-- On `[0, T]` the exact trajectory tracks the reduced complex curve within the Grönwall bound,
  and that bound vanishes as the initial mismatch and slaving defect jointly vanish. -/
  tracking : (∀ t ∈ Icc 0 T,
      dist (γ t) (mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t) • e0)
        ≤ gronwallBound δ K εf T) ∧
    Tendsto (fun p : ℝ × ℝ => gronwallBound p.1 K p.2 T) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0)

/-- **Assembly of the certified reduction.** Given a `K`-Lipschitz full enzyme field `full` with
exact integral curve `γ`, a nonnegative initial substrate `s₀`, a slaving defect at most `εf` of the
reduced complex curve against its own derivative, and an initial mismatch at most `δ`, the
constructed reduced flow `mmSubstrate Km Vmax hKm hV s₀` certifies the reduction: the substrate and
its reduced complex level are confined for all forward time, and the exact trajectory tracks the
reduced complex curve within the compact-time Grönwall bound on `[0, T]`. -/
theorem mmCertifiedReduction_of (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ)
    (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ} (hs0 : 0 ≤ s₀)
    (full : E → E) {K : ℝ≥0} (hl : LipschitzWith K full)
    {γ : ℝ → E} {T εf δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hεf : 0 ≤ εf)
    (hγd : ∀ t, HasDerivAt γ (full (γ t)) t)
    (hdef : ODE.QssaDefect full
      (fun t => mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t) • e0)
      (fun t => (Vmax * Km / (Km + mmSubstrate Km Vmax hKm hV s₀ t) ^ 2 *
        (-mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t))) • e0) 0 T εf)
    (h0 : dist (γ 0) (mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ 0) • e0) ≤ δ) :
    mmCertifiedReduction rate hrate Km Vmax hKm hV s₀ full K γ T εf δ where
  confined ht := mmSubstrate_mem_Icc Km Vmax hKm hV hs0 ht
  level_confined ht := mmReducedComplexLevel_mem_Icc Km Vmax hKm hV hs0 ht
  tracking := michaelisMenten_reduced_qssa_error rate hrate Km Vmax hKm hV hs0 full hl
    hT hδ hεf hγd hdef h0

/-- **The certified tracking constant is the horizon-dependent Grönwall bound.** The exact-versus-
reduced gap is controlled by `gronwallBound δ K εf T`, the compact-time bound. This makes explicit
that the certified reduction's tracking constant depends on the horizon `T`: an all-time constant is
not delivered, because for `K > 0` the bound grows with `T`. -/
theorem mmCertified_tracking_const_eq (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ)
    (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ} {full : E → E} {K : ℝ≥0} {γ : ℝ → E} {T εf δ : ℝ}
    (cert : mmCertifiedReduction rate hrate Km Vmax hKm hV s₀ full K γ T εf δ) :
    ∀ t ∈ Icc 0 T,
      dist (γ t) (mmComplexEquil Km Vmax (mmSubstrate Km Vmax hKm hV s₀ t) • e0)
        ≤ gronwallBound δ K εf T :=
  cert.tracking.1

end CRNT.MichaelisMenten

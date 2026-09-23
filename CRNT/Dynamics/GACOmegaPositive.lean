import CRNT.Dynamics.GlobalStability

/-!
# A single positive ω-limit point forces global convergence

The sharpest *general* reduction of the global attractor conjecture available from the
relative-entropy Lyapunov stack: for a weakly reversible complex-balanced mass-action semiflow,
if the ω-limit set of a trajectory contains **even one strictly positive point**, then the whole
ω-limit set is the equilibrium `{x*}`. No structural hypothesis (no siphon condition) is needed.

The mechanism. LaSalle pins the relative entropy to a constant `c` on the ω-limit set. A positive
ω-point `p` has a strictly positive forward orbit (still inside ω), along which the relative
entropy is constant; vanishing dissipation then makes `p` complex-balanced, so `p = x*` by
deficiency-zero uniqueness. Hence `x* ∈ ω` and `c = relEntropy x* x* = 0`. Positive-definiteness
of the relative entropy (`relEntropy_eq_zero_iff`) then forces **every** ω-point — boundary points
included — to equal `x*`.

Consequence: global convergence holds for *any* complex-balanced trajectory whose ω-limit set
meets the open positive orthant. The full conjecture is thereby reduced precisely to excluding
ω-limit sets contained entirely in the boundary — which is exactly the persistence question that
remains open in general. This subsumes the no-critical-siphon theorem (there every ω-point is
positive, so in particular one is).

The hypotheses are the standard mass-action semiflow facts a LaSalle construction supplies
(`hgenω` ω-orbits solve the genuine field, `hωc` constancy of the relative entropy on ω, `hωaff`
affine invariance, `hposorbit` positivity of orbits from positive ω-points).

Depends on: `CRNT.Dynamics.GlobalStability`.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **One positive ω-limit point ⇒ `ω = {x*}`.** For a weakly reversible network with a positive
complex-balanced reference `x*` and a positive start `x₀` in its class, suppose the mass-action
semiflow `ϕ` (curves `γ`) satisfies the standard LaSalle facts: ω-orbits solve the genuine field
(`hgenω`), the relative entropy is the constant `c` on the ω-limit set (`hωc`), ω-points are
nonnegative (`hωnn`) and affinely invariant (`hωaff`), and orbits from positive ω-points stay
positive (`hposorbit`). If the ω-limit set contains a single strictly positive point, it is
exactly `{x*}`. -/
theorem omegaLimit_eq_singleton_of_mem_positive
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0compat : N.StoichCompatible x₀ xstar)
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    (hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t))
    (hex : ∃ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p) :
    omegaLimit atTop ϕ {x₀} = {xstar} := by
  obtain ⟨p, hpω, hppos⟩ := hex
  -- forward invariance of the ω-limit set, transported to the curves `γ`
  have hyωt : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      γ y t ∈ omegaLimit atTop ϕ {x₀} := by
    intro y hy t ht
    have := (Flow.isInvariant_omegaLimit atTop ϕ {x₀}
      (fun s => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id) ⟨t, ht⟩) hy
    exact (hϕγ y ⟨t, ht⟩) ▸ this
  have hxstarmem : xstar ∈ N.positiveCompatibilityClass x₀ := ⟨hx0compat, hxs⟩
  -- the positive ω-point equals x*
  have hposyt : ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t) := hposorbit p hpω hppos
  have hyaff : p - x₀ ∈ N.stoichSubspace := hωaff p hpω
  have hyt_eq : ∀ t₀ : ℝ, 0 < t₀ → γ p t₀ = xstar := by
    intro t₀ ht₀
    have hposy : Concentration.Positive (γ p t₀) := hposyt t₀ ht₀.le
    have hydt : HasDerivAt (γ p) (N.massActionVectorField κ (γ p t₀)) t₀ := hgenω p hpω t₀ ht₀.le
    have hconst : ∀ t : ℝ, 0 ≤ t → relEntropy xstar (γ p t) = c :=
      fun t ht => hωc _ (hyωt p hpω t ht)
    have hchain := relEntropy_hasDerivAt hxs hposy (fun s => (hasDerivAt_pi.mp hydt) s)
    have heqc : (fun τ => relEntropy xstar (γ p τ)) =ᶠ[𝓝 t₀] (fun _ => c) := by
      filter_upwards [Ioi_mem_nhds ht₀] with τ hτ; exact hconst τ (le_of_lt hτ)
    have hd0 : HasDerivAt (fun τ => relEntropy xstar (γ p τ)) 0 t₀ :=
      (heqc.hasDerivAt_iff).mpr (hasDerivAt_const t₀ c)
    have hdiss : (∑ s, (Real.log (γ p t₀ s) - Real.log (xstar s))
        * N.massActionVectorField κ (γ p t₀) s) = 0 := hchain.unique hd0
    have hCB : N.IsComplexBalanced κ (γ p t₀) :=
      complexBalanced_of_dissipation_eq_zero N κ hposy hxs hcb hdiss
    have hmem : γ p t₀ ∈ N.positiveCompatibilityClass x₀ := by
      refine ⟨?_, hposy⟩
      show γ p t₀ - x₀ ∈ N.stoichSubspace
      have h1 : γ p t₀ - p ∈ N.stoichSubspace := by
        have hsoly : ∀ τ ∈ Set.Icc (0:ℝ) t₀,
            HasDerivAt (γ p) (N.massActionVectorField κ (γ p τ)) τ :=
          fun τ hτ => hgenω p hpω τ hτ.1
        have := sub_mem_stoichSubspace_of_solution N κ ht₀.le hsoly
        rwa [hγ0] at this
      have heq : γ p t₀ - x₀ = (γ p t₀ - p) + (p - x₀) := by ring
      rw [heq]; exact N.stoichSubspace.add_mem h1 hyaff
    exact N.isComplexBalanced_unique_in_positiveClass hwr κ hmem hxstarmem hCB hcb
  have hcont0 : ContinuousAt (γ p) 0 := (hgenω p hpω 0 le_rfl).continuousAt
  have htend1 : Tendsto (γ p) (𝓝[>] (0:ℝ)) (𝓝 p) := by
    have h1 : Tendsto (γ p) (𝓝[>] (0:ℝ)) (𝓝 (γ p 0)) :=
      hcont0.tendsto.mono_left nhdsWithin_le_nhds
    rwa [hγ0] at h1
  have htend2 : Tendsto (γ p) (𝓝[>] (0:ℝ)) (𝓝 xstar) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact (hyt_eq τ hτ).symm
  have hpx : p = xstar := tendsto_nhds_unique htend1 htend2
  -- hence x* ∈ ω, the LaSalle constant is 0, and every ω-point equals x*
  have hxω : xstar ∈ omegaLimit atTop ϕ {x₀} := hpx ▸ hpω
  have hc0 : c = 0 := by
    have h := hωc xstar hxω
    rw [(relEntropy_eq_zero_iff (fun i => (hxs i).le) hxs).mpr rfl] at h
    exact h.symm
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨hxω, fun w hw => ?_⟩
  have hw0 : relEntropy xstar w = 0 := by rw [hωc w hw, hc0]
  exact (relEntropy_eq_zero_iff (hωnn w hw) hxs).mp hw0

end Network

end CRNT

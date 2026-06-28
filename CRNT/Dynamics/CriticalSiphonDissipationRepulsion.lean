import CRNT.Dynamics.GenuineConfinement

/-!
# Asymptotic facet repulsion from a near-facet dissipation bound

At a critical siphon `{s*}` the mass-action field is tangent to the facet `{x_{s*} = 0}`, so the
finite-time influx bound `m_P(t) ≥ m_P(0)·e^{-ct}` of `SiphonFacetEscape` — which decays — does not
keep the ω-limit set off the facet. The repulsion that does is the integral mechanism of Anderson &
Shiu, _The dynamics of weakly reversible population processes near facets_: the relative-entropy
dissipation is integrable in time, so the orbit can spend only a bounded total time near a facet on
which the dissipation is bounded below, and the field's bounded log-derivative then holds the species
off the facet by a fixed positive margin.

This module formalizes that mechanism. The genuinely analytic content — that the dissipation is at
least a positive constant `ε` whenever `x_{s*}` is within `δ` of the facet — is carried as the
hypothesis `hnear`; it is the sharp Anderson–Shiu near-facet estimate, strictly weaker than the
persistence conclusion and dischargeable from the absence of a steady state near the facet. The
field's linear lower bound `-(G·x_{s*}) ≤ f_{s*}` (`hlog`) is the singleton-siphon influx bound of
`CriticalSiphonNearFacetInflux`/`SiphonFacetEscape`. From those two inputs the repulsion is proven
outright, with no further hypothesis.

## The argument

The relative entropy `V = relEntropy x*` is nonincreasing along the genuine orbit
(`genuineOrbit_relEntropy_le`), with dissipation `D = -V̇ ≥ 0`. Fix a time `t` at which `x_{s*} < δ`
and let `τ` be the last time before `t` at which `x_{s*} ≥ δ`. On `[τ, t]` the orbit stays within `δ`
of the facet, so `D ≥ ε`, hence `V̇ ≤ -ε`; integrating, `ε·(t − τ) ≤ V(γ τ) − V(γ t) ≤ V(γ 0)`, so
the excursion length is bounded: `t − τ ≤ V(γ 0)/ε`. On the same interval `d/dt log x_{s*} ≥ -G`, so
`x_{s*}(t) ≥ x_{s*}(τ)·e^{-G(t−τ)} ≥ δ·e^{-G·V(γ 0)/ε}`. The dissipation budget thus becomes a
**uniform positive floor** under the facet — the asymptotic repulsion the finite-time bound could not
give.

## Contents

* `Network.siphonFacet_floor_of_nearFacet_dissipation` — the genuine orbit through a positive start
  stays a fixed positive distance above the facet of `s*`, given the near-facet dissipation bound and
  the field's linear lower bound.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.GenuineConfinement`.
-/

open scoped BigOperators NNReal Topology
open Set

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Asymptotic facet repulsion from a near-facet dissipation bound.** Let `γ` be the genuine
mass-action orbit through a positive start of a positive complex-balanced class. For a species `s*`
and band width `δ > 0`, suppose:

* `hlog` — the field's linear lower bound `-(G·γ_{s*}) ≤ f_{s*}(γ)` (the singleton-siphon influx
  bound), giving `d/dt log γ_{s*} ≥ -G`;
* `hnear` — the **near-facet dissipation bound**: the relative-entropy dissipation
  `-∑_s (log γ_s − log x*_s)·f_s(γ)` is at least `ε > 0` whenever `γ_{s*} ≤ δ`;
* `hstart` — the start is off the facet, `δ ≤ γ_0 s*`.

Then `γ_{s*}` stays above the fixed positive floor `δ·exp(−G·V(γ 0)/ε)` for all forward time, with
`V = relEntropy x*`. The orbit is repelled from the facet of `s*` by a uniform margin — the
asymptotic statement the finite-time Grönwall bound does not provide. -/
theorem siphonFacet_floor_of_nearFacet_dissipation (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} {sstar : S} {δ ε G : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hG : 0 ≤ G)
    (hpos : ∀ t, 0 ≤ t → (γ t).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hlog : ∀ t, 0 ≤ t → -(G * γ t sstar) ≤ N.massActionVectorField κ (γ t) sstar)
    (hstart : δ ≤ γ 0 sstar)
    (hnear : ∀ t, 0 ≤ t → γ t sstar ≤ δ →
      ε ≤ -(∑ s, (Real.log (γ t s) - Real.log (xstar s)) * N.massActionVectorField κ (γ t) s)) :
    ∀ t, 0 ≤ t → δ * Real.exp (-(G * (relEntropy xstar (γ 0) / ε))) ≤ γ t sstar := by
  intro t ht
  set V0 : ℝ := relEntropy xstar (γ 0) with hV0
  have hV0nn : 0 ≤ V0 := relEntropy_nonneg (hpos 0 le_rfl).nonnegative hxs
  have hγcurve : ContinuousOn γ (Set.Icc 0 t) := fun s hs =>
    (hsol s hs.1).continuousAt.continuousWithinAt
  have hγcont : ContinuousOn (fun s => γ s sstar) (Set.Icc 0 t) := fun s hs =>
    ((hasDerivAt_pi.mp (hsol s hs.1)) sstar).continuousAt.continuousWithinAt
  have hγspos : ∀ s, 0 ≤ s → 0 < γ s sstar := fun s hs => hpos s hs sstar
  -- derivative of the entropy-plus-drift comparison function
  have hφd : ∀ s, 0 ≤ s → HasDerivAt (fun u => relEntropy xstar (γ u) + ε * u)
      ((∑ s', (Real.log (γ s s') - Real.log (xstar s')) *
        N.massActionVectorField κ (γ s) s') + ε) s := by
    intro s hs0
    have h2 : HasDerivAt (fun u : ℝ => ε * u) ε s := by simpa using (hasDerivAt_id s).const_mul ε
    exact (relEntropy_hasDerivAt hxs (hpos s hs0)
      (fun s' => (hasDerivAt_pi.mp (hsol s hs0)) s')).add h2
  -- derivative of the log-plus-drift comparison function
  have hψd : ∀ s, 0 ≤ s → HasDerivAt (fun u => Real.log (γ u sstar) + G * u)
      (N.massActionVectorField κ (γ s) sstar / γ s sstar + G) s := by
    intro s hs0
    have h1 : HasDerivAt (fun u => Real.log (γ u sstar))
        (N.massActionVectorField κ (γ s) sstar / γ s sstar) s :=
      ((hasDerivAt_pi.mp (hsol s hs0)) sstar).log (hγspos s hs0).ne'
    have h2 : HasDerivAt (fun u : ℝ => G * u) G s := by simpa using (hasDerivAt_id s).const_mul G
    exact h1.add h2
  by_cases hge : δ ≤ γ t sstar
  · -- above the band: the floor is `≤ δ ≤ γ_{s*}(t)`
    have hexp : Real.exp (-(G * (V0 / ε))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have : 0 ≤ G * (V0 / ε) := mul_nonneg hG (div_nonneg hV0nn hε.le)
        linarith)
    calc δ * Real.exp (-(G * (V0 / ε))) ≤ δ * 1 := mul_le_mul_of_nonneg_left hexp hδ.le
      _ = δ := mul_one δ
      _ ≤ γ t sstar := hge
  · rw [not_le] at hge
    -- the last exit time `τ` from `{γ_{s*} ≥ δ}` within `[0, t]`
    set A : Set ℝ := Set.Icc 0 t ∩ (fun s => γ s sstar) ⁻¹' Set.Ici δ with hA
    have hAcl : IsClosed A := hγcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hAne : A.Nonempty := ⟨0, ⟨Set.left_mem_Icc.mpr ht, hstart⟩⟩
    have hAbdd : BddAbove A := ⟨t, fun s hs => hs.1.2⟩
    set τ : ℝ := sSup A with hτ
    have hτA : τ ∈ A := hAcl.csSup_mem hAne hAbdd
    have hτ0 : 0 ≤ τ := hτA.1.1
    have hτt : τ ≤ t := hτA.1.2
    have hτδ : δ ≤ γ τ sstar := hτA.2
    have hτlt : τ < t := lt_of_le_of_ne hτt (fun h => absurd (h ▸ hτδ) (not_le.mpr hge))
    have hIccsub : Set.Icc τ t ⊆ Set.Icc 0 t := Set.Icc_subset_Icc hτ0 le_rfl
    -- below the band on `(τ, t]`
    have hbelow : ∀ s, τ < s → s ≤ t → γ s sstar < δ := by
      intro s hsτ hst
      by_contra hh
      rw [not_lt] at hh
      exact absurd (le_csSup hAbdd ⟨⟨le_trans hτ0 hsτ.le, hst⟩, hh⟩) (not_le.mpr hsτ)
    -- ===== relative-entropy descent on `[τ, t]`: `ε·(t − τ) ≤ V0` =====
    have hφanti : AntitoneOn (fun s => relEntropy xstar (γ s) + ε * s) (Set.Icc τ t) := by
      have hcont : ContinuousOn (fun s => relEntropy xstar (γ s) + ε * s) (Set.Icc τ t) :=
        ((relEntropy_continuous hxs).comp_continuousOn (hγcurve.mono hIccsub)).add (by fun_prop)
      refine antitoneOn_of_deriv_nonpos (convex_Icc τ t) hcont ?_ ?_
      · intro s hs
        rw [interior_Icc, mem_Ioo] at hs
        exact (hφd s (le_trans hτ0 hs.1.le)).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc, mem_Ioo] at hs
        rw [(hφd s (le_trans hτ0 hs.1.le)).deriv]
        have hbnd := hnear s (le_trans hτ0 hs.1.le) (le_of_lt (hbelow s hs.1 hs.2.le))
        linarith
    have hVdesc : ε * (t - τ) ≤ V0 := by
      have hle := hφanti (Set.left_mem_Icc.mpr hτlt.le) (Set.right_mem_Icc.mpr hτlt.le) hτlt.le
      have hVtnn : 0 ≤ relEntropy xstar (γ t) := relEntropy_nonneg (hpos t ht).nonnegative hxs
      have hVτ : relEntropy xstar (γ τ) ≤ V0 :=
        N.genuineOrbit_relEntropy_le κ hxs hcb hpos hsol τ hτ0
      nlinarith [hle, hVtnn, hVτ]
    have htmτ : t - τ ≤ V0 / ε := by rw [le_div_iff₀ hε, mul_comm]; exact hVdesc
    -- ===== log-derivative monotonicity on `[τ, t]`: `δ·e^{-G(t-τ)} ≤ γ_{s*}(t)` =====
    have hψmono : MonotoneOn (fun s => Real.log (γ s sstar) + G * s) (Set.Icc τ t) := by
      have hcont : ContinuousOn (fun s => Real.log (γ s sstar) + G * s) (Set.Icc τ t) :=
        ((hγcont.mono hIccsub).log (fun s hs => (hγspos s (le_trans hτ0 hs.1)).ne')).add (by fun_prop)
      refine monotoneOn_of_deriv_nonneg (convex_Icc τ t) hcont ?_ ?_
      · intro s hs
        rw [interior_Icc, mem_Ioo] at hs
        exact (hψd s (le_trans hτ0 hs.1.le)).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc, mem_Ioo] at hs
        have h0s : 0 ≤ s := le_trans hτ0 hs.1.le
        rw [(hψd s h0s).deriv]
        have hdiv : -G ≤ N.massActionVectorField κ (γ s) sstar / γ s sstar := by
          rw [le_div_iff₀ (hγspos s h0s)]; nlinarith [hlog s h0s]
        linarith
    -- assemble
    have hlogle : Real.log (γ τ sstar) - G * (t - τ) ≤ Real.log (γ t sstar) := by
      have hmono := hψmono (Set.left_mem_Icc.mpr hτlt.le) (Set.right_mem_Icc.mpr hτlt.le) hτlt.le
      have hGexp : G * (t - τ) = G * t - G * τ := by ring
      linarith [hmono, hGexp]
    have hkey : γ τ sstar * Real.exp (-(G * (t - τ))) ≤ γ t sstar := by
      have e1 : γ τ sstar * Real.exp (-(G * (t - τ)))
          = Real.exp (Real.log (γ τ sstar) + -(G * (t - τ))) := by
        rw [Real.exp_add, Real.exp_log (hγspos τ hτ0)]
      rw [e1, ← Real.exp_log (hγspos t ht)]
      exact Real.exp_le_exp.mpr (by linarith [hlogle])
    have hexpmono : Real.exp (-(G * (V0 / ε))) ≤ Real.exp (-(G * (t - τ))) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left htmτ hG))
    calc δ * Real.exp (-(G * (V0 / ε)))
        ≤ δ * Real.exp (-(G * (t - τ))) := mul_le_mul_of_nonneg_left hexpmono hδ.le
      _ ≤ γ τ sstar * Real.exp (-(G * (t - τ))) :=
          mul_le_mul_of_nonneg_right hτδ (Real.exp_pos _).le
      _ ≤ γ t sstar := hkey

end Network

end CRNT

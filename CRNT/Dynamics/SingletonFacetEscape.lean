import CRNT.Dynamics.CriticalSiphonNearFacetInflux
import CRNT.Dynamics.Persistence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Singleton critical-siphon facet escape: the Grönwall lower bound

Anderson & Shiu, _The dynamics of weakly reversible population processes near facets_ (2010),
close the singleton critical-siphon facet `SiphonFace {s*}` by integrating the near-facet influx
estimate. `CRNT.Dynamics.CriticalSiphonNearFacetInflux` records that estimate in differential form:
on a region bounded above by `M`, the `s*`-component of the mass-action field obeys
`-(c · x s*) ≤ ẋ_{s*}` for the explicit network constant `c`. This module integrates that
inequality into the exponential lower bound it implies.

The integration is a one-sided Grönwall step. For a scalar curve `f` on `[0, ∞)` with
`-(c · f t) ≤ f' t`, the product `g t = f t · exp (c t)` has `0 ≤ g' t`, so `g` is monotone:
`g 0 ≤ g t`, i.e. `f 0 ≤ f t · exp (c t)`, hence `f 0 · exp (-(c t)) ≤ f t`. Applied to the
`s*`-coordinate of a mass-action trajectory confined to the box `[0, M]` with a strictly positive
start, this gives

`γ 0 s* · exp (-(c t)) ≤ γ t s*`,

so `0 < γ t s*` for every `t ≥ 0`: from a positive start the trajectory never reaches the facet
in finite time. The singleton critical-siphon facet `SiphonFace {s*}` carries no point of such a
trajectory — the linear influx keeps the vanishing coordinate strictly positive along the whole
forward orbit.

Depends on: `CRNT.Dynamics.CriticalSiphonNearFacetInflux`,
`CRNT.Dynamics.Persistence`.
-/

open Set
open scoped BigOperators

namespace CRNT

/-- **One-sided Grönwall lower bound.** A scalar curve `f` differentiable on `[0, ∞)` whose
forward derivative satisfies the linear lower bound `-(c · f t) ≤ f' t` stays above its
exponentially-decaying initial value: `f 0 · exp (-(c t)) ≤ f t` for every `t ≥ 0`.

The auxiliary curve `g t = f t · exp (c t)` has derivative `(f' t + c · f t) · exp (c t) ≥ 0`, so
`g` is monotone on `[0, ∞)`; `g 0 ≤ g t` is `f 0 ≤ f t · exp (c t)`, and dividing by the positive
`exp (c t)` gives the claim. -/
theorem exp_lower_bound_of_deriv_ge {f f' : ℝ → ℝ} {c : ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t)
    (hge : ∀ t, 0 ≤ t → -(c * f t) ≤ f' t) {t : ℝ} (ht : 0 ≤ t) :
    f 0 * Real.exp (-(c * t)) ≤ f t := by
  -- the auxiliary product `g s = f s * exp (c s)`
  set g : ℝ → ℝ := fun s => f s * Real.exp (c * s) with hg
  -- its derivative on `[0, ∞)`, and the sign of that derivative
  have hgderiv : ∀ s ∈ Icc (0 : ℝ) t,
      HasDerivAt g ((f' s + c * f s) * Real.exp (c * s)) s := by
    intro s hs
    have hcs : HasDerivAt (fun u : ℝ => c * u) c s := by
      simpa using (hasDerivAt_id s).const_mul c
    have hexp : HasDerivAt (fun u => Real.exp (c * u)) (Real.exp (c * s) * c) s :=
      (Real.hasDerivAt_exp (c * s)).comp s hcs
    have hprod := (hf s hs.1).mul hexp
    have heq : (f' s + c * f s) * Real.exp (c * s)
        = f' s * Real.exp (c * s) + f s * (Real.exp (c * s) * c) := by ring
    rw [heq]
    exact hprod
  have hgderiv_nonneg : ∀ s ∈ Ico (0 : ℝ) t, 0 ≤ (f' s + c * f s) * Real.exp (c * s) := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have h1 : 0 ≤ f' s + c * f s := by
      have := hge s hs0; linarith
    exact mul_nonneg h1 (Real.exp_pos _).le
  -- monotonicity of `g` on `[0, t]` from the nonnegative derivative
  have hgcont : ContinuousOn g (Icc 0 t) := fun s hs => (hgderiv s hs).continuousAt.continuousWithinAt
  have hmono : g 0 ≤ g t := by
    rcases eq_or_lt_of_le ht with hzero | hpos
    · simp [hg, ← hzero]
    · have key : MonotoneOn g (Icc 0 t) := by
        refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
          (f' := fun s => (f' s + c * f s) * Real.exp (c * s)) hgcont
          (fun s hs => ?_) (fun s hs => ?_)
        · rw [interior_Icc] at hs
          exact (hgderiv s ⟨hs.1.le, hs.2.le⟩).hasDerivWithinAt
        · rw [interior_Icc] at hs
          exact hgderiv_nonneg s ⟨hs.1.le, hs.2⟩
      exact key (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
  -- unfold `g 0 ≤ g t` to `f 0 ≤ f t * exp (c t)` and divide
  have hg0 : g 0 = f 0 := by simp [hg]
  have hgt : g t = f t * Real.exp (c * t) := by simp [hg]
  rw [hg0, hgt] at hmono
  -- `f 0 * exp(-(c t)) ≤ f t` since `exp(-(c t)) * exp(c t) = 1`
  have hexp_pos : 0 < Real.exp (-(c * t)) := Real.exp_pos _
  have : f 0 * Real.exp (-(c * t)) ≤ (f t * Real.exp (c * t)) * Real.exp (-(c * t)) :=
    mul_le_mul_of_nonneg_right hmono hexp_pos.le
  calc
    f 0 * Real.exp (-(c * t)) ≤ (f t * Real.exp (c * t)) * Real.exp (-(c * t)) := this
    _ = f t * (Real.exp (c * t) * Real.exp (-(c * t))) := by ring
    _ = f t := by rw [← Real.exp_add]; simp

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The singleton near-facet influx constant
`c = ∑_r κ_r · (source_r s*) · (max M 1)^(D_r - 1)` of
`massActionVectorField_singleton_facet_ge`. -/
noncomputable def singletonFacetInfluxConst (N : Network S) (κ : N.RateConstants)
    (sstar : S) (M : ℝ) : ℝ :=
  ∑ r : N.R, κ.k r * ((N.reaction r).source sstar : ℝ)
    * (max M 1) ^ ((∑ s, (N.reaction r).source s) - 1)

/-- **Exponential lower bound on the vanishing coordinate (singleton critical siphon).** Let
`{s*}` be a siphon. Along a mass-action integral curve `γ` (`hγd`) confined to the box `[0, M]`
(`hγnn`, `hγM`) for all forward time, the `s*`-coordinate stays above its exponentially-decaying
initial value:

`γ 0 s* · exp (-(c · t)) ≤ γ t s*`  for every `t ≥ 0`,

with `c = singletonFacetInfluxConst`. This is the Anderson & Shiu near-facet influx estimate
`massActionVectorField_singleton_facet_ge` integrated by the one-sided Grönwall step
`exp_lower_bound_of_deriv_ge`. -/
theorem massActionTrajectory_singleton_coord_ge (N : Network S) (κ : N.RateConstants)
    {sstar : S} (hsiph : N.IsSiphon ({sstar} : Finset S)) {M : ℝ}
    {γ : ℝ → Concentration S}
    (hγd : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hγnn : ∀ t, 0 ≤ t → (γ t).Nonnegative) (hγM : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    γ 0 sstar * Real.exp (-(N.singletonFacetInfluxConst κ sstar M * t)) ≤ γ t sstar := by
  set c : ℝ := N.singletonFacetInfluxConst κ sstar M with hc
  -- the scalar `s*`-coordinate curve and its derivative
  set f : ℝ → ℝ := fun s => γ s sstar with hf
  have hfd : ∀ s, 0 ≤ s → HasDerivAt f (N.massActionVectorField κ (γ s) sstar) s := by
    intro s hs
    exact (hasDerivAt_pi.mp (hγd s hs)) sstar
  -- the influx bound rewritten as the differential inequality `-(c * f s) ≤ f' s`
  have hge : ∀ s, 0 ≤ s → -(c * f s) ≤ N.massActionVectorField κ (γ s) sstar := by
    intro s hs
    have := N.massActionVectorField_singleton_facet_ge κ hsiph (hγnn s hs) (hγM s hs)
    simpa [hc, hf, singletonFacetInfluxConst, mul_comm] using this
  exact exp_lower_bound_of_deriv_ge hfd hge ht

/-- **A positive confined trajectory never reaches the singleton siphon facet.** Under the
hypotheses of `massActionTrajectory_singleton_coord_ge`, if the start `γ 0` is strictly positive in
the `s*`-coordinate then `0 < γ t s*` for every `t ≥ 0`: the vanishing coordinate stays strictly
positive along the whole forward orbit. -/
theorem massActionTrajectory_singleton_coord_pos (N : Network S) (κ : N.RateConstants)
    {sstar : S} (hsiph : N.IsSiphon ({sstar} : Finset S)) {M : ℝ}
    {γ : ℝ → Concentration S}
    (hγd : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hγnn : ∀ t, 0 ≤ t → (γ t).Nonnegative) (hγM : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M)
    (hpos0 : 0 < γ 0 sstar) {t : ℝ} (ht : 0 ≤ t) :
    0 < γ t sstar := by
  have hlb := N.massActionTrajectory_singleton_coord_ge κ hsiph hγd hγnn hγM ht
  have hexp : 0 < Real.exp (-(N.singletonFacetInfluxConst κ sstar M * t)) := Real.exp_pos _
  exact lt_of_lt_of_le (mul_pos hpos0 hexp) hlb

/-- **The singleton critical-siphon facet carries no point of a positive confined trajectory.**
Under the hypotheses of `massActionTrajectory_singleton_coord_pos`, the trajectory never enters
`SiphonFace {s*}`: for every `t ≥ 0`, `γ t ∉ N.SiphonFace {s*}`. This is the Anderson & Shiu
facet-escape conclusion for the singleton case — the integrated linear influx keeps the vanishing
coordinate strictly positive, so the orbit stays off the codimension-1 facet for all forward
time. -/
theorem massActionTrajectory_notMem_singletonFacet (N : Network S) (κ : N.RateConstants)
    {sstar : S} (hsiph : N.IsSiphon ({sstar} : Finset S)) {M : ℝ}
    {γ : ℝ → Concentration S}
    (hγd : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hγnn : ∀ t, 0 ≤ t → (γ t).Nonnegative) (hγM : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M)
    (hpos0 : 0 < γ 0 sstar) {t : ℝ} (ht : 0 ≤ t) :
    γ t ∉ N.SiphonFace ({sstar} : Finset S) := by
  intro hmem
  have hzero : γ t sstar = 0 := hmem.2 sstar (Finset.mem_singleton_self sstar)
  have hpos := N.massActionTrajectory_singleton_coord_pos κ hsiph hγd hγnn hγM hpos0 ht
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

end Network

end CRNT

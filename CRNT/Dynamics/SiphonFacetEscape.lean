import CRNT.Dynamics.SingletonFacetEscape

/-!
# Critical-siphon facet escape: the aggregate Grönwall lower bound

Anderson & Shiu, _The dynamics of weakly reversible population processes near facets_ (2010),
close a critical-siphon facet `SiphonFace P` by integrating a near-facet influx estimate. The
singleton case `P = {s*}` is handled in `CRNT.Dynamics.SingletonFacetEscape`. This module lifts
that to a general species set `P` through the aggregate `P`-mass `∑_{s∈P} x s`.

Every reaction `r` contributes to the `P`-mass derivative the amount
`rate_r · (∑_{s∈P} reactionVector_r s)`, and `reactionVector_r s = target_r s − source_r s ≥
−source_r s`, so each per-species contribution `rate_r · reactionVector_r s` is bounded below by
`−(rate_r · source_r s)`. Where `source_r s ≠ 0` the source monomial carries a factor of the
vanishing coordinate `x s`, bounded by `x s · B^(D_r − 1)` on a box `[0, B]`; where `source_r s = 0`
the contribution is already nonnegative. Both cases give, on a region bounded above by `M` with
`B = max M 1` and `D_r = ∑_s source_r s` the source degree,

`−(κ_r · source_r s · B^(D_r − 1) · x s) ≤ rate_r · reactionVector_r s`.

Summing over `s ∈ P` and over reactions, and using `source_r s ≤ D_r`, bounds the aggregate
`P`-mass derivative below by `−(c · ∑_{s∈P} x s)` for the explicit network constant
`c = ∑_r κ_r · D_r · B^(D_r − 1)`:

`−(c · ∑_{s∈P} x s) ≤ ∑_{s∈P} N.massActionVectorField κ x s`.

Feeding this into the one-sided Grönwall step `exp_lower_bound_of_deriv_ge` gives, along a
mass-action trajectory confined to the box `[0, M]`,

`(∑_{s∈P} γ 0 s) · exp (−(c · t)) ≤ ∑_{s∈P} γ t s`  for every `t ≥ 0`,

so from a positive-`P`-mass start the aggregate `P`-mass stays strictly positive: the trajectory
never reaches the full siphon face `SiphonFace P` in finite time. This is the Anderson & Shiu
finite-time facet-escape conclusion for a general critical siphon. The ω-limit no-facet-point
conclusion needs the second-order subtangent estimate and is out of scope here.

Depends on: `CRNT.Dynamics.SingletonFacetEscape`.
-/

open Set
open scoped BigOperators

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Per-species near-facet influx bound.** On a region where every concentration is bounded above
by `M`, a single reaction's contribution to the `s`-component of the mass-action field is bounded
below by `−(κ_r · source_r s · B^(D_r − 1) · x s)` with `B = max M 1` and `D_r = ∑_s source_r s` the
source degree of `r`. A reaction not consuming `s` contributes nonnegatively; a reaction consuming
`s` carries a factor of the vanishing coordinate `x s` in its source monomial, bounded by
`x s · B^(D_r − 1)`. This is the singleton per-reaction bound without the siphon hypothesis, holding
for every species `s`. -/
theorem massActionRate_mul_reactionVector_coord_ge (N : Network S) (κ : N.RateConstants)
    (s : S) (r : N.R) {x : Concentration S} (hxnn : x.Nonnegative) {M : ℝ} (hxM : ∀ t, x t ≤ M) :
    -(κ.k r * ((N.reaction r).source s : ℝ)
        * (max M 1) ^ ((∑ t, (N.reaction r).source t) - 1) * x s)
      ≤ N.massActionRate κ r x * N.reactionVector r s := by
  set B : ℝ := max M 1 with hB
  have hB1 : (1 : ℝ) ≤ B := le_max_right _ _
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hxB : ∀ t, x t ≤ B := fun t => le_trans (hxM t) (le_max_left _ _)
  by_cases hsrc : (N.reaction r).source s = 0
  · -- `r` does not consume `s`: the reaction-vector entry at `s` is `target s − 0 ≥ 0`, so the
    -- contribution is nonnegative and the bound, whose left side is `0`, holds.
    have hvecnn : 0 ≤ N.reactionVector r s := by
      rw [reactionVector_apply, hsrc]
      simp [Nat.cast_nonneg]
    have hrate_nn : 0 ≤ N.massActionRate κ r x := N.massActionRate_nonneg κ r hxnn
    rw [hsrc]; push_cast
    simpa using mul_nonneg hrate_nn hvecnn
  · -- `r` consumes `s`: the source monomial carries a factor `x s`, bounded by `x s · B^(D−1)`.
    have hmonle : (N.reaction r).source.massActionMonomial x
        ≤ x s * B ^ ((∑ t, (N.reaction r).source t) - 1) :=
      massActionMonomial_le_coord_mul_pow hxnn hB1 hxB hsrc
    have hvecge : -((N.reaction r).source s : ℝ) ≤ N.reactionVector r s := by
      rw [reactionVector_apply]
      have : (0 : ℝ) ≤ ((N.reaction r).target s : ℝ) := Nat.cast_nonneg _
      linarith
    have hsrcnn : 0 ≤ ((N.reaction r).source s : ℝ) := Nat.cast_nonneg _
    have hrate_eq : N.massActionRate κ r x
        = κ.k r * (N.reaction r).source.massActionMonomial x := rfl
    have hrate_nn : 0 ≤ N.massActionRate κ r x := N.massActionRate_nonneg κ r hxnn
    calc
      -(κ.k r * ((N.reaction r).source s : ℝ)
          * B ^ ((∑ t, (N.reaction r).source t) - 1) * x s)
          ≤ -(κ.k r * ((N.reaction r).source s : ℝ)
              * (N.reaction r).source.massActionMonomial x) := by
            rw [neg_le_neg_iff]
            have hcoef : 0 ≤ κ.k r * ((N.reaction r).source s : ℝ) :=
              mul_nonneg (κ.positive r).le hsrcnn
            calc
              κ.k r * ((N.reaction r).source s : ℝ)
                  * (N.reaction r).source.massActionMonomial x
                  ≤ κ.k r * ((N.reaction r).source s : ℝ)
                      * (x s * B ^ ((∑ t, (N.reaction r).source t) - 1)) :=
                    mul_le_mul_of_nonneg_left hmonle hcoef
              _ = κ.k r * ((N.reaction r).source s : ℝ)
                      * B ^ ((∑ t, (N.reaction r).source t) - 1) * x s := by ring
      _ = N.massActionRate κ r x * (-((N.reaction r).source s : ℝ)) := by
            rw [hrate_eq]; ring
      _ ≤ N.massActionRate κ r x * N.reactionVector r s :=
            mul_le_mul_of_nonneg_left hvecge hrate_nn

/-- The aggregate near-facet influx constant
`c = ∑_r κ_r · D_r · (max M 1)^(D_r − 1)` with `D_r = ∑_s source_r s` the source degree of `r`.
This bounds the rate at which a confined trajectory can deplete the total `P`-mass `∑_{s∈P} x s`. -/
noncomputable def siphonFacetInfluxConst (N : Network S) (κ : N.RateConstants) (M : ℝ) : ℝ :=
  ∑ r : N.R, κ.k r * ((∑ s, (N.reaction r).source s : ℕ) : ℝ)
    * (max M 1) ^ ((∑ s, (N.reaction r).source s) - 1)

/-- **Aggregate near-facet influx bound (general critical siphon).** Let `P` be a species set.
On a region where every concentration is bounded above by `M`, the aggregate `P`-mass component of
the mass-action field is bounded below by `−(c · ∑_{s∈P} x s)` for the explicit network constant
`c = siphonFacetInfluxConst`:

`−(c · ∑_{s∈P} x s) ≤ ∑_{s∈P} N.massActionVectorField κ x s`.

Each reaction's contribution to each `P`-coordinate is bounded below by the per-species influx bound
`massActionRate_mul_reactionVector_coord_ge`; summing over `s ∈ P` and using `source_r s ≤ D_r`
collects the per-reaction constants into `c`. This is the codimension-`|P|` linear influx lower
bound of Anderson & Shiu: the net depletion of the `P`-mass is at most a multiple of the `P`-mass
itself, i.e. of the distance to the facet `SiphonFace P`. -/
theorem massActionVectorField_siphon_facet_ge (N : Network S) (κ : N.RateConstants)
    (P : Finset S) {x : Concentration S} (hxnn : x.Nonnegative) {M : ℝ} (hxM : ∀ s, x s ≤ M) :
    -(N.siphonFacetInfluxConst κ M * ∑ s ∈ P, x s)
      ≤ ∑ s ∈ P, N.massActionVectorField κ x s := by
  set B : ℝ := max M 1 with hB
  have hB1 : (1 : ℝ) ≤ B := le_max_right _ _
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  -- expand the field as a double sum and swap the order of summation
  have hexpand : ∑ s ∈ P, N.massActionVectorField κ x s
      = ∑ r : N.R, ∑ s ∈ P, N.massActionRate κ r x * N.reactionVector r s := by
    simp only [massActionVectorField_apply]
    rw [Finset.sum_comm]
  rw [hexpand]
  -- bound the RHS double sum below, reaction by reaction
  rw [siphonFacetInfluxConst, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum (fun r _ => ?_)
  -- per reaction: `-(κ_r · D_r · B^(D_r−1) · ∑_{s∈P} x s) ≤ ∑_{s∈P} rate_r · vec_r s`
  set D : ℕ := ∑ s, (N.reaction r).source s with hD
  have hpowB : 0 ≤ B ^ (D - 1) := pow_nonneg hB0 _
  have hcoef : 0 ≤ κ.k r * B ^ (D - 1) := mul_nonneg (κ.positive r).le hpowB
  -- lower bound on the reaction's `P`-mass contribution by the sum of per-species bounds
  have hper : ∑ s ∈ P, -(κ.k r * ((N.reaction r).source s : ℝ) * B ^ (D - 1) * x s)
      ≤ ∑ s ∈ P, N.massActionRate κ r x * N.reactionVector r s := by
    refine Finset.sum_le_sum (fun s _ => ?_)
    exact N.massActionRate_mul_reactionVector_coord_ge κ s r hxnn hxM
  refine le_trans ?_ hper
  -- collect: `κ_r · D_r · B^(D−1) · ∑_{s∈P} x s ≥ ∑_{s∈P} κ_r · source_r s · B^(D−1) · x s`
  rw [Finset.sum_neg_distrib]
  refine neg_le_neg ?_
  calc
    ∑ s ∈ P, κ.k r * ((N.reaction r).source s : ℝ) * B ^ (D - 1) * x s
        = κ.k r * B ^ (D - 1) * ∑ s ∈ P, ((N.reaction r).source s : ℝ) * x s := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun s _ => by ring)
    _ ≤ κ.k r * B ^ (D - 1) * ∑ s ∈ P, (D : ℝ) * x s := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef
          refine Finset.sum_le_sum (fun s _ => ?_)
          refine mul_le_mul_of_nonneg_right ?_ (hxnn s)
          -- `source_r s ≤ D_r = ∑_t source_r t`
          have : (N.reaction r).source s ≤ D :=
            Finset.single_le_sum (f := fun t => (N.reaction r).source t)
              (fun t _ => Nat.zero_le _) (Finset.mem_univ s)
          exact_mod_cast this
    _ = κ.k r * (D : ℝ) * B ^ (D - 1) * ∑ s ∈ P, x s := by
          rw [← Finset.mul_sum]; ring

/-- **Exponential lower bound on the aggregate `P`-mass (general critical siphon).** Along a
mass-action integral curve `γ` (`hγd`) confined to the box `[0, M]` (`hγnn`, `hγM`) for all forward
time, the aggregate `P`-mass `∑_{s∈P} γ t s` stays above its exponentially-decaying initial value:

`(∑_{s∈P} γ 0 s) · exp (−(c · t)) ≤ ∑_{s∈P} γ t s`  for every `t ≥ 0`,

with `c = siphonFacetInfluxConst`. This integrates the aggregate near-facet influx estimate
`massActionVectorField_siphon_facet_ge` by the one-sided Grönwall step
`exp_lower_bound_of_deriv_ge`. -/
theorem massActionTrajectory_siphon_mass_ge (N : Network S) (κ : N.RateConstants)
    (P : Finset S) {M : ℝ} {γ : ℝ → Concentration S}
    (hγd : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hγnn : ∀ t, 0 ≤ t → (γ t).Nonnegative) (hγM : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ s ∈ P, γ 0 s) * Real.exp (-(N.siphonFacetInfluxConst κ M * t)) ≤ ∑ s ∈ P, γ t s := by
  set c : ℝ := N.siphonFacetInfluxConst κ M with hc
  -- the scalar aggregate `P`-mass curve and its derivative
  set f : ℝ → ℝ := fun u => ∑ s ∈ P, γ u s with hf
  have hfd : ∀ u, 0 ≤ u → HasDerivAt f (∑ s ∈ P, N.massActionVectorField κ (γ u) s) u := by
    intro u hu
    have hcoord : ∀ s, HasDerivAt (fun v => γ v s) (N.massActionVectorField κ (γ u) s) u :=
      fun s => (hasDerivAt_pi.mp (hγd u hu)) s
    have hsum : HasDerivAt (fun v => ∑ s ∈ P, γ v s)
        (∑ s ∈ P, N.massActionVectorField κ (γ u) s) u :=
      HasDerivAt.fun_sum (fun s _ => hcoord s)
    exact hsum
  -- the influx bound rewritten as the differential inequality `-(c * f u) ≤ f' u`
  have hge : ∀ u, 0 ≤ u →
      -(c * f u) ≤ ∑ s ∈ P, N.massActionVectorField κ (γ u) s := by
    intro u hu
    exact N.massActionVectorField_siphon_facet_ge κ P (hγnn u hu) (hγM u hu)
  exact exp_lower_bound_of_deriv_ge hfd hge ht

/-- **A positive-`P`-mass confined trajectory keeps positive `P`-mass.** Under the hypotheses of
`massActionTrajectory_siphon_mass_ge`, if the start `γ 0` has strictly positive aggregate `P`-mass
then `0 < ∑_{s∈P} γ t s` for every `t ≥ 0`. -/
theorem massActionTrajectory_siphon_mass_pos (N : Network S) (κ : N.RateConstants)
    (P : Finset S) {M : ℝ} {γ : ℝ → Concentration S}
    (hγd : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hγnn : ∀ t, 0 ≤ t → (γ t).Nonnegative) (hγM : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M)
    (hpos0 : 0 < ∑ s ∈ P, γ 0 s) {t : ℝ} (ht : 0 ≤ t) :
    0 < ∑ s ∈ P, γ t s := by
  have hlb := N.massActionTrajectory_siphon_mass_ge κ P hγd hγnn hγM ht
  have hexp : 0 < Real.exp (-(N.siphonFacetInfluxConst κ M * t)) := Real.exp_pos _
  exact lt_of_lt_of_le (mul_pos hpos0 hexp) hlb

/-- **The critical-siphon facet carries no point of a positive-`P`-mass confined trajectory.**
Under the hypotheses of `massActionTrajectory_siphon_mass_pos`, the trajectory never enters
`SiphonFace P`: for every `t ≥ 0`, `γ t ∉ N.SiphonFace P`. This is the Anderson & Shiu finite-time
facet-escape conclusion for a general critical siphon — the integrated aggregate influx keeps the
total `P`-mass strictly positive, so the orbit stays off the facet `SiphonFace P` for all forward
time. -/
theorem massActionTrajectory_notMem_siphonFacet (N : Network S) (κ : N.RateConstants)
    (P : Finset S) {M : ℝ} {γ : ℝ → Concentration S}
    (hγd : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hγnn : ∀ t, 0 ≤ t → (γ t).Nonnegative) (hγM : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M)
    (hpos0 : 0 < ∑ s ∈ P, γ 0 s) {t : ℝ} (ht : 0 ≤ t) :
    γ t ∉ N.SiphonFace P := by
  intro hmem
  have hzero : ∀ s ∈ P, γ t s = 0 := hmem.2
  have hsum0 : ∑ s ∈ P, γ t s = 0 := Finset.sum_eq_zero hzero
  have hpos := N.massActionTrajectory_siphon_mass_pos κ P hγd hγnn hγM hpos0 ht
  rw [hsum0] at hpos
  exact lt_irrefl 0 hpos

end Network

end CRNT

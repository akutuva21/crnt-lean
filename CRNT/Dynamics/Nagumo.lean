import CRNT.Kinetics.Concentration
import CRNT.Dynamics.MassActionField
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Monotone

/-!
# Nagumo subtangentiality: closed forward-invariance of the nonnegative orthant

A dissipative Nagumo invariance theorem for closed coordinate halfspaces, over the proven
mean-value / exponential-modulus machinery.

* `nagumo_halfspace_scalar`: a differentiable scalar `g` with `0 ≤ g 0` and the one-sided
  inward inequality `-L·g ≤ g'` wherever `g < 0` stays nonnegative on `[0, ∞)`. The
  argument is a first-crossing-from-below: at the supremum `t₀` of the times in `[0, T]`
  where `g ≥ 0`, the function `z = g·exp(L·)` is nondecreasing on `[t₀, T]` (its derivative
  is `(g' + L·g)·exp ≥ 0`, since `g < 0` there activates the inward inequality), so
  `0 = z t₀ ≤ z T = g T·exp(L T) < 0`, a contradiction.
* `forwardInvariant_nonnegOrthant`: the vector bridge. A curve `γ` into the nonnegative
  orthant whose components satisfy the scalar hypotheses coordinatewise keeps every
  coordinate nonnegative for all forward time. This is the closed-orthant companion to the
  open-orthant strict-positivity lemma `pos_of_forward_deriv_ge`.
* `Network.massAction_forwardInvariant_nonneg`: the CRN specialization. The inward
  condition on the boundary faces `{x_s = 0}` is discharged unconditionally by
  `massActionVectorField_nonneg_of_zero`; the caller supplies the per-coordinate
  dissipativity bound that holds along the (already-constructed, locally bounded) curve.

The general Nagumo viability theorem over an arbitrary closed convex set, with a Bouligand
subtangent-cone hypothesis, is out of reach here: Mathlib has no tangent-cone-to-a-set
apparatus. The dissipative coordinate-halfspace form is the checkable form the persistence
and confinement arguments consume.

Depends on: `CRNT.Kinetics.Concentration`,
`CRNT.Dynamics.MassActionField`, `Mathlib.Analysis.Calculus.Deriv.MeanValue`,
`Mathlib.Analysis.SpecialFunctions.ExpDeriv`, `Mathlib.Topology.Order.Monotone`.
-/

namespace CRNT

open scoped BigOperators

/-- **Scalar dissipative Nagumo invariance for a closed halfspace.** If a differentiable
`g` has `0 ≤ g 0` and satisfies the one-sided inward inequality `-L·g ≤ g'` wherever
`g < 0`, then `g` stays nonnegative on `[0, ∞)`.

This is the closed-set companion to `pos_of_forward_deriv_ge`: that lemma yields strict
positivity from strict positivity and so cannot certify invariance of the *closed*
nonnegative halfspace; this lemma does. The proof is a first-crossing-from-below argument
on `z = g·exp(L·)`. -/
theorem nagumo_halfspace_scalar {g : ℝ → ℝ} {L : ℝ}
    (hd : ∀ t, HasDerivAt g (deriv g t) t)
    (hin : ∀ t, g t < 0 → -L * g t ≤ deriv g t) (h0 : 0 ≤ g 0) :
    ∀ t, 0 ≤ t → 0 ≤ g t := by
  have hcont : Continuous g := by
    rw [continuous_iff_continuousAt]; exact fun t => (hd t).continuousAt
  intro T hT
  by_contra hgT
  rw [not_le] at hgT
  -- the closed, nonempty, bounded-above set of "good" times in `[0, T]`
  set A : Set ℝ := Set.Icc 0 T ∩ {t | 0 ≤ g t} with hA
  have hAne : A.Nonempty := ⟨0, ⟨le_refl 0, hT⟩, h0⟩
  have hAcl : IsClosed A := isClosed_Icc.inter (isClosed_le continuous_const hcont)
  have hAbdd : BddAbove A := ⟨T, fun t ht => ht.1.2⟩
  set t₀ := sSup A with ht₀def
  have ht₀A : t₀ ∈ A := hAcl.csSup_mem hAne hAbdd
  have ht₀0 : 0 ≤ t₀ := ht₀A.1.1
  have ht₀T : t₀ ≤ T := ht₀A.1.2
  have hgt₀ : 0 ≤ g t₀ := ht₀A.2
  -- `t₀ < T`, since `g T < 0`
  have ht₀ltT : t₀ < T := lt_of_le_of_ne ht₀T (fun h => absurd (h ▸ hgt₀) (not_le.mpr hgT))
  -- after `t₀` (up to `T`) the function is strictly negative
  have hneg_after : ∀ t, t₀ < t → t ≤ T → g t < 0 := by
    intro t htlt htle
    by_contra hle
    rw [not_lt] at hle
    exact absurd (le_csSup hAbdd ⟨⟨le_trans ht₀0 htlt.le, htle⟩, hle⟩) (not_le.mpr htlt)
  -- `g t₀ = 0`: continuity forces the supremum value to be a zero
  have hgt₀eq : g t₀ = 0 := by
    refine le_antisymm ?_ hgt₀
    have htend : Filter.Tendsto g (nhdsWithin t₀ (Set.Ioi t₀)) (nhds (g t₀)) :=
      (hcont.continuousAt).continuousWithinAt.tendsto
    refine le_of_tendsto htend ?_
    -- eventually within `𝓝[>] t₀`, points lie in `(t₀, T)` where `g < 0`
    have hlt : ∀ᶠ t in nhdsWithin t₀ (Set.Ioi t₀), t < T :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀ltT)
    have hself : ∀ᶠ t in nhdsWithin t₀ (Set.Ioi t₀), t₀ < t :=
      eventually_mem_nhdsWithin.mono fun t ht => ht
    filter_upwards [hlt, hself] with t htT ht₀t
    exact (hneg_after t ht₀t htT.le).le
  -- `z = g · exp (L ·)` is nondecreasing on `[t₀, T]`
  set z : ℝ → ℝ := fun t => g t * Real.exp (L * t) with hz
  have hzd : ∀ t, HasDerivAt z ((deriv g t + L * g t) * Real.exp (L * t)) t := by
    intro t
    have he : HasDerivAt (fun s => Real.exp (L * s)) (Real.exp (L * t) * L) t := by
      simpa using (((hasDerivAt_id t).const_mul L)).exp
    have hm := (hd t).mul he
    have hval : deriv g t * Real.exp (L * t) + g t * (Real.exp (L * t) * L)
        = (deriv g t + L * g t) * Real.exp (L * t) := by ring
    rw [hz, ← hval]; exact hm
  have hzcont : Continuous z :=
    hcont.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hmono : MonotoneOn z (Set.Icc t₀ T) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc t₀ T) hzcont.continuousOn
      (fun t _ => (hzd t).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
    rw [interior_Icc, Set.mem_Ioo] at ht
    rw [(hzd t).deriv]
    have hgt : g t < 0 := hneg_after t ht.1 ht.2.le
    exact mul_nonneg (by linarith [hin t hgt]) (Real.exp_pos _).le
  have hz01 : z t₀ ≤ z T := hmono ⟨le_refl t₀, ht₀T⟩ ⟨ht₀T, le_refl T⟩ ht₀T
  -- `z t₀ = 0` but `z T < 0`, contradiction
  have hzt₀ : z t₀ = 0 := by rw [hz]; simp [hgt₀eq]
  have hzT : z T < 0 := mul_neg_of_neg_of_pos hgT (Real.exp_pos _)
  rw [hzt₀] at hz01
  exact absurd (lt_of_le_of_lt hz01 hzT) (lt_irrefl 0)

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Subtangency on the boundary faces.** The field `F` points into the nonnegative
orthant on each coordinate face `{x_s = 0}`: at any nonnegative concentration with a
vanishing coordinate `s`, the `s`-component of `F` is nonnegative. -/
def InwardOnBoundary (F : Concentration S → Concentration S) : Prop :=
  ∀ x : Concentration S, x.Nonnegative → ∀ s, x s = 0 → 0 ≤ F x s

omit [DecidableEq S] [Fintype S] in
/-- **Closed forward-invariance of the nonnegative orthant (vector form).** A curve `γ`
into the orthant, with derivative `F (γ t)` coordinatewise, an inward field on the boundary
faces (`InwardOnBoundary`), a per-coordinate dissipativity bound `-L·γ ≤ F(γ)` wherever the
coordinate is negative, and a nonnegative start, stays nonnegative for all forward time.

The dissipativity hypothesis `hLip` is phrased disjunctively: at each `t, s` either the
inward inequality holds or the coordinate is already nonnegative; this is exactly what the
scalar lemma activates only when the coordinate is strictly negative. -/
theorem forwardInvariant_nonnegOrthant {F : Concentration S → Concentration S}
    {γ : ℝ → Concentration S} {L : ℝ}
    (hderiv : ∀ t s, HasDerivAt (fun u => γ u s) (F (γ t) s) t)
    (hLip : ∀ t s, -L * (γ t s) ≤ F (γ t) s ∨ 0 ≤ γ t s)
    (h0 : (γ 0).Nonnegative) :
    ∀ t, 0 ≤ t → (γ t).Nonnegative := by
  intro t ht s
  -- specialize the scalar Nagumo lemma to the `s`-coordinate `g = fun u => γ u s`
  set g : ℝ → ℝ := fun u => γ u s with hg
  have hgderivval : ∀ u, deriv g u = F (γ u) s := fun u => (hderiv u s).deriv
  have hgderiv : ∀ u, HasDerivAt g (deriv g u) u := by
    intro u
    rw [hgderivval u]; exact hderiv u s
  have hgin : ∀ u, g u < 0 → -L * g u ≤ deriv g u := by
    intro u hu
    rw [hgderivval u]
    rcases hLip u s with hbound | hnonneg
    · exact hbound
    · exact absurd hnonneg (not_le.mpr hu)
  exact nagumo_halfspace_scalar hgderiv hgin (h0 s) t ht

/-- **Closed forward-invariance of the nonnegative orthant for mass action.** An integral
curve of the mass-action vector field starting in the nonnegative orthant, and satisfying a
per-coordinate dissipativity bound, stays in the orthant for all forward time. The
boundary-face inward condition is discharged automatically by
`massActionVectorField_nonneg_of_zero`. -/
theorem massAction_forwardInvariant_nonneg (N : Network S) (κ : RateConstants N)
    {γ : ℝ → Concentration S} {L : ℝ}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hLip : ∀ t s, -L * (γ t s) ≤ N.massActionVectorField κ (γ t) s ∨ 0 ≤ γ t s)
    (h0 : (γ 0).Nonnegative) :
    ∀ t, 0 ≤ t → (γ t).Nonnegative := by
  -- extract the per-coordinate derivative from the `Pi`-valued one
  have hderiv' : ∀ t s, HasDerivAt (fun u => γ u s) (N.massActionVectorField κ (γ t) s) t := by
    intro t s
    exact (hasDerivAt_pi.mp (hderiv t)) s
  exact forwardInvariant_nonnegOrthant hderiv' hLip h0

/-- The mass-action vector field is inward on every boundary face of the orthant. -/
theorem massActionVectorField_inwardOnBoundary (N : Network S) (κ : RateConstants N) :
    InwardOnBoundary (N.massActionVectorField κ) :=
  fun _ hx _ hs => N.massActionVectorField_nonneg_of_zero κ hx hs

end Network

end CRNT

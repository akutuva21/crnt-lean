import CRNT.Theorems.DeficiencyZero.AsymptoticStability
import CRNT.Dynamics.SublevelInvariant

/-!
# Confinement of the genuine mass-action orbit

The relative-entropy stability development of `Theorems/DeficiencyZero` confines the orbit of the
**cutoff** field `Γ' = f(clampBox B Γ)`: `orbit_pos` keeps it strictly positive and
`orbit_relEntropy_le` keeps its relative entropy below its initial value. Those statements carry the
clamp in the derivative, which decouples the upper box bound from positivity but ties the conclusions
to the cutoff dynamics. This module proves the same two facts for the **genuine** field
`Γ' = f(Γ)`, with no clamp, for any solution given on `[0, ∞)`.

The positivity argument no longer has the clamp to supply the box bound, so it is recovered from
compactness: on each compact interval `[0, T]` a genuine solution is continuous, hence bounded, which
furnishes the box on which the field's linear lower bound `f_s(x) ≥ −L·x_s`
(`exists_field_lower_bound`) holds. A first-crossing argument (`ge_mul_exp_of_forward_deriv_ge`) then
rules out any coordinate reaching zero, exactly as in `orbit_pos`. With positivity in hand, the
relative-entropy descent is the Lyapunov chain rule against the complex-balanced dissipation
inequality `dissipation_nonpos` (Horn & Jackson, *General mass action kinetics*, 1972).

These are the genuine-field forms of the persistence inputs that `gac_of_genuine_persistence` and
`gac_of_confinement` consume as hypotheses about arbitrary integral curves.

## Contents

* `Network.genuineOrbit_pos` — a genuine mass-action solution from a strictly positive start stays
  strictly positive for all forward time.
* `Network.genuineOrbit_relEntropy_le` — the relative entropy of a genuine positive orbit never
  exceeds its initial value.

Depends on:
`CRNT.Theorems.DeficiencyZero.AsymptoticStability`, `CRNT.Dynamics.SublevelInvariant`.
-/

open scoped BigOperators Topology
open Set

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Positivity of the genuine orbit.** A solution of the genuine mass-action dynamics
`Γ' = f(Γ)` (no clamp) starting strictly positive stays strictly positive on `[0, ∞)`.

Without the clamp, the box bound that the field's linear lower bound `f_s(x) ≥ −L·x_s` needs is
supplied by compactness: on each `[0, T]` the continuous orbit is bounded by some `Bb`, giving the
lower bound `L` from `exists_field_lower_bound`. A first-crossing argument then forces each
coordinate to satisfy `Γ_s(t) ≥ Γ_s(0)·e^{−L t} > 0` up to the first zero, contradicting any
crossing. -/
theorem genuineOrbit_pos (N : Network S) (κ : N.RateConstants)
    {Γ : ℝ → Concentration S} (hΓ0 : (Γ 0).Positive)
    (hΓd : ∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) :
    ∀ t, 0 ≤ t → (Γ t).Positive := by
  intro T hT
  show ∀ s, 0 < Γ T s
  by_contra hcon
  simp only [not_forall, not_lt] at hcon
  obtain ⟨s₀, hs₀⟩ := hcon
  -- Continuity of the orbit on the compact interval `[0, T]`.
  have hcontOn : ContinuousOn Γ (Set.Icc 0 T) :=
    fun t ht => (hΓd t ht.1).continuousAt.continuousWithinAt
  have hcs : ∀ s, ContinuousOn (fun t => Γ t s) (Set.Icc 0 T) :=
    fun s => (continuous_apply s).comp_continuousOn hcontOn
  -- A uniform box bound on `[0, T]` from compactness.
  obtain ⟨Bb, hBb⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontOn
  have hBbound : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ s, Γ t s ≤ Bb := by
    intro t ht s
    calc Γ t s ≤ |Γ t s| := le_abs_self _
      _ = ‖Γ t s‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖Γ t‖ := norm_le_pi_norm (Γ t) s
      _ ≤ Bb := hBb t ht
  -- The field's linear lower bound on that box.
  obtain ⟨L, _hLnn, hbound⟩ := N.exists_field_lower_bound κ Bb
  -- First crossing of zero, restricted to `[0, T]`.
  set A : Set ℝ := {t | (0 ≤ t ∧ t ≤ T) ∧ ∃ s, Γ t s ≤ 0} with hA
  have hAne : A.Nonempty := ⟨T, ⟨hT, le_refl T⟩, s₀, hs₀⟩
  have hAcl : IsClosed A := by
    have heq : A = ⋃ s : S, (Set.Icc 0 T ∩ (fun t => Γ t s) ⁻¹' Set.Iic 0) := by
      ext t
      simp only [hA, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage,
        Set.mem_Iic, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨h0, hT'⟩, s, hs⟩; exact ⟨s, ⟨h0, hT'⟩, hs⟩
      · rintro ⟨s, ⟨h0, hT'⟩, hs⟩; exact ⟨⟨h0, hT'⟩, s, hs⟩
    rw [heq]
    exact isClosed_iUnion_of_finite fun s =>
      (hcs s).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  set t₁ := sInf A with ht₁def
  have ht₁A : t₁ ∈ A := hAcl.csInf_mem hAne hAbdd
  have ht₁0 : 0 ≤ t₁ := ht₁A.1.1
  have ht₁leT : t₁ ≤ T := ht₁A.1.2
  obtain ⟨s₁, hs₁⟩ := ht₁A.2
  have hbefore : ∀ t, 0 ≤ t → t ≤ T → t < t₁ → (Γ t).Positive := by
    intro t ht0 htT htlt s
    by_contra hle
    rw [not_lt] at hle
    exact absurd (csInf_le hAbdd ⟨⟨ht0, htT⟩, s, hle⟩) (not_le.mpr htlt)
  rcases eq_or_lt_of_le ht₁0 with ht₁eq | ht₁pos
  · rw [← ht₁eq] at hs₁
    exact absurd (hΓ0 s₁) (not_lt.mpr hs₁)
  · -- The exponential lower bound on `[0, t₁)`, then passed to the limit at `t₁`.
    have key : ∀ t ∈ Set.Ico 0 t₁, Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁ := by
      intro t ht
      refine ge_mul_exp_of_forward_deriv_ge ht.1
        (fun τ hτ => (hasDerivAt_pi.mp (hΓd τ hτ.1)) s₁) ?_
      intro τ hτ
      have hτlt : τ < t₁ := lt_of_le_of_lt hτ.2 ht.2
      have hτT : τ ≤ T := le_of_lt (lt_of_lt_of_le hτlt ht₁leT)
      have hpos := hbefore τ hτ.1 hτT hτlt
      exact hbound (Γ τ) hpos.nonnegative (hBbound τ ⟨hτ.1, hτT⟩) s₁
    have hclosed :
        IsClosed (Set.Icc 0 T ∩ {t | Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁}) := by
      have hcd : ContinuousOn
          (fun τ => Γ τ s₁ - Γ 0 s₁ * Real.exp (-(L * τ))) (Set.Icc 0 T) :=
        (hcs s₁).sub ((continuous_const.mul
          (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg))).continuousOn)
      have heq2 : Set.Icc 0 T ∩ {t | Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁}
          = Set.Icc 0 T ∩ (fun τ => Γ τ s₁ - Γ 0 s₁ * Real.exp (-(L * τ))) ⁻¹' Set.Ici 0 := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici, sub_nonneg]
      rw [heq2]
      exact hcd.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hsub : Set.Ico 0 t₁ ⊆
        Set.Icc 0 T ∩ {t | Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁} := by
      intro τ hτ
      exact ⟨⟨hτ.1, le_of_lt (lt_of_lt_of_le hτ.2 ht₁leT)⟩, key τ hτ⟩
    have ht₁mem : t₁ ∈ Set.Icc 0 T ∩ {t | Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁} :=
      hclosed.closure_subset_iff.mpr hsub
        (by rw [closure_Ico (ne_of_lt ht₁pos)]; exact ⟨ht₁0, le_refl t₁⟩)
    exact absurd (lt_of_lt_of_le (mul_pos (hΓ0 s₁) (Real.exp_pos _)) ht₁mem.2) (not_lt.mpr hs₁)

/-- **Relative-entropy descent along the genuine orbit.** For a positive complex-balanced reference
`x*`, the relative entropy `relEntropy x* ·` of a genuine positive mass-action orbit never exceeds
its initial value. This is the Lyapunov chain rule (`relEntropy_hasDerivAt`) against the
complex-balanced dissipation inequality (`dissipation_nonpos`), routed through the sublevel-descent
wrapper `sublevel_invariant_along_curve`. -/
theorem genuineOrbit_relEntropy_le (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {Γ : ℝ → Concentration S}
    (hpos : ∀ t, 0 ≤ t → (Γ t).Positive)
    (hΓd : ∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) :
    ∀ t, 0 ≤ t → relEntropy xstar (Γ t) ≤ relEntropy xstar (Γ 0) := by
  intro t ht
  refine sublevel_invariant_along_curve (g := fun x => relEntropy xstar x) (γ := Γ)
    (D := fun τ => ∑ s, (Real.log (Γ τ s) - Real.log (xstar s))
      * N.massActionVectorField κ (Γ τ) s) ?_ ?_ ?_ ht
  · intro τ hτ
    exact (relEntropy_continuous hxs).continuousAt.comp_continuousWithinAt
      ((hΓd τ (Set.mem_Ici.mp hτ)).continuousAt.continuousWithinAt)
  · intro τ hτ
    exact relEntropy_hasDerivAt hxs (hpos τ hτ.le) (fun s => (hasDerivAt_pi.mp (hΓd τ hτ.le)) s)
  · intro τ hτ
    exact dissipation_nonpos N κ (hpos τ hτ.le) hxs hcb

/-- **Uniqueness of the genuine orbit inside a box.** Two genuine mass-action solutions from the same
start that both stay inside the box `{y | ∀ s, |y s| ≤ B}` agree for all forward time. Inside the
box the genuine field coincides with the globally Lipschitz cutoff `f ∘ clampBox B`
(`exists_cutoff`), so it is Lipschitz there; Mathlib's interval ODE-uniqueness
(`ODE_solution_unique_of_mem_Icc_right`) then identifies the two solutions on each `[0, T]`. -/
theorem genuineOrbit_unique_of_box (N : Network S) (κ : N.RateConstants) {B : ℝ} (hB : 0 ≤ B)
    {Γ₁ Γ₂ : ℝ → Concentration S}
    (hΓ₁d : ∀ t, 0 ≤ t → HasDerivAt Γ₁ (N.massActionVectorField κ (Γ₁ t)) t)
    (hΓ₂d : ∀ t, 0 ≤ t → HasDerivAt Γ₂ (N.massActionVectorField κ (Γ₂ t)) t)
    (hbox₁ : ∀ t, 0 ≤ t → ∀ s, |Γ₁ t s| ≤ B) (hbox₂ : ∀ t, 0 ≤ t → ∀ s, |Γ₂ t s| ≤ B)
    (h0 : Γ₁ 0 = Γ₂ 0) :
    ∀ t, 0 ≤ t → Γ₁ t = Γ₂ t := by
  obtain ⟨Klip, _M, hlip, _⟩ := N.exists_cutoff κ hB
  set box : Set (Concentration S) := {y | ∀ s, |y s| ≤ B} with hboxdef
  have hLOW : LipschitzOnWith Klip (N.massActionVectorField κ) box := by
    intro x hx y hy
    have hcx : clampBox B x = x := clampBox_eq_of_mem (fun s => hx s)
    have hcy : clampBox B y = y := clampBox_eq_of_mem (fun s => hy s)
    have hl := hlip x y
    simp only [Function.comp_apply, hcx, hcy] at hl
    exact hl
  intro T hT
  have key : Set.EqOn Γ₁ Γ₂ (Set.Icc 0 T) :=
    ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => N.massActionVectorField κ) (s := fun _ => box)
      (fun t _ => hLOW)
      (fun t ht => (hΓ₁d t ht.1).continuousAt.continuousWithinAt)
      (fun t ht => (hΓ₁d t ht.1).hasDerivWithinAt)
      (fun t ht => hbox₁ t ht.1)
      (fun t ht => (hΓ₂d t ht.1).continuousAt.continuousWithinAt)
      (fun t ht => (hΓ₂d t ht.1).hasDerivWithinAt)
      (fun t ht => hbox₂ t ht.1)
      h0
  exact key (Set.right_mem_Icc.mpr hT)

/-- **Uniqueness of the genuine orbit from a positive start.** For a positive complex-balanced
reference `x*`, any two genuine mass-action solutions from the same positive start agree for all
forward time. Each is confined by the relative entropy to the box past the coercivity bound of its
initial sublevel set (`genuineOrbit_pos`, `genuineOrbit_relEntropy_le`, `relEntropy_coord_le`), where
`genuineOrbit_unique_of_box` identifies them. This is the genuine-field counterpart of the
clamped-field uniqueness `ODE.exists_flow` rests on. -/
theorem genuineOrbit_unique (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {x₀ : Concentration S} (hx0 : x₀.Positive)
    {Γ₁ Γ₂ : ℝ → Concentration S} (hΓ₁0 : Γ₁ 0 = x₀) (hΓ₂0 : Γ₂ 0 = x₀)
    (hΓ₁d : ∀ t, 0 ≤ t → HasDerivAt Γ₁ (N.massActionVectorField κ (Γ₁ t)) t)
    (hΓ₂d : ∀ t, 0 ≤ t → HasDerivAt Γ₂ (N.massActionVectorField κ (Γ₂ t)) t) :
    ∀ t, 0 ≤ t → Γ₁ t = Γ₂ t := by
  set C₀ := relEntropy xstar x₀ with hC₀
  set B : ℝ := 1 + |C₀| + ∑ s, Real.exp 2 * xstar s with hBdef
  have hsumnn : 0 ≤ ∑ s, Real.exp 2 * xstar s :=
    Finset.sum_nonneg fun s _ => (mul_pos (Real.exp_pos 2) (hxs s)).le
  have hBnn : 0 ≤ B := by rw [hBdef]; have := abs_nonneg C₀; linarith
  have hBbig : ∀ s, max (Real.exp 2 * xstar s) C₀ < B := by
    intro s
    have hsum : Real.exp 2 * xstar s ≤ ∑ s', Real.exp 2 * xstar s' :=
      Finset.single_le_sum (fun s' _ => (mul_pos (Real.exp_pos 2) (hxs s')).le) (Finset.mem_univ s)
    rw [max_lt_iff, hBdef]
    exact ⟨by linarith [abs_nonneg C₀], by linarith [le_abs_self C₀]⟩
  have hboxOf : ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      ∀ t, 0 ≤ t → ∀ s, |Γ t s| ≤ B := by
    intro Γ hΓ0 hΓd t ht s
    have hΓ0p : (Γ 0).Positive := by rw [hΓ0]; exact hx0
    have hp := N.genuineOrbit_pos κ hΓ0p hΓd t ht
    have hre : relEntropy xstar (Γ t) ≤ C₀ := by
      have := N.genuineOrbit_relEntropy_le κ hxs hcb (N.genuineOrbit_pos κ hΓ0p hΓd) hΓd t ht
      rwa [hΓ0] at this
    rw [abs_le]
    exact ⟨by linarith [hp s], le_of_lt (lt_of_le_of_lt
      (relEntropy_coord_le hxs hp.nonnegative hre s) (hBbig s))⟩
  exact N.genuineOrbit_unique_of_box κ hBnn hΓ₁d hΓ₂d
    (hboxOf Γ₁ hΓ₁0 hΓ₁d) (hboxOf Γ₂ hΓ₂0 hΓ₂d) (by rw [hΓ₁0, hΓ₂0])

end Network

end CRNT

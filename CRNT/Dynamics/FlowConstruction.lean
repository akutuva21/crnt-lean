import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Dynamics.Flow

/-!
# Toward the flow of an autonomous Lipschitz vector field

This module collects the general dynamical-systems lemmas needed to package the solutions
of an autonomous ODE `ẋ = f(x)` (with `f` Lipschitz) into a continuous `Flow`. It is
CRN-free, Mathlib-style.

**Continuous dependence and uniqueness.** From Grönwall's inequality
(`dist_le_of_trajectories_ODE`): two global solutions of the same autonomous Lipschitz ODE
diverge at most exponentially (`dist_le_of_isIntegralCurve`), and hence a solution is
determined on `[0, ∞)` by its initial value (`eqOn_Ici_of_isIntegralCurve`).

**Global existence** (`exists_isIntegralCurve`). A *bounded* Lipschitz autonomous field
admits a global integral curve through every point. The key observation: because the field
is globally bounded, the Picard–Lindelöf ball radius can be taken arbitrarily large, so a
solution exists on `[-T, T]` for every `T` (no continuation-limit argument needed); these
interval solutions are then glued by uniqueness. This is the analytic step that the Mathlib
ODE library otherwise lacks.

**The forward semiflow** (`exists_flow`). Assembling the above, a bounded Lipschitz
autonomous field generates a `Flow ℝ≥0 E` whose orbits are its solutions — existence
supplies the orbits, uniqueness the semigroup law, and continuous dependence the joint
continuity. For mass action this applies after a cutoff to a bounded field together with the
`relEntropy` confinement (forward-invariant compact sublevel sets within a class).

-/

open Filter
open scoped NNReal Topology

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Continuous dependence on initial conditions.** Two global solutions of an autonomous
Lipschitz ODE `ẋ = f(x)` diverge at most exponentially in forward time. -/
theorem dist_le_of_isIntegralCurve {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f)
    {γ₁ γ₂ : ℝ → E} (h₁ : ∀ t, HasDerivAt γ₁ (f (γ₁ t)) t)
    (h₂ : ∀ t, HasDerivAt γ₂ (f (γ₂ t)) t) {t : ℝ} (ht : 0 ≤ t) :
    dist (γ₁ t) (γ₂ t) ≤ dist (γ₁ 0) (γ₂ 0) * Real.exp (K * t) := by
  have hc₁ : ContinuousOn γ₁ (Set.Icc 0 t) :=
    (continuous_iff_continuousAt.2 fun s => (h₁ s).continuousAt).continuousOn
  have hc₂ : ContinuousOn γ₂ (Set.Icc 0 t) :=
    (continuous_iff_continuousAt.2 fun s => (h₂ s).continuousAt).continuousOn
  have h := dist_le_of_trajectories_ODE (v := fun _ => f) (a := 0) (b := t)
    (δ := dist (γ₁ 0) (γ₂ 0)) (fun _ => hf) hc₁
    (fun s _ => (h₁ s).hasDerivWithinAt) hc₂ (fun s _ => (h₂ s).hasDerivWithinAt) le_rfl
    t (Set.right_mem_Icc.2 ht)
  simpa using h

/-- **Uniqueness on `[0, ∞)`.** A global solution of an autonomous Lipschitz ODE is
determined on forward time by its initial value. -/
theorem eqOn_Ici_of_isIntegralCurve {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f)
    {γ₁ γ₂ : ℝ → E} (h₁ : ∀ t, HasDerivAt γ₁ (f (γ₁ t)) t)
    (h₂ : ∀ t, HasDerivAt γ₂ (f (γ₂ t)) t) (h0 : γ₁ 0 = γ₂ 0) :
    Set.EqOn γ₁ γ₂ (Set.Ici 0) := by
  intro t ht
  have hle := dist_le_of_isIntegralCurve hf h₁ h₂ ht
  rw [h0, dist_self, zero_mul] at hle
  exact dist_le_zero.1 hle

variable [CompleteSpace E]

/-- A bounded Lipschitz autonomous field admits a solution on any symmetric open interval.
Because the field is globally bounded, the Picard–Lindelöf ball radius can be taken as large
as needed, so the interval of validity is unrestricted. -/
theorem exists_solution_Ioo {f : E → E} {K M : ℝ≥0} (hl : LipschitzWith K f)
    (hb : ∀ x, ‖f x‖ ≤ M) (x₀ : E) (R : ℝ≥0) :
    ∃ α : ℝ → E, α 0 = x₀ ∧ ∀ t ∈ Set.Ioo (-(R : ℝ)) (R : ℝ), HasDerivAt α (f (α t)) t := by
  have ht₀ : (0 : ℝ) ∈ Set.Icc (-(R : ℝ)) (R : ℝ) :=
    ⟨neg_nonpos_of_nonneg R.coe_nonneg, R.coe_nonneg⟩
  have hpl : IsPicardLindelof (fun _ => f) (⟨0, ht₀⟩ : Set.Icc (-(R : ℝ)) (R : ℝ)) x₀
      (M * R) 0 M K :=
    IsPicardLindelof.of_time_independent (fun x _ => hb x) hl.lipschitzOnWith (by
      simp only [NNReal.coe_mul, NNReal.coe_zero, sub_zero, sub_neg_eq_add, zero_add, max_self]
      simp)
  obtain ⟨α, hα0, hα⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt (Metric.mem_closedBall_self le_rfl)
  refine ⟨α, hα0, fun t ht => ?_⟩
  exact (hα t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- **Global existence for a bounded Lipschitz autonomous field.** Every starting point
admits a (two-sided) global solution of `ẋ = f(x)`. The interval solutions of
`exists_solution_Ioo` are glued by uniqueness. -/
theorem exists_isIntegralCurve {f : E → E} {K M : ℝ≥0} (hl : LipschitzWith K f)
    (hb : ∀ x, ‖f x‖ ≤ M) (x₀ : E) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t : ℝ, HasDerivAt γ (f (γ t)) t := by
  -- a solution on each interval `(-(n+1), n+1)`
  have hsol : ∀ n : ℕ, ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Set.Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1), HasDerivAt α (f (α t)) t := by
    intro n
    have hcast : (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have := exists_solution_Ioo hl hb x₀ ((n : ℝ≥0) + 1)
    rwa [hcast] at this
  choose α hα0 hα using hsol
  -- the solutions agree wherever both are defined
  have huniq : ∀ (a b : ℕ) (t : ℝ), t ∈ Set.Ioo (-((a : ℝ) + 1)) ((a : ℝ) + 1) →
      t ∈ Set.Ioo (-((b : ℝ) + 1)) ((b : ℝ) + 1) → α a t = α b t := by
    intro a b t hta htb
    have hca : min (a : ℝ) (b : ℝ) ≤ (a : ℝ) := min_le_left _ _
    have hcb : min (a : ℝ) (b : ℝ) ≤ (b : ℝ) := min_le_right _ _
    have hmn : (0 : ℝ) ≤ min (a : ℝ) (b : ℝ) := le_min (Nat.cast_nonneg a) (Nat.cast_nonneg b)
    have ht0 : (0 : ℝ) ∈ Set.Ioo (-(min (a : ℝ) (b : ℝ) + 1)) (min (a : ℝ) (b : ℝ) + 1) :=
      ⟨by linarith, by linarith⟩
    have hsa : Set.Ioo (-(min (a : ℝ) (b : ℝ) + 1)) (min (a : ℝ) (b : ℝ) + 1)
        ⊆ Set.Ioo (-((a : ℝ) + 1)) ((a : ℝ) + 1) :=
      Set.Ioo_subset_Ioo (by linarith) (by linarith)
    have hsb : Set.Ioo (-(min (a : ℝ) (b : ℝ) + 1)) (min (a : ℝ) (b : ℝ) + 1)
        ⊆ Set.Ioo (-((b : ℝ) + 1)) ((b : ℝ) + 1) :=
      Set.Ioo_subset_Ioo (by linarith) (by linarith)
    have htc : t ∈ Set.Ioo (-(min (a : ℝ) (b : ℝ) + 1)) (min (a : ℝ) (b : ℝ) + 1) := by
      rcases min_choice (a : ℝ) (b : ℝ) with h | h
      · rw [h]; exact hta
      · rw [h]; exact htb
    exact ODE_solution_unique_of_mem_Ioo (v := fun _ => f) (s := fun _ => Set.univ)
      (fun _ _ => hl.lipschitzOnWith) ht0
      (fun s hs => ⟨hα a s (hsa hs), Set.mem_univ _⟩)
      (fun s hs => ⟨hα b s (hsb hs), Set.mem_univ _⟩) (by rw [hα0 a, hα0 b]) htc
  -- glue: pick, at each `t`, the solution on a large enough interval
  have hmem : ∀ t : ℝ, t ∈ Set.Ioo (-((⌊|t|⌋₊ : ℝ) + 1)) ((⌊|t|⌋₊ : ℝ) + 1) := fun t =>
    Set.mem_Ioo.mpr (abs_lt.mp (Nat.lt_floor_add_one |t|))
  refine ⟨fun t => α ⌊|t|⌋₊ t, hα0 ⌊|(0 : ℝ)|⌋₊, fun t => ?_⟩
  have hEq : (fun s => α ⌊|s|⌋₊ s) =ᶠ[nhds t] α ⌊|t|⌋₊ :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds (hmem t))
      (fun s hs => huniq ⌊|s|⌋₊ ⌊|t|⌋₊ s (hmem s) hs)
  exact (hα ⌊|t|⌋₊ t (hmem t)).congr_of_eventuallyEq hEq

open scoped Topology in
/-- **The flow of a bounded Lipschitz autonomous field.** Such a field generates a forward
semiflow `Flow ℝ≥0 E` whose orbits are its solutions. Existence supplies the orbits,
uniqueness the semigroup law, and continuous dependence the joint continuity. -/
theorem exists_flow {f : E → E} {K M : ℝ≥0} (hl : LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ M) :
    ∃ (ϕ : Flow ℝ≥0 E) (γ : E → ℝ → E),
      (∀ x, γ x 0 = x) ∧ (∀ x t, HasDerivAt (γ x) (f (γ x t)) t) ∧
      (∀ x (t : ℝ≥0), ϕ t x = γ x (t : ℝ)) := by
  choose γ hγ0 hγd using fun x => exists_isIntegralCurve hl hb x
  have hγc : ∀ x, Continuous (γ x) :=
    fun x => continuous_iff_continuousAt.2 fun t => (hγd x t).continuousAt
  -- semigroup law from uniqueness of global solutions
  have hsemi : ∀ (x : E) (a b : ℝ), γ x (a + b) = γ (γ x b) a := by
    intro x a b
    have h1 : ∀ s : ℝ, HasDerivAt (fun u => γ x (u + b)) (f (γ x (s + b))) s := fun s => by
      have hg : HasDerivAt (fun u : ℝ => u + b) 1 s := by simpa using (hasDerivAt_id s).add_const b
      simpa [Function.comp_def] using (hγd x (s + b)).scomp s hg
    have heq : (fun s => γ x (s + b)) = γ (γ x b) :=
      ODE_solution_unique_univ (v := fun _ => f) (s := fun _ => Set.univ)
        (fun _ => hl.lipschitzOnWith) (fun s => ⟨h1 s, Set.mem_univ _⟩)
        (fun s => ⟨hγd (γ x b) s, Set.mem_univ _⟩) (by rw [zero_add, hγ0 (γ x b)])
    exact congrFun heq a
  -- joint continuity from continuous dependence
  have hcont : Continuous (Function.uncurry fun (t : ℝ≥0) (x : E) => γ x (t : ℝ)) := by
    refine continuous_iff_continuousAt.2 fun p => ?_
    obtain ⟨t₀, x₀⟩ := p
    have he : Continuous fun p : ℝ≥0 × E => Real.exp (K * (p.1 : ℝ)) :=
      Real.continuous_exp.comp (continuous_const.mul (NNReal.continuous_coe.comp continuous_fst))
    have h1 : Tendsto (fun p : ℝ≥0 × E => dist p.2 x₀ * Real.exp (K * (p.1 : ℝ)))
        (𝓝 (t₀, x₀)) (𝓝 0) := by
      have hcd : Continuous fun p : ℝ≥0 × E => dist p.2 x₀ * Real.exp (K * (p.1 : ℝ)) :=
        (continuous_snd.dist continuous_const).mul he
      exact hcd.tendsto' (t₀, x₀) 0 (by simp)
    have h2 : Tendsto (fun p : ℝ≥0 × E => dist (γ x₀ (p.1 : ℝ)) (γ x₀ (t₀ : ℝ)))
        (𝓝 (t₀, x₀)) (𝓝 0) := by
      have hcd : Continuous fun p : ℝ≥0 × E => dist (γ x₀ (p.1 : ℝ)) (γ x₀ (t₀ : ℝ)) :=
        ((hγc x₀).comp (NNReal.continuous_coe.comp continuous_fst)).dist continuous_const
      exact hcd.tendsto' (t₀, x₀) 0 (by simp)
    have hbound : Tendsto (fun p : ℝ≥0 × E =>
        dist p.2 x₀ * Real.exp (K * (p.1 : ℝ)) + dist (γ x₀ (p.1 : ℝ)) (γ x₀ (t₀ : ℝ)))
        (𝓝 (t₀, x₀)) (𝓝 0) := by simpa using h1.add h2
    rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun p => ?_) hbound
    calc dist (γ p.2 (p.1 : ℝ)) (γ x₀ (t₀ : ℝ))
        ≤ dist (γ p.2 (p.1 : ℝ)) (γ x₀ (p.1 : ℝ)) + dist (γ x₀ (p.1 : ℝ)) (γ x₀ (t₀ : ℝ)) :=
          dist_triangle _ _ _
      _ ≤ dist p.2 x₀ * Real.exp (K * (p.1 : ℝ)) + dist (γ x₀ (p.1 : ℝ)) (γ x₀ (t₀ : ℝ)) := by
          gcongr
          have hd := dist_le_of_isIntegralCurve hl (hγd p.2) (hγd x₀) (p.1).coe_nonneg
          rwa [hγ0 p.2, hγ0 x₀] at hd
  let ϕ : Flow ℝ≥0 E :=
    { toFun := fun t x => γ x (t : ℝ)
      cont' := hcont
      map_zero' := fun x => hγ0 x
      map_add' := fun t₁ t₂ x => by
        have hc : ((t₁ + t₂ : ℝ≥0) : ℝ) = (t₁ : ℝ) + (t₂ : ℝ) := NNReal.coe_add t₁ t₂
        simp only [hc]
        exact hsemi x (t₁ : ℝ) (t₂ : ℝ) }
  exact ⟨ϕ, γ, hγ0, hγd, fun _ _ => rfl⟩

end ODE

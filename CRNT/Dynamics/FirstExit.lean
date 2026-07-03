import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# First-exit time for a continuous curve leaving a closed set

A general-topology tool for Nagumo invariance arguments. Given a continuous curve
`γ : ℝ → α` into a topological space, a closed set `R` with `γ 0 ∈ R`, and *some* forward
time `t > 0` at which the curve has left `R`, the **exit set**
`exitSet γ R = {t | 0 ≤ t ∧ γ t ∉ R}` is nonempty and bounded below by `0`, so its infimum
`exitTime γ R = sInf (exitSet γ R)` is a well-defined first-exit time. The lemmas here pin
down its defining properties.

* `exitSet`, `exitTime` — the exit set and the first-exit time `τ = sInf (exitSet γ R)`.
* `exitTime_nonneg` — `0 ≤ τ`, since `0` is a lower bound of the exit set.
* `mem_of_lt_exitTime` — the curve stays in `R` strictly before `τ`: if `0 ≤ s < τ` then
  `γ s ∈ R` (otherwise `s` would itself lie in the exit set, contradicting `τ = sInf`).
* `mem_exitTime` — the closed endpoint is captured: `γ τ ∈ R`. For `τ = 0` this is the
  start hypothesis; for `τ > 0` it is the left limit of the in-set values `γ s` (`s < τ`)
  under continuity and closedness of `R`.
* `mem_Icc_exitTime` — the curve stays in `R` on the closed interval `[0, τ]`.
* `exit_accumulates_right` — exit points accumulate at `τ` from the right: for every
  `ε > 0` there is `s ∈ (τ, τ + ε)` with `γ s ∉ R`. This is `exists_lt_of_csInf_lt`
  applied to `τ < τ + ε`, with the lower endpoint `s > τ` forced because `γ τ ∈ R`
  removes `τ` itself from the exit set.
* `mem_frontier_exitTime` — `γ τ ∈ frontier R`: it lies in `R` (`mem_exitTime`) and in
  `closure Rᶜ` (the right-accumulating exit points tend to `γ τ` by continuity), and for a
  closed `R`, `frontier R = R ∩ closure Rᶜ`.

The development is pure topology: the order-topological field `ℝ` for the time axis and an
arbitrary topological space `α` for the state. No reaction-network content, no metric, no
separation axioms beyond what Mathlib's `frontier`/closure API supplies.

Depends on:
`Mathlib.Topology.Order.DenselyOrdered`, `Mathlib.Topology.Order.LeftRightNhds`,
`Mathlib.Order.ConditionallyCompleteLattice.Basic`.
-/

namespace CRNT

open Set Filter Topology

variable {α : Type*} [TopologicalSpace α]

section FirstExit

variable {γ : ℝ → α} {R : Set α} {t : ℝ}

/-- The **exit set**: forward times at which the curve has left `R`. -/
def exitSet (γ : ℝ → α) (R : Set α) : Set ℝ := {t | 0 ≤ t ∧ γ t ∉ R}

/-- The **first-exit time** `τ = sInf {t | 0 ≤ t ∧ γ t ∉ R}`. -/
noncomputable def exitTime (γ : ℝ → α) (R : Set α) : ℝ := sInf (exitSet γ R)

omit [TopologicalSpace α] in
theorem exitSet_bddBelow : BddBelow (exitSet γ R) := ⟨0, fun _ ht => ht.1⟩

omit [TopologicalSpace α] in
theorem exitSet_nonempty (ht : 0 < t) (htR : γ t ∉ R) : (exitSet γ R).Nonempty :=
  ⟨t, ht.le, htR⟩

omit [TopologicalSpace α] in
theorem mem_exitSet_iff {s : ℝ} : s ∈ exitSet γ R ↔ 0 ≤ s ∧ γ s ∉ R := Iff.rfl

omit [TopologicalSpace α] in
/-- The first-exit time is nonnegative: every element of the exit set is `≥ 0`, and the set
is nonempty under the exit hypothesis. -/
theorem exitTime_nonneg (ht : 0 < t) (htR : γ t ∉ R) : 0 ≤ exitTime γ R :=
  le_csInf (exitSet_nonempty ht htR) (fun _ hs => hs.1)

omit [TopologicalSpace α] in
/-- **The curve stays in `R` strictly before the first-exit time.** If `0 ≤ s < τ`, then
`γ s ∈ R`; otherwise `s` itself would lie in the exit set, forcing `τ ≤ s`. -/
theorem mem_of_lt_exitTime {s : ℝ} (hs0 : 0 ≤ s) (hsτ : s < exitTime γ R) : γ s ∈ R := by
  by_contra hsR
  exact absurd (csInf_le exitSet_bddBelow ⟨hs0, hsR⟩) (not_le.mpr hsτ)

/-- **The curve is in `R` at the first-exit time.** For `τ = 0` this is the start
hypothesis `γ 0 ∈ R`; for `τ > 0` the in-set values `γ s` (`0 ≤ s < τ`) tend to `γ τ` as
`s → τ⁻`, and `R` is closed. -/
theorem mem_exitTime (hγ : Continuous γ) (hR : IsClosed R) (h0 : γ 0 ∈ R)
    (ht : 0 < t) (htR : γ t ∉ R) : γ (exitTime γ R) ∈ R := by
  set τ := exitTime γ R with hτ
  rcases eq_or_lt_of_le (exitTime_nonneg ht htR) with hτ0 | hτ0
  · -- τ = 0
    show γ τ ∈ R
    rw [hτ, ← hτ0]; exact h0
  · -- τ > 0 : limit from the left
    have htend : Tendsto γ (𝓝[<] τ) (𝓝 (γ τ)) :=
      (hγ.tendsto τ).mono_left nhdsWithin_le_nhds
    refine hR.mem_of_tendsto htend ?_
    -- eventually within `𝓝[<] τ` the points lie in `(0, τ)`, where `γ ∈ R`
    filter_upwards [Ioo_mem_nhdsLT hτ0] with s hs
    exact mem_of_lt_exitTime hs.1.le hs.2

/-- **The curve stays in `R` on the closed interval `[0, τ]`.** -/
theorem mem_Icc_exitTime (hγ : Continuous γ) (hR : IsClosed R) (h0 : γ 0 ∈ R)
    (ht : 0 < t) (htR : γ t ∉ R) {s : ℝ} (hs : s ∈ Icc 0 (exitTime γ R)) : γ s ∈ R := by
  rcases eq_or_lt_of_le hs.2 with hsτ | hsτ
  · rw [hsτ]; exact mem_exitTime hγ hR h0 ht htR
  · exact mem_of_lt_exitTime hs.1 hsτ

/-- **Exit points accumulate at the first-exit time from the right.** For every `ε > 0`
there is `s ∈ (τ, τ + ε)` with `γ s ∉ R`. The strict lower bound `τ < s` uses that
`γ τ ∈ R`, so `τ` itself is not in the exit set. -/
theorem exit_accumulates_right (hγ : Continuous γ) (hR : IsClosed R) (h0 : γ 0 ∈ R)
    (ht : 0 < t) (htR : γ t ∉ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ Ioo (exitTime γ R) (exitTime γ R + ε), γ s ∉ R := by
  set τ := exitTime γ R with hτ
  have hne := exitSet_nonempty ht htR
  obtain ⟨s, hsE, hslt⟩ := exists_lt_of_csInf_lt hne (show τ < τ + ε by linarith)
  have hsτ : τ ≤ s := csInf_le exitSet_bddBelow hsE
  -- `s ≠ τ` since `γ τ ∈ R` but `γ s ∉ R`
  have hsne : s ≠ τ := by
    rintro rfl
    exact hsE.2 (mem_exitTime hγ hR h0 ht htR)
  exact ⟨s, ⟨lt_of_le_of_ne hsτ (Ne.symm hsne), hslt⟩, hsE.2⟩

/-- **The first-exit point lies on the frontier of `R`.** It is in `R` (`mem_exitTime`) and
in `closure Rᶜ` (the right-accumulating exit points tend to it under continuity); for a
closed `R`, `frontier R = R ∩ closure Rᶜ`. -/
theorem mem_frontier_exitTime (hγ : Continuous γ) (hR : IsClosed R) (h0 : γ 0 ∈ R)
    (ht : 0 < t) (htR : γ t ∉ R) : γ (exitTime γ R) ∈ frontier R := by
  set τ := exitTime γ R with hτ
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure (mem_exitTime hγ hR h0 ht htR), ?_⟩
  -- `γ τ ∈ closure Rᶜ`: exit points just above `τ` tend to `γ τ`
  have htend : Tendsto γ (𝓝[>] τ) (𝓝 (γ τ)) :=
    (hγ.tendsto τ).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_frequently_of_tendsto ?_ htend
  -- frequently in `𝓝[>] τ` there is an exit point (right-accumulation)
  rw [frequently_iff]
  intro V hV
  obtain ⟨u, hu, husub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hV
  obtain ⟨s, hs, hsR⟩ := exit_accumulates_right hγ hR h0 ht htR
    (show (0 : ℝ) < u - τ by exact sub_pos.mpr hu)
  refine ⟨s, husub ?_, hsR⟩
  exact ⟨hs.1, by linarith [hs.2]⟩

end FirstExit

end CRNT

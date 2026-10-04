import CRNT.Geometry.PolyhedralBarrier
import CRNT.Geometry.HalfPlaneSeparatingSurface

/-!
# `test/VacuityAudit` — non-vacuity and load-bearing-hypothesis witnesses for the two holes

Permanent regression guard for the **vacuity audit** of the dependency chains of

* hole A — `CRNT/Dynamics/HighCodimensionSiphonFace.lean` (Craciun v3 Theorem B), through
  `CRNT/Dynamics.ToricBarrierTrapping` → `CRNT/Geometry/PolyhedralBarrier` →
  `CRNT/Geometry/ZeroSeparatingInduction` → `CRNT/Geometry/FanFaceLattice` / `FanRefinement`; and
* hole B — `CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8607`
  (`stronglyConcordant_fullyOpen_of_trueSRCriterion`).

The lemmas here are **machine-checked refutations and inhabitedness witnesses**, not prose.  Most
have the shape

```
(¬ [one hypothesis]) ∧ (¬ [the conclusion with the remaining hypotheses])
```

which *proves* the named hypothesis is genuinely load-bearing and the surrounding theorem is not
a triviality; the inhabitedness lemmas exhibit a concrete instance so the surrounding predicate
cannot be unsatisfiable.  Both directions matter: a theorem is *vacuous* when its hypotheses
cannot be met, and *trivial* when its conclusion holds without them.

Covered here (report: `research/routes/vacuity-report.md`):

| lemma | claim |
|---|---|
| `forwardInvariant_vacuous_for_empty_field` | `DifferentialInclusion.Field E := E → Set E` has no nonemptiness requirement, so `ForwardInvariant F R` holds for **every** `R` when `F` is empty — all four `ForwardInvariant` conclusions of `PolyhedralBarrier` are then free |
| `forwardInvariant_not_vacuous_in_general` | …and the definition is *not* vacuous: `{x | x ≤ 0}` is not invariant for the field `{1}` |
| `barrier_descent_is_load_bearing` | `hdesc` of `barrier_le_of_local_descent` is load-bearing (one-piece identity barrier, `γ t = t`) |
| `identBarrierSublevel_not_forwardInvariant` | the same barrier is genuinely not invariant, so no cone-family data rescues it |
| `cone_descent_hpolar_is_vacuous_for_empty_cone` | `hpolar` of `forwardInvariant_of_cone_descent` is vacuous for `Λ i = ∅`; `hmem`, not `hpolar`, carries the geometry |
| `dist_ge_separation_is_load_bearing` | `hsep` of `dist_ge_of_local_descent` is load-bearing |
| `identBarrier_eval`, `minMaxBarrier_is_not_constant` | neither `barrier` nor `minMaxBarrier` is a constant (guards against a `barrier := 0` regression that would make every trapping theorem true) |
| `zeroSeparatingSurfaceExists_is_inhabited` | the surface interface hole A must discharge **is satisfiable** |
| `zeroSeparatingSurfaceExists_false_at_origin`, `zeroSeparatingSurfaceExists_start_ne_zero` | its `x₀ ≠ 0` guard is implicit and load-bearing: the interface is unsatisfiable at the origin |

This file must stay hole-free: it is in the `test` target of `lakefile.toml`.
-/

open scoped Topology RealInnerProductSpace
open Filter Set Metric

namespace CRNT.Test.VacuityAudit

open CRNT CRNT.DifferentialInclusion



private abbrev identL : Unit → (ℝ →L[ℝ] ℝ) := fun _ => 1

private abbrev identB : Unit → ℝ := fun _ => 0

private abbrev identML : Unit → Unit → (ℝ →L[ℝ] ℝ) := fun _ _ => 1

private abbrev identMB : Unit → Unit → ℝ := fun _ _ => 0

private def identSub : Set ℝ := {x | PolyhedralBarrier.barrier identL identB x ≤ 0}

theorem identBarrier_eval (x : ℝ) : PolyhedralBarrier.barrier identL identB x = x := by
  obtain ⟨i, hi⟩ := PolyhedralBarrier.exists_active (ι := Unit) identL identB x
  rw [show i = () from Subsingleton.elim _ _] at hi
  simpa using hi.symm

private theorem zero_mem_identSub : (0 : ℝ) ∈ identSub := by
  show PolyhedralBarrier.barrier identL identB 0 ≤ 0
  rw [identBarrier_eval]

private theorem id_is_inclusionSolution_1 :
    IsInclusionSolution (fun _ => ({1} : Set ℝ)) (fun t : ℝ => t) := by
  intro t
  have h1 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id' t
  have hd : deriv (fun t : ℝ => t) t = 1 := h1.deriv
  refine ⟨?_, ?_⟩
  · rw [hd]; exact h1
  · rw [hd]; simp

theorem forwardInvariant_vacuous_for_empty_field (R : Set ℝ) :
    DifferentialInclusion.ForwardInvariant (fun _ => (∅ : Set ℝ)) R := by
  intro γ hγ _ t _
  obtain ⟨-, hmem⟩ := hγ t
  exact absurd hmem (by simp)

theorem forwardInvariant_not_vacuous_in_general :
    ¬ DifferentialInclusion.ForwardInvariant (fun _ => ({1} : Set ℝ)) {x : ℝ | x ≤ 0} := by
  intro h
  have hres : ((fun t : ℝ => t) 1) ∈ ({x : ℝ | x ≤ 0} : Set ℝ) :=
    h (fun t : ℝ => t) id_is_inclusionSolution_1 (show (0 : ℝ) ≤ 0 by norm_num) 1
      (show (0 : ℝ) ≤ 1 by norm_num)
  norm_num at hres

theorem identBarrierSublevel_not_forwardInvariant :
    ¬ DifferentialInclusion.ForwardInvariant (fun _ => ({1} : Set ℝ)) identSub := by
  intro h
  have hres : ((fun t : ℝ => t) 1) ∈ identSub :=
    h (fun t : ℝ => t) id_is_inclusionSolution_1 zero_mem_identSub 1
      (show (0 : ℝ) ≤ 1 by norm_num)
  have hres' : PolyhedralBarrier.barrier identL identB 1 ≤ 0 := hres
  rw [identBarrier_eval] at hres'
  norm_num at hres'

theorem barrier_descent_is_load_bearing :
    (∀ t, 0 ≤ t → HasDerivAt (fun t : ℝ => t) 1 t) ∧
    (PolyhedralBarrier.barrier identL identB 0 ≤ 0) ∧
    (¬ ∀ t, 0 ≤ t → (0 : ℝ) ≤ PolyhedralBarrier.barrier identL identB t →
        ∀ i : Unit, identL i t - identB i = PolyhedralBarrier.barrier identL identB t →
          identL i 1 ≤ 0) ∧
    (¬ ∀ t, 0 ≤ t → PolyhedralBarrier.barrier identL identB t ≤ 0) := by
  refine And.intro (fun t _ => hasDerivAt_id' t) ?_
  refine And.intro zero_mem_identSub ?_
  refine And.intro ?_ ?_
  · intro h
    have hbad := h 0 (by norm_num) (by rw [identBarrier_eval]) () rfl
    norm_num at hbad
  · intro h
    have hbad := h 1 (by norm_num)
    rw [identBarrier_eval] at hbad
    norm_num at hbad

theorem cone_descent_hpolar_is_vacuous_for_empty_cone :
    (∀ (L : Unit → (ℝ →L[ℝ] ℝ)) (b : Unit → ℝ) (R : ℝ)
        (F : DifferentialInclusion.Field ℝ) (y : ℝ) (i : Unit) (c : ℝ),
      R ≤ PolyhedralBarrier.barrier L b y → c ∈ F y →
      L i y - b i = PolyhedralBarrier.barrier L b y →
      ∀ M ∈ (∅ : Set (ℝ →L[ℝ] ℝ)), M c ≤ 0) ∧
    (¬ ((1 : ℝ →L[ℝ] ℝ) ∈ (∅ : Set (ℝ →L[ℝ] ℝ)))) := by
  refine And.intro ?_ ?_
  · intro L b R F y i c hR hc hEq M hM
    simp at hM
  · intro h
    simp at h

theorem dist_ge_separation_is_load_bearing :
    (¬ ∃ r : ℝ, 0 < r ∧ ∀ t, 0 ≤ t → r ≤ dist ((fun t : ℝ => t) t) 0) := by
  rintro ⟨r, hr, h⟩
  have hz := h 0 (by norm_num)
  rw [dist_self] at hz
  exact absurd hr (not_lt.mpr hz)

theorem minMaxBarrier_is_not_constant :
    CRNT.PolyhedralBarrier.minMaxBarrier (ι' := Unit) (ι := Unit)
      identML identMB (1 : ℝ) = 1 := by
  obtain ⟨k, hk⟩ :=
    CRNT.PolyhedralBarrier.exists_min_branch (ι' := Unit) (ι := Unit)
      identML identMB (1 : ℝ)
  rw [← hk]
  exact identBarrier_eval 1

theorem zeroSeparatingSurfaceExists_is_inhabited :
    DifferentialInclusion.ZeroSeparatingSurfaceExists (fun _ : ℝ => 0) 1 :=
  DifferentialInclusion.zeroSeparatingSurfaceExists_halfPlane
    (f := fun _ : ℝ => 0) (x₀ := 1) (n := 1) (a := 1) (δ := 1)
    (norm_one : ‖(1 : ℝ)‖ = 1) one_pos one_pos (by norm_num) (by
      intro y _ _; simp)

theorem zeroSeparatingSurfaceExists_false_at_origin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E) :
    ¬ DifferentialInclusion.ZeroSeparatingSurfaceExists f 0 := by
  rintro h
  obtain ⟨g, g', c, δ, r, _, _, _, _, hx₀, hr, hsep⟩ := h.exists_surface
  have hnotmem : (0 : E) ∉ Metric.ball (0 : E) r := fun hh => hsep hx₀ hh
  have hlt : ¬ ((0 : ℝ) < r) := by simpa [Metric.mem_ball, dist_self] using hnotmem
  exact absurd hr hlt

theorem zeroSeparatingSurfaceExists_start_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → E} {x₀ : E}
    (h : DifferentialInclusion.ZeroSeparatingSurfaceExists f x₀) : x₀ ≠ 0 := by
  intro hz
  subst hz
  exact zeroSeparatingSurfaceExists_false_at_origin f h

end CRNT.Test.VacuityAudit

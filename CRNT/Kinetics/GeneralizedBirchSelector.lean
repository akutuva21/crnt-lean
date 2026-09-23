import CRNT.Kinetics.GeneralizedBirchExistence
import CRNT.Kinetics.GeneralizedBirchLocal

/-!
# Continuous generalized-Birch selectors

The generalized Birch quotient map is an open embedding under the closure condition.
Consequently, any continuous family of positive target representatives has a continuous
lift to the toric parameter space.  This packages the continuity that the Type-II
weakly-reversible deficiency-one argument needs.
-/

namespace CRNT

open scoped Classical

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [TopologicalSpace α]

/-- The generalized Birch quotient map is an open embedding. -/
theorem generalizedBirchQuotientMap_isOpenEmbedding
    {S T : Submodule ℝ (ι → ℝ)} (hclosure : GeneralizedClosureCondition S T)
    {xstar c : ι → ℝ} (hxs : ∀ i, 0 < xstar i) :
    Topology.IsOpenEmbedding (generalizedBirchQuotientMap S T xstar c) := by
  have hlocal := generalizedBirchQuotientMap_isLocalHomeomorph (c := c) hclosure hxs
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    hlocal.continuous (generalizedBirchQuotientMap_injective hclosure hxs) hlocal.isOpenMap

/-- A continuous positive family of target representatives admits a continuous lift through
    the generalized Birch quotient map. -/
theorem exists_continuous_generalizedBirchQuotientLift
    (S T : Submodule ℝ (ι → ℝ)) (hclosure : GeneralizedClosureCondition S T)
    (xstar : ι → ℝ) (hxs : ∀ i, 0 < xstar i)
    (c : α → (ι → ℝ)) (hcpos : ∀ a i, 0 < c a i) (hccont : Continuous c) :
    ∃ w : α → orthSum T, Continuous w ∧
      ∀ a, generalizedBirchQuotientMap S T xstar 0 (w a) = S.mkQ (c a) := by
  have hex : ∀ a, ∃ w : orthSum T,
      generalizedBirchQuotientMap S T xstar 0 w = S.mkQ (c a) := by
    intro a
    obtain ⟨x, hxpos, hxS, hxT⟩ :=
      generalized_birch_existence_of_conditions S T hclosure xstar (c a) hxs (hcpos a)
    let w : orthSum T := ⟨fun i => Real.log (x i) - Real.log (xstar i), hxT⟩
    refine ⟨w, ?_⟩
    rw [generalizedBirchQuotientMap]
    change S.mkQ (generalizedBirchExpAffine xstar 0 w.1) = S.mkQ (c a)
    have hxeq : (fun i => xstar i * Real.exp (w.1 i)) = x := by
      funext i
      dsimp [w]
      rw [Real.exp_sub, Real.exp_log (hxpos i), Real.exp_log (hxs i)]
      field_simp [(hxs i).ne']
    have haff : generalizedBirchExpAffine xstar 0 w.1 = x := by
      funext i
      simp [generalizedBirchExpAffine, congrFun hxeq i]
    rw [haff]
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero S).mpr hxS
  choose w hw using hex
  refine ⟨w, ?_, hw⟩
  have hemb := generalizedBirchQuotientMap_isOpenEmbedding (c := (0 : ι → ℝ)) hclosure hxs
  apply hemb.isInducing.continuous_iff.mpr
  have heq : generalizedBirchQuotientMap S T xstar 0 ∘ w = fun a => S.mkQ (c a) := by
    funext a
    exact hw a
  rw [heq]
  exact S.mkQL.continuous.comp hccont

/-- The lifted toric family itself is continuous and stays in the requested affine classes. -/
theorem exists_continuous_generalizedBirchSelector
    (S T : Submodule ℝ (ι → ℝ)) (hclosure : GeneralizedClosureCondition S T)
    (xstar : ι → ℝ) (hxs : ∀ i, 0 < xstar i)
    (c : α → (ι → ℝ)) (hcpos : ∀ a i, 0 < c a i) (hccont : Continuous c) :
    ∃ x : α → (ι → ℝ), Continuous x ∧ (∀ a i, 0 < x a i) ∧
      ∀ a, x a - c a ∈ S ∧
        (fun i => Real.log (x a i) - Real.log (xstar i)) ∈ orthSum T := by
  obtain ⟨w, hwcont, hwq⟩ :=
    exists_continuous_generalizedBirchQuotientLift S T hclosure xstar hxs c hcpos hccont
  let x : α → (ι → ℝ) := fun a i => xstar i * Real.exp ((w a).1 i)
  refine ⟨x, ?_, ?_, ?_⟩
  · apply continuous_pi
    intro i
    exact (continuous_const.mul (Real.continuous_exp.comp
      ((continuous_apply i).comp (continuous_subtype_val.comp hwcont))))
  · intro a i
    exact mul_pos (hxs i) (Real.exp_pos _)
  · intro a
    constructor
    · apply (Submodule.Quotient.mk_eq_zero S).mp
      have hz : S.mkQL (x a - c a) = 0 := by
        rw [map_sub]
        have hq := hwq a
        have hq' : S.mkQ (x a) = S.mkQ (c a) := by
          rw [← hq]
          congr 1
          funext i
          simp [x, generalizedBirchQuotientMap, generalizedBirchExpAffine]
        have hqL : S.mkQL (x a) = S.mkQL (c a) := hq'
        rw [hqL, sub_self]
      exact hz
    · have hwmem : ((w a : orthSum T) : ι → ℝ) ∈ orthSum T := (w a).2
      convert hwmem using 1
      funext i
      dsimp [x]
      rw [Real.log_mul (hxs i).ne' (Real.exp_ne_zero _), Real.log_exp]
      ring

end CRNT

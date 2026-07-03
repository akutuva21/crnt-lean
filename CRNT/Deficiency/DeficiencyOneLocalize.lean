import CRNT.Deficiency.DeficiencyOneDecomp
import CRNT.Deficiency.ClassConservation
import CRNT.Deficiency.SteadyStateKernel

/-!
# Localization of steady states to the deficient linkage class

Under the deficiency-one conditions the per-class deficiency subspace has dimension exactly the
class deficiency `δ_θ` (`finrank_linkageDeficiencySubspace`), so a deficiency-zero linkage class
contributes nothing (`linkageDeficiencySubspace_eq_bot_of_deficiency_zero`). Consequently a
mass-action steady state is complex-balanced on every deficiency-zero linkage class
(`restrictToClass_kineticImage_eq_zero`): the deficiency-one analysis localizes to the single
deficient class.

Depends on: `CRNT.Deficiency.DeficiencyOneDecomp`,
`CRNT.Deficiency.ClassConservation`, `CRNT.Deficiency.SteadyStateKernel`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Restricting a class-supported vector to its own class is the identity. -/
theorem restrictToClass_eq_self_of_mem_supportedOn (N : Network S) (q : Quotient N.linkedSetoid)
    {v : N.ComplexIdx → ℝ} (hv : v ∈ N.supportedOn q) : N.restrictToClass q v = v := by
  funext c
  by_cases hc : N.classOf c = q
  · exact restrictToClass_apply_of_eq N v hc
  · rw [restrictToClass_apply_of_ne N v hc, hv c hc]

/-- The coordinate subspace `supportedOn q` is linearly equivalent to functions on the class
fiber. -/
noncomputable def supportedOnEquiv (N : Network S) (q : Quotient N.linkedSetoid) :
    N.supportedOn q ≃ₗ[ℝ] ({c : N.ComplexIdx // N.classOf c = q} → ℝ) where
  toFun v := fun c => v.val c.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨fun c => if h : N.classOf c = q then f ⟨c, h⟩ else 0, fun c hc => dif_neg hc⟩
  left_inv v := by
    apply Subtype.ext; funext c
    by_cases h : N.classOf c = q
    · simp only [dif_pos h]
    · simp only [dif_neg h]; exact (v.property c h).symm
  right_inv f := by funext c; simp only [dif_pos c.property]

/-- **The dimension of `supportedOn q` is the number of complexes in the class.** -/
theorem finrank_supportedOn (N : Network S) (q : Quotient N.linkedSetoid) :
    Module.finrank ℝ (N.supportedOn q) = N.numComplexesIn q := by
  rw [(N.supportedOnEquiv q).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_subtype]
  rfl

/-- The class-sum functional: the total of a vector's entries over a linkage class. -/
noncomputable def classSum (N : Network S) (q : Quotient N.linkedSetoid) :
    (N.ComplexIdx → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ c, N.restrictToClass q v c
  map_add' v w := by
    simp only [restrictToClass, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : N.classOf c = q <;> simp [h]
  map_smul' a v := by
    simp only [restrictToClass, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : N.classOf c = q <;> simp [h]

/-- The per-class cut space: cut vectors supported on a single linkage class. -/
noncomputable def linkageCutSpace (N : Network S) (q : Quotient N.linkedSetoid) :
    Submodule ℝ (N.ComplexIdx → ℝ) :=
  LinearMap.range N.incidenceMap ⊓ N.supportedOn q

theorem linkageCutSpace_le_ker_classSum (N : Network S) (q : Quotient N.linkedSetoid) :
    N.linkageCutSpace q ≤ LinearMap.ker (N.classSum q) := by
  intro v hv
  rw [LinearMap.mem_ker]
  exact N.sum_restrictToClass_eq_zero_of_mem_range_incidenceMap (Submodule.mem_inf.mp hv).1 q

/-- The class deficiency subspace is the kernel of the complex map on the class cut space. -/
theorem linkageDeficiencySubspace_eq_inf (N : Network S) (q : Quotient N.linkedSetoid) :
    N.linkageDeficiencySubspace q = N.linkageCutSpace q ⊓ LinearMap.ker N.complexMap := by
  rw [linkageDeficiencySubspace, deficiencySubspace, linkageCutSpace]
  ext v; simp only [Submodule.mem_inf, LinearMap.mem_ker]; tauto

/-- **The per-class cut space has dimension at most `n_θ − 1`.** Its vectors are supported on the
class and sum to zero there. -/
theorem finrank_linkageCutSpace_le (N : Network S) (q : Quotient N.linkedSetoid) :
    Module.finrank ℝ (N.linkageCutSpace q) ≤ N.numComplexesIn q - 1 := by
  obtain ⟨c0, hc0⟩ := Quotient.exists_rep q
  -- the class-sum functional is nonzero on `supportedOn q`, so its kernel there is a hyperplane
  have hlt : N.supportedOn q ⊓ LinearMap.ker (N.classSum q) < N.supportedOn q := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    have hmem : Pi.single c0 (1 : ℝ) ∈ N.supportedOn q := by
      intro c hc
      have hne : c ≠ c0 := fun h => hc (by rw [h]; exact hc0)
      simp [hne]
    have hsum : N.classSum q (Pi.single c0 (1 : ℝ)) = 1 := by
      show ∑ c, N.restrictToClass q (Pi.single c0 (1 : ℝ)) c = 1
      rw [Finset.sum_eq_single c0]
      · rw [restrictToClass_apply_of_eq N _ hc0, Pi.single_eq_same]
      · intro c _ hcc
        by_cases h : N.classOf c = q
        · rw [restrictToClass_apply_of_eq N _ h]
          simp [hcc]
        · rw [restrictToClass_apply_of_ne N _ h]
      · intro h; exact absurd (Finset.mem_univ c0) h
    have : Pi.single c0 (1 : ℝ) ∈ LinearMap.ker (N.classSum q) := by
      rw [← heq] at hmem; exact (Submodule.mem_inf.mp hmem).2
    rw [LinearMap.mem_ker, hsum] at this
    exact one_ne_zero this
  have hle : N.linkageCutSpace q ≤ N.supportedOn q ⊓ LinearMap.ker (N.classSum q) :=
    le_inf inf_le_right (N.linkageCutSpace_le_ker_classSum q)
  have hlt2 : Module.finrank ℝ (N.supportedOn q ⊓ LinearMap.ker (N.classSum q) : Submodule ℝ _)
      < Module.finrank ℝ (N.supportedOn q) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_supportedOn] at hlt2
  exact Nat.le_sub_one_of_lt (lt_of_le_of_lt (Submodule.finrank_mono hle) hlt2)

/-- **The complex map carries the class cut space onto the per-class stoichiometric subspace.** -/
theorem linkageStoichSubspace_le_map_complexMap (N : Network S) (q : Quotient N.linkedSetoid) :
    N.linkageStoichSubspace q ≤ Submodule.map N.complexMap (N.linkageCutSpace q) := by
  rw [linkageStoichSubspace, Submodule.span_le]
  rintro _ ⟨r, hr, rfl⟩
  refine Submodule.mem_map.mpr ⟨N.incidenceMap (Pi.single r 1), ?_, ?_⟩
  · refine Submodule.mem_inf.mpr ⟨⟨Pi.single r 1, rfl⟩, ?_⟩
    intro c hc
    rw [incidenceMap_apply]
    refine Finset.sum_eq_zero fun r' _ => ?_
    rcases eq_or_ne r' r with rfl | hr'
    · have htgt : N.targetIdx r' ≠ c :=
        fun h => hc (by rw [← h, ← N.classOf_sourceIdx_eq_targetIdx r']; exact hr)
      have hsrc : N.sourceIdx r' ≠ c := fun h => hc (by rw [← h]; exact hr)
      rw [if_neg htgt, if_neg hsrc, sub_zero, mul_zero]
    · rw [Pi.single_eq_of_ne hr', zero_mul]
  · rw [← LinearMap.comp_apply, complexMap_comp_incidenceMap, stoichMap_single]

/-- **The per-class deficiency subspace has dimension at most the class deficiency.** -/
theorem finrank_linkageDeficiencySubspace_le (N : Network S) (q : Quotient N.linkedSetoid) :
    Module.finrank ℝ (N.linkageDeficiencySubspace q) ≤ (N.linkageDeficiency q).toNat := by
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (N.complexMap.domRestrict (N.linkageCutSpace q))
  have hker : Module.finrank ℝ
      (LinearMap.ker (N.complexMap.domRestrict (N.linkageCutSpace q)))
      = Module.finrank ℝ (N.linkageDeficiencySubspace q) := by
    rw [← Submodule.finrank_map_subtype_eq (N.linkageCutSpace q)
      (LinearMap.ker (N.complexMap.domRestrict (N.linkageCutSpace q))),
      LinearMap.ker_domRestrict, Submodule.map_comap_subtype, ← linkageDeficiencySubspace_eq_inf]
  have hrange : N.linkageStoichRank q ≤ Module.finrank ℝ
      (LinearMap.range (N.complexMap.domRestrict (N.linkageCutSpace q))) := by
    rw [LinearMap.range_domRestrict]
    exact Submodule.finrank_mono (N.linkageStoichSubspace_le_map_complexMap q)
  have hcut := N.finrank_linkageCutSpace_le q
  have hnn := N.linkageDeficiency_nonneg q
  have hdef : (N.linkageDeficiency q : ℤ)
      = (N.numComplexesIn q : ℤ) - 1 - (N.linkageStoichRank q : ℤ) := rfl
  rw [hker] at hrn
  omega

/-- **A deficiency-zero linkage class contributes nothing to the deficiency subspace.** -/
theorem linkageDeficiencySubspace_eq_bot_of_deficiency_zero (N : Network S)
    {q : Quotient N.linkedSetoid} (hq : N.linkageDeficiency q = 0) :
    N.linkageDeficiencySubspace q = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  have hle := N.finrank_linkageDeficiencySubspace_le q
  rw [hq] at hle
  exact Nat.le_zero.mp (by simpa using hle)

/-- **A mass-action steady state is complex-balanced on every deficiency-zero linkage class.**
Under the deficiency-one conditions the kinetic image vanishes when restricted to a linkage
class of deficiency zero — so only deficient classes carry the complex-balancing defect. -/
theorem restrictToClass_kineticImage_eq_zero (N : Network S) (h : N.DeficiencyOneConditions)
    (κ : RateConstants N) {x : Concentration S} (hx : N.IsMassActionSteadyState κ x)
    {q : Quotient N.linkedSetoid} (hq : N.linkageDeficiency q = 0) :
    N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector x)) = 0 := by
  have hmem := N.restrictToClass_mem_linkageDeficiencySubspace h
    (N.kineticMap_complexMonomial_mem_deficiencySubspace κ hx) q
  rw [N.linkageDeficiencySubspace_eq_bot_of_deficiency_zero hq] at hmem
  exact (Submodule.mem_bot ℝ).mp hmem

/-- **The deficiency mode of a deficiency-one network lives on its single deficient linkage
class.** The deficiency subspace equals the per-class deficiency subspace of the unique class of
deficiency one; every other class is deficiency-zero and contributes nothing. This concentrates
the entire complex-balancing defect of any steady state onto one linkage class — the launchpad
for the deficiency-one sign analysis. -/
theorem deficiencySubspace_eq_linkageDeficiencySubspace_of_deficiencyOne (N : Network S)
    (hδ : N.DeficiencyOne) (h : N.DeficiencyOneConditions) :
    ∃ q : Quotient N.linkedSetoid,
      N.linkageDeficiency q = 1 ∧ N.deficiencySubspace = N.linkageDeficiencySubspace q := by
  obtain ⟨q0, hq0, hq0uniq⟩ := N.existsUnique_deficient_of_deficiencyOne hδ h
  refine ⟨q0, hq0, ?_⟩
  rw [N.deficiencySubspace_eq_iSup h]
  refine le_antisymm (iSup_le fun q => ?_) (le_iSup _ q0)
  rcases N.linkageDeficiency_eq_zero_or_one h q with hz | ho
  · rw [N.linkageDeficiencySubspace_eq_bot_of_deficiency_zero hz]; exact bot_le
  · exact le_of_eq (congrArg N.linkageDeficiencySubspace (hq0uniq q ho))

end Network

end CRNT

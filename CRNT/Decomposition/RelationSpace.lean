import CRNT.Decomposition.Deficiency

/-!
# Inter-block relations and deficiency balance

For a reaction partition, each block contributes a stoichiometric subspace and an
incidence subspace.  Relations between blocks are tuples of block vectors whose sum is
zero.  Rank-nullity identifies the dimension of each relation space with the corresponding
rank loss under composition.  The resulting exact identity says that the difference
between the sum of block deficiencies and the network deficiency is the incidence
relation dimension minus the stoichiometric relation dimension.

This records the two kinds of coupling separately.  Either can be larger, so the identity
is stated over `ℤ` rather than using truncated natural subtraction.
-/

namespace CRNT
namespace Network
namespace ReactionPartition

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S} {ι : Type} [DecidableEq ι] [Fintype ι]

/-- Tuples choosing one stoichiometric vector from every reaction block. -/
abbrev StoichBlockProduct (D : ReactionPartition N ι) :=
  ∀ i, D.blockStoichSubspace i

/-- Tuples choosing one incidence vector from every reaction block. -/
abbrev IncidenceBlockProduct (D : ReactionPartition N ι) :=
  ∀ i, D.blockIncidenceSubspace i

/-- Sum the stoichiometric vectors selected from the blocks. -/
noncomputable def stoichBlockSumMap (D : ReactionPartition N ι) :
    D.StoichBlockProduct →ₗ[ℝ] (S → ℝ) where
  toFun z := ∑ i, (z i : S → ℝ)
  map_add' z w := by
    simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' a z := by
    simp only [Pi.smul_apply, Submodule.coe_smul_of_tower, RingHom.id_apply,
      Finset.smul_sum]

/-- Sum the incidence vectors selected from the blocks. -/
noncomputable def incidenceBlockSumMap (D : ReactionPartition N ι) :
    D.IncidenceBlockProduct →ₗ[ℝ] (N.ComplexIdx → ℝ) where
  toFun z := ∑ i, (z i : N.ComplexIdx → ℝ)
  map_add' z w := by
    simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' a z := by
    simp only [Pi.smul_apply, Submodule.coe_smul_of_tower, RingHom.id_apply,
      Finset.smul_sum]

@[simp] theorem stoichBlockSumMap_apply (D : ReactionPartition N ι)
    (z : D.StoichBlockProduct) :
    D.stoichBlockSumMap z = ∑ i, (z i : S → ℝ) := rfl

@[simp] theorem incidenceBlockSumMap_apply (D : ReactionPartition N ι)
    (z : D.IncidenceBlockProduct) :
    D.incidenceBlockSumMap z = ∑ i, (z i : N.ComplexIdx → ℝ) := rfl

/-- Stoichiometric inter-block relations: block contributions that cancel in the species
space. -/
noncomputable def stoichRelationSpace (D : ReactionPartition N ι) :
    Submodule ℝ D.StoichBlockProduct :=
  LinearMap.ker D.stoichBlockSumMap

/-- Incidence inter-block relations: block contributions that cancel in complex space. -/
noncomputable def incidenceRelationSpace (D : ReactionPartition N ι) :
    Submodule ℝ D.IncidenceBlockProduct :=
  LinearMap.ker D.incidenceBlockSumMap

theorem mem_stoichRelationSpace_iff (D : ReactionPartition N ι)
    (z : D.StoichBlockProduct) :
    z ∈ D.stoichRelationSpace ↔ ∑ i, (z i : S → ℝ) = 0 := by
  simp [stoichRelationSpace, LinearMap.mem_ker]

theorem mem_incidenceRelationSpace_iff (D : ReactionPartition N ι)
    (z : D.IncidenceBlockProduct) :
    z ∈ D.incidenceRelationSpace ↔
      ∑ i, (z i : N.ComplexIdx → ℝ) = 0 := by
  simp [incidenceRelationSpace, LinearMap.mem_ker]

/-- The block-sum map spans the full stoichiometric subspace. -/
theorem range_stoichBlockSumMap (D : ReactionPartition N ι) :
    LinearMap.range D.stoichBlockSumMap = N.stoichSubspace := by
  classical
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    rw [D.stoichSubspace_eq_span_blocks]
    apply Submodule.sum_mem
    intro i _
    exact le_iSup (fun i => D.blockStoichSubspace i) i (z i).property
  · rw [Network.stoichSubspace, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    obtain ⟨i, hri⟩ := D.exists_block r
    refine ⟨Pi.single i ⟨N.reactionVector r,
      Submodule.subset_span ⟨r, hri, rfl⟩⟩, ?_⟩
    simp only [stoichBlockSumMap_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim

/-- The block-sum map spans the full incidence image. -/
theorem range_incidenceBlockSumMap (D : ReactionPartition N ι) :
    LinearMap.range D.incidenceBlockSumMap = LinearMap.range N.incidenceMap := by
  classical
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    rw [D.incidenceRange_eq_span_blocks]
    apply Submodule.sum_mem
    intro i _
    exact le_iSup (fun i => D.blockIncidenceSubspace i) i (z i).property
  · rintro x ⟨v, rfl⟩
    let z : D.IncidenceBlockProduct := fun i =>
      ⟨D.blockIncidenceContribution i v, by
        unfold blockIncidenceContribution
        apply Submodule.sum_mem
        intro r hr
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, hr, rfl⟩)⟩
    refine ⟨z, ?_⟩
    rw [incidenceBlockSumMap_apply]
    change (∑ i : ι, D.blockIncidenceContribution i v) = N.incidenceMap v
    funext c
    simp only [blockIncidenceContribution, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Network.incidenceMap_apply]
    rw [← Finset.sum_biUnion]
    · simpa [D.covers]
    · intro i _ j _ hij
      exact D.disjoint i j hij

/-- Product dimensions add across the stoichiometric blocks. -/
theorem finrank_stoichBlockProduct (D : ReactionPartition N ι) :
    Module.finrank ℝ D.StoichBlockProduct = ∑ i, D.blockStoichRank i := by
  classical
  rw [Module.finrank_pi_fintype]
  rfl

/-- Product dimensions add across the incidence blocks. -/
theorem finrank_incidenceBlockProduct (D : ReactionPartition N ι) :
    Module.finrank ℝ D.IncidenceBlockProduct = ∑ i, D.blockIncidenceRank i := by
  classical
  rw [Module.finrank_pi_fintype]
  rfl

/-- Rank-nullity for block stoichiometric relations, stated without truncated
subtraction. -/
theorem finrank_stoichRelationSpace_add_stoichRank (D : ReactionPartition N ι) :
    Module.finrank ℝ D.stoichRelationSpace + N.stoichRank =
      ∑ i, D.blockStoichRank i := by
  have hdim := LinearMap.finrank_range_add_finrank_ker D.stoichBlockSumMap
  rw [D.range_stoichBlockSumMap, D.finrank_stoichBlockProduct] at hdim
  change N.stoichRank + Module.finrank ℝ D.stoichRelationSpace =
      ∑ i, D.blockStoichRank i at hdim
  omega

/-- Rank-nullity for block incidence relations, stated without truncated
subtraction. -/
theorem finrank_incidenceRelationSpace_add_incidenceRank (D : ReactionPartition N ι) :
    Module.finrank ℝ D.incidenceRelationSpace + N.incidenceRank =
      ∑ i, D.blockIncidenceRank i := by
  have hdim := LinearMap.finrank_range_add_finrank_ker D.incidenceBlockSumMap
  rw [D.range_incidenceBlockSumMap, D.finrank_incidenceBlockProduct] at hdim
  change N.incidenceRank + Module.finrank ℝ D.incidenceRelationSpace =
      ∑ i, D.blockIncidenceRank i at hdim
  omega

/-- Stoichiometric independence is exactly the absence of nonzero inter-block
stoichiometric relations. -/
theorem stoichIndependent_iff_relationSpace_eq_bot (D : ReactionPartition N ι) :
    D.StoichIndependent ↔ D.stoichRelationSpace = ⊥ := by
  rw [D.stoichIndependent_iff_rank_additive]
  constructor
  · intro h
    apply Submodule.finrank_eq_zero.mp
    have hdim := D.finrank_stoichRelationSpace_add_stoichRank
    omega
  · intro h
    have hzero : Module.finrank ℝ D.stoichRelationSpace = 0 :=
      Submodule.finrank_eq_zero.mpr h
    have hdim := D.finrank_stoichRelationSpace_add_stoichRank
    omega

/-- Incidence independence is exactly the absence of nonzero inter-block incidence
relations. -/
theorem incidenceIndependent_iff_relationSpace_eq_bot (D : ReactionPartition N ι) :
    D.IncidenceIndependent ↔ D.incidenceRelationSpace = ⊥ := by
  rw [D.incidenceIndependent_iff_rank_additive]
  constructor
  · intro h
    apply Submodule.finrank_eq_zero.mp
    have hdim := D.finrank_incidenceRelationSpace_add_incidenceRank
    omega
  · intro h
    have hzero : Module.finrank ℝ D.incidenceRelationSpace = 0 :=
      Submodule.finrank_eq_zero.mpr h
    have hdim := D.finrank_incidenceRelationSpace_add_incidenceRank
    omega

/-- The deficiency gap of an arbitrary reaction partition is exactly the excess of
incidence relations over stoichiometric relations.  This integer identity quantifies the
two opposing coupling effects even when neither independence condition holds. -/
theorem deficiencyGap_eq_incidenceRelations_sub_stoichRelations
    (D : ReactionPartition N ι) :
    D.totalBlockDeficiencyInt - N.deficiencyInt =
      (Module.finrank ℝ D.incidenceRelationSpace : ℤ) -
        (Module.finrank ℝ D.stoichRelationSpace : ℤ) := by
  have hI : (Module.finrank ℝ D.incidenceRelationSpace : ℤ) +
        (N.incidenceRank : ℤ) = ∑ i, (D.blockIncidenceRank i : ℤ) := by
    exact_mod_cast D.finrank_incidenceRelationSpace_add_incidenceRank
  have hS : (Module.finrank ℝ D.stoichRelationSpace : ℤ) +
        (N.stoichRank : ℤ) = ∑ i, (D.blockStoichRank i : ℤ) := by
    exact_mod_cast D.finrank_stoichRelationSpace_add_stoichRank
  rw [D.network_deficiency_eq_incidence_sub_stoich]
  unfold totalBlockDeficiencyInt blockDeficiencyInt
  rw [Finset.sum_sub_distrib]
  omega

/-- Block deficiencies add exactly when the incidence and stoichiometric relation spaces
have equal dimension.  Equality of total deficiencies therefore does not by itself imply
bi-independence: both relation spaces may have the same positive dimension. -/
theorem deficiency_additivity_iff_relationDimensions_eq (D : ReactionPartition N ι) :
    D.totalBlockDeficiencyInt = N.deficiencyInt ↔
      Module.finrank ℝ D.incidenceRelationSpace =
        Module.finrank ℝ D.stoichRelationSpace := by
  constructor
  · intro h
    have hgap := D.deficiencyGap_eq_incidenceRelations_sub_stoichRelations
    rw [h, sub_self] at hgap
    have hcast : (Module.finrank ℝ D.incidenceRelationSpace : ℤ) =
        (Module.finrank ℝ D.stoichRelationSpace : ℤ) :=
      sub_eq_zero.mp hgap.symm
    exact_mod_cast hcast
  · intro h
    have hgap := D.deficiencyGap_eq_incidenceRelations_sub_stoichRelations
    have hcast : (Module.finrank ℝ D.incidenceRelationSpace : ℤ) =
        (Module.finrank ℝ D.stoichRelationSpace : ℤ) := by
      exact_mod_cast h
    rw [hcast, sub_self] at hgap
    exact sub_eq_zero.mp hgap

/-- Under stoichiometric independence, the deficiency gap is precisely the incidence
relation dimension. -/
theorem deficiencyGap_eq_incidenceRelationDimension_of_stoichIndependent
    (D : ReactionPartition N ι) (h : D.StoichIndependent) :
    D.totalBlockDeficiencyInt - N.deficiencyInt =
      (Module.finrank ℝ D.incidenceRelationSpace : ℤ) := by
  have hbot : D.stoichRelationSpace = ⊥ :=
    D.stoichIndependent_iff_relationSpace_eq_bot.mp h
  have hzero : Module.finrank ℝ D.stoichRelationSpace = 0 :=
    Submodule.finrank_eq_zero.mpr hbot
  rw [D.deficiencyGap_eq_incidenceRelations_sub_stoichRelations, hzero]
  simp

/-- Under incidence independence, the deficiency gap is the negative of the
stoichiometric relation dimension. -/
theorem deficiencyGap_eq_neg_stoichRelationDimension_of_incidenceIndependent
    (D : ReactionPartition N ι) (h : D.IncidenceIndependent) :
    D.totalBlockDeficiencyInt - N.deficiencyInt =
      - (Module.finrank ℝ D.stoichRelationSpace : ℤ) := by
  have hbot : D.incidenceRelationSpace = ⊥ :=
    D.incidenceIndependent_iff_relationSpace_eq_bot.mp h
  have hzero : Module.finrank ℝ D.incidenceRelationSpace = 0 :=
    Submodule.finrank_eq_zero.mpr hbot
  rw [D.deficiencyGap_eq_incidenceRelations_sub_stoichRelations, hzero]
  simp

/-- If stoichiometric independence holds but incidence independence fails, the sum of
block deficiencies is strictly larger than the network deficiency. -/
theorem deficiencyInt_lt_totalBlockDeficiencyInt_of_stoichIndependent_of_not_incidenceIndependent
    (D : ReactionPartition N ι) (hs : D.StoichIndependent)
    (hi : ¬ D.IncidenceIndependent) :
    N.deficiencyInt < D.totalBlockDeficiencyInt := by
  have hdim : 0 < Module.finrank ℝ D.incidenceRelationSpace := by
    by_contra hnot
    have hz : Module.finrank ℝ D.incidenceRelationSpace = 0 :=
      Nat.eq_zero_of_not_pos hnot
    have hb : D.incidenceRelationSpace = ⊥ := Submodule.finrank_eq_zero.mp hz
    exact hi ((D.incidenceIndependent_iff_relationSpace_eq_bot).mpr hb)
  have hgap := D.deficiencyGap_eq_incidenceRelationDimension_of_stoichIndependent hs
  omega

/-- If incidence independence holds but stoichiometric independence fails, the sum of
block deficiencies is strictly smaller than the network deficiency. -/
theorem totalBlockDeficiencyInt_lt_deficiencyInt_of_incidenceIndependent_of_not_stoichIndependent
    (D : ReactionPartition N ι) (hi : D.IncidenceIndependent)
    (hs : ¬ D.StoichIndependent) :
    D.totalBlockDeficiencyInt < N.deficiencyInt := by
  have hdim : 0 < Module.finrank ℝ D.stoichRelationSpace := by
    by_contra hnot
    have hz : Module.finrank ℝ D.stoichRelationSpace = 0 :=
      Nat.eq_zero_of_not_pos hnot
    have hb : D.stoichRelationSpace = ⊥ := Submodule.finrank_eq_zero.mp hz
    exact hs ((D.stoichIndependent_iff_relationSpace_eq_bot).mpr hb)
  have hgap := D.deficiencyGap_eq_neg_stoichRelationDimension_of_incidenceIndependent hi
  omega

end ReactionPartition
end Network
end CRNT

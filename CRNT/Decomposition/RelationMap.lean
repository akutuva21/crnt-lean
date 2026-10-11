import CRNT.Decomposition.RelationSpace

/-!
# The complex map on inter-block relations

Applying the complex map block by block sends incidence vectors to stoichiometric
vectors and preserves the relation condition.  Its kernel consists exactly of the
inter-block relations whose individual components lie in the block deficiency kernels.
The image criterion below records the obstruction to surjectivity in the global
deficiency space.
-/

namespace CRNT
namespace Network
namespace ReactionPartition

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S} {ι : Type} [DecidableEq ι] [Fintype ι]

/-- The complex map restricted from one block's incidence space to its stoichiometric
space. -/
noncomputable def blockComplexMap (D : ReactionPartition N ι) (i : ι) :
    D.blockIncidenceSubspace i →ₗ[ℝ] D.blockStoichSubspace i :=
  (N.complexMap.domRestrict (D.blockIncidenceSubspace i)).codRestrict
    (D.blockStoichSubspace i) (by
      intro z
      rw [← D.map_complexMap_blockIncidence i]
      exact ⟨z.1, z.2, rfl⟩)

/-- On each block, the restricted complex map is onto its stoichiometric subspace. -/
theorem blockComplexMap_surjective (D : ReactionPartition N ι) (i : ι) :
    Function.Surjective (D.blockComplexMap i) := by
  rintro ⟨y, hy⟩
  rw [← D.map_complexMap_blockIncidence i] at hy
  rcases hy with ⟨x, hx, hxy⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxy

/-- Apply the complex map independently to every reaction block. -/
noncomputable def blockComplexMapProduct (D : ReactionPartition N ι) :
    D.IncidenceBlockProduct →ₗ[ℝ] D.StoichBlockProduct where
  toFun z := fun i => D.blockComplexMap i (z i)
  map_add' z w := by
    funext i
    exact map_add (D.blockComplexMap i) (z i) (w i)
  map_smul' a z := by
    funext i
    exact map_smul (D.blockComplexMap i) a (z i)

@[simp] theorem blockComplexMapProduct_apply (D : ReactionPartition N ι)
    (z : D.IncidenceBlockProduct) (i : ι) :
    D.blockComplexMapProduct z i = D.blockComplexMap i (z i) := rfl

/-- The blockwise complex map commutes with summing the block contributions. -/
theorem blockComplexMapProduct_comp_incidenceBlockSumMap (D : ReactionPartition N ι) :
    D.stoichBlockSumMap.comp D.blockComplexMapProduct =
      N.complexMap.comp D.incidenceBlockSumMap := by
  apply LinearMap.ext
  intro z
  change (∑ i, (D.blockComplexMap i (z i) : S → ℝ)) =
    N.complexMap (∑ i, (z i : N.ComplexIdx → ℝ))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- The complex map induced on the inter-block relation spaces. -/
noncomputable def interblockRelationMap (D : ReactionPartition N ι) :
    D.incidenceRelationSpace →ₗ[ℝ] D.stoichRelationSpace :=
  (D.blockComplexMapProduct.domRestrict D.incidenceRelationSpace).codRestrict
    D.stoichRelationSpace (by
      intro z
      have hz : D.incidenceBlockSumMap z.1 = 0 := LinearMap.mem_ker.mp z.2
      change D.stoichBlockSumMap (D.blockComplexMapProduct z.1) = 0
      calc
        D.stoichBlockSumMap (D.blockComplexMapProduct z.1) =
            (D.stoichBlockSumMap.comp D.blockComplexMapProduct) z.1 := by
              rw [LinearMap.comp_apply]
        _ = (N.complexMap.comp D.incidenceBlockSumMap) z.1 := by
              rw [D.blockComplexMapProduct_comp_incidenceBlockSumMap]
        _ = N.complexMap (D.incidenceBlockSumMap z.1) := by
              rw [LinearMap.comp_apply]
        _ = 0 := by rw [hz, map_zero])

@[simp] theorem interblockRelationMap_apply_val (D : ReactionPartition N ι)
    (z : D.incidenceRelationSpace) :
    (D.interblockRelationMap z : D.StoichBlockProduct) =
      D.blockComplexMapProduct z.1 := by
  rfl

/-- The local deficiency space of block `i`, namely the kernel of its restricted
complex map. -/
noncomputable def blockDeficiencySubspace (D : ReactionPartition N ι) (i : ι) :
    Submodule ℝ (D.blockIncidenceSubspace i) :=
  LinearMap.ker (D.blockComplexMap i)

/-- Tuples of block incidence vectors that lie in every block's deficiency space. -/
noncomputable def blockDeficiencyProductSpace (D : ReactionPartition N ι) :
    Submodule ℝ D.IncidenceBlockProduct :=
  LinearMap.ker D.blockComplexMapProduct

theorem mem_blockDeficiencyProductSpace_iff (D : ReactionPartition N ι)
    (z : D.IncidenceBlockProduct) :
    z ∈ D.blockDeficiencyProductSpace ↔
      ∀ i, z i ∈ D.blockDeficiencySubspace i := by
  rw [blockDeficiencyProductSpace, LinearMap.mem_ker]
  constructor
  · intro hz i
    apply LinearMap.mem_ker.mpr
    have hi := congrArg (fun f : D.StoichBlockProduct => f i) hz
    change D.blockComplexMap i (z i) = 0
    exact hi
  · intro hz
    apply funext
    intro i
    change D.blockComplexMap i (z i) = 0
    exact LinearMap.mem_ker.mp (hz i)

/-- The global complex-space subspace obtained by summing vectors from the individual
block deficiency kernels. -/
noncomputable def blockDeficiencySumSubspace (D : ReactionPartition N ι) :
    Submodule ℝ (N.ComplexIdx → ℝ) :=
  LinearMap.range (D.incidenceBlockSumMap.domRestrict D.blockDeficiencyProductSpace)

theorem mem_blockDeficiencySumSubspace_iff (D : ReactionPartition N ι)
    (x : N.ComplexIdx → ℝ) :
    x ∈ D.blockDeficiencySumSubspace ↔
      ∃ z : D.IncidenceBlockProduct,
        (∀ i, z i ∈ D.blockDeficiencySubspace i) ∧
          D.incidenceBlockSumMap z = x := by
  rw [blockDeficiencySumSubspace, LinearMap.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z.1, (D.mem_blockDeficiencyProductSpace_iff z.1).1 z.2, ?_⟩
    exact hz
  · rintro ⟨z, hz, hx⟩
    refine ⟨⟨z, (D.mem_blockDeficiencyProductSpace_iff z).2 hz⟩, ?_⟩
    exact hx

/-- Summing block deficiency vectors always gives a global deficiency vector. -/
theorem blockDeficiencySumSubspace_le_deficiencySubspace (D : ReactionPartition N ι) :
    D.blockDeficiencySumSubspace ≤ N.deficiencySubspace := by
  rintro x ⟨z, rfl⟩
  apply Submodule.mem_inf.mpr
  constructor
  · apply LinearMap.mem_ker.mpr
    change N.complexMap (D.incidenceBlockSumMap z.1) = 0
    have hp : D.blockComplexMapProduct z.1 = 0 :=
      LinearMap.mem_ker.mp z.2
    have hsq := congrArg (fun f => f z.1)
      D.blockComplexMapProduct_comp_incidenceBlockSumMap
    change D.stoichBlockSumMap (D.blockComplexMapProduct z.1) =
      N.complexMap (D.incidenceBlockSumMap z.1) at hsq
    rw [← hsq, hp]
    simp
  · rw [← D.range_incidenceBlockSumMap]
    exact ⟨z.1, rfl⟩

/-- The global deficiency subspace is exactly the sum of the block deficiency kernels
if and only if every stoichiometric relation between blocks lifts to an incidence
relation between blocks.  Equivalently, the induced relation map is surjective. -/
theorem deficiencySubspace_eq_blockDeficiencySumSubspace_iff_interblockRelationMap_surjective
    (D : ReactionPartition N ι) :
    N.deficiencySubspace = D.blockDeficiencySumSubspace ↔
      Function.Surjective D.interblockRelationMap := by
  classical
  constructor
  · intro hEq w
    let z : D.IncidenceBlockProduct := fun i =>
      Classical.choose (D.blockComplexMap_surjective i (w.1 i))
    have hz : D.blockComplexMapProduct z = w.1 := by
      funext i
      change D.blockComplexMap i (z i) = w.1 i
      exact Classical.choose_spec (D.blockComplexMap_surjective i (w.1 i))
    have hcomplex : N.complexMap (D.incidenceBlockSumMap z) = 0 := by
      have hsq := congrArg (fun f => f z)
        D.blockComplexMapProduct_comp_incidenceBlockSumMap
      change D.stoichBlockSumMap (D.blockComplexMapProduct z) =
        N.complexMap (D.incidenceBlockSumMap z) at hsq
      rw [← hsq, hz]
      exact LinearMap.mem_ker.mp w.2
    have hrange : D.incidenceBlockSumMap z ∈ LinearMap.range N.incidenceMap := by
      rw [← D.range_incidenceBlockSumMap]
      exact ⟨z, rfl⟩
    have hglobal : D.incidenceBlockSumMap z ∈ N.deficiencySubspace :=
      Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr hcomplex, hrange⟩
    rw [hEq] at hglobal
    rcases (D.mem_blockDeficiencySumSubspace_iff _).mp hglobal with
      ⟨k, hkparts, hk_sum⟩
    have hpk : D.blockComplexMapProduct k = 0 := by
      apply funext
      intro i
      change D.blockComplexMap i (k i) = 0
      exact LinearMap.mem_ker.mp (hkparts i)
    have hrel : z - k ∈ D.incidenceRelationSpace := by
      change D.incidenceBlockSumMap (z - k) = 0
      calc
        D.incidenceBlockSumMap (z - k) =
            D.incidenceBlockSumMap z - D.incidenceBlockSumMap k :=
          map_sub D.incidenceBlockSumMap z k
        _ = 0 := by rw [hk_sum]; simp
    let r : D.incidenceRelationSpace := ⟨z - k, hrel⟩
    have hout : D.interblockRelationMap r = w := by
      apply Subtype.ext
      change D.blockComplexMapProduct (z - k) = w.1
      calc
        D.blockComplexMapProduct (z - k) =
            D.blockComplexMapProduct z - D.blockComplexMapProduct k :=
          map_sub D.blockComplexMapProduct z k
        _ = w.1 := by rw [hpk, sub_zero, hz]
    exact ⟨r, hout⟩
  · intro hsurj
    apply le_antisymm
    · intro x hx
      have hxker : N.complexMap x = 0 :=
        LinearMap.mem_ker.mp (Submodule.mem_inf.mp hx).1
      have hxrange : x ∈ LinearMap.range N.incidenceMap :=
        (Submodule.mem_inf.mp hx).2
      rw [← D.range_incidenceBlockSumMap] at hxrange
      rcases LinearMap.mem_range.mp hxrange with ⟨z, hz⟩
      have hsq := congrArg (fun f => f z)
        D.blockComplexMapProduct_comp_incidenceBlockSumMap
      change D.stoichBlockSumMap (D.blockComplexMapProduct z) =
        N.complexMap (D.incidenceBlockSumMap z) at hsq
      have hstoich : D.stoichBlockSumMap (D.blockComplexMapProduct z) = 0 := by
        rw [hsq, hz]
        exact hxker
      let w : D.stoichRelationSpace :=
        ⟨D.blockComplexMapProduct z, hstoich⟩
      obtain ⟨r, hr⟩ := hsurj w
      have hrval : D.blockComplexMapProduct r.1 = D.blockComplexMapProduct z := by
        have hval := congrArg Subtype.val hr
        change D.blockComplexMapProduct r.1 = D.blockComplexMapProduct z at hval
        exact hval
      have hsub : D.blockComplexMapProduct (z - r.1) = 0 := by
        calc
          D.blockComplexMapProduct (z - r.1) =
              D.blockComplexMapProduct z - D.blockComplexMapProduct r.1 :=
            map_sub D.blockComplexMapProduct z r.1
          _ = 0 := by rw [hrval]; simp
      have hparts : ∀ i, (z - r.1) i ∈ D.blockDeficiencySubspace i :=
        (D.mem_blockDeficiencyProductSpace_iff (z - r.1)).1
          (LinearMap.mem_ker.mpr hsub)
      have hsum : D.incidenceBlockSumMap (z - r.1) = x := by
        have hrzero : D.incidenceBlockSumMap r.1 = 0 :=
          LinearMap.mem_ker.mp r.2
        calc
          D.incidenceBlockSumMap (z - r.1) =
              D.incidenceBlockSumMap z - D.incidenceBlockSumMap r.1 :=
            map_sub D.incidenceBlockSumMap z r.1
          _ = x := by rw [hrzero, sub_zero, hz]
      exact (D.mem_blockDeficiencySumSubspace_iff x).2
        ⟨z - r.1, hparts, hsum⟩
    · exact D.blockDeficiencySumSubspace_le_deficiencySubspace

/-- A relation maps to zero precisely when every block component is killed by its own
restricted complex map.  Those component kernels are the block deficiency spaces. -/
theorem interblockRelationMap_mem_ker_iff (D : ReactionPartition N ι)
    (z : D.incidenceRelationSpace) :
    z ∈ LinearMap.ker D.interblockRelationMap ↔
      ∀ i, D.blockComplexMap i (z.1 i) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hz i
    have hprod : D.blockComplexMapProduct z.1 = 0 := by
      have hv := congrArg Subtype.val hz
      simpa [D.interblockRelationMap_apply_val] using hv
    have hi := congrArg (fun f : D.StoichBlockProduct => f i) hprod
    change D.blockComplexMap i (z.1 i) = 0
    simpa [blockComplexMapProduct_apply] using hi
  · intro hz
    apply Subtype.ext
    change D.blockComplexMapProduct z.1 = 0
    funext i
    change D.blockComplexMap i (z.1 i) = 0
    exact hz i

/-- Injectivity of the relation map is equivalent to the absence of nonzero inter-block
relations assembled from the individual block deficiency kernels. -/
theorem interblockRelationMap_injective_iff_blockDeficiencyRelations_trivial
    (D : ReactionPartition N ι) :
    Function.Injective D.interblockRelationMap ↔
      ∀ z : D.incidenceRelationSpace,
        (∀ i, D.blockComplexMap i (z.1 i) = 0) → z = 0 := by
  constructor
  · intro h z hz
    have hz' : z ∈ LinearMap.ker D.interblockRelationMap :=
      (D.interblockRelationMap_mem_ker_iff z).2 hz
    apply h
    simpa using (LinearMap.mem_ker.mp hz')
  · intro h x y hxy
    have hz : x - y ∈ LinearMap.ker D.interblockRelationMap := by
      rw [LinearMap.mem_ker]
      calc
        D.interblockRelationMap (x - y) =
            D.interblockRelationMap x - D.interblockRelationMap y :=
          map_sub D.interblockRelationMap x y
        _ = 0 := by rw [sub_eq_zero.mpr hxy]
    have hparts := (D.interblockRelationMap_mem_ker_iff (x - y)).1 hz
    have hzero : x - y = 0 := h (x - y) hparts
    exact sub_eq_zero.mp hzero

end ReactionPartition
end Network
end CRNT

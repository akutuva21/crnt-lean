import CRNT.Dynamics.ComplexBalanceCycleDecomposition
import CRNT.Dynamics.ToricInclusion

/-!
# Toric-field inclusion on stoichiometric space

This module restricts the source-order toric differential inclusion to the stoichiometric
subspace. It provides an intrinsic finite cone family covering that subspace and places the
complex-balanced mass-action vector field in the toric field at the projected relative-log
state. These are local ingredients for a zero-separating-surface argument.
-/

open scoped InnerProductSpace

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

private theorem massActionVectorField_stoichForFan (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : N.massActionVectorField κ x ∈ N.stoichSubspace := by
  rw [N.massActionVectorField_eq_sum κ x]
  exact Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)

/-- The finite source-order chamber family, reoriented and restricted to the stoichiometric space.
Every cone is the preimage of an ambient negative source-order cone under the subspace inclusion. -/
noncomputable def relativeSourceOrderNegativeConeStoichFan (N : Network S) :
    CRNT.Fan N.euclideanStoichSubspace := by
  classical
  exact N.relativeSourceOrderNegativeConeFamily.image fun C =>
    C.comap N.euclideanStoichSubspace.subtypeL

/-- The negative chamber selected by a projected relative logarithm occurs in the restricted fan. -/
theorem relativeSourceOrderNegativeConeInStoich_mem_fan (N : Network S) (w : S → ℝ) :
    (N.relativeSourceOrderNegativeCone w).comap N.euclideanStoichSubspace.subtypeL ∈
      N.relativeSourceOrderNegativeConeStoichFan := by
  classical
  rw [relativeSourceOrderNegativeConeStoichFan]
  apply Finset.mem_image.mpr
  refine ⟨N.relativeSourceOrderNegativeCone w, ?_, rfl⟩
  exact N.relativeSourceOrderNegativeCone_mem_family w

/-- The restricted negative source-order cones cover the whole stoichiometric subspace. -/
theorem exists_relativeSourceOrderNegativeConeStoichFan_mem (N : Network S)
    (z : N.euclideanStoichSubspace) :
    ∃ C ∈ N.relativeSourceOrderNegativeConeStoichFan, z ∈ C := by
  classical
  have hzstoich : CRNT.toEuclid.symm z.1 ∈ N.stoichSubspace := by
    have hzproperty := z.property
    change z.1 ∈ Submodule.map CRNT.toEuclid.toLinearMap N.stoichSubspace at hzproperty
    rw [Submodule.mem_map] at hzproperty
    rcases hzproperty with ⟨u, hu, huz⟩
    rw [← huz]
    simpa using hu
  obtain ⟨C, hC, hzC⟩ := N.exists_relativeSourceOrderNegativeConeFamily_mem hzstoich
  refine ⟨C.comap N.euclideanStoichSubspace.subtypeL, ?_, ?_⟩
  · rw [relativeSourceOrderNegativeConeStoichFan]
    exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
  · exact ProperCone.mem_comap.mpr hzC

/-- The complex-balanced mass-action vector field lies in the intrinsic toric field at the
negative projected relative-log state. -/
theorem massActionVectorField_mem_toricField_relativeSourceOrderNegativeConeStoichFan
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {δ : ℝ} (hδ : 0 < δ) :
    let u : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
    let w := N.relativeLogStoichProjection u
    ⟨CRNT.toEuclid (N.massActionVectorField κ x), by
      rw [Network.euclideanStoichSubspace, Submodule.mem_map]
      exact ⟨N.massActionVectorField κ x,
        N.massActionVectorField_stoichForFan κ x, rfl⟩⟩ ∈
      CRNT.toricField N.relativeSourceOrderNegativeConeStoichFan δ
        (-⟨CRNT.toEuclid w, by
          rw [Network.euclideanStoichSubspace, Submodule.mem_map]
          exact ⟨w, N.relativeLogStoichProjection_mem u, rfl⟩⟩) := by
  dsimp
  let u : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
  let w : S → ℝ := N.relativeLogStoichProjection u
  have hfieldStoich : N.massActionVectorField κ x ∈ N.stoichSubspace :=
    N.massActionVectorField_stoichForFan κ x
  let v : N.euclideanStoichSubspace := ⟨CRNT.toEuclid (N.massActionVectorField κ x), by
    rw [Network.euclideanStoichSubspace, Submodule.mem_map]
    exact ⟨N.massActionVectorField κ x, hfieldStoich, rfl⟩⟩
  have hprojStoich : w ∈ N.stoichSubspace := N.relativeLogStoichProjection_mem u
  let X : N.euclideanStoichSubspace := ⟨CRNT.toEuclid w, by
    rw [Network.euclideanStoichSubspace, Submodule.mem_map]
    exact ⟨w, hprojStoich, rfl⟩⟩
  let Cambient : ProperCone ℝ (EuclideanSpace ℝ S) := N.relativeSourceOrderNegativeCone w
  let C : ProperCone ℝ N.euclideanStoichSubspace :=
    Cambient.comap N.euclideanStoichSubspace.subtypeL
  have hC : C ∈ N.relativeSourceOrderNegativeConeStoichFan :=
    N.relativeSourceOrderNegativeConeInStoich_mem_fan w
  have hX : -X ∈ C := by
    change (N.euclideanStoichSubspace.subtypeL (-X)) ∈ Cambient
    have hstate : -CRNT.toEuclid w ∈ Cambient :=
      N.negativeRelativeLogStoichProjection_mem_relativeSourceOrderNegativeCone u
    simpa [X] using hstate
  have hdist : Metric.infDist (-X) (C : Set N.euclideanStoichSubspace) = 0 :=
    Metric.infDist_zero_of_mem hX
  have hnear : Metric.infDist (-X) (C : Set N.euclideanStoichSubspace) < δ := by
    rw [hdist]
    exact hδ
  have hpolar := N.massActionVectorField_mem_polar_relativeSourceOrderStoichProjection
    κ hx hxs hcb
  have hdual : v ∈ coneDual (C : Set N.euclideanStoichSubspace) := by
    rw [mem_coneDual]
    intro z hz
    have hzamb : z.1 ∈ Cambient := by
      change z ∈ C at hz
      exact ProperCone.mem_comap.mp hz
    have hzpos : -z.1 ∈ N.relativeSourceOrderStoichCone w := by
      change z.1 ∈ N.relativeSourceOrderNegativeCone w at hzamb
      exact (N.mem_relativeSourceOrderNegativeCone w z.1).mp hzamb
    have hle : ⟪-z.1, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ ≤ 0 := by
      rw [mem_polarCone] at hpolar
      exact hpolar hzpos
    have hinner : ⟪z, v⟫_ℝ = -⟪-z.1, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ := by
      simp [v]
    rw [hinner]
    exact neg_nonneg.mpr hle
  have htoric := CRNT.coneDual_le_toricField hC hnear hdual
  simpa [v, X, C, Cambient] using htoric

/-- The relative-log toric field on concentrations.  Its state is a positive concentration
vector, while its admissible velocities are the image in concentration coordinates of the
intrinsic stoichiometric toric field.  At nonpositive states the field is unrestricted so that
ODE-selection lemmas can be stated without global positivity side conditions. -/
noncomputable def relativeSourceOrderToricInclusionField (N : Network S)
    (xstar : Concentration S) (δ : ℝ) :
    DifferentialInclusion.Field (Concentration S) := by
  classical
  exact fun x =>
    if x.Positive then
      let u : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
      let w := N.relativeLogStoichProjection u
      let X : N.euclideanStoichSubspace := ⟨CRNT.toEuclid w, by
        rw [Network.euclideanStoichSubspace, Submodule.mem_map]
        exact ⟨w, N.relativeLogStoichProjection_mem u, rfl⟩⟩
      (fun v : N.euclideanStoichSubspace => CRNT.toEuclid.symm v.1) ''
        (CRNT.toricField N.relativeSourceOrderNegativeConeStoichFan δ (-X) :
          Set N.euclideanStoichSubspace)
    else Set.univ

/-- **Mass-action selects the relative-log toric field.** For a positive complex-balanced
equilibrium `xstar`, the genuine mass-action velocity is admitted at every concentration.  At
positive states this is the intrinsic polar-cone inclusion; at other states the field is
unrestricted. -/
theorem massActionVectorField_mem_relativeSourceOrderToricInclusionField
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) {δ : ℝ} (hδ : 0 < δ)
    (x : Concentration S) :
    N.massActionVectorField κ x ∈
      N.relativeSourceOrderToricInclusionField xstar δ x := by
  classical
  unfold relativeSourceOrderToricInclusionField
  by_cases hx : x.Positive
  · simp only [hx]
    let u : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
    let w := N.relativeLogStoichProjection u
    let X : N.euclideanStoichSubspace := ⟨CRNT.toEuclid w, by
      rw [Network.euclideanStoichSubspace, Submodule.mem_map]
      exact ⟨w, N.relativeLogStoichProjection_mem u, rfl⟩⟩
    let v : N.euclideanStoichSubspace := ⟨CRNT.toEuclid (N.massActionVectorField κ x), by
      rw [Network.euclideanStoichSubspace, Submodule.mem_map]
      exact ⟨N.massActionVectorField κ x,
        N.massActionVectorField_stoichForFan κ x, rfl⟩⟩
    have hv := N.massActionVectorField_mem_toricField_relativeSourceOrderNegativeConeStoichFan
      κ hx hxs hcb hδ
    have hvX : v ∈ CRNT.toricField N.relativeSourceOrderNegativeConeStoichFan δ (-X) := by
      simpa [v, X, u, w] using hv
    simpa [v] using Set.mem_image_of_mem
      (fun q : N.euclideanStoichSubspace => CRNT.toEuclid.symm q.1) hvX
  · simp [hx]

/-- A genuine mass-action trajectory is a solution of the relative-log toric inclusion. -/
theorem isInclusionSolution_massAction_relativeSourceOrder
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) {δ : ℝ} (hδ : 0 < δ)
    {γ : ℝ → Concentration S}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t) :
    DifferentialInclusion.IsInclusionSolution
      (fun x => N.relativeSourceOrderToricInclusionField xstar δ x) γ := by
  apply DifferentialInclusion.IsInclusionSolution.of_ode hderiv
  intro x
  exact N.massActionVectorField_mem_relativeSourceOrderToricInclusionField
    κ hxs hcb hδ x


private theorem euclideanStoichSubspace_subtypeL_isClosedEmbedding (N : Network S) :
    Topology.IsClosedEmbedding N.euclideanStoichSubspace.subtypeL := by
  apply Submodule.isClosedEmbedding_subtypeL
  exact Submodule.closed_of_finiteDimensional N.euclideanStoichSubspace

private theorem properMap_subtype_eq_pointedMap (N : Network S)
    (C : ProperCone ℝ N.euclideanStoichSubspace) :
    ((ProperCone.map N.euclideanStoichSubspace.subtypeL C :
      ProperCone ℝ (EuclideanSpace ℝ S)) : PointedCone ℝ (EuclideanSpace ℝ S)) =
      PointedCone.map N.euclideanStoichSubspace.subtypeL.toLinearMap
        (C : PointedCone ℝ N.euclideanStoichSubspace) := by
  apply PointedCone.ext
  intro x
  change x ∈ ProperCone.map N.euclideanStoichSubspace.subtypeL C ↔
    x ∈ PointedCone.map N.euclideanStoichSubspace.subtypeL.toLinearMap
      (C : PointedCone ℝ N.euclideanStoichSubspace)
  rw [ProperCone.mem_map]
  have hclosed : IsClosed
      (N.euclideanStoichSubspace.subtypeL '' (C : Set N.euclideanStoichSubspace)) :=
    (N.euclideanStoichSubspace_subtypeL_isClosedEmbedding.isClosed_iff_image_isClosed).mp
      C.isClosed
  change x ∈ closure
      (N.euclideanStoichSubspace.subtypeL '' (C : Set N.euclideanStoichSubspace)) ↔ _
  rw [hclosed.closure_eq, PointedCone.mem_map]
  simp only [Set.mem_image]
  exact Iff.rfl

private theorem map_comap_negativeStoichFamily (N : Network S)
    {C : ProperCone ℝ (EuclideanSpace ℝ S)}
    (hC : C ∈ N.relativeSourceOrderNegativeConeFamily) :
    ProperCone.map N.euclideanStoichSubspace.subtypeL
        (C.comap N.euclideanStoichSubspace.subtypeL) = C := by
  have hV : ∀ x : EuclideanSpace ℝ S, x ∈ C →
      x ∈ N.euclideanStoichSubspace := by
    intro x hx
    rw [Network.euclideanStoichSubspace, Submodule.mem_map]
    refine ⟨CRNT.toEuclid.symm x,
      N.stoich_of_mem_relativeSourceOrderNegativeConeFamily hC hx, ?_⟩
    exact CRNT.toEuclid.apply_symm_apply x
  have himage :
      N.euclideanStoichSubspace.subtypeL ''
          (C.comap N.euclideanStoichSubspace.subtypeL :
            Set N.euclideanStoichSubspace) = (C : Set (EuclideanSpace ℝ S)) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ProperCone.mem_comap.mp hz
    · intro hx
      refine ⟨⟨x, hV x hx⟩, ProperCone.mem_comap.mpr hx, rfl⟩
  apply ProperCone.ext
  intro x
  rw [ProperCone.mem_map]
  have hclosed : IsClosed
      (N.euclideanStoichSubspace.subtypeL ''
        (C.comap N.euclideanStoichSubspace.subtypeL :
          Set N.euclideanStoichSubspace)) := by
    rw [himage]
    exact C.isClosed
  change x ∈ closure
      (N.euclideanStoichSubspace.subtypeL ''
        (C.comap N.euclideanStoichSubspace.subtypeL :
          Set N.euclideanStoichSubspace)) ↔ _
  rw [hclosed.closure_eq, himage]
  rfl

private theorem comap_map_subtype_eq (N : Network S)
    (C : ProperCone ℝ N.euclideanStoichSubspace) :
    (ProperCone.map N.euclideanStoichSubspace.subtypeL C).comap
        N.euclideanStoichSubspace.subtypeL = C := by
  have hmap := N.properMap_subtype_eq_pointedMap C
  have hinj : Function.Injective
      N.euclideanStoichSubspace.subtypeL.toLinearMap := by
    intro x y h
    exact Subtype.ext h
  apply ProperCone.ext
  intro x
  constructor
  · intro hx
    have hproper : N.euclideanStoichSubspace.subtypeL x ∈
        (ProperCone.map N.euclideanStoichSubspace.subtypeL C :
          PointedCone ℝ (EuclideanSpace ℝ S)) := ProperCone.mem_comap.mp hx
    have hx' : N.euclideanStoichSubspace.subtypeL x ∈
        PointedCone.map N.euclideanStoichSubspace.subtypeL.toLinearMap
          (C : PointedCone ℝ N.euclideanStoichSubspace) := by
      simpa only [hmap] using hproper
    obtain ⟨y, hy, hxy⟩ := PointedCone.mem_map.mp hx'
    have : y = x := hinj hxy
    simpa [this] using hy
  · intro hx
    apply ProperCone.mem_comap.mpr
    have hx' : N.euclideanStoichSubspace.subtypeL x ∈
        PointedCone.map N.euclideanStoichSubspace.subtypeL.toLinearMap
          (C : PointedCone ℝ N.euclideanStoichSubspace) :=
      PointedCone.mem_map.mpr ⟨x, hx, rfl⟩
    have hproper : N.euclideanStoichSubspace.subtypeL x ∈
        (ProperCone.map N.euclideanStoichSubspace.subtypeL C :
          PointedCone ℝ (EuclideanSpace ℝ S)) := by
      simpa only [hmap] using hx'
    exact ProperCone.mem_comap.mpr hproper

private theorem comap_inf_stoich (N : Network S)
    (C D : ProperCone ℝ (EuclideanSpace ℝ S)) :
    (C ⊓ D).comap N.euclideanStoichSubspace.subtypeL =
      C.comap N.euclideanStoichSubspace.subtypeL ⊓
        D.comap N.euclideanStoichSubspace.subtypeL := by
  apply ProperCone.ext
  intro z
  simp

/-- Every exposed face of a cone in the intrinsic negative source-order fan is again in the fan. -/
theorem relativeSourceOrderNegativeConeStoichFan_faces_mem (N : Network S)
    {C : ProperCone ℝ N.euclideanStoichSubspace}
    (hC : C ∈ N.relativeSourceOrderNegativeConeStoichFan)
    {D : ProperCone ℝ N.euclideanStoichSubspace}
    (hface : CRNT.IsExposedFaceOf D C) :
    D ∈ N.relativeSourceOrderNegativeConeStoichFan := by
  classical
  rw [relativeSourceOrderNegativeConeStoichFan] at hC ⊢
  obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hC
  have hface' : PointedCone.IsFaceOf (D : PointedCone ℝ N.euclideanStoichSubspace)
      (C₀.comap N.euclideanStoichSubspace.subtypeL :
        PointedCone ℝ N.euclideanStoichSubspace) :=
    CRNT.isExposedFaceOf_isFaceOf hface
  have hinj : Function.Injective
      N.euclideanStoichSubspace.subtypeL.toLinearMap := by
    intro x y h
    exact Subtype.ext h
  have hmapped := PointedCone.IsFaceOf.map
    N.euclideanStoichSubspace.subtypeL.toLinearMap hinj hface'
  have hmapped' :
      ((ProperCone.map N.euclideanStoichSubspace.subtypeL D :
        ProperCone ℝ (EuclideanSpace ℝ S)) :
          PointedCone ℝ (EuclideanSpace ℝ S)).IsFaceOf C₀ := by
    rw [← N.map_comap_negativeStoichFamily hC₀,
      N.properMap_subtype_eq_pointedMap]
    simpa only [N.properMap_subtype_eq_pointedMap] using hmapped
  have hD₀ := N.relativeSourceOrderNegativeConeFamily_face_mem hC₀ hmapped'
  apply Finset.mem_image.mpr
  refine ⟨ProperCone.map N.euclideanStoichSubspace.subtypeL D, hD₀, ?_⟩
  exact N.comap_map_subtype_eq D

/-- Intersections of cones in the intrinsic negative source-order family belong to the family. -/
theorem relativeSourceOrderNegativeConeStoichFan_inter_mem (N : Network S)
    {C D : ProperCone ℝ N.euclideanStoichSubspace}
    (hC : C ∈ N.relativeSourceOrderNegativeConeStoichFan)
    (hD : D ∈ N.relativeSourceOrderNegativeConeStoichFan) :
    C ⊓ D ∈ N.relativeSourceOrderNegativeConeStoichFan := by
  classical
  rw [relativeSourceOrderNegativeConeStoichFan] at hC hD ⊢
  obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨D₀, hD₀, rfl⟩ := Finset.mem_image.mp hD
  have hCD := N.relativeSourceOrderNegativeConeFamily_inter_mem hC₀ hD₀
  refine Finset.mem_image.mpr ⟨C₀ ⊓ D₀, hCD, ?_⟩
  exact (N.comap_inf_stoich C₀ D₀).symm

/-- **The intrinsic negative source-order family is a finite polyhedral fan.** Its exposed faces and
intersections come from the ambient source-order fan; coverage follows by restricting the ambient
cover to the stoichiometric subspace. -/
theorem relativeSourceOrderNegativeConeStoichFan_isPolyhedralFan (N : Network S) :
    CRNT.IsPolyhedralFan N.relativeSourceOrderNegativeConeStoichFan := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro C hC D hface
    exact N.relativeSourceOrderNegativeConeStoichFan_faces_mem hC hface
  · intro C hC D hD
    refine ⟨C ⊓ D, N.relativeSourceOrderNegativeConeStoichFan_inter_mem hC hD, ?_⟩
    ext z
    simp
  · ext z
    simp only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨C, hC, hz⟩ := N.exists_relativeSourceOrderNegativeConeStoichFan_mem z
      exact ⟨C, hC, hz⟩

end Network
end CRNT

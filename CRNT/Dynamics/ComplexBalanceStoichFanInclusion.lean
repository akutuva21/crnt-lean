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

end Network
end CRNT

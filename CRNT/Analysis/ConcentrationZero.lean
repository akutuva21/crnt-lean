import CRNT.Analysis.BrouwerZero
import CRNT.Kinetics.Concentration
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Brouwer zero-of-field corollary in concentration space

The Euclidean Brouwer zero-of-field corollary `exists_zero_of_displacement_mapsTo` transported
along the coordinate isomorphism `Concentration S ≃L[ℝ] EuclideanSpace ℝ (Fin (Fintype.card S))`:
a continuous vector field on a nonempty compact convex set of concentrations whose inward
displacement `x ↦ x - v x` preserves that set has a zero there.

The inward-displacement hypothesis is genuine: it is the concentration-space form of the inwardness
condition under which Brouwer's theorem produces a fixed point of the displacement map, hence a zero
of the field.

Depends on: `CRNT.Analysis.BrouwerZero`,
`CRNT.Kinetics.Concentration`.
-/

namespace CRNT.Analysis

open CRNT

/-- Reindexing CLE from concentration space to Euclidean space. -/
noncomputable def concEquiv (S : Type) [Fintype S] :
    Concentration S ≃L[ℝ] EuclideanSpace ℝ (Fin (Fintype.card S)) :=
  (LinearEquiv.piCongrLeft ℝ (fun _ : Fin (Fintype.card S) => ℝ)
        (Fintype.equivFin S)).toContinuousLinearEquiv.trans
    (EuclideanSpace.equiv (Fin (Fintype.card S)) ℝ).symm

/-- Brouwer equilibrium in concentration space: a continuous vector field whose inward
displacement preserves a nonempty compact convex set of concentrations has a zero there. -/
theorem exists_zero_of_displacement_mapsTo_concentration {S : Type} [Fintype S]
    {K : Set (Concentration S)} (hne : K.Nonempty) (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (v : Concentration S → Concentration S) (hv : ContinuousOn v K)
    (hmaps : Set.MapsTo (fun x => x - v x) K K) : ∃ x ∈ K, v x = 0 := by
  set Φ := concEquiv S with hΦ
  set K' := Φ '' K with hK'
  -- Transport the hypotheses on `K` to `K'`.
  have hne' : K'.Nonempty := hne.image Φ
  have hconv' : Convex ℝ K' := hconv.linear_image Φ.toLinearMap
  have hcomp' : IsCompact K' := hcomp.image Φ.continuous
  -- The conjugated vector field on `K'`.
  set w := fun y => Φ (v (Φ.symm y)) with hw
  have hw_cont : ContinuousOn w K' := by
    have hcomp_cont : ContinuousOn (fun y => v (Φ.symm y)) K' := by
      have hsymm : ContinuousOn (fun y : EuclideanSpace ℝ (Fin (Fintype.card S)) => Φ.symm y) K' :=
        Φ.symm.continuous.continuousOn
      have hmaps_symm : Set.MapsTo (fun y => Φ.symm y) K' K := by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        simp only [Φ.symm_apply_apply]
        exact hx
      exact hv.comp hsymm hmaps_symm
    exact Φ.continuous.comp_continuousOn hcomp_cont
  -- The conjugated displacement maps `K'` into itself.
  have hmaps' : Set.MapsTo (fun y => y - w y) K' K' := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxsymm : Φ.symm (Φ x) = x := Φ.symm_apply_apply x
    have : (fun y => y - w y) (Φ x) = Φ (x - v x) := by
      simp only [hw, hxsymm, map_sub]
    rw [this]
    exact ⟨x - v x, hmaps hx, rfl⟩
  -- Apply the Euclidean corollary.
  obtain ⟨y, hyK', hwy⟩ :=
    exists_zero_of_displacement_mapsTo (K := K') hne' hconv' hcomp' w hw_cont hmaps'
  -- Pull the zero back to concentration space.
  rcases hyK' with ⟨x, hx, rfl⟩
  refine ⟨x, hx, ?_⟩
  have hΦvx : Φ (v x) = 0 := by
    have h := hwy
    simp only [hw, Φ.symm_apply_apply] at h
    exact h
  exact Φ.map_eq_zero_iff.mp hΦvx

end CRNT.Analysis

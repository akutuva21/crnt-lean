import CRNT.Analysis.ConcentrationZero
import CRNT.Dynamics.MassActionField
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Brouwer normal-cone variational inequality for the mass-action field

The Stampacchia variational inequality for the mass-action vector field on a nonempty compact
convex set of concentrations. Brouwer's fixed-point theorem, in the projected form
`CRNT.Analysis.exists_projected_fixedPoint`, produces a point `x ∈ K` at which the field `F x`
lies in the outward normal cone of `K`: `0 ≤ ∑ s, F x s · (w s − x s)` for every `w ∈ K`. The
field is `C^∞`, hence continuous, so this holds with no further hypothesis on `K`.

The proof transports `K` along the coordinate isometry
`concEquiv : Concentration S ≃L[ℝ] EuclideanSpace ℝ (Fin (Fintype.card S))`, applies the Euclidean
projected fixed-point theorem to the conjugated field, and pulls the inequality back, rewriting the
`EuclideanSpace` inner product as the coordinate sum over species.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.ConcentrationZero`,
`CRNT.Dynamics.MassActionField`.
-/

namespace CRNT.Network

open CRNT
open scoped RealInnerProductSpace

/-- Coordinatewise value of the reindexing isometry: `concEquiv` sends a concentration `a` to the
Euclidean vector whose `i`-th coordinate is `a` at the species `(Fintype.equivFin S).symm i`. -/
private theorem concEquiv_apply {S : Type} [Fintype S] (a : Concentration S)
    (i : Fin (Fintype.card S)) :
    CRNT.Analysis.concEquiv S a i = a ((Fintype.equivFin S).symm i) := by
  simp only [CRNT.Analysis.concEquiv]
  conv_lhs =>
    rw [show (i : Fin (Fintype.card S))
          = (Fintype.equivFin S) ((Fintype.equivFin S).symm i) from
        (Equiv.apply_symm_apply _ _).symm]
  simp [LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']

/-- The Euclidean inner product of two reindexed concentrations is their coordinate sum over
species. -/
private theorem concEquiv_inner {S : Type} [Fintype S] (a b : Concentration S) :
    (⟪CRNT.Analysis.concEquiv S a, CRNT.Analysis.concEquiv S b⟫ : ℝ) = ∑ s, a s * b s := by
  rw [PiLp.inner_apply]
  have hstep : ∀ i, (⟪CRNT.Analysis.concEquiv S a i, CRNT.Analysis.concEquiv S b i⟫ : ℝ)
      = a ((Fintype.equivFin S).symm i) * b ((Fintype.equivFin S).symm i) := by
    intro i
    rw [concEquiv_apply, concEquiv_apply, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  exact Equiv.sum_comp (Fintype.equivFin S).symm (fun s => a s * b s)

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Stampacchia variational inequality for mass action.** On a nonempty compact convex set of
concentrations the mass-action field satisfies a normal-cone variational inequality at some point:
there is `x ∈ K` with `F x` in the outward normal cone of `K` at `x`, that is
`0 ≤ ∑ s, F x s · (w s − x s)` for every `w ∈ K`. This is Brouwer's fixed-point theorem in its
projected (Stampacchia) form applied to the continuous mass-action field. -/
theorem exists_steadyState_normalCone_of_compact (N : Network S) (κ : N.RateConstants)
    {K : Set (Concentration S)} (hne : K.Nonempty) (hconv : Convex ℝ K) (hcomp : IsCompact K) :
    ∃ x ∈ K, ∀ w ∈ K, 0 ≤ ∑ s, N.massActionVectorField κ x s * (w s - x s) := by
  set Φ := CRNT.Analysis.concEquiv S with hΦ
  set F := N.massActionVectorField κ with hF
  set K' := Φ '' K with hK'
  -- Transport the hypotheses on `K` to `K'`.
  have hne' : K'.Nonempty := hne.image Φ
  have hconv' : Convex ℝ K' := hconv.linear_image Φ.toLinearMap
  have hcomp' : IsCompact K' := hcomp.image Φ.continuous
  -- The conjugated field on `K'`.
  set v := fun y => Φ (F (Φ.symm y)) with hv
  have hv_cont : ContinuousOn v K' :=
    Φ.continuous.comp_continuousOn
      (((massActionVectorField_contDiff N κ (n := 1)).continuous).comp Φ.symm.continuous).continuousOn
  -- Apply the Euclidean projected fixed-point theorem.
  obtain ⟨y, hyK', _, hvar⟩ := CRNT.Analysis.exists_projected_fixedPoint hne' hconv' hcomp' v hv_cont
  -- Pull the fixed point back to a concentration.
  rcases hyK' with ⟨x, hx, rfl⟩
  refine ⟨x, hx, ?_⟩
  intro w₀ hw₀
  -- The conjugated field at `Φ x` is `Φ (F x)`.
  have hvΦx : v (Φ x) = Φ (F x) := by simp only [hv, Φ.symm_apply_apply]
  -- Specialize the variational inequality at `w' = Φ w₀ ∈ K'`.
  have h := hvar (Φ w₀) ⟨w₀, hw₀, rfl⟩
  rw [hvΦx] at h
  -- Translate the Euclidean inner product into the coordinate sum over species.
  have hsub : Φ w₀ - Φ x = Φ (w₀ - x) := (map_sub Φ w₀ x).symm
  rw [hsub, concEquiv_inner] at h
  simpa only [Pi.sub_apply] using h

end CRNT.Network

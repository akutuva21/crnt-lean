import CRNT.Decision.StoichBasisQ
import CRNT.Dynamics.Hurwitz3Matrix

/-!
# A rational Hopf-boundary proximity scalar

For a `3 × 3` matrix the cubic Routh–Hurwitz Hopf boundary is the vanishing of the penultimate
Hurwitz determinant `det − trace · c₂Fin3` (the combination `boundaryFn` of the worked Hopf network
example). This module gives its exact rational evaluation `hopfBoundaryQ` on a `Matrix (Fin 3) (Fin
3) ℚ`, the network-level scalar `hopfBoundaryMarginQ` obtained from the rational mass-action Jacobian
at the all-ones concentration with unit rate constants, and the cast bridges to the genuine real
combination (`hopfBoundaryQ_cast`, `hopfBoundaryMarginQ_cast`). The scalar vanishes exactly on the
cubic Hopf boundary, so it is a graded proximity-to-oscillation signal at one chart point; it is not a
bifurcation verdict (the limit-cycle conclusion needs center-manifold theory).

This follows the degree-3 Routh–Hurwitz combination of Liénard and Chipart and the matrix invariants
of `Matrix.charpoly_fin_three`.

Depends on: `CRNT.Decision.StoichBasisQ`,
`CRNT.Dynamics.Hurwitz3Matrix`.
-/

namespace CRNT

open Matrix

/-- The `3 × 3` Routh–Hurwitz Hopf-boundary combination over ℚ: `det − trace · c₂Fin3`, the
penultimate Hurwitz determinant whose vanishing marks the cubic Hopf boundary. -/
def hopfBoundaryQ (M : Matrix (Fin 3) (Fin 3) ℚ) : ℚ :=
  M.det - M.trace * M.c₂Fin3

/-- The real cast of `hopfBoundaryQ` is the real Hopf-boundary combination of the cast matrix. -/
theorem hopfBoundaryQ_cast (M : Matrix (Fin 3) (Fin 3) ℚ) :
    ((hopfBoundaryQ M : ℚ) : ℝ)
      = (M.map (Rat.castHom ℝ)).det - (M.map (Rat.castHom ℝ)).trace
          * (M.map (Rat.castHom ℝ)).c₂Fin3 := by
  have htr : (M.map (Rat.castHom ℝ)).trace = (M.trace : ℝ) :=
    (AddMonoidHom.map_trace (Rat.castHom ℝ) M).symm
  have hdet : (M.map (Rat.castHom ℝ)).det = (M.det : ℝ) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  have hc₂ : (M.map (Rat.castHom ℝ)).c₂Fin3 = (M.c₂Fin3 : ℝ) := by
    simp only [c₂Fin3, Matrix.map_apply, Rat.coe_castHom]
    push_cast
    ring
  rw [hopfBoundaryQ, htr, hdet, hc₂]
  push_cast
  ring

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The network's `3 × 3` Hopf-boundary scalar at the all-ones concentration with unit rate
constants: `det − trace · c₂Fin3` of the rational mass-action Jacobian. Zero exactly on the cubic
Hopf boundary — a graded proximity-to-oscillation signal at one chart point. -/
def hopfBoundaryMarginQ (N : Network (Fin 3)) : ℚ :=
  hopfBoundaryQ (N.massActionJacobianQ (fun _ => 1) (fun _ => 1))

/-- The real cast of `hopfBoundaryMarginQ` is the real Hopf-boundary combination of the genuine
mass-action Jacobian at the all-ones concentration, for any unit rate constants. -/
theorem hopfBoundaryMarginQ_cast (N : Network (Fin 3)) (κ : N.RateConstants)
    (hk : ∀ r, κ.k r = 1) :
    ((N.hopfBoundaryMarginQ : ℚ) : ℝ)
      = (N.massActionJacobian κ (fun _ => 1)).det
        - (N.massActionJacobian κ (fun _ => 1)).trace
          * (N.massActionJacobian κ (fun _ => 1)).c₂Fin3 := by
  have hk' : ∀ r, κ.k r = ((1 : ℚ) : ℝ) := by intro r; rw [hk r]; norm_num
  rw [hopfBoundaryMarginQ, hopfBoundaryQ_cast,
    N.massActionJacobianQ_map_eq (fun _ => 1) (fun _ => 1) κ hk']
  norm_num

end Network

end CRNT

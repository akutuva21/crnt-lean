import CRNT.Decision.StoichBasisQ
import CRNT.Dynamics.HurwitzGershgorin

/-!
# A rational Gershgorin local-stability spectral margin

Gershgorin's circle theorem read as a stability criterion gives a dimension-free sufficient Hurwitz
test: a real matrix whose every row diagonal entry is negative and strictly dominates the off-diagonal
absolute-value sum has all eigenvalues in the open left half-plane. This module records the exact
rational margin of that test — `gershgorinMarginQ`, the worst row value `max_k ( M k k + ∑_{j≠k} |M k
j| )` over `ℚ` — and the network-level scalar `gershgorinStabilityMarginQ` obtained from the rational
mass-action Jacobian at the all-ones concentration with unit rate constants. The margin is negative
exactly when the row diagonal-dominance test fires, so it certifies local stability there
(`gershgorinStabilityMarginQ_hurwitz`); its magnitude grades the stability robustness, and unlike the
cubic Routh–Hurwitz Hopf-boundary scalar it is defined in every dimension. It is a one-directional
sufficient stability margin, not a full spectral verdict: it can fail for matrices that are
nonetheless Hurwitz.

This is the classical diagonal-dominance stability test of Gershgorin's circle theorem, graded as an
exact rational scalar.

Depends on: `CRNT.Decision.StoichBasisQ`,
`CRNT.Dynamics.HurwitzGershgorin`.
-/

namespace CRNT

open Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The Gershgorin row value of row `k` over `ℚ`: the diagonal entry plus the off-diagonal
absolute-value sum, `M k k + ∑_{j≠k} |M k j|`. Strict negativity for every row is the row
diagonal-dominance Hurwitz condition. -/
def gershgorinRowValueQ (M : Matrix S S ℚ) (k : S) : ℚ :=
  M k k + ∑ j ∈ Finset.univ.erase k, |M k j|

/-- The Gershgorin stability margin over `ℚ`: the worst (largest) row value
`max_k ( M k k + ∑_{j≠k} |M k j| )`. The strict diagonal-dominance Hurwitz test fires exactly when
this margin is negative; its magnitude grades the stability robustness. -/
def gershgorinMarginQ [Nonempty S] (M : Matrix S S ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (gershgorinRowValueQ M)

/-- The Gershgorin margin is negative exactly when every Gershgorin row value is negative — the
strict row diagonal-dominance Hurwitz condition. -/
theorem gershgorinMarginQ_neg_iff [Nonempty S] (M : Matrix S S ℚ) :
    gershgorinMarginQ M < 0 ↔ ∀ k, gershgorinRowValueQ M k < 0 := by
  rw [gershgorinMarginQ, Finset.sup'_lt_iff]
  simp

/-- The real cast of the Gershgorin row value is the row value of the cast matrix. -/
theorem gershgorinRowValueQ_cast (M : Matrix S S ℚ) (k : S) :
    ((gershgorinRowValueQ M k : ℚ) : ℝ)
      = (M.map (Rat.castHom ℝ)) k k
        + ∑ j ∈ Finset.univ.erase k, |(M.map (Rat.castHom ℝ)) k j| := by
  simp only [gershgorinRowValueQ, Rat.cast_add, Rat.cast_sum, Rat.cast_abs, Matrix.map_apply,
    Rat.coe_castHom]

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The network's Gershgorin stability margin at the all-ones concentration with unit rate constants:
`max_k ( J k k + ∑_{j≠k} |J k j| )` of the rational mass-action Jacobian. Negative exactly when the
row diagonal-dominance Hurwitz test certifies local stability there. -/
def gershgorinStabilityMarginQ [Nonempty S] (N : Network S) : ℚ :=
  gershgorinMarginQ (N.massActionJacobianQ (fun _ => 1) (fun _ => 1))

/-- **Certified local-stability margin.** When the Gershgorin stability margin is negative, the
mass-action Jacobian at the all-ones concentration with unit rate constants is strictly row
diagonally dominant with negative diagonal, so every eigenvalue of its complexification lies in the
open left half-plane: the linearization there is Hurwitz, in any number of species. This is the exact
rational form of the dimension-free Gershgorin stability test. -/
theorem gershgorinStabilityMarginQ_hurwitz [Nonempty S] (N : Network S) (κ : N.RateConstants)
    (hk : ∀ r, κ.k r = 1) (h : N.gershgorinStabilityMarginQ < 0) :
    ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toLin' ((N.massActionJacobian κ (fun _ => 1)).map (algebraMap ℝ ℂ))) μ →
        μ.re < 0 := by
  have hcast : N.massActionJacobian κ (fun _ => 1)
      = (N.massActionJacobianQ (fun _ => 1) (fun _ => 1)).map (Rat.castHom ℝ) := by
    rw [N.massActionJacobianQ_map_eq (fun _ => 1) (fun _ => 1) κ (fun r => by rw [hk r]; norm_num)]
    congr 1
    funext s
    norm_num
  rw [hcast]
  apply hurwitz_of_strict_diag_dominance_real
  intro k
  rw [← gershgorinRowValueQ_cast]
  have hrow := (gershgorinMarginQ_neg_iff (N.massActionJacobianQ (fun _ => 1) (fun _ => 1))).mp h k
  exact_mod_cast hrow

end Network

end CRNT

import CRNT.Dynamics.GershgorinMarginQ
import CRNT.Dynamics.HurwitzGershgorinColumn

/-!
# A rational column-form Gershgorin local-stability spectral margin

Gershgorin's circle theorem applies equally to the columns of a matrix: a real matrix whose every
column diagonal entry is negative and strictly dominates the off-diagonal column absolute-value sum
has all eigenvalues in the open left half-plane. This module records the exact rational margin of that
column test — `gershgorinColMarginQ`, the worst column value `max_k ( M k k + ∑_{i≠k} |M i k| )` over
`ℚ` — and the network-level scalar `gershgorinColStabilityMarginQ` obtained from the rational
mass-action Jacobian at the all-ones concentration with unit rate constants. The margin is negative
exactly when the column diagonal-dominance test fires, so it certifies local stability there
(`gershgorinColStabilityMarginQ_hurwitz`); its magnitude grades the stability robustness, and like the
row margin it is defined in every dimension. It is the column companion of `gershgorinMarginQ`: the
row and column tests are distinct sufficient conditions, so a matrix may pass one and fail the other,
and the two margins are independent stability certificates.

This is the column form of the classical diagonal-dominance stability test of Gershgorin's circle
theorem, graded as an exact rational scalar.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.GershgorinMarginQ`,
`CRNT.Dynamics.HurwitzGershgorinColumn`.
-/

namespace CRNT

open Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The Gershgorin column value of column `k` over `ℚ`: the diagonal entry plus the off-diagonal
column absolute-value sum, `M k k + ∑_{i≠k} |M i k|`. Strict negativity for every column is the
column diagonal-dominance Hurwitz condition. -/
def gershgorinColValueQ (M : Matrix S S ℚ) (k : S) : ℚ :=
  M k k + ∑ i ∈ Finset.univ.erase k, |M i k|

/-- The column-form Gershgorin stability margin over `ℚ`: the worst (largest) column value
`max_k ( M k k + ∑_{i≠k} |M i k| )`. The strict column diagonal-dominance Hurwitz test fires exactly
when this margin is negative; its magnitude grades the stability robustness. -/
def gershgorinColMarginQ [Nonempty S] (M : Matrix S S ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (gershgorinColValueQ M)

/-- The column-form Gershgorin margin is negative exactly when every Gershgorin column value is
negative — the strict column diagonal-dominance Hurwitz condition. -/
theorem gershgorinColMarginQ_neg_iff [Nonempty S] (M : Matrix S S ℚ) :
    gershgorinColMarginQ M < 0 ↔ ∀ k, gershgorinColValueQ M k < 0 := by
  rw [gershgorinColMarginQ, Finset.sup'_lt_iff]
  simp

/-- The real cast of the Gershgorin column value is the column value of the cast matrix. -/
theorem gershgorinColValueQ_cast (M : Matrix S S ℚ) (k : S) :
    ((gershgorinColValueQ M k : ℚ) : ℝ)
      = (M.map (Rat.castHom ℝ)) k k
        + ∑ i ∈ Finset.univ.erase k, |(M.map (Rat.castHom ℝ)) i k| := by
  simp only [gershgorinColValueQ, Rat.cast_add, Rat.cast_sum, Rat.cast_abs, Matrix.map_apply,
    Rat.coe_castHom]

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The network's column-form Gershgorin stability margin at the all-ones concentration with unit rate
constants: `max_k ( J k k + ∑_{i≠k} |J i k| )` of the rational mass-action Jacobian. Negative exactly
when the column diagonal-dominance Hurwitz test certifies local stability there. -/
def gershgorinColStabilityMarginQ [Nonempty S] (N : Network S) : ℚ :=
  gershgorinColMarginQ (N.massActionJacobianQ (fun _ => 1) (fun _ => 1))

/-- **Certified local-stability margin (column form).** When the column-form Gershgorin stability
margin is negative, the mass-action Jacobian at the all-ones concentration with unit rate constants is
strictly column diagonally dominant with negative diagonal, so every eigenvalue of its complexification
lies in the open left half-plane: the linearization there is Hurwitz, in any number of species. This is
the exact rational form of the dimension-free column Gershgorin stability test. -/
theorem gershgorinColStabilityMarginQ_hurwitz [Nonempty S] (N : Network S) (κ : N.RateConstants)
    (hk : ∀ r, κ.k r = 1) (h : N.gershgorinColStabilityMarginQ < 0) :
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
  apply hurwitz_of_strict_col_diag_dominance_real
  intro k
  rw [← gershgorinColValueQ_cast]
  have hcol := (gershgorinColMarginQ_neg_iff (N.massActionJacobianQ (fun _ => 1) (fun _ => 1))).mp h k
  exact_mod_cast hcol

end Network

end CRNT

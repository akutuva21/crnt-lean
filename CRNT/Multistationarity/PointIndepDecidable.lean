import CRNT.Multistationarity.SRSignDecidable
import CRNT.Multistationarity.SRCoverPointIndependence

/-!
# A decidable certificate for the point-free full-Jacobian P-matrix verdict

The point-independence keystone (`isPMatrix_massActionJacobian_box_of_pointIndep`) makes the full
mass-action Jacobian a P-matrix at *every* positive concentration from two conditions read off the
signed species–reaction graph alone: the cover-weight nonnegativity `SignCoverWeightNonneg` and the
positive-diagonal-drive condition `PositiveDiagonalDrive`. Both are stated over the reals through
`signedEdge`, the `SignType` sign of a real reaction-vector coordinate, so neither sign can be
settled by computation as written.

This module makes both conditions computable. The cover-weight condition is already mirrored by the
decidable `ConsistentSRSign` of `SRSignDecidable`, whose real cast is `SignCoverWeightNonneg`
(`hweight_of_consistentSRSign`). The diagonal-drive condition is mirrored here by
`ConsistentDiagonalDrive`, the same per-species existence statement with the noncomputable
`signedEdge` replaced by the decidable `intSignedEdge`; it agrees with `PositiveDiagonalDrive`
(`positiveDiagonalDrive_of_consistentDiagonalDrive`) since the two incidence signs coincide
(`intSignedEdge_eq`). The combination is a fully decidable, point-free certificate that discharges
the full-Jacobian P-matrix verdict by a kernel computation:

* `ConsistentDiagonalDrive` — the decidable diagonal-drive predicate over the finite domain
  `S × N.R`, with its `Decidable` instance.
* `positiveDiagonalDrive_of_consistentDiagonalDrive` — the decidable certificate implies the
  real-valued diagonal-drive condition.
* `isPMatrix_massActionJacobian_box_of_decide` — from the two decidable certificates the full
  mass-action Jacobian is a P-matrix at every positive concentration of a set, with no per-point
  hypothesis.

The full-Jacobian P-matrix verdict is the point-free keystone of the Craciun–Feinberg
species–reaction graph injectivity criterion. Carrying it to compatibility-class injectivity needs a
coordinate chart of the stoichiometric subspace whose reduced Jacobian is a P-matrix on a box; the
reduced Jacobian of any such chart is a Schur-style oblique compression of the full Jacobian, not a
principal submatrix, so the full-Jacobian P-matrix property does not transport to the reduced
Jacobian by submatrix selection. Reaching `InjectiveOnClass` from these decidable certificates alone
is therefore not sound, and the chart-box reduced-Jacobian P-matrix hypothesis remains a consumer
input (see `massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix`).

This is the computable face of the point-independent species–reaction graph injectivity keystone of
Craciun and Feinberg ("Multiple equilibria in complex chemical reaction networks: I. The injectivity
property" and "II. The species–reaction graph"), whose conclusion feeds the global-univalence theorem
of Gale and Nikaido ("The Jacobian matrix and global univalence of mappings").

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Multistationarity.SRSignDecidable`, `CRNT.Multistationarity.SRCoverPointIndependence`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The decidable positive-diagonal-drive predicate.** Each species `i` has a reaction `r` that
genuinely depends on it (`1 ≤ source coefficient at i`) and increases it
(`intSignedEdge i r = 1`, a positive net stoichiometric change). It is the computable companion of
`PositiveDiagonalDrive`, with the noncomputable `signedEdge` replaced by the natural-multiplicity
comparison `intSignedEdge`. The quantifiers range over the finite domain `S × N.R`, so the predicate
is decidable. -/
def ConsistentDiagonalDrive (N : Network S) : Prop :=
  ∀ i : S, ∃ r : N.R, 1 ≤ (N.reaction r).source i ∧ N.intSignedEdge i r = 1

instance (N : Network S) : Decidable N.ConsistentDiagonalDrive := by
  unfold ConsistentDiagonalDrive; infer_instance

/-- The decidable diagonal-drive certificate implies the real-valued diagonal-drive condition: the
computable incidence sign `intSignedEdge` agrees with `signedEdge` (`intSignedEdge_eq`), so a
positively-driving reaction witnessed over `intSignedEdge` is one over `signedEdge` too. -/
theorem positiveDiagonalDrive_of_consistentDiagonalDrive (N : Network S)
    (h : N.ConsistentDiagonalDrive) : N.PositiveDiagonalDrive := by
  intro i
  obtain ⟨r, hsrc, hsign⟩ := h i
  exact ⟨r, hsrc, by rw [← N.intSignedEdge_eq i r]; exact hsign⟩

/-- **The box-quantified full-Jacobian P-matrix verdict from decidable certificates.** From the
decidable cover-weight certificate `ConsistentSRSign` and the decidable diagonal-drive certificate
`ConsistentDiagonalDrive`, the full mass-action Jacobian is a P-matrix at every positive
concentration of a set `C`. Both certificates are settled by `decide`, so a concrete network
discharges the point-free P-matrix verdict over the whole box by a kernel sign computation, with no
per-point hypothesis. -/
theorem isPMatrix_massActionJacobian_box_of_decide (N : Network S) (κ : N.RateConstants)
    (C : Set (Concentration S)) (hC : ∀ x ∈ C, x.Positive)
    (hsign : N.ConsistentSRSign) (hdrive : N.ConsistentDiagonalDrive) :
    ∀ x ∈ C, (N.massActionJacobian κ x).IsPMatrix :=
  N.isPMatrix_massActionJacobian_box_of_pointIndep κ C hC
    (fun s σ ρ => N.hweight_of_consistentSRSign hsign s σ ρ)
    (N.positiveDiagonalDrive_of_consistentDiagonalDrive hdrive)

end Network

end CRNT

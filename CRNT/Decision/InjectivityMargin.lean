import CRNT.Multistationarity.PointIndepDecidable

/-!
# A graded injectivity-robustness margin

The point-free full-Jacobian P-matrix verdict requires the per-species positive-diagonal-drive
condition `ConsistentDiagonalDrive`: every species has a reaction that depends on it and increases
it. That condition is a Boolean. This module exposes its graded companion `numDiagonalDriveSpecies`:
the number of species that *do* carry a positive diagonal drive. It is bounded by the species count,
fast to decide, and equals the species count exactly when `ConsistentDiagonalDrive` holds
(`numDiagonalDriveSpecies_eq_card_iff`). It is a dense robustness signal toward the diagonal-drive
half of the Craciun–Feinberg injectivity precondition; it does **not** grade the signed-cover half
(`ConsistentSRSign`), whose cover domain is too large for a small scalar.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Multistationarity.PointIndepDecidable`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The number of species carrying a positive diagonal drive: a reaction that genuinely depends on
the species (`1 ≤ source coefficient`) and increases it (`intSignedEdge = 1`). A graded companion of
`ConsistentDiagonalDrive`, bounded by the species count. -/
def numDiagonalDriveSpecies (N : Network S) : ℕ :=
  (Finset.univ.filter
    (fun i : S => ∃ r : N.R, 1 ≤ (N.reaction r).source i ∧ N.intSignedEdge i r = 1)).card

/-- The diagonal-drive species count equals the species count exactly when every species is
positively driven, i.e. when `ConsistentDiagonalDrive` holds. -/
theorem numDiagonalDriveSpecies_eq_card_iff (N : Network S) :
    N.numDiagonalDriveSpecies = Fintype.card S ↔ N.ConsistentDiagonalDrive := by
  unfold numDiagonalDriveSpecies ConsistentDiagonalDrive
  constructor
  · intro h i
    have hu : (Finset.univ.filter
        (fun i : S => ∃ r : N.R, 1 ≤ (N.reaction r).source i ∧ N.intSignedEdge i r = 1))
        = Finset.univ := Finset.eq_univ_of_card _ h
    have hi : i ∈ Finset.univ.filter
        (fun i : S => ∃ r : N.R, 1 ≤ (N.reaction r).source i ∧ N.intSignedEdge i r = 1) := by
      rw [hu]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hi).2
  · intro h
    rw [Finset.filter_true_of_mem (fun i _ => h i), Finset.card_univ]

end Network

end CRNT

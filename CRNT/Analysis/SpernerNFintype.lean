import CRNT.Analysis.SpernerNIncidence
import Mathlib.Data.Fintype.Perm

/-!
# Finiteness of the `N`-subdivision lattice and its Kuhn cells

The handshaking count behind the `n`-dimensional Sperner lemma — counting cells, rainbow cells, and
door facets — needs the lattice points `Pt n N` and the Kuhn cells `Cell n N` to be finite types.
A barycentric point has every coordinate bounded by `N` (the coordinates are nonnegative and sum to
`N`), so `Pt n N` injects into `Fin (n+1) → Fin (N+1)`; a Kuhn cell is determined by its base point
and permutation (`Cell.eq_of_base_perm`), so `Cell n N` injects into `Pt n N × Equiv.Perm (Fin n)`.
Both targets are finite, giving the `Fintype` instances.

Depends on: `CRNT.Analysis.SpernerNIncidence`.
-/

namespace CRNT.Analysis.SpernerN

open Finset

variable {n N : ℕ}

/-- A barycentric coordinate is bounded by the total `N` (nonnegativity + sum). -/
theorem Pt.coord_le (p : Pt n N) (i : Fin (n + 1)) : p.1 i ≤ N := by
  have h := Finset.single_le_sum (f := p.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rwa [p.2] at h

/-- **The `N`-subdivision lattice is finite.** Each point injects into `Fin (n+1) → Fin (N+1)` by
clamping its (bounded) coordinates. -/
noncomputable instance instFintypePt : Fintype (Pt n N) :=
  Fintype.ofInjective
    (fun p : Pt n N => fun i : Fin (n + 1) => (⟨p.1 i, Nat.lt_succ_of_le (p.coord_le i)⟩ : Fin (N + 1)))
    (by
      intro a b hab
      apply Pt.ext
      funext i
      have h := congrFun hab i
      exact congrArg Fin.val h)

/-- **The Kuhn cells of the `N`-subdivision form a finite type.** A cell injects into
`Pt n N × Equiv.Perm (Fin n)` via its base point and permutation; a cell is determined by those
(`Cell.eq_of_base_perm`). -/
noncomputable instance instFintypeCell : Fintype (Cell n N) :=
  Fintype.ofInjective
    (fun c : Cell n N => ((⟨c.base, c.sum_base⟩ : Pt n N), c.perm) : Cell n N → Pt n N × Equiv.Perm (Fin n))
    (by
      intro a b hab
      rw [Prod.ext_iff] at hab
      exact Cell.eq_of_base_perm (congrArg Subtype.val hab.1) hab.2)

end CRNT.Analysis.SpernerN

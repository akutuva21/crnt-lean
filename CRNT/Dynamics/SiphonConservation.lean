import CRNT.Dynamics.Siphon
import CRNT.Stoich.Subspace
import CRNT.LinearAlgebra.OrthogonalComplement

/-!
# Siphon criticality as orthogonality to the stoichiometric subspace

A *positive conservation law supported on `P`* is the analytic obstruction in
`Network.IsCriticalSiphon`: a nonnegative species vector `v`, strictly positive exactly on the
siphon `P`, with `∑ s, v s · (reaction vector)_s = 0` for every reaction. The conservation
condition is, term by term, orthogonality of `v` to each reaction vector; since the stoichiometric
subspace is their span, it is exactly membership of `v` in the dot-product orthogonal complement
`orthSum N.stoichSubspace`.

This module makes that identification precise (`conservationLaw_iff_mem_orthSum`) and rewrites
`IsCriticalSiphon` through it (`isCriticalSiphon_iff_mem_orthSum`). The reformulation moves the
criticality predicate out of the per-reaction sum form and into the linear-algebra layer, where the
existence of a sign-restricted vector in `orthSum N.stoichSubspace` is a Farkas/linear-programming
feasibility question — the entry point for deciding criticality and, downstream, for the persistence
(boundary-repelling) analysis.

## Main results

* `conservationLaw_iff_mem_orthSum` — the conservation clause equals membership in
  `orthSum N.stoichSubspace`.
* `isCriticalSiphon_iff_mem_orthSum` — `IsCriticalSiphon` reframed through that complement.

Depends on: `CRNT.Dynamics.Siphon`,
`CRNT.Stoich.Subspace`, `CRNT.LinearAlgebra.OrthogonalComplement`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Conservation clause as orthogonality.** A species vector `v` is orthogonal to every reaction
vector — `∑ s, v s · (reaction vector r)_s = 0` for all `r` — iff it lies in the dot-product
orthogonal complement of the stoichiometric subspace (the span of the reaction vectors). -/
theorem conservationLaw_iff_mem_orthSum (N : Network S) (v : S → ℝ) :
    (∀ r : N.R, ∑ s, v s * N.reactionVector r s = 0) ↔ v ∈ orthSum N.stoichSubspace := by
  constructor
  · intro h
    refine mem_orthSum_span ?_
    rintro g ⟨r, rfl⟩
    exact h r
  · intro h r
    exact (mem_orthSum.mp h) (N.reactionVector r) (N.reactionVector_mem_stoichSubspace r)

/-- **Critical siphon reframed through the orthogonal complement.** A nonempty siphon `P` is
critical iff there is no nonnegative species vector strictly positive exactly on `P` that lies in
`orthSum N.stoichSubspace`. This rewrites the conservation clause of `IsCriticalSiphon` into the
linear-algebra layer, exposing it as a sign-restricted feasibility question. -/
theorem isCriticalSiphon_iff_mem_orthSum (N : Network S) (P : Finset S) :
    N.IsCriticalSiphon P ↔
      P.Nonempty ∧ N.IsSiphon P ∧
        ¬ ∃ v : S → ℝ, (∀ s, 0 ≤ v s) ∧ (∀ s, 0 < v s ↔ s ∈ P) ∧
          v ∈ orthSum N.stoichSubspace := by
  unfold IsCriticalSiphon
  refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
  refine not_congr (exists_congr (fun v => and_congr_right (fun _ => and_congr_right (fun _ => ?_))))
  exact N.conservationLaw_iff_mem_orthSum v

end Network

end CRNT

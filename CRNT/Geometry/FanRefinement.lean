import CRNT.Geometry.ZeroSeparatingInduction
import CRNT.Geometry.FaithfulCurve

/-!
# Craciun's fan-refinement repair of the ℝ⁴ over-determination (§4.4)

Craciun's §4.4 observes that the *naive* direct generalization of the 3-D zero-separating surface
fails in ℝ⁴: forcing one ruled patch to align simultaneously with several attracting directions gives
a constraint system that is over-determined in ℝ⁴ (the `finrank` threshold of
`ZeroSeparatingInduction.over_determined_in_dim_four`). He **repairs** it by *refining the fan*:
subdivide each cell with extra points along its advance edge, build the zero-separating surface for
the finer toric inclusion `T'`, and observe that for each coarse cell the surface's normals (away
from the coarse uncertainty regions) land in the coarse cell's attracting cone — so the finer surface
is **faithful for the coarse inclusion** `T`. Refinement breaks each over-constrained patch into a
*sequence* of patches, each crossing a single uncertainty region, restoring the per-patch constraint
count below `finrank` (the planar angular chaining of `FaithfulCurve2D`, lifted to `n` dimensions).

This module formalizes the two engines of that repair, sorry-free and axiom-clean:

* the **faithful-transfer engine** — admissibility for a finer cell transfers to the containing coarse
  cell, so the finer surface's normals are admissible for the coarse fan; and

* the **feasibility restoration** — a refined patch carrying fewer than `finrank ℝ E` active
  attracting directions always admits a valid surface normal, so the refinement (which keeps each
  patch's crossing count low) avoids the naive over-determination.

## What this module formalizes (sorry-free)

* `Refines F' F` — the refinement relation: every cell of `F'` is contained (as a set) in some cell
  of `F`.

* `attractsToward_coarse_of_fine` — a normal admissible for a finer cell `C' ⊆ C` is admissible for
  the coarse cell `C` (`Faithful.AttractsToward` is monotone under cell containment).

* `coneDual_coarse_subset_halfPlane_of_fine_mem` — consequently the coarse cell's toric-field polar
  `coneDual C` lies in the normal's region-side half-plane `{y | 0 ≤ ⟪n, y⟫_ℝ}`: a fine-admissible
  normal makes the coarse field inward.

* `exists_coarse_cell_of_refines` — packaged over `Refines`: a normal admissible for a cell of the
  refinement is admissible for some cell of the coarse fan.

* `refined_patch_normal_exists` — feasibility restoration: a refined patch with fewer than
  `finrank ℝ E` attracting-direction constraints admits a nonzero orthogonal surface normal — the
  refinement keeps each patch below the over-determination threshold.

## Proven vs. residue

PROVEN here, sorry-free and axiom-clean: the refinement relation, the faithful-transfer of
admissibility (and of field inwardness) from fine to coarse cells, and the feasibility restoration
that the refinement exploits. Together these are the algebraic content of §4.4's repair: refining the
fan transfers faithfulness downward while keeping each patch under the `finrank` threshold.

RESIDUE, named in prose only: the explicit §4.5 stripe/tunnel decomposition that produces the refined
fan with each patch crossing a single uncertainty region (the figure-driven combinatorics), and the
toric analysis matching the per-patch attracting directions. This module supplies the transfer and
feasibility engines those constructions consume.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Geometry.ZeroSeparatingInduction`,
`CRNT.Geometry.FaithfulCurve`.
-/

namespace CRNT

namespace FanRefinement

open scoped InnerProductSpace
open CRNT.Faithful ZeroSeparatingInduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The refinement relation.** `F'` refines `F` when every cell of `F'` is contained, as a set, in
some cell of `F`. This is the fan refinement of §4.4: each coarse cell is subdivided into finer
cells, so the finer fan resolves the coarse one. -/
def Refines [CompleteSpace E] (F' F : Fan E) : Prop :=
  ∀ C' ∈ F', ∃ C ∈ F, (C' : Set E) ⊆ (C : Set E)

/-- **Admissibility transfers from fine to coarse.** If a finer cell `C'` is contained in a coarse
cell `C` and the normal `n` attracts toward `C'` (`n ∈ C'`), then `n` attracts toward `C`: the
attracting-direction condition is monotone under cell containment. This is why a surface faithful for
the refined fan is faithful for the coarse fan — its normals, admissible for the finer cells, are
admissible for the containing coarse cells. -/
theorem attractsToward_coarse_of_fine {n : E} {C C' : ProperCone ℝ E}
    (hsub : (C' : Set E) ⊆ (C : Set E)) (h : AttractsToward n C') : AttractsToward n C :=
  hsub h

/-- **The coarse field is inward for a fine-admissible normal.** If `n ∈ C'` with the finer cell
`C'` contained in the coarse cell `C`, then the coarse cell's toric-field polar `coneDual C` lies in
the region-side half-plane `{y | 0 ≤ ⟪n, y⟫_ℝ}`. The fine-fan surface's normal makes the coarse toric
field point into the region — the support side of faithfulness transferred from fine to coarse. -/
theorem coneDual_coarse_subset_halfPlane_of_fine_mem [CompleteSpace E] {n : E} {C C' : ProperCone ℝ E}
    (hsub : (C' : Set E) ⊆ (C : Set E)) (h : n ∈ (C' : Set E)) :
    (coneDual (C : Set E) : Set E) ⊆ {y : E | 0 ≤ ⟪n, y⟫_ℝ} :=
  coneDual_subset_dualHalfPlane_of_mem (hsub h)

/-- **Admissibility for a refinement cell gives a coarse cell.** Packaged over `Refines`: if `n`
attracts toward a cell `C'` of the refinement `F'`, then `n` attracts toward some cell `C` of the
coarse fan `F`. The faithful-transfer at the fan level. -/
theorem exists_coarse_cell_of_refines [CompleteSpace E] {F' F : Fan E} (href : Refines F' F)
    {C' : ProperCone ℝ E} (hC' : C' ∈ F') {n : E} (h : AttractsToward n C') :
    ∃ C ∈ F, AttractsToward n C := by
  obtain ⟨C, hCF, hsub⟩ := href C' hC'
  exact ⟨C, hCF, attractsToward_coarse_of_fine hsub h⟩

/-- **Feasibility restoration by refinement.** A refined patch crossing fewer than `finrank ℝ E`
uncertainty regions carries fewer than `finrank ℝ E` attracting-direction constraints, so a nonzero
surface normal orthogonal to all of them exists. The refinement of §4.4 keeps every patch below this
threshold — each patch crossing a single uncertainty region — which is exactly how it avoids the
naive over-determination of `over_determined_in_dim_four`. -/
theorem refined_patch_normal_exists [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (v : ι → E)
    (hcard : Fintype.card ι < Module.finrank ℝ E) :
    ∃ n : E, n ≠ 0 ∧ ∀ i, ⟪v i, n⟫_ℝ = 0 :=
  exists_orthogonal_normal_of_card_lt_finrank v hcard

end FanRefinement

end CRNT

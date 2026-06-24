import CRNT.Decision.ExactDeficiency
import CRNT.Decision.Linkage

/-!
# A computable deficiency assembly

`CRNT.Decision.ExactDeficiency` pins the deficiency to `computeDeficiency`, but that `def` is
`noncomputable`: it takes the linkage count from `numLinkageClasses`, a quotient cardinality. The
connected-component count of the undirected reaction graph is the same number
(`numLinkageClasses_eq_card_connectedComponent`) and *does* evaluate, so writing the assembly through
it gives a genuinely computable deficiency.

* `computeNumLinkageClasses N := Fintype.card N.linkageGraph.ConnectedComponent`, a computable `ℓ`.
* `computableDeficiency N := numComplexes − computeNumLinkageClasses − computeRank stoichMatrixQ`,
  a computable `δ`, with `deficiency_eq_computableDeficiency : N.deficiency = N.computableDeficiency`.

The value still does not reduce under kernel `decide` — `computeRank` is a determinant
permutation-sum — so the deficiency of a concrete network is obtained by compiled evaluation
(`#eval`, or an external compiled analyzer), not by `decide`. The bridge theorem is the axiom-clean
link back to the propositional `deficiency`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Decision.ExactDeficiency`,
`CRNT.Decision.Linkage`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

open CRNT.GaussianRank

/-- **A computable linkage-class count**: the number of connected components of the undirected
reaction graph. It equals `numLinkageClasses` (`numLinkageClasses_eq_card_connectedComponent`) but,
unlike that quotient cardinality, it evaluates. -/
def computeNumLinkageClasses (N : Network S) : ℕ :=
  Fintype.card N.linkageGraph.ConnectedComponent

/-- The computable linkage count agrees with `numLinkageClasses`. -/
theorem computeNumLinkageClasses_eq_numLinkageClasses (N : Network S) :
    N.computeNumLinkageClasses = N.numLinkageClasses :=
  (N.numLinkageClasses_eq_card_connectedComponent).symm

/-- **A computable deficiency**: `δ = n − ℓ − s` with the computable linkage count and the computable
rational rank. Unlike `computeDeficiency` it carries no `noncomputable`, so a compiled evaluator can
run it; the value still does not reduce under kernel `decide` (the `computeRank` determinant
permutation-sum). -/
def computableDeficiency (N : Network S) : ℕ :=
  N.numComplexes - N.computeNumLinkageClasses - computeRank N.stoichMatrixQ

/-- **The deficiency equals its computable form**, for every deficiency value. -/
theorem deficiency_eq_computableDeficiency (N : Network S) :
    N.deficiency = N.computableDeficiency := by
  rw [deficiency_eq_computeDeficiency]
  simp only [computeDeficiency, computableDeficiency, computeNumLinkageClasses_eq_numLinkageClasses]

/-- **Computable deficiency-zero criterion** (an `iff` bridge, not a kernel-`decide` reduction). -/
theorem deficiencyZero_iff_computableDeficiency_eq_zero (N : Network S) :
    N.DeficiencyZero ↔ N.computableDeficiency = 0 := by
  rw [deficiencyZero_iff_computeDeficiency_eq_zero, computeDeficiency, computableDeficiency,
    computeNumLinkageClasses_eq_numLinkageClasses]

end Network

end CRNT

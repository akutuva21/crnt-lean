import CRNT.Decision.Rank
import CRNT.Decision.ComputableDeficiency

/-!
# The `crnt_deficiency_zero` tactic

An axiom-clean deficiency-zero certificate reduces, by `deficiencyZero_of_minor`, to two obligations:
a `k × k` stoichiometric minor with nonzero rational determinant (witnessing `s ≥ k`), and the count
inequality `n ≤ k + ℓ`. Discharging these by hand is linear algebra an external tool will not write.

`crnt_deficiency_zero f, σ` takes the witnessing selection — `f : Fin k → N.R` choosing `k` reactions
and `σ : Fin k → S` choosing `k` species — and proves `N.DeficiencyZero` automatically:

* the determinant obligation closes by `simp` with the closed-form determinant lemmas
  (`det_fin_one`/`two`/`three`, with a `det_succ_row_zero` cofactor fallback for larger `k`) under
  ground reduction, which evaluates the concrete reaction-vector entries in either the codegen
  (inductive `Species`) or the data-driven (`Fin n`) encoding;
* the count obligation closes by rewriting the noncomputable `numLinkageClasses` to the evaluable
  `computeNumLinkageClasses` and then `decide`.

The consumer (e.g. an external evaluator that already holds the stoichiometric matrix) finds the
witnessing minor's indices and supplies them; the tactic supplies the proof. The result is
axiom-clean — `decide` and `simp` stay on the kernel path; no `native_decide`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Decision.Rank`,
`CRNT.Decision.ComputableDeficiency`.
-/

namespace CRNT

/-- Close a `Network.DeficiencyZero` goal from an explicit nonsingular-minor witness: `f` selects the
`k` reactions and `σ` the `k` species of a stoichiometric minor with nonzero determinant. -/
macro "crnt_deficiency_zero" f:term ", " σ:term : tactic =>
  `(tactic|
    (refine CRNT.Network.deficiencyZero_of_minor _ $f $σ ?_ ?_
     · first
         | simp +decide [Matrix.det_fin_one, Matrix.det_fin_two, Matrix.det_fin_three]
         | simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
     · rw [← CRNT.Network.computeNumLinkageClasses_eq_numLinkageClasses]
       decide))

end CRNT

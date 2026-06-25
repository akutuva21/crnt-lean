import CRNT.Decision.LinkageDeficiencyExact
import CRNT.Decision.ComputableDeficiency
import CRNT.Deficiency.DeficiencyOne

/-!
# A decidable test for the deficiency-one linkage conditions

`DeficiencyOneConditions` bundles conditions (i) and (ii) of Feinberg's deficiency-one theorem:
every linkage class has deficiency at most one, and the per-class deficiencies sum to the network
deficiency. Both fields range over the noncomputable `Fintype` on the linkage-class quotient
(`instFintypeQuotientLinked`), and the per-class deficiency `linkageDeficiency` is itself
noncomputable, so the structure has no default `Decidable` instance.

This module supplies one by routing each field through its computable bridge:

* `sum_linkageDeficiency_eq_deficiencyInt_iff_compute` — the tightness identity
  `∑ q, linkageDeficiency q = deficiencyInt` is equivalent to the fully computable
  `∑ q, computeLinkageDeficiency q = (computableDeficiency : ℤ)`, rewriting the summand via
  `linkageDeficiency_eq_computeLinkageDeficiency` and the right side via `deficiencyInt_eq_deficiency`
  and `deficiency_eq_computableDeficiency`;
* the `∀ q` and `∑ q` deciders force the *computable* `instFintypeQuotientLinkageClass`, so the
  terms compile and `#eval`, and reconcile with the structure fields (stated against the ambient
  noncomputable `Fintype`) through `Subsingleton.elim` on `Fintype`;
* `decidableDeficiencyOneConditions` — the resulting `Decidable DeficiencyOneConditions`, total and
  axiom-clean.

As with the per-class `decidableLinkageDeficiency_le_one` and the whole-network
`computableDeficiency`, the instance is `#eval`-evaluable but does **not** reduce under kernel
`decide`: `computeRank` expands a determinant over a permutation sum, and the `Subsingleton.elim`
block over `Fintype` does not reduce in the kernel. Concrete decisions are obtained by compiled
evaluation, not by `decide`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Decision.LinkageDeficiencyExact`,
`CRNT.Decision.ComputableDeficiency`, `CRNT.Deficiency.DeficiencyOne`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The tightness identity in fully computable form.** The per-class deficiencies sum to the
network deficiency exactly when their computable counterparts sum to the computable network
deficiency, rewriting the summand and both endpoints through their bridge theorems. -/
theorem sum_linkageDeficiency_eq_deficiencyInt_iff_compute (N : Network S) :
    (∑ q, N.linkageDeficiency q = N.deficiencyInt) ↔
      (∑ q, N.computeLinkageDeficiency q = (N.computableDeficiency : ℤ)) := by
  have hsum : (∑ q, N.linkageDeficiency q) = ∑ q, N.computeLinkageDeficiency q :=
    Finset.sum_congr rfl fun q _ => N.linkageDeficiency_eq_computeLinkageDeficiency q
  have hdef : N.deficiencyInt = (N.computableDeficiency : ℤ) := by
    rw [N.deficiencyInt_eq_deficiency, N.deficiency_eq_computableDeficiency]
  rw [hsum, hdef]

/-- **The per-class bound `∀ q, δ_θ ≤ 1` is decidable.** The decider forces the computable
`instFintypeQuotientLinkageClass`; reconciliation with the ambient noncomputable `Fintype` of the
field is by `Subsingleton.elim`. Total and axiom-clean, `#eval`-evaluable but not `decide`-reducing
(the underlying per-class test expands `computeRank`). -/
instance decidableForallLinkageDeficiency_le_one (N : Network S) :
    Decidable (∀ q, N.linkageDeficiency q ≤ 1) :=
  @Fintype.decidableForallFintype _ _
    (fun q => N.decidableLinkageDeficiency_le_one q) (instFintypeQuotientLinkageClass N)

/-- **The tightness identity is decidable**, through its computable form. Forces the computable
`instFintypeQuotientLinkageClass` for the sum. Total and axiom-clean; `#eval`-evaluable but not
`decide`-reducing. -/
instance decidableSumLinkageDeficiency_eq (N : Network S) :
    Decidable (∑ q, N.linkageDeficiency q = N.deficiencyInt) :=
  decidable_of_iff _ (N.sum_linkageDeficiency_eq_deficiencyInt_iff_compute).symm

/-- **The deficiency-one linkage conditions are decidable.** The structure is the conjunction of its
two decidable fields. Total and axiom-clean; `#eval`-evaluable but not `decide`-reducing, since
`computeRank` is a determinant permutation-sum and the `Subsingleton.elim` reconciliation of the
two `Fintype` instances does not reduce in the kernel. -/
instance decidableDeficiencyOneConditions (N : Network S) :
    Decidable N.DeficiencyOneConditions :=
  decidable_of_iff
    ((∀ q, N.linkageDeficiency q ≤ 1) ∧ (∑ q, N.linkageDeficiency q = N.deficiencyInt))
    (by
      have hfin :
          (@Finset.univ (Quotient N.linkedSetoid) (instFintypeQuotientLinkageClass N)) =
            (@Finset.univ (Quotient N.linkedSetoid) (instFintypeQuotientLinked N)) :=
        congrArg (@Finset.univ (Quotient N.linkedSetoid)) (Subsingleton.elim _ _)
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [hfin] at h2; exact h2
      · rintro h
        refine ⟨h.linkageDeficiency_le_one, ?_⟩
        rw [hfin]; exact h.sum_eq)

end Network

end CRNT

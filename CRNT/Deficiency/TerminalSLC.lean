import CRNT.Deficiency.DeficiencyOneHypotheses

/-!
# Counting terminal strong linkage classes

Feinberg's third deficiency-one condition is that each linkage class contains exactly one
terminal strong linkage class (`OneTerminalSLCPerLinkageClass`). This module records its
structural consequence: that condition is exactly a bijection between linkage classes and
terminal strong linkage classes (`terminalSLCEquivLinkage`), so the number of terminal
strong linkage classes `t` equals the number of linkage classes `ℓ`
(`numTerminalSLC_eq_numLinkageClasses`).

The bijection is the scaffold for the deficiency-one theorem proper, whose argument runs one
terminal strong linkage class — equivalently one linkage class — at a time.

This module is **stable**. Depends on: `CRNT.Deficiency.DeficiencyOneHypotheses`.
-/

namespace CRNT

namespace Network

open scoped Classical

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A **terminal strong linkage class**: a strong linkage class that is terminal. -/
abbrev TerminalSLC (N : Network S) : Type :=
  {σ : Quotient N.stronglyLinkedSetoid // N.IsTerminalSLClass σ}

noncomputable instance instFintypeTerminalSLC (N : Network S) : Fintype N.TerminalSLC :=
  Fintype.ofFinite _

/-- The number of terminal strong linkage classes, `t`. -/
noncomputable def numTerminalSLC (N : Network S) : ℕ := Fintype.card N.TerminalSLC

/-- **Condition (iii) is a bijection between linkage classes and terminal strong linkage
classes.** A linkage class maps to its unique terminal strong linkage class; a terminal
strong linkage class maps back to the linkage class it refines. -/
noncomputable def terminalSLCEquivLinkage (N : Network S)
    (h : N.OneTerminalSLCPerLinkageClass) :
    Quotient N.linkedSetoid ≃ N.TerminalSLC where
  toFun θ := ⟨(h θ).choose, (h θ).choose_spec.1.2⟩
  invFun σ := N.strongToLinkage σ.val
  left_inv θ := (h θ).choose_spec.1.1
  right_inv σ := Subtype.ext
    ((h (N.strongToLinkage σ.val)).choose_spec.2 σ.val ⟨rfl, σ.property⟩).symm

/-- **The number of terminal strong linkage classes equals the number of linkage classes**
`t = ℓ` under the deficiency-one condition that each linkage class has a unique terminal
strong linkage class. -/
theorem numTerminalSLC_eq_numLinkageClasses (N : Network S)
    (h : N.OneTerminalSLCPerLinkageClass) :
    N.numTerminalSLC = N.numLinkageClasses := by
  rw [numTerminalSLC, Fintype.card_congr (N.terminalSLCEquivLinkage h).symm, card_quotient_eq]

end Network

end CRNT

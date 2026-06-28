import CRNT.Deficiency.TerminalSLC
import CRNT.Deficiency.DeficiencyOneDecide

/-!
# Computable terminal strong linkage class count

The number of terminal strong linkage classes `t` (`numTerminalSLC`) is defined as a `Fintype.card`
over a noncomputable `Fintype.ofFinite` instance. This module supplies the computable companion
`computeNumTerminalSLC`: a decidable filter-cardinality over the computable strong linkage class
quotient, with `computeNumTerminalSLC_eq_numTerminalSLC` proving the two agree. A terminal strong
linkage class is a strong linkage class with no reaction edge leaving it, and that terminality is
decidable (`instDecidableIsTerminalSLClass`), so the filter is computable.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Deficiency.TerminalSLC`,
`CRNT.Deficiency.DeficiencyOneDecide`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The computable count of terminal strong linkage classes: the decidable filter-cardinality of
the (computable) strong linkage class quotient by terminality. -/
def computeNumTerminalSLC (N : Network S) : ℕ :=
  (Finset.univ.filter (fun σ : Quotient N.stronglyLinkedSetoid => N.IsTerminalSLClass σ)).card

/-- The computable terminal-SLC count agrees with the cardinality definition `numTerminalSLC`. -/
theorem computeNumTerminalSLC_eq_numTerminalSLC (N : Network S) :
    N.computeNumTerminalSLC = N.numTerminalSLC := by
  rw [computeNumTerminalSLC, numTerminalSLC,
    ← Fintype.card_subtype (fun σ : Quotient N.stronglyLinkedSetoid => N.IsTerminalSLClass σ)]

end Network

end CRNT

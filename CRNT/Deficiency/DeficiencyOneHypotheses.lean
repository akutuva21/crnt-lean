import CRNT.Deficiency.LinkageDeficiency
import CRNT.Decision.StrongLinkage

/-!
# The hypotheses of the deficiency-one theorem

Feinberg's deficiency-one theorem applies to networks meeting three structural conditions:

1. each linkage class has deficiency at most one,
2. the class deficiencies sum to the network deficiency, and
3. each linkage class contains exactly one terminal strong linkage class.

Conditions (1) and (2) are `DeficiencyOneConditions` (`CRNT.Deficiency.LinkageDeficiency`).
This module formalizes (3): terminality lifts from complexes to strong linkage classes
(`IsTerminalSLClass`, well defined because `StronglyLinked` is an equivalence and terminality
is constant on its classes), strong linkage classes map to linkage classes
(`strongToLinkage`), and `OneTerminalSLCPerLinkageClass` records that each linkage class has a
unique terminal strong linkage class. `DeficiencyOneHypotheses` bundles all three.

Depends on: `CRNT.Deficiency.LinkageDeficiency`,
`CRNT.Decision.StrongLinkage`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Terminality is constant on a strong linkage class.** -/
theorem isTerminalSLC_congr (N : Network S) {x y : Complex S} (h : N.StronglyLinked x y) :
    N.IsTerminalSLC x ↔ N.IsTerminalSLC y := by
  constructor
  · exact fun hx r hr => h.symm.trans (hx r (h.trans hr))
  · exact fun hy r hr => h.trans (hy r (h.symm.trans hr))

/-- A strong linkage class is **terminal** when its complexes form a terminal strong linkage
class. -/
def IsTerminalSLClass (N : Network S) (σ : Quotient N.stronglyLinkedSetoid) : Prop :=
  Quotient.liftOn σ (fun c => N.IsTerminalSLC c.val)
    (fun _ _ hab => propext (N.isTerminalSLC_congr hab))

@[simp] theorem isTerminalSLClass_mk (N : Network S) (c : {c : Complex S // c ∈ N.complexes}) :
    N.IsTerminalSLClass (Quotient.mk N.stronglyLinkedSetoid c) = N.IsTerminalSLC c.val := rfl

/-- The linkage class of a strong linkage class: strong linkage refines linkage. -/
def strongToLinkage (N : Network S) (σ : Quotient N.stronglyLinkedSetoid) :
    Quotient N.linkedSetoid :=
  Quotient.liftOn σ (fun c => Quotient.mk N.linkedSetoid c)
    (fun _ _ hab => Quotient.sound (StronglyLinked.linked hab))

@[simp] theorem strongToLinkage_mk (N : Network S) (c : {c : Complex S // c ∈ N.complexes}) :
    N.strongToLinkage (Quotient.mk N.stronglyLinkedSetoid c) = Quotient.mk N.linkedSetoid c := rfl

/-- **Condition (3):** each linkage class contains exactly one terminal strong linkage
class. -/
def OneTerminalSLCPerLinkageClass (N : Network S) : Prop :=
  ∀ θ : Quotient N.linkedSetoid, ∃! σ : Quotient N.stronglyLinkedSetoid,
    N.strongToLinkage σ = θ ∧ N.IsTerminalSLClass σ

/-- **The full hypotheses of the deficiency-one theorem.** -/
structure DeficiencyOneHypotheses (N : Network S) : Prop where
  /-- Each linkage class has deficiency at most one, and the class deficiencies sum to `δ`. -/
  conditions : N.DeficiencyOneConditions
  /-- Each linkage class has a unique terminal strong linkage class. -/
  oneTerminal : N.OneTerminalSLCPerLinkageClass

end Network

end CRNT

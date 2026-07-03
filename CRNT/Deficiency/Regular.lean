import CRNT.Deficiency.Consistent
import CRNT.Deficiency.CutPair
import CRNT.Deficiency.DeficiencyOneHypotheses
import CRNT.Decision.StrongLinkage

/-!
# Regular networks

A reaction network is **regular** when it satisfies the three structural conditions underlying
Feinberg's Deficiency One Algorithm (Ji, *Uniqueness of equilibria for complex chemical reaction
networks*, Ohio State University, 2011, §1.6):

1. **Consistency** — the reaction vectors are positively dependent (`IsConsistent`);
2. **One terminal strong linkage class per linkage class** (`OneTerminalSLCPerLinkageClass`);
3. **Cut-pair condition** — every pair of directly linked complexes lying in a (single) terminal
   strong linkage class is a cut pair (`CutPair`).

Regularity is a hypothesis on the network's graph structure alone; the Deficiency One Algorithm
applies to regular networks that *additionally* have deficiency one, a condition imposed separately
at the theorem (not folded into regularity).

* `RegularNetwork` — the conjunction of the three conditions.

Depends on: `CRNT.Deficiency.Consistent`,
`CRNT.Deficiency.CutPair`, `CRNT.Deficiency.DeficiencyOneHypotheses`, `CRNT.Decision.StrongLinkage`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Regular network.** Consistency, one terminal strong linkage class per linkage class, and the
cut-pair condition: every directly linked pair of complexes in a common terminal strong linkage
class is a cut pair. (Strong linkage of the pair pins them to the same class; terminality of one
end then transfers to the other.) -/
def RegularNetwork (N : Network S) : Prop :=
  N.IsConsistent ∧ N.OneTerminalSLCPerLinkageClass ∧
    ∀ y y' : {c : Complex S // c ∈ N.complexes},
      N.linkageGraph.Adj y y' → N.IsTerminalSLC y.val → N.StronglyLinked y.val y'.val →
      N.CutPair y y'

/-- A regular network is consistent. -/
theorem RegularNetwork.isConsistent {N : Network S} (h : N.RegularNetwork) : N.IsConsistent :=
  h.1

/-- A regular network has one terminal strong linkage class per linkage class. -/
theorem RegularNetwork.oneTerminalSLCPerLinkageClass {N : Network S} (h : N.RegularNetwork) :
    N.OneTerminalSLCPerLinkageClass := h.2.1

/-- In a regular network, directly linked complexes of a common terminal strong linkage class form
a cut pair. -/
theorem RegularNetwork.cutPair {N : Network S} (h : N.RegularNetwork)
    {y y' : {c : Complex S // c ∈ N.complexes}} (hadj : N.linkageGraph.Adj y y')
    (hterm : N.IsTerminalSLC y.val) (hsl : N.StronglyLinked y.val y'.val) : N.CutPair y y' :=
  h.2.2 y y' hadj hterm hsl

end Network

end CRNT

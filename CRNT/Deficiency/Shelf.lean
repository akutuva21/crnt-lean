import CRNT.Deficiency.Regular
import CRNT.Deficiency.Confluence
import CRNT.Deficiency.Signature

/-!
# Shelf partitions of the Deficiency One Algorithm

Given a confluence vector `g`, the Deficiency One Algorithm enumerates **shelf partitions** of the
complexes into an upper, middle, and lower shelf, and from each reads off a linear system in the
unknown `μ` (Ji, *Uniqueness of equilibria for complex chemical reaction networks*, Ohio State
University, 2011, §1.6). A shelf partition is constrained so that

* every nonterminal complex lies on the middle shelf, and
* complexes in a common strong linkage class share a shelf

(the latter captures "complexes in the same nontrivial terminal strong linkage class on the same
shelf"; nonterminal complexes are forced to the middle by the first condition, so the two together
encode Ji's placement rules for terminal strong linkage classes).

From a shelf partition `sp` and confluence vector `g`, the **placement rules** generate the
constraints on `μ` (`ShelfPartition.imposes`):

* `y` strictly above `y'` ⟹ `y · μ > y' · μ`;
* `y, y'` both on the middle shelf ⟹ `y · μ = y' · μ`;
* a cut pair `(y, y')` on the upper shelf ⟹ the sign of `[g, y→y', y]` orders `y · μ` versus
  `y' · μ` (positive ⟹ `>`, negative ⟹ `<`, zero ⟹ `=`); on the lower shelf the strict
  inequalities are reversed.

**Faithfulness note.** The shelf-comparison and equality rules are encoded over *all* ordered pairs
of complexes, the literal reading of the rules. The algorithm's additional *nondegeneracy*
conditions on the upper/lower shelves (depending on trivial terminal strong linkage classes), which
restrict *which* partitions are enumerated, are not imposed here; omitting them only enlarges the
set of partitions considered. The headline statement pins that restriction.

* `Shelf`, `Shelf.rank` — the three shelves and their height;
* `ShelfPartition` — a shelf assignment meeting the two placement constraints;
* `ShelfPartition.imposes` — the generated constraints on `μ`;
* `ShelfPartition.ne_zero_of_imposes_of_higher` — a `μ` meeting a strict (height) constraint is
  nonzero.

Depends on: `CRNT.Deficiency.Regular`,
`CRNT.Deficiency.Confluence`, `CRNT.Deficiency.Signature`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- The three shelves of a Deficiency One Algorithm partition. -/
inductive Shelf
  | lower
  | middle
  | upper
deriving DecidableEq

/-- The height of a shelf: `lower < middle < upper`. -/
def Shelf.rank : Shelf → ℕ
  | .lower => 0
  | .middle => 1
  | .upper => 2

/-- **A shelf partition.** An assignment of each complex to a shelf such that every nonterminal
complex is on the middle shelf and complexes of a common strong linkage class share a shelf. -/
structure ShelfPartition (N : Network S) where
  /-- The shelf assigned to each complex. -/
  shelf : N.ComplexIdx → Shelf
  /-- Nonterminal complexes lie on the middle shelf. -/
  nonterminal_middle : ∀ c : N.ComplexIdx, ¬ N.IsTerminalSLC c.val → shelf c = Shelf.middle
  /-- Complexes of a common strong linkage class share a shelf. -/
  sameClass_sameShelf : ∀ c d : N.ComplexIdx, N.StronglyLinked c.val d.val → shelf c = shelf d

/-- **The constraints a shelf partition imposes on `μ`**, via the placement rules read against the
confluence vector `g`. -/
def ShelfPartition.imposes (sp : N.ShelfPartition) (g : N.ComplexIdx → ℝ) (μ : S → ℝ) : Prop :=
  (∀ y y' : N.ComplexIdx, (sp.shelf y').rank < (sp.shelf y).rank →
      complexPairing y'.val μ < complexPairing y.val μ) ∧
    (∀ y y' : N.ComplexIdx, sp.shelf y = Shelf.middle → sp.shelf y' = Shelf.middle →
      complexPairing y.val μ = complexPairing y'.val μ) ∧
    (∀ y y' : N.ComplexIdx, N.CutPair y y' → sp.shelf y = Shelf.upper →
      (0 < N.cutSum g y y' → complexPairing y'.val μ < complexPairing y.val μ) ∧
        (N.cutSum g y y' < 0 → complexPairing y.val μ < complexPairing y'.val μ) ∧
        (N.cutSum g y y' = 0 → complexPairing y.val μ = complexPairing y'.val μ)) ∧
    (∀ y y' : N.ComplexIdx, N.CutPair y y' → sp.shelf y = Shelf.lower →
      (0 < N.cutSum g y y' → complexPairing y.val μ < complexPairing y'.val μ) ∧
        (N.cutSum g y y' < 0 → complexPairing y'.val μ < complexPairing y.val μ) ∧
        (N.cutSum g y y' = 0 → complexPairing y.val μ = complexPairing y'.val μ))

/-- **A height constraint forces `μ` to be nonzero.** At `μ = 0` all pairings vanish, so no strict
inequality between shelves can hold. -/
theorem ShelfPartition.ne_zero_of_imposes_of_higher (sp : N.ShelfPartition)
    {g : N.ComplexIdx → ℝ} {μ : S → ℝ} (h : sp.imposes g μ)
    {y y' : N.ComplexIdx} (hr : (sp.shelf y').rank < (sp.shelf y).rank) : μ ≠ 0 := by
  rintro rfl
  exact absurd (h.1 y y' hr) (by simp [complexPairing_zero])

end Network

end CRNT

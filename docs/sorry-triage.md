# `sorry` triage

Mechanical classification of every `sorry` in the tree, by the content of the enclosing
declaration and its preceding comment. Regenerate with `scripts/triage_sorries.py`.

| class | count | meaning |
|---|---:|---|
| unclassified | 77 | no keyword matched; needs individual inspection |
| linear-algebra | 60 | finrank/kernel/basis/submodule goals -- mostly real work, some reachable via existing `finrank_orthSum`-style lemmas |
| major-theorem | 21 | deficiency / Shinar--Feinberg / Matrix--Tree / toric / concordance -- classical theorems, each a project |
| bookkeeping | 20 | reindexing, subtype sums, cardinality, casts -- the tractable class |
| already-elsewhere | 17 | name also declared in another file |
| graph | 16 | arborescence / spanning tree / linkage / circulation |
| analysis | 3 | derivative / compactness / limit / Poincare--Floquet |

## The `already-elsewhere` class is mostly *duplicated* sorries

Of 17, only **5** had a name whose other copy was actually proved, and of those only one
(`isClosed_compatibilityClass`) was the same statement -- now discharged by transferring the
proof written earlier today in `Dynamics/PermanenceAssembly.lean`. The rest are same-name,
different-statement (per-example lemmas), or genuine duplication where *both* copies are
unproved:

* `deficiency_le_totalBlockDeficiency_of_stoichIndependent` and
  `totalBlockDeficiency_le_deficiency_of_incidenceIndependent` are each stated and sorried in
  **both** `Decomposition/Deficiency.lean` and `Decomposition/BlockDeficiency.lean`.
* `finrank_complexBalancedTangentSpace` and `positiveComplexBalancedSet_pathConnected` likewise in
  both `Equilibria/ComplexBalanceGeometry.lean` and `Equilibria/GeneralizedComplexBalanceGeometry.lean`.

So the 214 figure overstates the distinct mathematical content: several theorems are counted twice.
Deduplicating those modules is engineering, and would cut the number without proving anything --
worth doing, but it should not be reported as progress on the mathematics.

## Verdict on "fix all 214"

Not achievable. 21 are classical theorems (Deficiency Zero/One, Shinar--Feinberg, Matrix--Tree,
toric, concordance); 60 are linear-algebra goals of which a minority are reachable; 77 are
unclassified and need reading one by one. The ~35 closed today were drawn almost entirely from the
20-strong `bookkeeping` class plus the one already-proved duplicate. That class is now close to
exhausted, which is the honest reason the rate is falling -- not lack of effort.

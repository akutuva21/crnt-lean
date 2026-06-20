# Tutorial

This walkthrough builds the reversible pair `A ⇌ B` and checks its structural
properties. The complete, proved version is in
[`CRNT/Examples/ReversiblePair.lean`](../CRNT/Examples/ReversiblePair.lean).

## 1. Species

Species form a finite type with decidable equality:

```lean
import CRNT
open CRNT

inductive Species | A | B deriving DecidableEq, Fintype, Repr
open Species
```

## 2. Complexes

A complex assigns a natural-number coefficient to each species:

```lean
def cA : Complex Species := fun s => match s with | A => 1 | B => 0
def cB : Complex Species := fun s => match s with | A => 0 | B => 1
```

The zero complex is `Complex.zero`; degradation reactions target it.

## 3. Reactions

A reaction is a directed edge between complexes. Index the reactions by a finite type:

```lean
inductive Rxn | fwd | bwd deriving DecidableEq, Fintype, Repr

def rxn : Rxn → Reaction Species
  | .fwd => { source := cA, target := cB }
  | .bwd => { source := cB, target := cA }
```

## 4. Network

```lean
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }
```

## 5. Count complexes

`Network.complexes` is the finite set of complexes appearing in reactions; its
cardinality is `numComplexes`. For concrete networks it reduces by `decide`:

```lean
example : N.numComplexes = 2 := by decide
```

## 6. Check weak reversibility

The network is weakly reversible when every reaction has a directed return path. Here
each direction is a single reaction, so witnesses are immediate:

```lean
example : N.WeaklyReversible := by
  intro r; cases r
  · exact Network.Reaches.single ⟨Rxn.bwd, rfl, rfl⟩  -- B → A returns A → B's edge
  · exact Network.Reaches.single ⟨Rxn.fwd, rfl, rfl⟩
```

For longer return paths, chain steps with `Network.Reaches.trans` /
`Network.Reaches.tail`, or use the walk-certificate checker `N.reaches_of_walk` (see
the certificate guide).

## 7. The mass-action vector field

A choice of positive rate constants induces the mass-action vector field:

```lean
example (κ : Network.RateConstants N) (x : Concentration Species) : Species → ℝ :=
  N.massActionVectorField κ x
```

Component `s` is `∑ r, massActionRate κ r x * reactionVector r s`. The reaction vector
of a reaction is `target − source`:

```lean
example : N.reactionVector .fwd = fun s => match s with | A => (-1 : ℝ) | B => 1 := by
  funext s; cases s <;> simp [Network.reactionVector, N, rxn, Reaction.vector, cA, cB]
```

## 8. Deficiency

With `n = 2` complexes, `ℓ = 1` linkage class, and stoichiometric rank `s = 1`, the
deficiency is `δ = 2 − 1 − 1 = 0`:

```lean
example : N.DeficiencyZero := ReversiblePair.deficiencyZero
```

`DeficiencyZero` is `deficiencyInt = 0`, equivalently `numComplexes = numLinkageClasses
+ stoichRank` (`Network.deficiencyZero_iff_eq`).

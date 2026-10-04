# Route: the `RR` reaction-arc builder and the ear-extraction gluability

**Agent:** `form-sr-deg2a` · **round 1** · **status: landed (9 machine-checked declarations)**

Branch `research/form-sr-deg2a`. New file
`CRNT/Multistationarity/TrueSRReactionArc.lean`. All nine declarations check with

```
#print axioms CRNT.Network.TrueSRCycle.reactionArcFwd
... depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. **no `sorryAx`** — the file imports no hole-bearing module.

---

## 1. Why this is on the critical path

`research/DEAD-ENDS.md` B-12 says the surviving Hole B route closes in `hSR.2`, never in `hnd`
(B-1 proves `hnd` unsatisfiable). The Shinar–Feinberg Lemma A.6 Case 2 discharge
(`lemmaA6_case2_arrangement1/2/4/6/interleaved`, ported from `backup-fig8`) is stated entirely in
terms of `TrueSRPathRR` / `RRGluable` / `rrGluedCycle`.

The **species** flavour of "cut a cycle into two arcs" is fully built in the tree:

| object | site |
| --- | --- |
| `TrueSRCycle.speciesArc`, `speciesArcBwd` | `TrueSRSpeciesPath.lean:645`, `:755` |
| `TrueSRCycle.arcFwd`, `arcBwd` | `TrueSRCycleSplit.lean:85`, `:88` |
| `ss_gluable_arcs` (the two species-arcs glue for free) | `TrueSRSpeciesPath.lean:902` |
| `TrueSRSSPath.SSGluable`, `ssGlueCycle` | `TrueSRSpeciesPath.lean:392`, `:548` |

The **reaction** flavour was missing entirely. `TrueSRParityRR.lean` has `TrueSRPathRR` (:57),
`RRGluable` (:260), `glueArc` (:388, public) and `rrGluedCycle` (:518) — but `glueArc` builds the
*closing* arc of an **already-given pair** of RR paths, so it cannot supply the first one, and no
other module could. Any theorem whose statement mentions `rrGluedCycle` was therefore untypeable in
practice. That is the prerequisite Main identified, and this file builds it.

## 2. What is built (exact Lean signatures)

All in `namespace CRNT.Network.TrueSRCycle`, with `variable {S} [DecidableEq S] [Fintype S]
{N : Network S} {n : ℕ} {C : N.TrueSRCycle n}`.

### 2.1 The builder

```lean
noncomputable def reactionArcFwd (i j : Fin n) (hij : i.1 < j.1) :
    N.TrueSRPathRR (j.1 - i.1 - 1)
```

`i.1 < j.1` so the arc does not wrap; a wrapping arc is `(C.rotate r).reactionArcFwd i' j'`.
The length parameter `j.1 - i.1 - 1` is the number of **interior** reaction vertices (a
`TrueSRPathRR j` has `2j + 2` edges).

### 2.2 Accessors (all proved)

```lean
theorem reactionArcFwd_startReaction (i j : Fin n) (hij : i.1 < j.1) :
    ((reactionArcFwd C i j hij).startReaction : N.InternalTrueReaction).1 = C.reaction i

theorem reactionArcFwd_endReaction (i j : Fin n) (hij : i.1 < j.1) :
    ((reactionArcFwd C i j hij).endReaction : N.InternalTrueReaction).1 = C.reaction j

theorem reactionArcFwd_edge_cases (i j : Fin n) (hij : i.1 < j.1)
    (k : Fin (2 * (j.1 - i.1 - 1) + 2)) :
    ((reactionArcFwd C i j hij).edgeAt k = C.rightEdge i ∧ k.1 = 0) ∨
      (∃ t : Fin n, i.1 < t.1 ∧ t.1 ≤ j.1 ∧
        (reactionArcFwd C i j hij).edgeAt k = C.leftEdge t) ∨
      (∃ t : Fin n, i.1 < t.1 ∧ t.1 < j.1 ∧
        (reactionArcFwd C i j hij).edgeAt k = C.rightEdge t)

theorem reactionArcFwd_edge_on_cycle (i j : Fin n) (hij : i.1 < j.1)
    (k : Fin (2 * (j.1 - i.1 - 1) + 2)) :
    C.ContainsEdge ((reactionArcFwd C i j hij).edgeAt k)

theorem reactionArcFwd_vertex_cases (i j : Fin n) (hij : i.1 < j.1)
    (p : Fin (2 * (j.1 - i.1 - 1) + 3)) :
    (∃ (h : TrueReaction.Internal N (C.reaction i)), p.1 = 0 ∧
        (reactionArcFwd C i j hij).vertexAt p = Sum.inr ⟨C.reaction i, h⟩) ∨
      (∃ (t : Fin n), i.1 < t.1 ∧ t.1 ≤ j.1 ∧
        (reactionArcFwd C i j hij).vertexAt p = Sum.inl (C.species t)) ∨
      (∃ (t : Fin n) (h : TrueReaction.Internal N (C.reaction t)), i.1 < t.1 ∧ t.1 ≤ j.1 ∧
        (reactionArcFwd C i j hij).vertexAt p = Sum.inr ⟨C.reaction t, h⟩)

theorem reactionArcFwd_species (i j : Fin n) (hij : i.1 < j.1) {x : S}
    (h : (reactionArcFwd C i j hij).HasSpecies x) :
    ∃ t : Fin n, i.1 < t.1 ∧ t.1 ≤ j.1 ∧ x = C.species t

theorem reactionArcFwd_reaction (i j : Fin n) (hij : i.1 < j.1)
    {ρ : N.InternalTrueReaction} (h : (reactionArcFwd C i j hij).HasReaction ρ) :
    ρ.1 = C.reaction i ∨ (∃ t : Fin n, i.1 < t.1 ∧ t.1 ≤ j.1 ∧ ρ.1 = C.reaction t)
```

### 2.3 The ear-extraction step (the point of the exercise)

```lean
theorem rrGluable_reactionArcFwd (i j : Fin n) (hij : i.1 < j.1) {L : ℕ}
    (A : N.TrueSRPathRR L)
    (hstart : (A.startReaction : N.InternalTrueReaction).1 = C.reaction i)
    (hend   : (A.endReaction   : N.InternalTrueReaction).1 = C.reaction j)
    (hspec  : ∀ s : S, A.HasSpecies s → ¬ C.HasSpecies s)
    (hint   : ∀ p : Fin (2 * L + 3), p.1 ≠ 0 → ¬ C.HasVertex (A.vertexAt p))
    (hedge  : ∀ l : Fin (2 * L + 2), ¬ C.ContainsEdge (A.edgeAt l)) :
    TrueSRPathRR.RRGluable (reactionArcFwd C i j hij) A
```

That is: **an off-cycle reaction-to-reaction path whose two endpoints are `C.reaction i` and
`C.reaction j`, and which meets `C` nowhere else, glues to the reaction arc of `C` between those
two reactions.** `TrueSRPathRR.rrGluedCycle (reactionArcFwd C i j hij) A
(rrGluable_reactionArcFwd …)` is then a `TrueSRCycle` carrying the ear — the object the ported
`lemmaA6_case2_*` discharge consumes.

## 3. Mathematical content and the construction

A `TrueSRCycle C : TrueSRCycle n` is encoded by `species`, `reaction` (both injective `Fin n →
…`), and for each `i` two SR edges: `leftEdge i` joining `species i` to `reaction i`, and
`rightEdge i` joining `species (i+1 mod n)` to `reaction i`. Traversing **with** the orientation
from the reaction vertex `reaction i`:

```
R_i --rightEdge i--> S_{i+1} --leftEdge (i+1)--> R_{i+1} --rightEdge (i+1)--> …
```

so the arc from `R_i` to `R_j` (`i < j`) has `2 (j - i)` edges, leaves by `rightEdge i`, arrives by
`leftEdge j`, and passes the intermediate reaction vertices `R_{i+1} … R_{j-1}` — exactly
`j - i - 1` of them, matching the `TrueSRPathRR (j - i - 1)` length.

A `TrueSRPathRR` is *literally* "a first edge, plus a species-to-reaction tail":

```lean
structure TrueSRPathRR (N) (j) where
  first : N.TrueSREdge
  tail  : N.TrueSRPath (2 * j + 1)
  first_species       : Sum.inl first.species = tail.vertex 0
  first_ne_tail_edge  : ∀ i, ¬ first.SameIncidence (tail.edge i)
  first_ne_tail_vertex: ∀ i, Sum.inr ⟨first.reaction, first.internal⟩ ≠ tail.vertex i
```

So the arc is built by taking `first := C.rightEdge i` and

```lean
tail := (C.rotate (i.1 + 1)).initialArcPath (j.1 - i.1 - 1)
```

`C.rotate r` (`TrueSRRotate.lean:40`) re-indexes the cycle by `⟨(i.1 + r) % n⟩`; rotating by
`i.1 + 1` puts `species (i + 1)` at position `0`, and the arc of the rotated cycle from species `0`
to reaction `j.1 - i.1 - 1` is exactly the tail (it starts at `S_{i+1}` and ends at `R_j`).
Because `i.1 < j.1 ≤ n - 1`, every rotated index satisfies `q.1 / 2 + (i.1 + 1) ≤ j.1 < n`, so the
modulo never wraps and `Nat.mod_eq_of_lt` discharges each occurrence — this is what
`reactionArcFwd_edge_cases` / `_vertex_cases` make explicit.

The three `TrueSRPathRR` obligations are then:

* `first_species` — `rightEdge i` lands on `C.species (i+1)`, the rotated tail's first vertex.
* `first_ne_tail_edge` — the tail's edges are cycle edges at indices in `(i, j]`.
  A left edge is never same-incidence with a right edge (`C.not_sameIncidence_left_right`); a right
  edge at rotated index `t` is `C.rightEdge t` with `i < t ≤ j`, hence `≠ i` (equal indices would
  need `q.1/2 ≡ n-1`, excluded by `q.1/2 ≤ j - i - 1`), so
  `C.sameIncidence_rightEdge_iff` closes it.
* `first_ne_tail_vertex` — the start reaction does not recur inside the tail: even tail positions
  are species (`Sum.inr_ne_inl`), odd ones are `C.reaction t` with `i < t ≤ j`.

`rrGluable_reactionArcFwd` then discharges the five `RRGluable` fields from the five hypotheses,
using `reactionArcFwd_species` / `_reaction` (which give exactly the interior vertices of the arc) and
`reactionArcFwd_edge_cases` (which give exactly its edges). The `p.1 = 0` case of
`reaction_disjoint` is why `hint` may be stated with only `p.1 ≠ 0`: `vertexAt_zero` is the ear's
own start reaction, which is the anchor.

## 4. Dependency order for the rest of the route

Everything below now consumes this file. Nothing below was touched.

1. **DONE (this PR).** `reactionArcFwd` + accessors + `rrGluable_reactionArcFwd`.
2. **Lift the escape path.** `relPathToTrueSRSSPath` is `private noncomputable def` at
   `TrueChemistrySRCriterion.lean:5478`, so the aggregate `RelPath` from `qC` to the off-cycle class
   `q` must be turned into a `TrueSRPathRR` by an analogous direct construction, or `prepend`
   (`TrueSRParityRR.lean:276`, **also private**) must be lifted. **This is the next bottleneck and
   it is a privacy problem, not a mathematical one** — see §5.
3. **The ear.** From the escape: `A : TrueSRPathRR L` with
   `A.startReaction = ⟨C.reaction i, _⟩`, `A.endReaction` a reaction vertex of `C`,
   `hint` from `hQ0late`, `hedge` from "every off-cycle SR edge is not a cycle edge".
   Then `rrGluable_reactionArcFwd` applies and `rrGluedCycle` gives `X`.
4. **Evenness.** `X.Even` must come from `SignDirected σ` — the sign-directed cycle lemma
   (`TrueSRCycle.even_of_signChange`, `TrueSRCycle.even_of_signChange` is **private** at
   `TrueChemistrySRCriterion.lean:6885`; a public version must be authored, as Main notes).
5. **Discharge.** Feed `X`, `Y` and the arrangement data to `lemmaA6_case2_*` to contradict `hSR.2`.

## 5. Dead ends (do not re-walk)

* **`TrueSRPathRR.prepend` is `private`** (`TrueSRParityRR.lean:276`). Main suggested lifting the
  modifier; **it is unnecessary.** `reactionArcFwd` is built directly from `first` + `tail` and does
  not touch `prepend`. No privacy change is needed for the arc side. (It may still be needed for
  step 2 above, where the *ear* — not the arc — has to be assembled.)
* **Dot notation on `reactionArcFwd` fails** from inside `namespace TrueSRCycle`
  (`Function reactionArcFwd does not have a usable parameter of type TrueSRCycle … for which to
  substitute C`). This is a resolution quirk, not a typing failure: write
  `reactionArcFwd C i j hij` explicitly. Recorded because it cost several iterations here and will
  cost them again.
* **`rewriting `TrueSRCycle.rotate_reaction` / `rotate_species` / `initialArcPath_endReaction`
  across a `Subtype` whose proof field mentions the rewritten term fails** with
  `motive is not type correct` — the abstracted `internal`/`reaction_internal` proof no longer
  typechecks. Fix: build the target value with `congrArg` + `Fin.ext` + `Nat.mod_eq_of_lt`, never by
  `rw` across the proof field. (`rw` on `.1` / `Subtype.val` of the *value* is fine.)
* **Inside a `where` block you cannot refer to the definition being defined.** The
  `first_ne_tail_vertex` obligation was originally proved via `C.reactionArcFwd i j hij`, which
  fails. State the obligation about `first`/`tail` directly and use `change` / `rfl`.
* **`C.reaction_internal i` is the right internality witness**, not `⟨C.reaction i, …⟩`:
  `TrueReaction.Internal` is a `def … : Prop` built by `Quotient.liftOn`, not a structure, so the
  anonymous-constructor notation is rejected.
* **`refute/negative**: the `hnd` route is dead (B-1) and must not be revisited; the ear closes in
  `hSR.2` only.

## 6. Concrete consumer sketch

```lean
-- X : the cycle carrying the ear
let hq := C.reactionArcFwd_reaction i j hij (ear_endReaction)
-- hq : ρ.1 = C.reaction i ∨ ∃ t, i.1 < t.1 ∧ t.1 ≤ j.1 ∧ ρ.1 = C.reaction t
```

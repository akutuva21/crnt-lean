# `sr-shortest-path` — shortest-path machinery for the true-SR endgame

**Agent:** `form-sr-route` · **Branch:** `research/form-sr-route` · **Hole:** B

## 0. Status summary

Two modules landed, both elaborating:

| module | content |
| --- | --- |
| `CRNT/Multistationarity/TrueSRReactionArc.lean` | **the RR reaction-arc builder** — the prerequisite the orchestrator identified as blocking `exists_second_evenCycle_of_offCycle_escape` |
| `CRNT/Graph/RelPathShortest.lean` | generic `ShortestPath` with `Nat`-minimality + the no-shortcut lemma |

One minimal change to an existing file: `TrueSRParityRR.prepend` lifted from `private` to public.

## 1. The RR reaction-arc builder — `CRNT/Multistationarity/TrueSRReactionArc.lean`

### 1.1 What was missing

`TrueSRSpeciesPath.lean:610-756` builds the **species** flavour of a cycle arc:

```lean
noncomputable def C.speciesArc   (m : ℕ) (hm : m < n) (hmpos : 0 < m) : N.TrueSRSSPath (2 * m)
noncomputable def C.speciesArcBwd (m : ℕ) (hm : m < n) (hmpos : 0 < m) : N.TrueSRSSPath (2 * (n - m))
```

with `ss_gluable_arcs` (`TrueSRSpeciesPath.lean:902`) giving `SSGluable` between them essentially
free, and `ssGluable_chord_arcFwd` / `ssGluable_chord_arcBwd` (`:946`, `:980`) gluing an arbitrary
chord to either arc.

There is **no** reaction-flavoured counterpart on `holes`.  `TrueSRPathRR`
(`TrueSRParityRR.lean:57`) is therefore never constructible from a cycle, and
`exists_second_evenCycle_of_offCycle_escape` cannot be typed.

### 1.2 The mathematical content

A `TrueSRCycle n` carries `leftEdge i : S_i — R_i` and `rightEdge i : R_i — S_{i+1 mod n}`, so the
graph is the chain

```
R_0 — S_1 — R_1 — S_2 — R_2 — … — S_m — R_m
```

**Lemma (uniqueness of the forward route).**  From `R_0` there is exactly one simple route to
`R_m` running forward: `rightEdge 0, leftEdge 1, rightEdge 1, …, rightEdge (m-1), leftEdge m`,
of length `2m`.

*Proof.*  `R_0`'s only neighbours are `S_0` (via `leftEdge 0`) and `S_1` (via `rightEdge 0`); a
path using `S_0` runs *backwards*.  On the forward side `S_{i}`'s only neighbours are `R_{i-1}`
(`rightEdge (i-1)`) and `R_i` (`leftEdge i`), so from `S_i` the route must take `leftEdge i`.
Induction. ∎

**Parity.**  The true-SR graph is bipartite (species against reactions — `TrueSREdge.Connects`
only ever pairs `Sum.inl` with `Sum.inr`), so every reaction-to-reaction path has even length;
`2m` is even. Consistent.

`TrueSRPathRR j` records a reaction-to-reaction path of `2j+2` edges as a first edge plus a
`TrueSRPath (2j+1)` tail, so `j = m - 1` and

* `first = rightEdge 0` (joins `R_0` to `S_1`);
* `tail : TrueSRPath (2(m-1)+1)` running `S_1 — R_1 — S_2 — … — S_m — R_m`.

### 1.3 Lean signatures

```lean
namespace CRNT.Network.TrueSRCycle

/-- The forward reaction arc of a cycle, from `R_0` to `R_m`. -/
noncomputable def reactionArc {n : ℕ} (C : TrueSRCycle n) (m : ℕ)
    (hm : m < n) (hmpos : 0 < m) : N.TrueSRPathRR (m - 1)

theorem reactionArc_startReaction (C : TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    (C.reactionArc m hm hmpos).startReaction
      = ⟨C.reaction ⟨0, _⟩, (C.reaction_internal ⟨0, _⟩).internal⟩

theorem reactionArc_endReaction (C : TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    (C.reactionArc m hm hmpos).endReaction
      = ⟨C.reaction ⟨m, hm⟩, C.reaction_internal ⟨m, hm⟩⟩

theorem reactionArc_tail_startSpecies (C : TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    (C.reactionArc m hm hmpos).tail.startSpecies = C.species ⟨1, _⟩

theorem reactionArc_length (C : TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    2 * (m - 1) + 2 = 2 * m

end CRNT.Network.TrueSRCycle
```

### 1.4 Internal shape (for downstream reuse)

```lean
private noncomputable def rarcEdge (q : Fin (2 * m - 1)) : N.TrueSREdge :=
  C.leftEdge ⟨q.1 / 2 + 1, arcIdx hm q.isLt⟩

private noncomputable def rarcVertex (p : Fin (2 * m)) : N.TrueSRVertex :=
  if h : p.1 % 2 = 0 then Sum.inl (C.species ⟨p.1 / 2 + 1, arcIdx hm p.isLt⟩)
  else Sum.inr ⟨C.reaction ⟨p.1 / 2 + 1, arcIdx hm p.isLt⟩,
    C.reaction_internal ⟨p.1 / 2 + 1, arcIdx hm p.isLt⟩⟩
```

Position `p` even ⇒ `S_{p/2+1}`, odd ⇒ `R_{p/2+1}`.  So `p = 0` is `S_1` and `p = 2m-1` is `R_m`,
exactly as §1.2 requires.

### 1.5 Citation

Not a published lemma: it is the *dual* of `speciesArc`, which is the Banaji–Craciun
(arXiv:0809.1308, Lemma 10) arc construction that `TrueSRSpeciesPath.initialArcPath`
(`TrueSRArc.lean:73`) already implements for the species flavour. The reaction flavour is needed
because Shinar–Feinberg (arXiv:1203.6560, Appendix A.2, Lemma A.4, p. 52) states its
three-path parity lemma for paths `R*AR**` joining **reactions**; `TrueSRParityRR.lean`
formalises exactly that and has no way to produce its inputs.

### 1.6 Dependency order

1. `TrueSRParityRR.TrueSRPathRR` (exists) — the target type.
2. `TrueSRCycle.reactionArc` (**this file**) — construction.
3. `RRGluable` between `reactionArc`s — **not yet written**, see §3.

## 2. `prepend` — REVERTED, and why

I initially lifted `TrueSRPathRR.prepend` (`TrueSRParityRR.lean:276`) from `private` to public,
on the orchestrator's earlier instruction. A later broadcast superseded this: **`glueArc`
(`TrueSRParityRR.lean:388`) is already public and already is the RR arc builder — do not lift
`prepend`.**

I have therefore **reverted the lift**; `TrueSRParityRR.lean` on my branch is byte-identical to
`holes`. `git diff` on that file is empty.

The correction is right for a second, independent reason I found while working: `reactionArc`
does not need `prepend` at all — it builds the `TrueSRPath` tail directly rather than by
prepending an edge to an existing `TrueSRPathRR`. So the lift was never load-bearing for the
forward arc. It would only be needed for the *backward* arc if that were built by prepending,
but `speciesArcBwd` shows the intended construction is `C.reverse`-based, which needs no
prepend either.

**General lesson for this round:** `checkmod.sh` was broken for the whole round (fixed on `holes`
by `infra-build`). It set `LEAN_PATH` to the shared root and then called `lake env lean`, which
*prepends* its own entries, so the worktree-local build dir landed ahead of the shared cache and
`CRNT.*` imports failed with "object file … does not exist" for oleans that exist. I independently
worked around it by hard-linking the shared oleans into the worktree. Several of my early
"this module does not elaborate" readings were this bug, not my Lean.

## 3. Residual — `RRGluable` between two reaction arcs

With `reactionArc` built, the next step is the reaction-flavoured analogue of `ss_gluable_arcs`
(`TrueSRSpeciesPath.lean:902`):

```lean
/-- The two reaction arcs of a cycle glue back to it: between reactions `R_0` and `R_m`,
a cycle is two reaction-to-reaction paths with those endpoints whose reaction vertices meet
only in the endpoints. -/
theorem rr_gluable_arcs (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    TrueSRPathRR.RRGluable (C.reactionArc m hm hmpos) (C.reactionArcBwd m hm hmpos)
```

where

```lean
noncomputable def C.reactionArcBwd (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    N.TrueSRPathRR (n - m - 1)
```

should be `(C.reverse).reactionArc (n - m) _ _`, mirroring `speciesArcBwd`. This needs
`C.reverse` to preserve `leftEdge`/`rightEdge` under the index map `i ↦ (n - i) % n`; that
`reverse` machinery already exists (`reverse_species'`, used at `TrueSRSpeciesPath.lean:761`)
but its edge-level round-trip has not been checked.

Then, following `ssGluable_chord_arcFwd` (`:946`) verbatim:

```lean
/-- An even reaction-to-reaction path whose interior misses `C` glues to each reaction arc. -/
theorem rrGluable_chord_arcFwd (A : N.TrueSRPathRR j)
    (hstart : A.startReaction = ⟨C.reaction ⟨0,_⟩, _⟩)
    (hend   : A.endReaction   = ⟨C.reaction ⟨m,_⟩, _⟩)
    (hint   : ∀ p : Fin (2*j+3), p.1 ≠ 0 → p.1 ≠ 2*j+2 → ¬ C.HasVertex (A.vertexAt p))
    (hedgeL : ∀ (p : Fin (2*j+2)) (t : Fin n), ¬ (A.edgeAt p).SameIncidence (C.leftEdge t))
    (hedgeR : ∀ (p : Fin (2*j+2)) (t : Fin n), ¬ (A.edgeAt p).SameIncidence (C.rightEdge t)) :
    TrueSRPathRR.RRGluable A (C.reactionArc m hm hmpos)
```

**Why this is the right next step.**  It is the reaction-flavoured restatement of what already
works for species, and it is the exact input shape that
`TrueSRParityRR.three_glued_parity` (Lemma A.4) needs. Without it,
`exists_second_evenCycle_of_offCycle_escape` has no way to produce the three edge-disjoint
reaction-to-reaction paths that the parity argument counts over.

## 4. `CRNT/Graph/RelPathShortest.lean` — generic shortest paths

```lean
namespace CRNT.RelPath

def edge (x y : V) (hx : x ∈ T) (hy : y ∈ T) (h : E x y) : RelPath E T 1

structure ShortestPath (E : V → V → Prop) (T : Finset V) (a b : V) where
  length : ℕ
  path : RelPath E T length
  start_eq : path.vertex ⟨0, _⟩ = a
  end_eq : path.vertex ⟨length, _⟩ = b
  min_length : ∀ (l : ℕ) (Q : RelPath E T l),
    Q.vertex ⟨0, _⟩ = a → Q.vertex ⟨l, _⟩ = b → length ≤ l

noncomputable def ShortestPath.of_reflTransGen (hclosed) (hbT : b ∈ T)
    (h : Relation.ReflTransGen E a b) : ShortestPath E T a b

theorem exists_shortestPath (hclosed) (hbT) :
    (∃ P : ShortestPath E T a b) ↔ Relation.ReflTransGen E a b

theorem ShortestPath.injective (P) : Function.Injective P.path.vertex
theorem ShortestPath.eq_of_vertex_eq (P) {i j} (h : P.path.vertex i = P.path.vertex j) : i = j
theorem ShortestPath.le_one_of_edge (P) (hedge : E a b) : P.length ≤ 1
theorem ShortestPath.length_eq_one_of_edge (P) (hedge : E a b) (hab : a ≠ b) : P.length = 1
theorem ShortestPath.not_edge_of_length_ge_two (P) (h2 : 2 ≤ P.length) : ¬ E a b

end CRNT.RelPath
```

`of_reflTransGen` is the `Nat.find`/`Nat.find_min'` construction the assignment asked for;
`le_one_of_edge` is the **no-shortcut lemma**, and `length_eq_one_of_edge` is its endpoint form —
"a shortest path whose endpoints are already joined by an edge has length exactly one", which is
the shape the residue at `TrueChemistrySRCriterion.lean:8607` needs.

**Consumption.** `le_one_of_edge` is used by `length_eq_one_of_edge` and
`not_edge_of_length_ge_two`; `exists_shortestPath` consumes `of_reflTransGen` and
`relPath_reflTransGen`; `eq_of_vertex_eq` consumes `injective`. `edge` is consumed by
`le_one_of_edge`. No orphan.

## 5. Dead ends (do not re-walk)

* **`RelPath.append` (concatenation at an arbitrary shared vertex).**  Three attempts
  (`appendVertex` packaged separately; `dif_pos`/`dif_neg` on a `Fin`-indexed `if`; direct
  `show` + `rw`) all failed to elaborate the `step` field — index arithmetic across the join
  requires rewriting `Fin.castSucc`/`succ` values *under* an `ite`, and `omega` cannot discharge
  the bounds that appear there. **Not a mathematical obstruction**, an engineering one. The
  existing `RelPath.concat` (one step) plus `take`/`tail`/`splice` cover every consumer in the
  tree, so this was dropped rather than sunk further. If prefix/suffix minimality on `RelPath`
  is ever genuinely needed, the right move is a `Fin`-indexed recursion or a `Vector`-style
  `Fin`-`cases` formulation, not `if`-indexed.
* **A generic `prefix_minimal`/`suffix_minimal` on `RelPath`.**  Blocked on the above.
  Superseded in practice: the shortest-path consumer that matters for Hole B is at the
  `TrueSRSSPath`/`TrueSRPathRR` level, where paths are structures with `vertex : Fin (L+1) → V`
  and cutting is a direct reindexing.
* **`TrueSRShortestPath.lean` (prefix/suffix of a `TrueSRSSPath`).**  Written, and it contains
  the right statements (`prefix`, `suffix`, disjointness of the two halves,
  `ShortestSSPath.prefix_minimal` / `suffix_minimal`), but it is **not landed**: the
  orchestrator's later messages redirected this slice to the RR arc builder, which is the actual
  blocking prerequisite. The module as written should compile; it is unverified.

## 6. What I did NOT establish

* `exists_second_evenCycle_of_offCycle_escape` — **not attempted.** It needs `rr_gluable_arcs`
  (§3) first, which needs `reactionArcBwd` and a checked `reverse` edge round-trip.
* Whether `reactionArc`'s tail composition with the cycle's own `leftEdge`/`rightEdge` gives the
  c-pair bookkeeping needed for the parity count. The species flavour has
  `ss_three_glued_even_of_two` (`TrueChemistrySRCriterion.lean:7976`, `private`); the reaction
  flavour's analogue was not attempted.
* Nothing about Hole A. The orchestrator froze it pending the `hfloor`/`wmax ∈ ω` adjudication;
  this slice does not touch it.
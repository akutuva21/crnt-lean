# Independent verification of PR #10, and the reconciliation of `TrueSRReactionArc.lean`

**agent:** `form-sr-only` · **round 2** · **branch:** `research/FormSrOnly`
**base:** `holes` (`90bddfc`) · **stacks on:** PR #10 (`research/form-sr-case2`, `d1db040`)

Evidence grades used throughout (`research/README.md` §10):
`[M]` machine-checked by a command reproduced here, `[S]` read from source at the cited
`file:line` this session, `[N]` never checked.

---

## 0. TL;DR

1. **PR #10 is sound.** Both modules elaborate with zero `error:` and zero
   `declaration uses 'sorry'`; every public declaration's axiom footprint is exactly
   `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`** `[M]`.
2. **`reactionArcFrom` is well-formed**: it typechecks as a `N.TrueSRPathRR k` with all three
   `TrueSRPathRR` obligations discharged inside the structure literal `[M]`.
3. **The `k < n` refutation is reproduced, and it is stronger than PR #10 claimed.** It is not
   that PR #10's *proof* breaks at `k = n-1`; **no value of the structure `TrueSRPathRR (n-1)`
   has those `first`/`tail` fields at all.** Landed as
   `CRNT/Multistationarity/TrueSRArcNaturalBound.lean` `[M]`.
4. **The orchestrator's broadcast that the four `TrueSRReactionArc.lean` files are byte-identical
   is FALSE** — four distinct files, 174–396 differing lines on every pair `[M]`.
   `form-sr-cycle` needs the real thing.
5. **`harr` has no producer, and the reason is not a missing glue instance** (§5).

---

## 1. What was checked, and how

### 1.1 A toolchain hazard that invalidates naive `checkmod.sh` runs — **[M]**

`research/scripts/checkmod.sh:41` sets `LEAN_PATH="$SHARED:$BASE_LEAN_PATH"`, i.e. **the shared
root comes first**. The shared cache at
`$CRNT_ROOT/.lake/build/lib/lean/CRNT/Multistationarity/` contained a **stale**
`TrueSRReactionArc.olean` dated `Oct 3 23:33`. So a `checkmod.sh` run of a module that *imports*
`TrueSRReactionArc` resolves that import against the stale shared `.olean`, **not** against the
file you just built — and reports `OK` while proving something else.

Reproduce:

```sh
ls -la /Users/akutuva/Documents/Proofs/crnt-lean/.lake/build/lib/lean/CRNT/Multistationarity/ | grep -i reactionarc
# -rw-r--r--  1 akutuva staff  84616 Oct  3 23:33 TrueSRReactionArc.olean
```

**Fix used here, and recommended for every stacked PR audit:** build an isolated olean root and
put it *first*.

```sh
rm -rf /tmp/srcheck
cp -a "$CRNT_ROOT/.lake/build/lib/lean" /tmp/srcheck
rm -f /tmp/srcheck/CRNT/Multistationarity/TrueSRReactionArc.olean
cd <worktree>
export LEAN_PATH="/tmp/srcheck:$(lake env printenv LEAN_PATH)"
lean -o /tmp/srcheck/CRNT/Multistationarity/TrueSRReactionArc.olean CRNT/Multistationarity/TrueSRReactionArc.lean
lean -o /tmp/srcheck/CRNT/Multistationarity/TrueSREarCase2.olean  CRNT/Multistationarity/TrueSREarCase2.lean
```

Exit status 0 for both, no `error:` line, `sorry-warnings: 0` `[M]`.

### 1.2 Axiom footprint — **[M]**

`/tmp/srcheck/AxCheck10.lean` runs `#print axioms` on all eleven public declarations of the two
modules. **Every line reads `[propext, Classical.choice, Quot.sound]`:**

```
reactionArcFrom, reactionArcFrom_startReaction, reactionArcFrom_endReaction,
TrueSRCycle.SignDirected, TrueSRCycle.even_of_signDirected,
TrueSRPath.HasEdge, TrueSRSSPath.HasEdge, TrueSRPathRR.HasEdge,
TrueSRCycle.sToRIntersectionOfTwoPaths,
lemmaA6_case2_twoComponents, lemmaA6_case2_oneComponent
```

**No `sorryAx`.** The B-11 isolation (`TrueSREarCase2.lean` must not import
`TrueChemistrySRCriterion`) is intact and machine-checked, not merely asserted. `prepend` is still
`private noncomputable def` at `TrueSRParityRR.lean:276` and no branch in the repo touches that
file `[M]` (loop over all `origin/*` refs, `git diff -- CRNT/Multistationarity/TrueSRParityRR.lean`,
zero output).

### 1.3 `reactionArcFrom` is well-formed — **[S]**

Read `TrueSRReactionArc.lean:78-138`. It is a structure literal for
`N.TrueSRPathRR k` (`TrueSRParityRR.lean:57-68`) with all five fields present:

| field | line | discharged by |
| --- | --- | --- |
| `first` | 80 | `(C.rotate r).rightEdge (lastIdx C)` |
| `tail` | 81 | `(C.rotate r).initialArcPath k _`, length `2k+1` ✓ |
| `first_species` | 82-96 | `right_species` + `initialArcPath_vertex_even` at `⟨0,_⟩` |
| `first_ne_tail_edge` | 97-121 | even/odd split, `reaction_injective`, `omega` on `n-1 ≠ i/2` |
| `first_ne_tail_vertex` | 122-138 | even case is `Sum.inr_ne_inl`; odd case is `reaction_injective` |

Note `first_ne_tail_edge` needs, in the odd case, that `i/2 ≠ n-1`, i.e. `i ≠ 2n-2`, i.e. the
condition `k + 1 < n` — so **both** `first_ne_tail_*` obligations, not only
`first_ne_tail_vertex`, are where the bound is load-bearing. PR #10's header describes only the
vertex obligation; the edge obligation is the same obstruction.

---

## 2. The `k < n` refutation, landed — **[M]**

New file **`CRNT/Multistationarity/TrueSRArcNaturalBound.lean`**, imports only
`TrueSRReactionArc`. Four declarations, all axiom-clean.

### 2.1 The identity — `wholeCycle_tail_vertex_eq_first_reaction`

```lean
theorem wholeCycle_tail_vertex_eq_first_reaction (C : N.TrueSRCycle n) (r : ℕ) :
    ((C.rotate r).initialArcPath (n - 1) _).vertex (Fin.last (2 * (n - 1) + 1)) =
      Sum.inr ⟨((C.rotate r).rightEdge (lastIdx C)).reaction,
                ((C.rotate r).rightEdge (lastIdx C)).internal⟩
```

The tail's **last** vertex *is* the arc's own start-reaction vertex. Proof: `Fin.last` is odd,
`initialArcPath_vertex_odd` (`TrueSRArc.lean:212-216`) gives `Sum.inr ⟨reaction ⌈p/2⌉, _⟩` with
`p = 2n-1`, so `p/2 = n-1 = lastIdx C`, and `right_reaction` identifies that with `first.reaction`.

### 2.2 The field obstruction — `not_first_ne_tail_vertex_of_wholeCycle`

`¬ ∀ i, Sum.inr ⟨first.reaction, first.internal⟩ ≠ tail.vertex i`.

### 2.3 **The statement-level refutation** — `not_exists_reactionArcFrom_of_wholeCycle`

```lean
theorem not_exists_reactionArcFrom_of_wholeCycle (C : N.TrueSRCycle n) (r : ℕ) :
    ¬ ∃ (A : N.TrueSRPathRR (n - 1)),
        A.first = (C.rotate r).rightEdge (lastIdx C) ∧
        A.tail = (C.rotate r).initialArcPath (n - 1) _
```

**This is the real content, and it is stronger than the broadcast's phrasing.** A natural

```lean
noncomputable def reactionArcFrom' (C) (r) (k : ℕ) (hk : k < n) : N.TrueSRPathRR k
```

with the same body **cannot type-check at `k = n - 1`** — not "is harder to prove", but has no
possible proof of the `first_ne_tail_vertex` field. So the bound `k + 1 < n` in PR #10 is not a
convenience; it is the exact boundary of a false statement.

### 2.4 The complement — `reactionArcFrom_of_lt`

`k + 1 < n → k ≤ n - 2`. Together with §2.3 this **localises the obstruction to `k = n - 1`
alone**: the bound costs exactly one length out of `n` possible values, and nothing else.

### 2.5 Search space and certification method (round-1 RULE compliance)

* **Searched, exactly:** the single identity of §2.1, by `omega` + one `rw` through
  `initialArcPath_vertex_odd`. Two arithmetic facts, both exact integer reasoning:
  `(2 * (n-1) + 1) % 2 = 1` and `(2 * (n-1) + 1) / 2 = n - 1`. **No floats, no enumeration, no
  case analysis.**
* **Not searched, and deliberately:** whether some *other* `TrueSRPathRR (n-1)` exists. It does
  (two edges plus a tail, for `n ≥ 3`). The claim proved is the correct one: **the whole-cycle
  arc is not one.**
* **Not searched:** the analogous statement for the *other three* arc builders. §4 says they have
  different indices, so each needs its own check; do not assume this transfers.

---

## 3. The `Gluable` / `RRGluable` instance census — **[S]**

My brief asked which instances exist and which the ear still needs. Answered by reading the tree,
not relayed.

### 3.1 What `TrueSRGlueMaps.lean:233` / `:245` instantiate

Both are **`Gluable` consumers**, not builders:

* `glueWalk (h : Gluable P Q) (hn : 2 ≤ i+j+1) : N.TrueSRClosedWalk (i+j+1)` (`:233`)
* `glueCycle (h : Gluable P Q) (hn : 2 ≤ i+j+1) : N.TrueSRCycle (i+j+1)` (`:245`)

**They are already instantiable today.** `Gluable` is the species-to-reaction structure
(`TrueSRGlueInterface.lean:59-65`) and **`TrueSRCycle.gluable_arcs` already exists**, at
`TrueSRCycleSplit.lean:262-263`:

```lean
theorem gluable_arcs (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) :
    Gluable (C.arcFwd m hm) (C.arcBwd m hm) where ...
```

So `glueCycle (C.gluable_arcs m hm) _ : TrueSRCycle (n-1)` is reachable **on `holes`, with no PR
merged.** *Task 2 of my brief is already satisfied for `:233`/`:245`* — that is a positive finding,
not a gap. (`n - 1` because `arcFwd : TrueSRPath (2m+1)`, `arcBwd : TrueSRPath (2(n-1-m)+1)`, so
`i+j+1 = m + (n-1-m) = n-1`.)

Also present: `gluable_chord_arcFwd` (`TrueSRCycleSplit.lean:443`), `gluable_chord_arcBwd` (`:492`),
and three inline instances in `TrueSRNoArcChord.lean:56,127,172`.

### 3.2 The `SSGluable` counterpart exists too — **[S]**

`TrueSRSSPath.ss_gluable_arcs` (`TrueSRSpeciesPath.lean:902-903`):
`SSGluable (C.speciesArc m hm hmpos) (C.speciesArcBwd m hm hmpos)`, plus
`ss_gluable_chord_arcFwd` (`:946`) and `ss_gluable_chord_arcBwd` (`:980`).

### 3.3 `RRGluable`: **zero instances exist anywhere in the tree** — **[M]**

`RRGluable` (`TrueSRParityRR.lean:260-272`) appears **only** at its definition and in its four
consumers `glueArc` (`:388`), `gluable_of_RRGluable` (`:442`), `rrGluedCycle` (`:518`),
`rrGluedCycle_numCPairs` (`:702`), `rr_three_glued_even_of_two` (`:775`). **No declaration in
`CRNT/` builds one.** So `rr_gluable_arcs` — the `TrueSRPathRR` counterpart of `ss_gluable_arcs` —
is genuinely missing, and `form-sr-glue` owns it (per orchestrator broadcast). **I did not build
it**, to avoid colliding.

Command and control (the control is the point: an empty result is only evidence if the pattern
is known to match):

```sh
grep -rn "RRGluable" CRNT/ --include=*.lean
grep -rc "RRGluable" CRNT/ --include=*.lean | grep -v ':0'
# control -> TrueSREarCase2.lean:1  TrueSRParityRR.lean:23  TrueSRReactionArc.lean:3  (non-empty)
```

Every one of those 27 hits is either the `structure RRGluable` line, a **hypothesis binder**
`(h : RRGluable X Y)` / `(hAB : RRGluable A B)`, or `gluable_of_RRGluable`, which consumes an
`RRGluable` rather than producing one. **There is no construction site.**

### 3.4 The shape it needs, stated once so nobody re-derives it — **[S]**

`RRGluable`'s five fields (`TrueSRParityRR.lean:262-272`) for a cycle `C` split at reaction index
`m` with `0 < m < n`:

| field | forward arc `ρ₀ ⇝ ρ_m` | backward arc `ρ₀ ⇝ ρ_m` | range argument |
| --- | --- | --- | --- |
| `same_start` | `ρ₀` | `ρ₀` | definitional |
| `same_end` | `ρ_m` | `ρ_m` | `reaction_injective` |
| `species_disjoint` | `S₁ … S_m` | `S₀, S_{m+1} … S_{n-1}` | `[1,m] ∩ ({0} ∪ [m+1,n-1]) = ∅` |
| `reaction_disjoint` | `ρ₀ … ρ_m` | `{ρ₀} ∪ ρ_m … ρ_{n-1}` | share only `ρ₀`, `ρ_m` |
| `edge_disjoint` | `rightEdge i` (`i<m`), `leftEdge j` (`1≤j≤m`) | `leftEdge 0`, `rightEdge i` (`m≤i<n`), `leftEdge j` (`m+1≤j<n`) | left/right split disjoint by index; cross-type by `not_sameIncidence_left_right` (`TrueSRCycleSplit.lean:57-76`) |

Length check: forward `2m` edges ⇒ `TrueSRPathRR (m-1)`; backward `2(n-m)` edges ⇒
`TrueSRPathRR (n-m-1)`; and `(m-1) + (n-m-1) + 2 = n`, matching `rrGluedCycle`'s
`TrueSRCycle (y+1+x+1)`. **The parity count is already available** —
`rr_three_glued_even_of_two` at `TrueSRParityRR.lean:775` — so parity needs nothing new.

**Caveat for the reconciler:** the index ranges in the last two rows are written in the
**`m-1` parameterisation** (PR #19's). PR #9's `fwd_idx_le` / `bwd_idx_ge` /
`fwd_bwd_index_split` are stated for **`(C.rotate 1).initialArcPath (m-1)`** and
**`(C.reverse).initialArcPath (n-m-1)`** — i.e. PR #9's *forward* arc is PR #10's at `r = 1`, and
its *backward* arc is the same object mine is. So PR #9's lemdas are **reusable only if** the
reconciler keeps that parameterisation; they are not stated for PR #19's `reactionArc` indices.

---

## 4. The reconciliation: the four files are NOT identical — **[M]**

The orchestrator relayed `form-sr-route.ArcBuilderFix`'s claim that the arc files are
byte-identical and the merge is "take any one copy and union the four extras". **That is false.**

```sh
for b in deg2b case2 parity route; do
  git show origin/research/form-sr-$b:CRNT/Multistationarity/TrueSRReactionArc.lean > /tmp/arcf/$b.lean; done
md5 /tmp/arcf/*.lean; wc -l /tmp/arcf/*.lean
for p in "deg2b case2" "deg2b parity" "deg2b route" "case2 parity" "case2 route" "parity route"; do
  set -- $p; printf "%s vs %s: %s differing lines\n" $1 $2 "$(diff /tmp/arcf/$1.lean /tmp/arcf/$2.lean | grep -cE '^[<>]')"; done
```

| branch | PR | lines | md5 | public content |
| --- | --- | --- | --- | --- |
| `form-sr-deg2b` | #9 | 127 | `85ceae68b2abab671b81733a3c5a3043` | **no `TrueSRPathRR`** — index arithmetic only |
| `form-sr-case2` | #10 | 157 | `296461a543017ab2b4e2191482817b48` | `reactionArcFrom (r k)`, `hk : k+1 < n` — **compiles** |
| `form-sr-parity` | #17 | 111 | `d72d2f7f8e27f5ce620cc2d76f5c252d` | **zero public declarations** |
| `form-sr-route` | #19 | 305 | `22c60f14fc2b5f11dc5050689c535f9b` | `reactionArc (m)`, four obligations all proved |

Pairwise differing lines: `deg2b/case2` 224, `deg2b/parity` 174, `deg2b/route` 368,
`case2/parity` 202, `case2/route` 396, `parity/route` 352. **Not one pair is close.**

What each actually declares, read this session:

* **#10** — `lastIdx`, `reactionArcFrom (C) (r k) (hk : k + 1 < n) : N.TrueSRPathRR k`,
  `reactionArcFrom_startReaction`, `reactionArcFrom_endReaction`.
* **#19** — `reactionArc (C) (m) (hm) (hmpos)`, `reactionArc_startReaction`, `_endReaction`,
  `_tail_startSpecies`, `_length`. Different parameterisation (`j = m-1`), **no `k+1<n`
  restriction**, and the `rfl`-transferable `rarcEdge`/`rarcVertex`.
* **#9** — `zero_lt_of_nontrivial`, `arc_len_lt`, `rev_len_lt`, `fwd_idx_lt`, `fwd_idx_le`,
  `bwd_idx_lt`, `bwd_idx_ge`, `fwd_bwd_index_split`. Its own header (`:47-56`) says the assembly
  of `arcFwdRR`/`arcBwdRR` "follows from `initialArcPath_edge_even`/`_odd`" and "the `RRGluable`
  instance then follows". **It builds no path and no glue instance.**
* **#17** — `one_lt_n`, `rotate_speciesAt`, `rotate1_reaction`, **all `private`**; the
  `section ReactionArc` at `:120-125` is **empty**. The orchestrator's table entry
  "`reactionArcFwd`, 2 of 5 obligations OPEN" corresponds to nothing in the file: there is no
  `reactionArcFwd` in #17 at all, and its header simultaneously claims "Three of its five
  obligations are discharged" — **zero are**, because zero of the declarations are public.

**Consequence for `form-sr-cycle`:** the reconciliation is a real API decision over **three
incompatible parameterisations**, not a file union. #17 is disposable (private-only, zero public
content, and a straight duplicate of #19's `rarcEdge` transfer argument). #9's lemmas are the
only thing worth salvaging, and **only if** the winner keeps #9's indices.

### 4.1 The `reactionArc_startReaction` API delta — **[S]**

`#10` proves it at `.1` (`TrueSRReactionArc.lean:143-146`);
`#19` states the same fact at the `Subtype` level (`/tmp/arcf/route.lean:267-274`).
`startReaction` is `⟨first.reaction, first.internal⟩` definitionally
(`TrueSRParityRR.lean:77-79`), so the `.1` form is sufficient and the `Subtype` form follows by
`Subtype.ext` — it is *derivable*, not a different fact. **There is no mathematical delta**;
only the ergonomics differ. *(I did not compile #19, so I grade "derivable" `[S]`: it follows
from `startReaction`'s definition, which I read.)*

### 4.2 The two bounds are the **same inequality**, and #19's `m < n` is *true* — **[S]**

This is the sharpest thing I can hand the reconciler, and it corrects a natural misreading of
§2. Read at `/tmp/arcf/route.lean:127-131` and `TrueSRReactionArc.lean:78`, both this session:

* **#19** fixes the start at `R_0` (`first := C.rightEdge ⟨0,_⟩`) and reaches `R_m`. Its tail
  carries reaction indices `[1, m]`, so its "whole cycle" would be `m = n` — **already excluded
  by `hm : m < n`**. #19's statement is therefore *true as written* and needs no `k+1<n` guard.
* **#10** starts at `R_{n-1}` (`first := (C.rotate r).rightEdge (lastIdx C)`) and reaches `R_k`,
  so its whole cycle is `k = n-1`, which is why it needs `k + 1 < n`.
* **Under `r = 1`, #10's `k` is #19's `m - 1`.** The two constructions therefore coincide and the
  two bounds are the same inequality, stated in different words.

**Do not "fix" #19 by importing #10's `k + 1 < n`, and do not carry §2's refutation over to #19
without re-deriving it at `m = n`.** What §2 refutes is precisely the *naive* `k < n` restatement
of #10 — not either published statement.

---

## 5. `harr`: why it has no producer, and why it is not waiting on a glue instance — **[S]**

`harr` is the arrangement datum of `lemmaA6_case2_twoComponents`
(`TrueSREarCase2.lean:419`):

```lean
(harr : ∀ e, QE e ∧ VE e ↔ (c₁.HasEdge e ∨ c₂.HasEdge e))
```

Its siblings are `hdecX`, `hdecY` (`:414-415`) and `hCP`, `hCV`, `hQP` (`:416-418`).

**The comment at `TrueSREarCase2.lean:399-405` says** these describe "the *decomposition* of each
cycle into 'the ear plus the closing arc'". So `harr` is not a glue identity at all: it is the
statement that **the two closing arcs meet in exactly the listed S-to-R component paths**.

**Where it would have to be produced.** `lemmaA6_case2_twoComponents` takes **two cycles**
`X : TrueSRCycle m` and `Y : TrueSRCycle n` plus the four edge predicates `CE QE PE VE`. Grep over
`CRNT/Multistationarity/TrueChemistrySRCriterion.lean` for `harr|hdecX|hdecY|CE|QE|PE|VE` returns
**no matches at all** `[M]`. Reading the residue in context (`TrueChemistrySRCriterion.lean:8579-8612`):
the theorem `stronglyConcordant_fullyOpen_of_trueSRCriterion` begins at `:8003`, and at `:8579` it
is inside `cases hv0 : Q0.vertex ⟨0,_⟩ with | inl s0 =>`. The context there contains **one cycle
`C`, one path `Q0`, an integer `m`, species `s`, `s0`, `ρ0`, and `hattachment`** — and the
conclusion being proved is `False`.

**So: the second cycle does not exist at the residue.** There is no `X` to decompose, no `CE`/`QE`
to define, and therefore no `harr`. This confirms B-10 from source rather than by relay, and it
means:

> **`harr` is not downstream of the glue instances. It is downstream of a *second cycle*, and the
> second cycle is exactly what the (unbuilt) ear-extraction
> `exists_second_evenCycle_of_offCycle_escape` would supply.** Fixing the glue instances does not
> move `harr` by one step.

This is a **negative result about the dependency ordering in the route**, not about the hole. It
is recorded because the surviving-route checklist in `DEAD-ENDS.md` currently lists `harr` as
waiting on gluing data, which would send the next agent to the wrong file.

**What was not checked:** whether `harr` is provable *conditional* on a supplied second cycle
(obviously it is — `lemmaA6_case2_*` take it as a hypothesis). The claim is only about **where a
producer can be written**.

---

## 6. Suggested next steps

1. **`form-sr-cycle`**: discard #17; pick #10 or #19 as the arc; re-derive #9's index lemmas
   against the winner's indices. **§4.2 is the thing to read first** — it shows the two bounds
   are the same inequality, so this is a choice of *indexing*, not of mathematics, and neither
   published statement is false. Only the naive `k < n` restatement of #10 is, and §2 refutes it.
2. **`form-sr-glue`**: §3.4 is the range table for `rr_gluable_arcs`; §3.3 confirms no instance
   exists yet. `rr_three_glued_even_of_two` (`TrueSRParityRR.lean:775`) means parity is free.
3. **Anyone auditing a stacked PR**: §1.1. The shared `.olean` cache shadows worktree files on
   `LEAN_PATH`, and `checkmod.sh` will happily certify a stale import.
4. **Hole B's real residue**: per §5 it is the *second cycle*, i.e. the ear extraction, and per
   B-26 that ear is being built for a class with no known member. Per B-1 the `hnd` clause at
   `:8609-8612` is refutable, so the closure must go through `hSR.2`.

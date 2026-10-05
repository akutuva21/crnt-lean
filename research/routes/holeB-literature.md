# Literature scour: Shinar–Feinberg, and what it settles about Hole B

**Every claim below is `[SOURCED]` — read in the TeX source this session**, not relayed from a
brief. Source: `curl https://arxiv.org/e-print/1203.6560v3` → gzip tarball,
`Concordant-SRGraph.tex` (172 KB), 2012-04-25 (v3).

**Correction to the repo's own notes (DEAD-ENDS A-15).** `research/DEAD-ENDS.md` A-15 says
"`arxiv.org/e-print/…` returns an archive listing, not the `.tex` body" and A-10 says figures are
"not machine-extractable." **Both are false.** The e-print endpoint returns a real gzip tarball and
the body extracts cleanly. The `.eps` figure sources are present and named:

```
Concordant-SRGraph.tex  Concordant-SRGraph.bbl  concordant-srgraph.toc
SixCases.eps             SBlockLemmaArgument.eps   SBlockLemmaArgumentPart2.eps
EarIllustration.eps      ProofOfEvenProp.eps       R-to-RThreeCycleCasesUndirected.eps
BlockTreeGraph.eps       BlockIllustration.eps     FirstSRGraphExample.eps
```

So `SixCases.eps` (the six arrangements of Fig. 8) **is** recoverable, which the repo believed
impossible. Anyone who wants the numeric arrangement data should extract these rather than guess.

## 1. The citation "Lemma A.6" does not exist in the paper

The paper's appendices (from `concordant-srgraph.toc`, verbatim):

| appendix | title | line |
|---|---|---|
| A | Proof of Propositions 5.8 and 5.10 | 51 |
| A.1 | Some graph theoretical preliminaries: Ears | 51 |
| A.2 | **Two lemmas about R-to-R and S-to-S intersections of even cycles** | 52 |
| **A.3** | **Proof of Proposition 5.8** | 55 |
| A.4 | Proof of Proposition 5.10 | 60 |
| B | Proof of Proposition 5.12 | 63 |
| C | Proof of Lemma 6.2 | 67 |

There is no "Lemma A.6". The module docstring in
`CRNT/Multistationarity/TrueSREarCase2.lean` ("Case 2 of Lemma A.6", "Appendix A.3") is pointing at
**Proposition 5.8**, proved in Appendix A.3, *together with* the two unnamed lemmas of **Appendix
A.2**. The statements are numbered `lem:R-to-REarDecomposition` and `lem:S-to-SEarDecomposition` in
the body (§Appendix A.3), not "A.6". This is a citation error, not a content error — the
formalised content is the right content — but it should be corrected, and per
`DEAD-ENDS.md` A-54's own recommendation the same pass should fix the mis-attributed Anderson
citations at `SiphonDimensionDescent.lean:25-27` and `:120-122`.

## 2. What Proposition 5.8 actually says — and it is *not* an ear-exclusion lemma

Verbatim (`Concordant-SRGraph.tex:1370-1378`):

> **Proposition 5.8.** *Suppose that, for the reaction network under consideration, the
> Species-Reaction Graph satisfies condition (ii) of Theorem 2.1. Then, in any source-block of the
> sign-causality graph, at most one of the following can obtain:*
>
> *(i) There is a reaction vertex having more than two adjacent species vertices.*
>
> *(ii) There is a species vertex having more than two adjacent reaction vertices.*

**This is a degree statement, not "the species-to-species ear is impossible."** That distinction
matters for Hole B. The repo's `TrueSREarCase1.lean`/`TrueSREarCase2.lean` docstrings describe the
argument as ruling out "an ear joining two vertices of the stage cycle", which reads as an
exclusion of the configuration. What the paper actually shows (`:1391-1399`) is:

> "we shall suppose the former case and then argue in Lemma `R-to-REarDecomposition` that **all
> subsequent ears in the ear-decomposition must also be reaction-to-reaction paths**. Thus, at each
> stage of the decomposition, new edges are adjoined to old vertices only at R-vertices. **In this
> case, the block can contain no species vertex adjacent to more than two edges.** That is, the
> block is an S-block."

So the proof is a *conditional dichotomy on the first ear*: R-to-R first ear ⟹ S-block (no
high-degree species vertex); S-to-S first ear ⟹ R-block (no high-degree reaction vertex), "by an
almost identical argument, via Lemma `S-to-SEarDecomposition`, with the roles of species and
reactions reversed" (`:1399`). Both ears are *possible*; what is excluded is having both kinds of
high-degree vertex. Framing it as "Case 2 is impossible" overstates the paper.

**Consequence for the residue.** `TrueSRCycleSpeciesDegree.classFlux_trichotomy` (landed in PR #36)
shows a cycle species has exactly one out- and one in-neighbour **over the cycle classes**. The
residue's ear produces a **second out-neighbour, off-cycle**. Proposition 5.8 says that is
impossible *provided* the block has no reaction vertex with more than two adjacent species — which
is precisely the alternative (i) that Proposition 5.8 forbids **together with** (ii). So the residue
is not blocked by a missing σ-sign estimate; it is blocked by needing to establish which alternative
holds, i.e. the dichotomy is a **statement about the block that must be derived, and the paper
derives it from the ear decomposition of the whole block** — not from a single cycle plus a single
path. That is a sharper statement of B-10 than the repo has, and it is `[SOURCED]`.

## 3. Evenness is a *transfer*, never a fresh σ-sign estimate

`Concordant-SRGraph.tex:1437` (the six-arrangements paragraph) verbatim:

> "In each case there are two cycles — one containing the R-to-R ear and the other containing the
> S-to-S ear — that have an S-to-R intersection. Moreover, **each of these cycles is even, either
> because the cycle is directed or as a consequence of Lemma A.4 or A.5**…"

So evenness of the two extracted cycles comes from exactly two sources: (a) the cycle is
*directed* (Appendix A.2's parity lemma), or (b) the A.4/A.5 transfer along a third gluing. This is
what `TrueSREarCase2.lean` implements as `SignDirected σ` (route (a)) and `ssGlueCycle_even_of_partner`
/ `rr_three_glued_even_of_two` (route (b)). **The paper never asks for a σ-sign estimate on off-cycle
species** — which is precisely why `SignDirected` on an ear species is not provable from the
residue's hypotheses, as recorded in `holeB-ss-ear-discharger.md` §4. The Lean formulation is
faithful; the *residue's* hypotheses are too weak to feed it, because the paper's context is a
whole source-block whose species all lie in blocks covered by Proposition 5.10
("all cycles within a source's R-blocks and S-blocks are even", `:859`).

## 3b. The actual target: Proposition 5.11, not `SignDirected` on the ear
Re-reading the source gives a stronger and cleaner statement than the one above. Proposition 5.10
(`prop:EvenCyclesWithinSBlocksRBlocks`, `:863-864`, verbatim):

> **Proposition.** *Every (not necessarily directed) cycle that lies within an S-block or an R-block
> of a sign-causality graph source is even.*

— and it "does not presuppose that condition (ii) of Theorem 2.1 is satisfied" (`:859`). Immediately
after it comes the proposition the residue actually wants (`:869-871`, verbatim):

> **Proposition (`prop:EvenCyclesWithinSource`).** *Suppose that, for the reaction network under
> consideration, the Species-Reaction Graph satisfies condition (ii) of Theorem 2.1. Then in any
> source of the sign-causality graph **every cycle is even**.*

Note the shape: `hSR.2` **is** condition (ii) — the repo's `TrueSRStrongCriterion`
(`TrueChemistrySRCriterion.lean:271-274`) is the two clauses "every even cycle is an s-cycle" and
"no two even cycles have an S-to-R intersection", and the paper's condition (ii) is the latter.
Proposition 5.11 then gives ambient evenness over **every cycle in the source**: no σ-sign
hypothesis, no `SignDirected`, no sign bookkeeping at all.

**So the correct target for the residue is a Lean port of Proposition 5.11.** The ear cycle would
then be even for free and `lemmaA6_case2_*` would apply. It is graph-theoretic, over blocks and
cycles in a source, and the repo already has the vocabulary in-file: `DirectedEarDecomposition`
(`TrueChemistrySRCriterion.lean:183`) and `stronglyConnected_of_directedEarDecomposition` (`:190`),
both unused at the residue.

This supersedes the prioritisation in `holeB-ss-ear-discharger.md` §4: the blocker is **not** a
σ-sign estimate and **not** `harr`. It is that Proposition 5.11 has never been ported, and it is
stated over *blocks of a source*, which needs the block decomposition (paper §5.5,
`BlockTreeGraph.eps`) — the very structure DEAD-ENDS B-10 identified as absent. The next step is to
port Proposition 5.11, not to attempt `no_species_species_ear_of_trueSRCriterion`.

## 4. Is the ear route avoidable? — settled negatively, but for a different reason

Searched the whole `.tex` for an alternative: `grep -n "conc\|Lyapunov\|Liapunov\|deficiency one\|Anderson"`.
The proof of Theorem 2.1 (§5) is entirely the sign-causality-graph route; there is no
Lyapunov-family or deficiency-one shortcut anywhere in the paper, and no reference to Anderson.
Theorem 2.6 (§6) and §7 handle non-fully-open networks by normality/weak-normality/nondegeneracy
and are *extensions*, not alternatives. **The ear decomposition is the proof.** But see §2: the
target is Proposition 5.8/5.10, and the repo's framing ("Case 2 impossible") is stronger than what
is proved.

## 5. The `k = 1` claim

The in-file comment at `TrueChemistrySRCriterion.lean:8600-8607` says "`k = 1` is forced by `hopp`".
Nothing in the paper supports this: `hopp` corresponds to the s-cycle's causal orientation on **cycle**
classes only, and the ear's first hop leaves the cycle by construction. The repo's own DEAD-ENDS B-8
already recorded this as wrong and PR #20's `classFlux_trichotomy` machine-checks the correction.
`[SOURCED]` for the absence: the paper's ear arguments (§Appendix A.3) never invoke a
single-hop-forcing step.

## 6. Summary of what the literature settles

| question | verdict | evidence grade |
|---|---|---|
| "Lemma A.6" | **does not exist**; the content is Prop. 5.8 + App. A.2 lemmas | `[SOURCED]` toc + body |
| S-to-S ear impossible? | **No** — Prop. 5.8 is a degree dichotomy; both ear kinds are possible | `[SOURCED]` `:1370-1399` |
| evenness needs σ-signs on off-cycle species? | **No** — by Prop. 5.10 ambient block-level statement | `[SOURCED]` `:859`, `:1437` |
| is there a route avoiding the ear decomposition? | **No** within this paper | `[SOURCED]` full-text grep |
| `k = 1` forced by `hopp`? | **No** | `[SOURCED]` absence + B-8 |
| are the six arrangements recoverable? | **Yes**, `SixCases.eps` ships in the source tarball | `[SOURCED]` tarball listing |

**Net effect on the residue.** The route is *not* dead, but the target moves: from
`no_species_species_ear_of_trueSRCriterion` (which would need `SignDirected` on ear species, i.e. an
estimate the hypotheses cannot supply) to **a block-level evenness statement in the style of
Proposition 5.10**, applied to the block containing `C` and the ear. That is a restructuring of what
the residue should ask for, not a new analytic estimate — and it is the first time either hole has
been narrowed by an external source rather than by the repo's own ledger.

## 7. Addendum: the corrected target, stated precisely

Re-reading the source after §6 was drafted gave a stronger result, recorded here rather than
rewriting the sections above.

Proposition 5.10 (`prop:EvenCyclesWithinSBlocksRBlocks`, `Concordant-SRGraph.tex:863-864`, verbatim):

> **Proposition.** *Every (not necessarily directed) cycle that lies within an S-block or an R-block
> of a sign-causality graph source is even.*

— and it "does not presuppose that condition (ii) of Theorem 2.1 is satisfied" (`:859`). Immediately
after it comes the proposition the residue actually wants (`:869-871`, verbatim):

> **Proposition (`prop:EvenCyclesWithinSource`).** *Suppose that, for the reaction network under
> consideration, the Species-Reaction Graph satisfies condition (ii) of Theorem 2.1. Then in any
> source of the sign-causality graph **every cycle is even**.*

Note the shape: `hSR.2` **is** condition (ii) — the repo's `TrueSRStrongCriterion`
(`TrueChemistrySRCriterion.lean:271-274`) is the two clauses "every even cycle is an s-cycle" and
"no two even cycles have an S-to-R intersection", and the paper's condition (ii) is the latter.
Proposition 5.11 then gives ambient evenness over **every cycle in the source**: no σ-sign
hypothesis, no `SignDirected`, no sign bookkeeping at all.

**So the correct target for the residue is a Lean port of Proposition 5.11.** The ear cycle would
then be even for free and `lemmaA6_case2_*` would apply. It is graph-theoretic, over blocks and
cycles in a source, and the repo already has the vocabulary in-file: `DirectedEarDecomposition`
(`TrueChemistrySRCriterion.lean:183`) and `stronglyConnected_of_directedEarDecomposition` (`:190`),
both unused at the residue.

### Revised prioritisation

| candidate target | verdict |
|---|---|
| `no_species_species_ear_of_trueSRCriterion` | **wrong target.** Needs `SignDirected` on off-cycle species, which the residue's hypotheses provably cannot supply (`holeB-ss-ear-discharger.md` §4, `hlocal` is a sum). |
| `harr` (the arrangement datum) | **second-order.** Real, tractable finite combinatorics, but only reachable once evenness is in hand. |
| **Proposition 5.11** | **the target.** Under `hSR.2`, every cycle in the source is even; no σ-sign hypothesis; needs the block decomposition (paper §5.5, `BlockTreeGraph.eps`). |

This supersedes the prioritisation in `holeB-ss-ear-discharger.md` §4 and revises my own §4b
assessment there, which named the σ-sign estimate as the true blocker — wrong, because the paper
never asks for one. It also revises the repo's framing: `TrueSREarCase2.lean`'s docstring
("Case 2 of Lemma A.6") both mis-cites (no such lemma; see §1) and overstates (Prop. 5.8 is a degree
dichotomy, not an exclusion of the S-to-S ear; see §2).

Block decomposition of a source is precisely what DEAD-ENDS B-10 identified as absent from the
in-tree proof, so this does not make the residue easy — it makes it a *specific, named, external*
target rather than an open-ended search. No other open PR targets it.

## 8. The definitions a port of Prop. 5.8 / 5.11 needs, verbatim

`Concordant-SRGraph.tex:851-852` (`def:SBlockRBlock`, verbatim):

> A source-block in the sign-causality graph is a **species block (S-block)** if *each species node is
> adjacent to precisely two reaction nodes*. A source-block in the sign-causality graph is a
> **reaction block (R-block)** if *each reaction node is adjacent to precisely two species nodes*.

And `:855`:

> Proposition 5.8 tells us that when condition (ii) … is satisfied, every block within the
> sign-causality graph source is **either an S-block or an R-block** (or both in the case that the
> source-block is simply a single cycle).

Prop. 5.11 (`:869-871`) is stated to be "a direct consequence of the two preceding ones" — i.e.
Prop. 5.8 (block is S or R) composed with Prop. 5.10 (every cycle in such a block is even). It is
**not** independently proved, so a Lean port must supply both halves.

### Why this is the right shape for the residue, stated precisely

Combine the two with the trichotomy already landed in PR #36
(`TrueSRCycleSpeciesDegree.classFlux_trichotomy`). At a cycle species `C.species b`:

- over **cycle** classes: exactly one out-neighbour and one in-neighbour (the trichotomy), so the
  cycle contributes degree 1 out / 1 in at `b`;
- the residue's ear contributes a **second out-neighbour**, which is off-cycle.

So at `b` the block has degree ≥ 2 out — and if the ear's first hop reaches a *third* class,
degree 3, `b` is not an S-block. Prop. 5.8 says that then the block must be an R-block, i.e. **no
reaction vertex has more than two adjacent species vertices**. The ear's interior is off-cycle, and
`hQ0late` forces every interior vertex off-cycle — which is consistent with, not contradictory to,
the R-block reading. The dichotomy therefore does **not** by itself kill the residue; what kills it
is Prop. 5.10's evenness applied to the ear cycle, which is exactly the datum that was never ported.

**Concretely, the port is a three-part development:**
1. `DirectedEarDecomposition`-based decomposition of the block containing `C` (in-file at `:183`,
   `stronglyConnected_of_directedEarDecomposition` at `:190`, currently unused);
2. Prop. 5.8 as an `IsSBlock ∨ IsRBlock` disjunction over that block;
3. Prop. 5.10 as `IsSBlock → (every cycle in the block).Even` and `IsRBlock → (ditto)`.

Only (3) is new mathematics for this tree; (1) is in-file and unused; (2) is a finite
degree-counting argument over a block, which is where `harr` and the six arrangements of
`SixCases.eps` fit. **This is the first concrete decomposition of the residue that has an external
justification for every piece.**

## 9. Mechanical inventory at the residue (checked, so a prover need not re-derive it)

The `W` produced by `exists_minimal_escape` (`:7585`) is a
`(CRNT.relationGraphOn … T).Walk`, **not** a `CRNT.RelPath`. The concatenation `Q0 ++ W` therefore
needs `W` lifted first.

| step | status | evidence |
|---|---|---|
| `RelPath` structure | `vertex`, `mem`, `step` — all three available from `W.getVert`, `W.getVert_mem_support`, `W.connects` | `CRNT/Graph/RelPath.lean` |
| `Walk → RelPath` helper | **NONE in the tree.** `grep -rn "relPathOf\|ofWalk\|toRelPath"` returns zero | checked |
| `RelPath → Adj` helper | exists, `N.relPathAdj` at `:5200` — **wrong direction** | `:5200-5213` |
| `RelPath → Adj` reversed | exists, `N.relPathAdjRev` at `:5554` — also the wrong direction | `:5554` |
| `RelPath` concatenation | exists, `RelPath.concat`, used at `:8400`-ish in the residue's own branch | in-file |
| `RelPath` → `TrueSRSSPath` | exists, `N.relPathToTrueSRSSPath` at `:5475`, **species at both ends** | `:5475-5485` |
| `TrueSRSSPath` ↔ cycle arcs | `ss_gluable_arcs` (`TrueSRSpeciesPath.lean:902`), `ssGlueCycle` (`:548`) | in-tree |
| evenness transfer | `ssGlueCycle_numCPairs` (`TrueSRSSGlueCPairs.lean:107`), `ssGlueCycle_even_of_partner` (Case-2 port) | in-tree |

**So exactly one new mechanical lemma is needed before any mathematics: a `Walk → RelPath` lift
for `relationGraphOn`.** It is a ~10-line structure literal (`RelPath.mk`) and is the first thing to
write. Everything downstream of it is either in-tree or is the Prop. 5.10 port identified in §7-8.

This narrows the residue's *mechanical* cost to one small lemma, and its mathematical cost to the
Prop. 5.10 port — and it confirms the two are separable, so the mechanical one can be landed and
machine-checked independently of the open question about evenness.

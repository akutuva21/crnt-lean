# Negative checklist — routes currently being walked

**Companion to [`../DEAD-ENDS.md`](../DEAD-ENDS.md).** That file records what is dead. This file
records what is *alive*, so a new researcher does not duplicate a colleague's round, and so a
route that quietly dies is not re-walked next round.

**How to read `status`:**

| status | meaning |
| --- | --- |
| `active` | a named researcher is walking it this round |
| `stalled` | announced but no movement visible; a candidate for re-seeding |
| `landed` | produced an elaborating lemma on this route |
| `killed` | dead — see the `DEAD-ENDS #` reference |
| `open` | nobody is on it; **these are the openings** |

**Last refreshed:** round 1, late (post-reframe), 2026-10-03, `adv-negative`. Re-read §1b before taking a slice: the priority order changed three times this round.

> **Round-1 revision (2026-10-03).** Two orchestrator directives landed after this file was first
> written and changed the priority order materially. Both are folded in below:
> * **Hole A was re-read** (`research/HOLEA-FRAMING.md`, ledger §3c, entries **F-1…F-4**). Hole A
>   is **not** Craciun's Theorem B; the conclusion is **strictly weaker** than a ZSH (4.6(i) and
>   4.6(ii) can be dropped); **the hypotheses never supply the fan**, which is the real blocker;
>   and **δ-uniformity is unnecessary** (Remark 9.8). Rows `arch-delta` and `form-scales` are
>   **retired by premise**, and the face-fill routes are **demoted, not killed**.
> * **Hole B's round-1 slices were refuted** (ledger §3b, entries **B-1…B-10**) and reallocated to
>   a single forced route. See §3b of this file for the reallocation table.

---

## 1b. Reallocation tables

### Hole B — round 1 slices refuted, one route survives

Circulated by the orchestrator 2026-10-03. **Read `DEAD-ENDS.md` §3b (B-1…B-10) before taking any
hole-B slice.**

| was | status | ledger ref | now |
| --- | --- | --- | --- |
| `form-sr-deg2a`, `form-sr-deg2b`, `form-sr-parity` | **killed** (degree split degenerate: only deg 3b survives; flux facts already sharp) | B-2, B-5 | **build `exists_second_evenCycle_of_offCycle_escape`** (step 2 of the surviving route) |
| `form-sr-case2` | **killed** — *the datum does not exist in this tree* | **B-9** | **port** the four A.6 Case-2 items from `backup-fig8`/`637a970` |
| `form-sr-hopp` | **killed** as assigned (`hopp` does not force `k = 1`; `hopp` orientation conflicts) | **B-8**, B2 | only `oneStep_fromCycleSpecies_eq_leftEdge`, else help on step 2 |
| `form-sr-route` | **repointed** | — | shortest-path machinery on **`TrueSRSSPath`**, not generic `RelPath` |

**The surviving hole-B route, in order** (step 2 is worth more than 1 and 3 combined):

1. **Port** from `backup-fig8` / `637a970` into a new `CRNT/Multistationarity/TrueSREarCase2.lean`
   (import from `CRNT.lean`): `lemmaA6_case2_twoComponents`, `lemmaA6_case2_oneComponent`,
   `TrueSRCycle.SignDirected`, `TrueSRCycle.sToRIntersectionOfTwoPaths`. **Do not cherry-pick the
   branch wholesale** — its other content depends on unmerged `sr-blocks` (`84e49f2`) and
   `sr-route-ear` (`9285de1`).
2. **Build `exists_second_evenCycle_of_offCycle_escape`** — the actual blocker. Start from
   `relPathToTrueSRSSPath` (`TrueChemistrySRCriterion.lean:5475`); use `ss_three_glued_even_of_two`
   (`:7976`) for parity. If the full statement is false, that is a +30 result — find the
   counterexample.
3. **Only then** edit `:8601–8607`. The 170-line positive branch at `:8376–8546` must keep
   elaborating untouched: do not move `by_cases hv0r` (`:8371`), `exfalso` (`:8355`), or the `hvr`
   split (`:8301`).

**Hole B is AUTHORING, NOT REPAIR** (**B-15**). Repo-wide grep for
`lemmaA6_case2|offCycle_escape|SignDirected|sToRIntersectionOfTwoPaths` over `CRNT/` returns **no
matches**, and `exists_second_evenCycle_of_offCycle_escape` does not exist anywhere in the tree.
Five declarations are being written from scratch.

**Use the public `glueArc` — do NOT lift the `private` modifier** (**B-14**). `TrueSRPath.prepend`
is `private noncomputable def` at `TrueSRParityRR.lean:276` and is unreachable, but it is
consumed internally by the **public**
`glueArc {x y} (X : TrueSRPathRR x) (Y : TrueSRPathRR y) (h : RRGluable X Y) : TrueSRPath
(2 * (y + 1) + 1)` (`:388`), which also carries the edge- and species-disjointness side conditions
a hand-rolled builder would have to re-establish. Species-flavour public entry points: `glueWalk`
(`TrueSRGlueMaps.lean:233`), `glueCycle` (`:245`). **The work is constructing `RRGluable`/`Gluable`
instances, not building paths.**

**The order, in dependency sequence:**

1. Construct the `RRGluable` / `Gluable` instances via the public `glueArc`.
2. Author `SignDirected` — the sign condition that **is** B-12's `hSR.2`, and the missing
   prerequisite.
3. Author `sToRIntersectionOfTwoPaths`, `lemmaA6_case2_twoComponents`,
   `lemmaA6_case2_oneComponent` into a new `CRNT/Multistationarity/TrueSREarCase2.lean`,
   **imported from `CRNT.lean`**.
4. Build `exists_second_evenCycle_of_offCycle_escape` (start from `relPathToTrueSRSSPath`,
   `TrueChemistrySRCriterion.lean:5475`; parity via `ss_three_glued_even_of_two`, `:7976`).
5. Close it in **`hSR.2`**, **never** `hnd` (**B-12**, from **B-1**).
6. **Never** import `TrueChemistrySRCriterion` into the new file — it drags `sorryAx` into the
   ported file's own axiom footprint and couples it to the file we are closing (**B-11**). Note
   that a hole-bearing module still *elaborates* (**F-5**), so only a transitive `#print axioms`
   catches this.
7. Only then edit `:8601–8607`. The 170-line positive branch at `:8376–8546` must keep
   elaborating untouched: do not move `by_cases hv0r` (`:8371`), `exfalso` (`:8355`), or the `hvr`
   split (`:8301`).

**If the full statement of `exists_second_evenCycle_of_offCycle_escape` turns out to be false, that
is a +30 result — find the counterexample.**

### Hole A — **STOP. Every route in this tree is dead.** (ledger §3h)

**Four earlier priority orders are superseded and all four are now void.** Do not start a hole-A
slice from any of them.

**The unifying fact (`3h`, `A-19`, compiled).** `def Permanent`
(`EndotacticPermanence.lean:58`) is
`∃ K, IsCompact K ∧ (∀ y ∈ K, y.Positive) ∧ ∃ v ∈ atTop, closure (image2 ϕ v {x₀}) ⊆ K`.
`omegaLimit_meets_positive_of_permanent` (`:79`) gets `p ∈ K` via
`omegaLimit_subset_closure_image2`, and `hKpos` is **universal over `K`**. So every such
certificate yields **`∀ w ∈ ω, w.Positive`**, while the hole asks only **`∃ p ∈ ω, p.Positive`**
*while permitting* boundary ω-points (`hwmax`, `hzeroMax`, `hPmaxne`). **The hole's hypotheses
assert the negation of the universal form.** No choice of region, barrier or tile data avoids it.

| route | verdict | ledger ref |
| --- | --- | --- |
| `exists_positive_omegaPoint_of_faceRelevantCore` / `_of_tiled_faceCores` | **DEAD** — routes through `exists_positive_omegaPoint_of_coordinate_floors` with `T = S`, and composes `Permanent`. **This kills my own §3g F-3 "branch 1 is live"; recorded, not dropped.** | **3h**, **C-1**, **F-3** |
| `exists_positive_omegaPoint_of_upperRegion` | **DEAD** — `hfloor` cannot hold for a convex region containing both `x₀` and `wmax` | **F-1** |
| `_of_blueprintData` / `_selfConsistent_normals` / `_convex_tiles` / `_of_toric_blueprint` / `_of_toric_halfspace` | **DEAD** — compiled `False` (`BlueprintRouteRefutation`) | **C-1** |
| anything concluding through a `PersistentFrom` certificate | **DEAD** — same fact | **3h** |
| `hm` / `hstart` / `hface` / `hcore` as inputs to any of the above | **WORTHLESS** — they build a goal-equivalent or refuted criterion | **3h**, **#A27** |
| `N.ComparableGrowthDescent` as the surviving target | **DEAD as a stepping stone** — `comparableGrowthDescent_iff_omegaPointPositive` (`:368`) is an `⟨Or.inl h⟩` equivalence. The hole's own header (`:360–367`) admits it. | **3h** |
| **the hole itself** | **NOT refuted.** Craciun's Theorem D (`∀` convergence) is consistent with `wmax`; `wmax` is a transient ω-orbit point. **Craciun delivers `∀`; the hole needs `∃`.** `CodimTwoFaceModel` shows every hypothesis but `hsol` is satisfiable with a false conclusion, so **no static argument of any kind closes hole A.** It needs a genuinely new idea — one that lands in the gap between "positive enough" and "positive universally". | **3h**, **#A16** |

**Scoring warning for round 2 (`A-18`).** The danger now is landing a **goal-equivalent** theorem
and the metric reading it as progress. `measure.py` counts `sorry`s and is honest, but the round
score must apply the **−200 "provable only via a vacuous or goal-equivalent step"** penalty
(`research/README.md` §5) to any such landing.

| priority | route | ledger ref |
| --- | --- | --- |
| — | **Hole A: nothing in this tree works. Assign it only as "find a genuinely new idea".** | **3h** |

**Dropped outright — do not re-seed on any of these:**

| route | why | ledger ref |
| --- | --- | --- |
| build a fan from the stoichiometric data | **RETRACTED — the fan already exists** (`ComplexBalanceStoichFan.lean:98`, `:330`, `:305`, `:140`, `:250`) | **R-1** |
| `ToricEmbeddingWR.lean` | weaker path, `CycleDecomposition` is built by nothing, `mono` refuted (`CycleRateNonMonotone.lean:89`) | **R-2** |
| δ-uniformity / δ-propagation | Remark 9.8 kills it; one blueprint at one δ suffices | **F-4**, A-4 |
| §7.3, and the ε̃ scale system | already proved (five times over) | **A-3**, **A-4** |
| `oneBit*` recursors | prove the wrong theorem (projected, not ambient, rank) | **A-1**, **A-2** |
| deriving `hinterior` from Craciun's hypothesis | `C ⊆ interior K` is **false** on symmetry hyperplanes (`x_i = x_j`) — the normal case | **A-11** |
| a slack `ε(δ)` on the normal | Lemma 9.7's normal conclusion is **non-strict**; any such statement is an unproved strengthening | **A-12** |
| quoting the width-≥δ flatness claim | fails at vertices and 1-dimensional pieces (empty cone interior) | **A-14** |
| consulting `arxiv.org/html/1501.02860v3` | truncates silently at §6.1.2; **no §7, §8, §9**, and `#S9` anchors return the same prefix | **A-10**, **A-15** |
| full-strength faithful blueprints | over-attempted — 4.6(i) and 4.6(ii) need not be established | **#F-2** |

---

## 1. How this file is kept current

This is the single most perishable thing in `research/`. Do this, in this order, each round:

1. **Find the route docs.**
   ```sh
   git ls-tree -r --name-only research/swarm research/routes
   for b in $(git branch -r --list 'origin/research/*' | sed 's|origin/||'); do
     git ls-tree -r --name-only "$b" research/routes 2>/dev/null | sed "s|^|$b: |"
   done
   ```
2. **Read each new or changed `research/routes/*.md`.** Extract: agent, hole, the target Lean
   signature, the claim it depends on.
3. **Cross-check against `../DEAD-ENDS.md`.** If the route's central claim is already an entry
   there, this is a **duplicate**. Do two things, not one:
   * mark the row `killed` with the `DEAD-ENDS #`, **and**
   * message the owning agent (`write agent://<name>`) with the entry number, so the duplicate
     dies in the route doc rather than only in this file.
4. **Add anything new to `../DEAD-ENDS.md`** the owner reported — including their own dead ends,
   which are the most valuable part of a route doc and the part most likely to be dropped.
5. **Update the row** and the "Last refreshed" date.

**Protocol:** §4 of `../DEAD-ENDS.md` (entry format, grading, upgrade rules). If you add a row
here you do not need to touch `DEAD-ENDS.md` unless you learned a failure.

---

## 2. Routes currently being walked

Sourced from `research/LEDGER.md`'s round-1 roster (branch `holes`, swarm base `research/swarm`).
No route documents had landed as of the refresh date; the "target" column is the slice each
researcher was assigned, not a claim about a committed route.

| # | agent | hole | target / slice | status | DEAD-ENDS ref |
| --- | --- | --- | --- | --- | --- |
| 1 | `arch-fanface` | A | polytope / face-lattice architecture; weakest-satisfiable-hypothesis reading; witness construction | active | — see **open route 3** below |
| 2 | `arch-fanfill` | A | recursive face fill, v3 §7.4.3, well-foundedness | active | **#A3** (convex/zonotope global barrier) and **#A27** (recursion principle is vacuous) are the boundaries |
| 3 | `arch-delta` | A | δ-slack, Lemma 9.5/9.7, uniform-vs-combinatorial decay | **retired by premise** | **#F-4** — Remark 9.8: one blueprint at one δ suffices; δ-uniformity is unnecessary. **Do not re-seed on δ-propagation.** |
| 4 | `arch-alt` | A+B | alternative routes and legitimate restatement options | active | — |
| 5 | `arch-sr-case2` | B | A.6 Case-2 source-block datum; in-scope verdict | **killed → port** | **#B-9** — the datum is **not in `holes`**; it lives on `backup-fig8`/`637a970` and must be *ported*, not searched for. **#B-10** — there is no upstream case analysis to thread it from |
| 6 | `arch-sr-deg2` | B | degree-two isolation route, graph-theoretic statement | **killed** | **#B-2** (degree split degenerate), **#B-5** (flux facts already sharp), **#B-1** (`hspan` unsatisfiable), **#B4** (`hopp` unsatisfiable), **#B7**/B-4 (degree-two voids `hSR.2`) |
| 7 | `form-fanface-core` | A | rational cones, faces, normal-cone construction | active | — |
| 8 | `form-fan-incidence` | A | face lattice, common faces, strict rank decrease, ℝ/ℚ bridge | active | **#A27** (lexicographic order ≠ well-foundedness) |
| 9 | `form-domination` | A | dominance ⇒ polarity; non-vacuous 2D witness | active | — |
| 10 | `form-scales` | A | scale hierarchy arithmetic; uniform decay question | **demoted** | **#F-4** (uniformity unnecessary) + **#A-4** (the ε̃ scale system is *already proved five times over*). Live only as joint finite-face-lattice coherence, not as per-chain scale selection. **#A2**: `binaryWordValue` is the wrong termination measure |
| 11 | `form-tiles` | A | tile covering, seam agreement, satisfiability verdict | active | **#A6** (do NOT reintroduce the all-`x` tile), **#A9** (band premise), **#A10** (`hm_of_cone_family`) |
| 12 | `form-barrier` | A | verify + complete the consumer chain; bridge-gap recheck | active | **#P5** — all three bridges are already discharged; do not re-derive them |
| 13 | `form-sr-hopp` | B | `hopp` / k=1 forcing lemma | **killed as assigned** | **#B-8** — `hopp` does **not** force `k = 1` (it constrains only cycle classes; `Q0`'s first hop is off-cycle). **#B2** — the cycle constructor provably cannot satisfy `hopp`. Keep the slice only for `oneStep_fromCycleSpecies_eq_leftEdge` |
| 14 | `form-sr-route` | B | species→reaction shortest-path machinery | **repointed** | **#B9** (global `hnd` unusable), **#B10** (edge- vs vertex-disjointness). Now needs shortest paths on **`TrueSRSSPath`**, not generic `RelPath` |
| 15 | `form-sr-case2` | B | land the A.6 Case-2 datum | **killed → port** | **#B-9**, **#B-10** |
| 16 | `form-sr-deg2a` | B | degree-two case analysis, first half | **killed** | **#B-2** — deg 0/1 impossible, deg 2 vacuous |
| 17 | `form-sr-deg2b` | B | degree-two parity consequences | **killed** | **#B-2** — only deg 3b survives and `hSR` is silent on it; **#B5** |
| 18 | `form-sr-parity` | B | general parity invariant + extension | **killed** | **#B-3** (S-to-S chord invisible to `hSR.2`), **#B13** (`finRotate` is not an involution) |
| 19 | `form-scaffold` | both | three new CRNT concepts formalized | active | — |
| 20 | `form-audit` | both | vacuity, statement-drift, axiom-scan, measure-diff tooling | active | **#P1** (stated-and-elaborated ≠ correct) |
| 21 | `infra-mathlib-poly` | A | empirical Mathlib convex-geometry survey + thin layer | active | **#P4** (no polytope/face-lattice/normal-fan API) |
| 22 | `infra-mathlib-fan` | A | pointed-fan API with constructed examples | active | **#P4** (`IsCompletePointedPolyhedralFan` undefined; `ToricFan.lean:47–51`) |
| 23 | `infra-scaffold-crnt` | both | theorem index, glossary, duplication map, unformalized roadmap | active | — |
| 24 | `infra-build` | both | transactional `close_hole.sh`, ledger reconciliation, `pr_score.py` | active | — |
| 25 | `papers-craciun` | A | Craciun v3 full transcription with Lean notation map | active | **#A29** — the transcription must record the §4/§8 gap |
| 26 | `papers-sf` | A+B | Shinar–Feinberg, Craciun–Fiebig–Singleton, Anderson–Shiu transcriptions | active | **#B5** (A.1/A.3 ear-decomposition existence) |
| 27 | `adv-refute` | A | try to refute hole A's statement; small-instance search | active | **#A16** — a refutation of hole A is *not* possible without violating `hsol`; read this first |
| 28 | `adv-vacuity` | both | vacuous proofs, degenerate definitions, permanent non-vacuity tests | active | **#P1**, **#B15** |
| 29 | `adv-audit` | both | axiom audit of the two chains; statement-drift audit | active | — |
| 30 | `adv-negative` | both | this ledger, evidence grading, negative checklist | active | — |

**Roster source:** `research/LEDGER.md` §Roster. **Route-doc source:** none had landed as of the
refresh date; the "target" column is the assigned slice, not a committed route document. **This
table is therefore the weakest artifact in `research/`** — refresh it as soon as route docs exist.

---

## 3. Open routes — nobody is on these, or the on-owner has not moved

These are the **openings**. Each is grounded in a machine-checked boundary, so it is known to be
worth attempting rather than known to be impossible.

### Hole A

| # | route | grounded in | note |
| --- | --- | --- | --- |
| A-open-1 | **Branch (2): the `K_{x₀}` Step-4 assembly.** Produce a non-convex upper region `Zupper` with a uniform coordinate floor `ε`, containing `x₀`, that the orbit never leaves. | `exists_positive_omegaPoint_of_upperRegion` (`:1596`), `orbit_stays_in_upperRegion` (`:1508`), `persistentFrom_of_upperRegion` (`:1538`) — all three already machine-checked; the *construction of the region* is what is missing. | **The most concrete live route in the file.** It needs no `hMclass`, no convex barrier, no `hsep` — so **#A1** and **#A5** do not touch it. It *is* v3's unproved Step 4 (**#A29**), so a proof here is a genuinely new result. |
| A-open-2 | **Flag-indexed tile shapes with a scale chain** (v3 §7.4.3). Pieces indexed by orderings of `P` with levels from an `ε(α)` chain, simultaneously satisfying `hstart`, `hregime`, `hdeep`. | `margin_of_scale_ratio` → `hm_of_cone_family_margins` → `hm_of_cone_family` are machine-checked; the *shape* claim is not. | **#A11** records exactly why species-indexed pieces fail. **#A6** and **#A9** bound the formulation. `CraciunV3BlueprintScales` gives the scale-selection half only. |
| A-open-3 | **The polytope / normal-fan object itself.** Theorem B needs a family `n C ∈ C` indexed by the cones — the face points of a polytope whose normal fan refines the fan. | absent from Mathlib (**#P4**). | Infrastructure + mathematics. Nothing in the tree can start this without the Mathlib layer. `docs/gac-v3-face-fill-plan.md:150–160` has the target signature. |
| A-open-4 | **The `oneBitFanFaceDependency` recursor's missing caller.** | `FanRefinement` / `ToricUniformWallMargin` carry a well-founded recursor and a complete local atlas, both audit clean, with **no caller emitting geometric data**. | Narrow and well-specified: a face-indexed recursive filler returning the geometric output + compatibility invariant. **#A27** warns that `fill_by_decreasing_rank` is a *vacuous* recursion principle — do not mistake it for this caller. |
| A-open-5 | **A dynamical exclusion of branch (I)** (strictly smaller carried critical siphon). | **#A12** kills the topological method; **#A13** kills the descent iteration. | Must consume `hsol` essentially (**#A16**) and must not route through `ComparableGrowthDescent`. This is Anderson's comparable-growth estimate, unformalised. |

### Hole B

| # | route | grounded in | note |
| --- | --- | --- | --- |
| B-open-1 | **The A.6 Case-2 source-block datum.** | the residue at `:8600–8606` asks for exactly this, or for `hrest` degree-two isolation. | **#B5** is upstream of it: without block maximality and a block tree, `IsEndBlockOn` cannot be inhabited. **#B4** says the naive `hrest` scoping is self-refuting. |
| B-open-2 | **Build the block / directed-ear-decomposition theory.** | `CRNT/Graph/SourceBlocks.lean` has only the first vocabulary layer. | Real unformalized content, a natural `CRNT/Graph/` expansion, and it unblocks B-open-1. Watch the definitional trap recorded at the top of that file (**#B5**). |
| B-open-3 | **Re-orient `hopp` or apply the aggregate endgame.** | **#B2** proves the current constructor cannot satisfy the degree-two endgame's `hopp`. | A **restatement of an existing lemma**, not of the hole — permitted if the commit message carries the mathematical justification. `no_degree_two_aggregate_causal_cycle` (`:4520`) already has a corrected `hopp`. |
| B-open-4 | **Verify or refute B14 (`hreac` needs `hSR.2`).** | the cited script `hreac_needs_hSR.py` is **not in the tree** (**#B18**). | Cheapest open item on either hole. A confirmation or refutation is worth +30 and it is an [N]→[M] upgrade. |
| B-open-5 | **Prop 5.12 for a general source-block structure.** | `exists_cycle_multipliers` (`:3763`) does it for a **single** cycle. | **#B6** says `multiplier_chain` chains in the wrong direction, so the extremal shortest-path solution is not optional. `TrueSRParityRR` notes no max-flow machinery is needed *for the parity lemma*. |

---

## 4. Duplicate warnings

Flagged during the round-1 consolidation, for whoever touches them next:

| route claim | duplicate of | action |
| --- | --- | --- |
| "instantiate `..._of_blueprintData` from the residual's hypotheses" | **DEAD-ENDS #A1**, and **#A5** for `hMclass`, **#A8** for the `hlevel`/`hmin` per-species obstruction | dead before any work is done |
| "prove a globally homogeneous convex barrier / choose zonotope weights" | **DEAD-ENDS #A3** | dead |
| "close branch (I) by iterating the siphon-cardinality descent" | **DEAD-ENDS #A13** | dead |
| "close branch (I) by splitting the species set and using connectedness" | **DEAD-ENDS #A12** | dead |
| "close the tie branch (disjunct 4) with a two-closed-set argument" | **DEAD-ENDS #A15** | **already landed** — this one is closed |
| "restate the true-SR s-cycle condition in net coefficients" | **DEAD-ENDS #B1** | refuted at `S = Fin 2` |
| "apply `no_degree_two_causal_cycle` to the causal-orbit cycle" | **DEAD-ENDS #B2** | refuted (`constructed_hopp_false`) |
| "prove `hSR.2` for a two-species / degree-two network by exhibiting an `SToRIntersection`" | **DEAD-ENDS #B7** | refuted |
| "use `hreac` as a free hypothesis" | **DEAD-ENDS #B14** | [N], unverified lead |
| "supply `hnd` from a minimal causal path" | **DEAD-ENDS #B9** | must use the local form |
| "cite `Gluable → TrueSRCycle` as an unbuilt interface" | **DEAD-ENDS #B17** | superseded — built in `TrueSRGlueMaps.lean:245` |
| "use `TrueSRCounterexample.lean` as a non-vacuity template" | **DEAD-ENDS #B15** | it is **vacuous**; use `TrueSRNetCoeffCounterexample.lean` |
| "prove anything from the static hypotheses of the residual" | **DEAD-ENDS #A16** | dead; `hsol` is the only load-bearing premise |
| "cite relative-entropy blow-up to exclude boundary ω-points" | **DEAD-ENDS #A17** | dead; Mathlib's `log 0 = 0` |
| "use active-wall estimates to build a separating surface" | **DEAD-ENDS #A25** | refuted for weakly reversible networks |
| "attack codimension 0 or a one-species face" | **DEAD-ENDS #A21** | vacuous |
| "rederive the three bridge-gap obligations" | **DEAD-ENDS #P5** | all three already discharged |
| "reparametrise the orbit by `fun t => γ x₀ (max t 0)` for continuity" | **DEAD-ENDS #P5** | fails `HasDerivAt` at `t = 0` |
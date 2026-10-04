# CRNT-Lean proof swarm — charter

**Branch of record:** `holes` (the swarm branches from `research/swarm`, itself a child of `holes`).
**Objective (single scalar, lexicographic):** drive `research/scripts/measure.py` to `holes = 0`.

There are exactly **two** executable `sorry`s left in the whole `CRNT/` tree:

| id | site | theorem | mathematical content |
| --- | --- | --- | --- |
| **A** | `CRNT/Dynamics/HighCodimensionSiphonFace.lean:135` | `Network.exists_positive_omegaPoint_of_highCodimension_siphonFace` | Craciun v3, Theorem B: a toric differential inclusion over a complete pointed fan admits an exhaustive family of zero-separating hypersurfaces. Blocks the Global Attractor Conjecture. |
| **B** | `CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8607` | `Network.stronglyConcordant_fullyOpen_of_trueSRCriterion` | Classical SR graph criterion: reactant/product-separated + every e-cycle an s-cycle + no two e-cycles share an S-to-R intersection ⟹ the fully open extension is strongly concordant. Blocks the multistationarity package. |

Everything else in the tree is `sorry`-free and audits to `[propext, Classical.choice, Quot.sound]`.

---

## 1. The autoresearch formulation

This swarm is modelled on Karpathy's *autoresearch* loop, transplanted to Lean.

1. **One frozen metric.** `research/scripts/measure.py`. Nobody argues about whether progress was
   made; they move the number or they did not.
2. **Many independent trials.** 30 researchers, each owning a disjoint slice of the search space,
   each free to attack it however they judge best.
3. **Keep the improvements, kill the rest.** Every round the orchestrator scores all
   researchers, culls the bottom 30%, and re-seeds with fresh ones. Dead ends are not failures of
   effort; they are the measurement working.

4. **Persistent individuals.** A researcher that finds something real keeps its identity, its
   branch, its worktree, and its accumulated notes across rounds. Continuity beats amnesia.
5. **No self-congratulation.** A lemma that compiles is worth less than a lemma that *closes a
   route step*. A route document nobody can act on is worth nothing. Scoring is done by the
   orchestrator from the tree, not by the researcher from its own optimism.

## 2. Tier hierarchy

The swarm is organised as four tiers with a strict information flow downward. Every tier exists
because a lower tier cannot be done well without it.

### Tier A — Route Architects (`arch-*`)

Own **the mathematics**. Read Craciun v3 / Shinar–Feinberg / Craciun–Fiebig–Singleton / the SR-graph
literature and the existing Lean modules, and decide *what is actually true and sufficient* to
close A or B. Their output is a **route document** in `research/routes/<name>.md` containing:

* a numbered list of the exact intermediate statements, in Lean signature form;
* for each, the mathematical proof sketch with the citation it comes from;
* the dependency order (what must be proved before what);
* an explicit statement of what is *false* or dead, so nobody re-walks it.

Tier A may write Lean, but only to test whether a signature elaborates. Their score is dominated by
whether Tier B can actually execute their route.

### Tier B — Formalization Engineers (`form-*`)

Own **the proofs**. Given a Tier A route, they machine-check the individual steps, one to a few
per researcher, in their own worktree. They may also originate small lemmas and promote them into
routes. Output is committed Lean that elaborates.

### Tier C — Infrastructure & Scaffolding (`infra-*`)

Own **the ground floor**: Mathlib API gaps (there is no polytope/face-lattice/normal-fan API in
Mathlib — this is the single largest infrastructural blocker for Hole A), the `Scaffold/` CRNT
expansion, build/audit tooling, and paper transcription into `research/papers/`. Tier B depends on
Tier C existing; Tier A depends on Tier C for references.

### Tier D — Adversaries & Verifiers (`adv-*`)

Own **honesty**. This is frontier mathematics that has never been formalized, and the dominant
failure mode of an LLM swarm is to produce a beautiful, elaborating, meaningless proof of something
false, or to quietly weaken a hypothesis to make a goal reachable. Adversaries:

* try to **refute** each hole statement and each intermediate lemma, with exact computations and
  small models where possible;
* audit every merged PR for statement-faithfulness (does the proved statement still mean the
  intended one?), for hypothesis-weakening, and for `axiom`/`admit`/`native_decide` abuse;
* verify `#print axioms` on the real declarations;
* maintain the negative-results ledger so dead routes are not re-tried.

A swarm without adversaries converges on self-deception within two rounds.

## 3. Hard rules

* **Never** introduce `axiom`, `admit`, `@[implemented_by]`, `native_decide` over non-`Decidable`
  data, or `sorry` anywhere in `CRNT/` or `Scaffold/`. Two exceptions only, both pre-existing and
  both tracked: the two holes themselves, and `test/` probes.
* **Never** change a theorem's *statement* to make it provable without writing, in the same commit
  message, a mathematical justification and a check that the change is faithful. This happened
  before in this repo (`stronglyConcordant_of_fullyOpen_of_weaklyNormal` was **false as stated**
  and was repaired by adding `hsep`); it is acceptable when documented, and unacceptable when silent.
* **Never** weaken a hypothesis of a hole statement. The two hole statements are fixed. If you
  believe a hole statement is false, that is a Tier D finding, and it must be *proved* (a Lean
  counterexample or exact-rational computation), not argued.
* **Never** run a full `lake build`. Use `research/scripts/checkmod.sh`. The shared build cache
  belongs to the orchestrator; a full build from a researcher destroys the round for everyone.
* **Never** touch another researcher's worktree or branch.
* **Never** merge a PR. Opening and force-pushing is allowed; merging is the human's.

## 4. Work protocol

Each researcher owns:

* a **branch** `research/<agent-name>` off `research/swarm`,
* a **worktree** at `/Users/akutuva/Documents/Proofs/crnt-wt/<agent-name>`,
* at most **one PR** into `akutuva21/crnt-lean`, force-pushed as it accumulates.

Setup (orchestrator does this once; agents do not re-create worktrees):

```sh
research/scripts/newagent.sh <agent-name>     # branch + worktree + .lake/packages symlink
```

Checking your work:

```sh
cd /Users/akutuva/Documents/Proofs/crnt-wt/<agent-name>
research/scripts/checkmod.sh CRNT/Geometry/YourModule.lean
```

Committing and publishing:

```sh
git add -A && git commit -m "..." 
git push -f origin research/<agent-name>
gh pr create --fill --base holes --head research/<agent-name> || gh pr edit --head research/<agent-name>
```

## 5. Scoring

The orchestrator computes each researcher's round score from the tree, not from their report.

| event | points |
| --- | --- |
| a `sorry` in `CRNT/` eliminated and the enclosing module still elaborates | **+100** |
| the whole tree reaches `holes = 0` | **+1000** (split across contributors) |
| a new machine-checked lemma on an identified route, elaborating, used downstream | **+25** |
| a new machine-checked lemma on an identified route, elaborating | **+10** |
| a new `Scaffold/`/`CRNT/` module that others can consume, elaborating | **+8** |
| a route document with signatures + citations + dead-end list that survives adversary review | **+12** |
| a machine-checked **refutation** that kills a route or a statement | **+30** |
| a proved lemma that another researcher's PR builds on | **+15** |
| no commit this round | **0** |
| introduced `sorry`/`axiom`/`admit` outside the two holes | **−60** |
| broke a static gate | **−60** |
| weakened a hole statement's hypotheses silently | **−200** |
| statement provable only via a false step / vacuous hypothesis (caught by audit) | **−200** |

Bottom 30% of the field is retired at the end of each round and re-seeded.

## 6. Provenance corrections

The swarm's own briefs are fallible material and are corrected here as errors are found. These
entries are part of the record, not an embarrassment to be edited away.

### Round 1 — Anderson–Shiu citation (found by `papers-sf`)

An earlier draft of the papers brief cited "Anderson & Shiu, *A facet-scheme for the global
attractor conjecture*, arXiv:2006.02483". Wrong on both counts: arXiv:2006.02483 is a dengue
time-series epidemiology paper, and there is no such facet-scheme paper under that name. The
correct reference is D. F. Anderson, *The dynamics of weakly reversible population processes near
facets*, SIAM J. Appl. Math. **70** (2010), 1840–1858, **arXiv:0903.0901**. The repository already
cites it correctly at `CRNT/Dynamics/FacetRepulsionAndersonShiu.lean:22-24`. Anderson's Theorem 3.2
is the near-facet estimate that closes hole A's codimension-1 case, and its corollary covers GAC
where the associated invariant manifolds are two-dimensional — precisely the boundary hole A sits
on. **Do not "fix" the repository toward the wrong identifier.**

### Round 1 — provenance of the `wmax`/`Pmax` package (found by `papers-sf`)

`BRIEF-B`'s framing attributed the persistence entry-loss function and entry-time matrix to
Craciun–Nazarov–Pantea and claimed the `wmax`/`Pmax` package "comes from it". Having read CNP in
full (arXiv:1010.3050; note the publication year is **2013**, SIAM J. Appl. Math. 73(1), 305–329,
not 2010), that premise is **false**: CNP contains no entry-loss function, no entry times and no
entry-time matrix. Its mechanism is an invariant convex polygon whose sides are orthogonal to
normals of `conv(SC(N))`, and it is a two-/three-dimensional theory. The entry-time machinery
belongs to D. F. Anderson, *Global asymptotic stability for a class of nonlinear chemical
equations*, SIAM J. Appl. Math. **68** (2008), 1464–1476 (full text not accessed; only the
bibliographic fact is asserted). Separately, `relEntropy` + tiers + Stiemke is Anderson,
arXiv:1101.0761 (SIAM J. Appl. Math. 71 (2011), 1487–1508), whose mechanism is monomial tiering
along a subsequence — also not an entry-loss function. The repository's existing provenance notes
(`CRNT/Dynamics/KnownGlobalPersistenceClasses.lean:16-17`, `CRNT/Dynamics/EndotacticPermanence.lean:9`)
were correct; the brief was not.
---

## 7. The ledger trap — read before you touch `scripts/unverified_modules.txt`

**`scripts/unverified_modules.txt` is a list of modules Lean has never successfully elaborated. It
is not a registry of interesting modules, of frontier candidates, or of things you want built.**

It becomes `excludeGlobs` of the `CRNT` lean library. **Listing a hole-free module there removes it
from `lake build CRNT`**, and it stops being elaborated by `CRNTFrontier` too. You would be taking a
working module out of every build target in the tree, silently, and everything downstream of it
would stop being checked.

What happens for free, with no ledger edit and no generator run:

* A new file under `CRNT/` is picked up automatically. The verified library's globs are
  `["CRNT", "CRNT.+"]` — pattern-based — so a new module is in `lake build CRNT` the moment it
  exists.
* Not appearing in `CRNTFrontier.lean` is not lost coverage. That target is the set of modules that
  have **ever failed** to elaborate; it is a diagnostic, not a build.
* To get a module into the verified *umbrella*, give it an `import` line in `CRNT.lean`. That is an
  import, not a ledger line — and it is what `scripts/promote.py` and `scripts/close_hole.sh` do.
* `python3 scripts/gen_lakefile.py --add M` is correct in exactly one situation: you added a module
  and `lake build` genuinely cannot elaborate it yet (a stub, or it depends on an unproved hole).
  It refuses to write if the entry would transitively hide anything.

**Never hand-edit `lakefile.toml` or `CRNTFrontier.lean`.** Both are generator-owned. Run
`python3 scripts/gen_lakefile.py` and commit the result; `--check` is a CI step.

**The ledger cannot detect holes — by construction.** Every hole is off-ledger, because a
hole-bearing module still *elaborates* (with `sorryAx`). That is why `scripts/close_hole.sh` treats
`scripts/dump_sorries.py` as the primary signal and the ledger step as the follow-up, and why its
`#print axioms` check is the **transitive** version: it catches a module that is clean in isolation
but imports something unverified — exactly the trap `TrueChemistrySRCriterion` sets for Hole B.

*found-by `infra-build`, round 1.*

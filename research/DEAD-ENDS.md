# Dead ends

Consolidated negative results. **A route listed here must not be re-walked** until the stated
condition for reviving it is met.

Evidence grades: **[V]** verified by reading the cited source in this repo or by a check that was
actually run; **[H]** hearsay — paraphrased by a prior agent and never independently verified.

Format: one block per entry. `found-by` / `round` / `revive-when` are mandatory.

---

## A-1. The `oneBit*` fan-face recursors prove the wrong statement **[V]**

- **found-by:** `arch-fanfill` · **round 1** · **revive-when:** a recursor ranking **ambient** faces
  exists with a genuinely rank-decreasing Case 1.1 → 1.2 edge.
- **What was tried:** drive Craciun v3 §7.4.3 Case 1.1 → Case 1.2 through the existing
  `oneBitFanFaceDependency` / `OneBitFanFaceSeamDependency` / `finiteOverlapDependency`
  recursors in `CRNT/Geometry/FanRefinement.lean`.
- **Why it fails:** all three rank their tasks by the `coneSpanRank` of the **projected** (`Fin n`)
  fan cell plus a strip/endpoint bit. Craciun's Case 1.1 → 1.2 edge joins two **ambient**
  (`n+1`)-dimensional faces with the *same* `π_n`-image. In that order the edge has rank change 0,
  exactly the zero-decrease case flagged in the comment at
  `hyperplaneArrangementCommonFace_rank_decrease` (`FanRefinement.lean:2221`).
- **Why this is dangerous:** a proof built on these recursors elaborates, looks right, and proves a
  different theorem. It will not fail loudly.
- **Evidence:** the ranking fields of the three recursors versus the projection-equality edge
  required by Craciun Remark 7.6 (`f-nbhd(σ₀) = ⋃{T_n : basepoint(T_n) ∈ σ}`).

## A-2. `binaryWordValue` is the wrong termination measure **[V]**

- **found-by:** `arch-fanfill` · **round 1** · **revive-when:** a well-founded word order that
  *decreases* along the recursion edge is defined.
- **Why it fails:** it is **anti-monotone**. Later letters carry larger weights, so
  `value (α ++ [true]) = value (α ++ [false]) + 1` — the recursion runs *upward*. Craciun's footnote
  81 says ε(α) "grows exactly in the opposite direction than the standard ordering of the binary
  numbers", confirming the Lean encoding uses the wrong order.
- **Site:** `CRNT/Geometry/ZeroSeparatingInduction.lean:2337`.

## A-3. §7.3 is **not** open — do not re-attack **[V]**

- **found-by:** `arch-fanfill` · **round 1** · **revive-when:** never.
- **Status:** closed **for a single chain**. `CoordinateProjectedFaceChain.preBlueprintNeighborhood`
  (`ZeroSeparatingInduction.lean:1831`) is a `def` well-founded by `termination_by k => k`, with
  `face_subset_preBlueprintNeighborhood` (:1845), `preBlueprintNeighborhood_projected`
  (:1882 — the §7.3 projection-compatibility equation verbatim) and
  `isCompact_preBlueprintNeighborhood` (:1905) all proved.
- **What actually remains:** the *joint finite-face-lattice* version with Step 2 subdivision.

## A-4. The ε̃ scale system (Craciun eq. 19) is **not** open — do not re-attack **[V]**

- **found-by:** `arch-fanfill` · **round 1** · **revive-when:** never.
- **Status:** proved five times over in `CRNT/Geometry/ZeroSeparatingInduction.lean`:
  `exists_binaryWordTileScale_separation_on_chain` (:2741),
  `exists_uniform_binaryWordTileScale_separation_on_chains` (:2784),
  `exists_binaryWordTileScale_separation_on_allOnes` (:2831),
  `exists_uniform_coherentBinaryWordTileScale_full_chain_separation` (:2866),
  `exists_uniform_coherentBinaryWordTileScale_separation` (:3061).
- **Consequence:** any route needing coherent scales *on one chain* already has them.

## A-5. `Refines` is set-containment, not face-to-face equality **[V]**

- **found-by:** `arch-fanfill` · **round 1** · **revive-when:** a refinement predicate carrying the
  projection equality as a field exists.
- **Why it fails:** `Refines` (`FanRefinement.lean:94`) is set containment, and that module's own
- **Evidence:** the definition at `FanRefinement.lean:94` is `⊆`, not equality; the module's own
  comment at :3675 says the raw image family "need not satisfy the fan intersection axioms itself".
  So `π_n(B^ff_n) = B^ff_{n-1}` cannot be extracted from it.

## A-6. ~~"IsCompletePointedPolyhedralFan does not exist"~~ — **RETRACTED, the entry was WRONG** **[V]**

- **found-by:** `arch-fanfill` · **round 1** · **RETRACTED in round 1; orchestrator verified against
  the tree.**
- **The claim was false.** `IsPolyhedralFan` **does exist**, at
  `CRNT/Geometry/ConeFace.lean:196`, as a structure over `Fan E` carrying exactly the three clauses
  the plan said were missing: `faces_mem` (closure under exposed faces), `inter_common` (pairwise
  intersections coincide with a common cone), `covers` (the cones cover the ambient space).
  `CRNT/Geometry/PolyhedralFan.lean` exists and is already imported by `ToricInclusion.lean`;
  `IsPolyhedralFan.negated` is proved at :242.
- **Where the real gap is, corrected:** not the *predicate* but the **witness**. Nothing constructs
  a `Fan E` satisfying `IsPolyhedralFan` from CRNT data. That is task P1 in
  `research/HOLEA-FRAMING.md`.
- **Lesson recorded.** This entry was an inference from `docs/gac-v3-face-fill-plan.md`, not a
  check against the tree — a prior document's claim relayed as fact. **Grep the tree before
  recording an absence.** The retraction is kept, not deleted: the history of the error is part of
  the record.
## A-11. `CraciunZSH.hinterior` is **not** the paper's hypothesis, and the difference is fatal **[V]**

- **found-by:** `arch-delta` · **round 1** · **revive-when:** never.
- The repo packages the hypothesis as `C ⊆ interior K_C`. Craciun's actual hypothesis is
  **`C ⊆ relint_Ω K_C`**. Deriving the packaged version from the paper's version is **false** for
  every cone lying in a symmetry hyperplane `x_i = x_j` — which is the normal case for the
  `x₁–x₃`-symmetric arrangement fan the paper assumes (its own footnote 127).
- **Action:** attempt the **relint-chamber variant**, not the interior variant. Add a
  `chamber : Set E` hypothesis with `C ⊆ chamber` and `chamber ⊆ K`, replace `C ⊆ interior K` by
  `∀ x ∈ C ∩ sphere 0 1, ∃ ρ > 0, ball x ρ x ⊆ K ∩ (affine span of chamber)`, and conclude
  `∃ M, ∀ x, infDist x C < δ → M < ‖x‖ → x ∈ K`. That is exactly Lemma 9.7's hypothesis and it
  unblocks every real application.

## A-12. Lemma 9.7 has **no** quantitative bound on normal straying **[V]**

- **found-by:** `arch-delta` · **round 1** · **revive-when:** never.
- `BRIEF-A.md` §A.5 item 3 asked for "how far a normal may stray". That premise was wrong: the
  lemma's normal-membership conclusion is **non-strict** (`n ∈ C`, a closed cone), and the only
  quantification is an existential threshold "ε̂ small enough", realised in the proof as
  `‖log P‖ ≥ max_C M_C`. **Any Lean statement putting a slack `ε(δ)` on the normal would be an
  unproved strengthening nobody has made.** Do not attempt it.

## A-13. The n-dimensional upgrade of Lemma 9.7 is **not in the paper** **[V]**

- **found-by:** `arch-delta` · **round 1** · **revive-when:** only by proving it from scratch.
- Lemma 9.5/9.7 are stated only for `ℝ³` / `(0,1)³`, yet §8 Step 2 invokes 9.7 in `n` dimensions.
  The upgrade is not written down in v3 and is not derivable from the printed statements.
  **Record it as an independent, unwritten generalization** rather than assuming it.

## A-14. The width-≥δ flatness claim needs a qualification the repo omits **[V]**

- **found-by:** `arch-delta` · **round 1** · **revive-when:** never as stated.
- As written in `HANDOFF_gac_hole.md` §4 and the `HighCodimensionSiphonFace.lean` header, the
  argument fails at vertices (dimension 0) and on 1-dimensional pieces, where the cone has empty
  interior. The **polyhedrality conclusion survives** via the weaker dimension-free and δ-free
  statement; the intermediate claim does not hold everywhere.

## A-15. Craciun v3 §7/§9 is reachable only via alphaxiv **[V]**

- **found-by:** `arch-delta` · **round 1** · **revive-when:** never.
- `arxiv.org/html/1501.02860v3` silently truncates at §6.1.2 with **no error**; `#S9` anchors return
  the same truncated prefix. `arxiv.org/e-print/…` returns an archive listing, not the `.tex` body.
  ar5iv times out. The working route is `https://www.alphaxiv.org/abs/1501.02860v3`; the PDF is
  complete. **A researcher who fetches the HTML concludes §7–§9 do not exist.**

## B-11. The `TrueSREarCase2.lean` port cannot be a file copy **[V]**

- **found-by:** `arch-sr-case2` · **round 1** · **revive-when:** never.
- Line 1 of that file is `import CRNT.Multistationarity.TrueSREarCase1`, and
 **`TrueSREarCase1.lean` does not exist on `holes`**. The port must be re-authored from the import
  line up.
- Similarly `TrueSRCycle.even_of_signChange` appears nowhere in `CRNT/`; the base has only
  `private theorem N.trueSRCycle_even_of_signChange` (`TrueChemistrySRCriterion.lean:6885`). A
  public version must be proved.
- **Do not** let the ported file import `TrueChemistrySRCriterion` — it would drag `sorryAx` into
  the port's axiom footprint and couple it to the file we are trying to close. The branch file's
  comment at line 190 deliberately avoids this; **preserve that isolation**.

## B-12. The ear route must terminate in `hSR.2`, not in `hnd` **[V]**

- **found-by:** `arch-sr-case2` · **round 1** · **revive-when:** never.
- By B-1, every cycle-species-to-cycle-reaction SR edge is itself a cycle edge, so an ear glued to
  `C` reintroduces cycle edges at its endpoints and `hnd` can never hold. The ear must close via
  `hSR.2` using `lemmaA6_case2_*` / `sToRIntersectionOfTwoPaths`.

## A-7. The Anderson–Shiu route is correctly cited and must not be "corrected" **[V]**

- **found-by:** `papers-sf` · **round 1** · **revive-when:** never.
- Correct source: D. F. Anderson, *The dynamics of weakly reversible population processes near
  facets*, SIAM J. Appl. Math. **70** (2010) 1840–1858, **arXiv:0903.0901**. Theorem 3.2 is the
  near-facet estimate closing hole A's codimension-1 case.
- `CRNT/Dynamics/FacetRepulsionAndersonShiu.lean:22-24` already cites it correctly.
- **arXiv:2006.02483 is a dengue epidemiology paper and is not the source.** An early swarm brief
  asserted it was; that assertion was wrong and is recorded rather than deleted.

## A-8. CNP does not contain the entry-loss function or the entry-time matrix **[V]**

- **found-by:** `papers-sf` · **round 1** · **revive-when:** never.

## A-9. Craciun v3 is **arXiv:1501.02860**, not 2306.03055 **[V]**

- **found-by:** `papers-craciun` · **round 1** · **revive-when:** never.
- arXiv:2306.03055 is "Analyzing Syntactic Generalization Capacity of Pre-trained Language Models
  on Japanese Honorific Conversion" (Sekizawa & Yanaka, cs.CL). The correct paper is
  **arXiv:1501.02860**, G. Craciun, *Toric Differential Inclusions and a Proof of the Global
  Attractor Conjecture*, v3.
- The repository's own notes were right (`docs/persistence-gac.md:283`, `:300`); the swarm brief
  was wrong.

## A-10. The arXiv HTML of Craciun v3 is truncated — do not use it **[V]**

- **found-by:** `papers-craciun` · **round 1** · **revive-when:** never.
- `arxiv.org/html/1501.02860v3` ends mid-sentence in §6.1.1 and contains **no §7, §8 or §9**.
- Those are exactly the sections hole A needs. **A researcher who consults the HTML will
  silently conclude §7–§9 do not exist.** Use `arxiv.org/pdf/1501.02860v3` (91 pages, complete).
- Additionally: figures 1–15 are not machine-extractable and the constructions in §5, §6.1.1 and
  §6.2.1 are specified largely by figure reference, so their numeric blueprint data (specific ε
  values, red-dot placements, face enumerations) is **not recoverable from text**. Routes needing
  those numbers must reconstruct them or route through the textual §7.
- The LaTeX source tarball exists but the read tool cannot descend into the gzip; statements must
  be taken from the PDF.
- Craciun–Nazarov–Pantea (arXiv:1010.3050; **SIAM J. Appl. Math. 73 (2013), 305–329** — the year is
  2013, not 2010) contains no entry-loss function, no entry times, no entry-time matrix. Its
  mechanism is an invariant convex polygon orthogonal to normals of `conv(SC(N))`, in dimension
  ≤ 3. The entry-time machinery is D. F. Anderson, SIAM J. Appl. Math. **68** (2008), 1464–1476
  (full text not accessed; bibliographic fact only). `relEntropy` + tiers + Stiemke is Anderson
  arXiv:1101.0761.
- **Consequence:** the `wmax`/`Pmax` package in `HighCodimensionSiphonFace.lean` is **not** CNP's
  construction and must not be justified by citing CNP.

---

## B-1. The `hspan` witness for `no_spanning_path_of_trueSRCriterion` is **refuted** **[V]**

- **found-by:** `arch-sr-deg2` · **round 1** · **revive-when:** never, unless `hnd` is replaced by a
  satisfiable predicate.
- **What was tried:** supply the `hspan` witness (`∃ M, Q, hQ0, hQlast, hQnd`) that
  `no_spanning_path_of_trueSRCriterion` needs at `TrueChemistrySRCriterion.lean:8610`, the last step
  before the `sorry` at :8607.
- **Why it fails — a refutation, not a gap:** by `containsEdge_iff_cycleNeighbour`
  (`CRNT/Multistationarity/TrueSRCPairThirdEdge.lean:186`) together with
  `no_single_edge_chord_of_trueSRCriterion`
  (`CRNT/Multistationarity/TrueSRChordExtraction.lean:42`), **every** SR edge joining a cycle species
  to a cycle reaction is a cycle edge. Hence `hnd` at :8610 fails at `p = M−1` for **every**
  candidate `Q`.
- **This is the headline finding of round 1:** the Hole B residue is not merely unproved — the
  hypothesis it needs is unsatisfiable given the lemmas already proved above it.

## B-2. Degree splitting at the residue is degenerate **[V]**

- **found-by:** `arch-sr-deg2` · **round 1** · **revive-when:** never.
- **deg 0 / deg 1:** impossible — `TrueSRDegreeTwoNoSToR.left_right_species_ne` /
  `left_not_sameIncidence_right`.
- **deg 2:** vacuous — `hQ0late` forces `Q0.vertex 1` to be an off-cycle reaction.
- **deg 3a** (extra edge to a cycle reaction): empty, by B-1.
- **deg 3b:** the only surviving case, and `hSR` is silent about it.

## B-3. `hrest` cannot be discharged at the residue **[V]**

- **found-by:** `arch-sr-deg2` · **round 1** · **revive-when:** the upstream case analysis is
  restructured so that `hrest` dominates line 8607.
- **Evidence:** `hrest` is not in scope at line 8607 — it occurs only at lines 1652, 1699, 4327,
  4466, 4536, 4665, 7035, 7117. Its natural instance at the attachment species is refuted by
  `hattachment` itself. Already documented in the docstring of
  `no_degree_two_aggregate_causal_cycle_of_offCycle_hrest` (lines 7006–7018).

## B-4. `no_sToRIntersection_of_degree_two` is unusable as a closer **[V]**

- **found-by:** `arch-sr-deg2` · **round 1** · **revive-when:** never.
- Its hypothesis makes the second conjunct of `TrueSRStrongCriterion` vacuous — it removes the very
  tool the residue relies on.

## B-5. `hopp` / `hcausal` / `¬hnc` are already sharp **[V]**

- **found-by:** `arch-sr-deg2` · **round 1** · **revive-when:** never.
- They determine the class flux at `C.species b` for **all** `n` cycle reactions exactly — two
  nonzeros of opposite sign at the two neighbours, zero elsewhere, by
  `nonAdjacent_cycleClassFlux_eq_zero`. No slack remains to strengthen.

## B-6. The species-interior analogue does not apply **[V]**

- **found-by:** `arch-sr-deg2` · **round 1** · **revive-when:** never.
- Closing Case B via `no_reaction_species_ear_of_trueSRCriterion`
  (`TrueChemistrySRCriterion.lean:5735`) on `qC ⇝ … ⇝ q → s` fails because `s0` sits *strictly
  inside* every such path as an on-cycle species. That is precisely the S4/S5 obligation.

## B-7. `no_spanning_path_of_trueSRCriterion` cannot be applied to `Q0` **[V]**

- **found-by:** `arch-sr-case2` · **round 1** · **revive-when:** never.
- Blocked *provably*, not merely missing. Its hypothesis
  `hlast : C.HasVertex (Q.vertex ⟨M, _⟩)` is unsatisfiable: `hqm` puts `q` at position `m`, and
  `hQ0late` together with `hmpos : 0 < m` forces every index other than `0` off the cycle.
  `Q0` is **half-spanning**, never spanning.

## B-8. `hopp` does **not** force `k = 1` here **[V]**

- **found-by:** `arch-sr-case2` · **round 1** · **revive-when:** never.
- `hopp`, `hcausal` and `¬hnc` together constrain only **cycle** classes at cycle species. The
  first hop of `Q0` lands on an **off-cycle** class, because
  `TrueInternalAggregateCausalEdge` has no `inl → inl` case.
- The source comment's "k = 1 is forced by `hopp`" is therefore **only true for a path that stays
  on the cycle**, and `Q0` is not such a path. **The comment's stated reason is wrong.**

## B-9. **The residue's source comment is factually wrong about the tree** **[V]**

- **found-by:** `arch-sr-case2` · **round 1** · **revive-when:** the port lands.
- The comment at `TrueChemistrySRCriterion.lean:8600-8607` says the residue "awaits the A.6 Case-2
  source-block datum or `hrest` degree-two isolation". **Neither exists in `holes`.**
- The A.6 Case-2 machinery — `CRNT/Multistationarity/TrueSREarCase2.lean` — was written on
  `sr-fig8` / `backup-fig8` (commit `637a970`). That branch was **`reset: moving to ef8048c`** and
  **never merged into `holes`**. The comment describes a proof architecture that is not in this
  tree.
- **Do not search `holes` for the datum. It is not there. Port it.**

## B-10. There is no upstream case analysis to thread a datum from **[V]**

- **found-by:** `arch-sr-case2` · **round 1** · **revive-when:** never.
- `harr`, `hdecX`, `hdecY`, `CE`/`QE`/`PE`/`VE` appear **nowhere above** line 8607, and the whole
  proof constructs only **one** cycle plus **one** aggregate `RelPath`. A.6 Case-2 is not "one
  level up"; it is a different proof.

---

## The Hole B route that survives round 1

Every other route is refuted, so this one is forced and narrow. In order:

1. **Port** from branch `backup-fig8` (commit `637a970`,
   `CRNT/Multistationarity/TrueSREarCase2.lean`) exactly four items:
   `lemmaA6_case2_twoComponents`, `lemmaA6_case2_oneComponent`,
   `TrueSRCycle.SignDirected`, `TrueSRCycle.sToRIntersectionOfTwoPaths`.
   Add a new file and import it from `CRNT.lean`. **Do not cherry-pick the branch wholesale** —
   its remaining content depends on further unmerged side branches (`sr-blocks` `84e49f2`,
   `sr-route-ear` `9285de1`).
2. **Build** `exists_second_evenCycle_of_offCycle_escape` — the ear-extraction producer, which is
   the actual blocker. Start from `relPathToTrueSRSSPath`
   (`TrueChemistrySRCriterion.lean:5475`) to lift the species-to-species `RelPath` to a
   `TrueSRSSPath`, and use the in-tree `ss_three_glued_even_of_two` (:7976) for parity.
3. **Only then** edit lines 8601–8607 to close the ear with the in-scope `hattachment` and feed
   the resulting two even cycles to `lemmaA6_case2_*`. The 170-line positive branch at
   8376–8546 must keep elaborating untouched: do not move the `by_cases hv0r` at :8371, the
   `exfalso` at :8355, or the `hvr` split at :8301.

Step 2 is worth more than steps 1 and 3 combined. It is the single theorem Hole B waits on.

---

## Maintenance protocol

```
### <ID>. <one-line title> **[grade]**
- **found-by:** <agent> · **round** <n> · **revive-when:** <condition, or `never`>
- **Evidence:** <file:line, or the check that was actually run>
```

1. **Grade honestly.** `[V]` only if *you* read the cited source or ran the check this round. `[H]`
   for anything you are relaying. Never upgrade a grade you did not earn.
2. **One block per route.** Merge duplicates, keep both `found-by` attributions.
3. **Add on discovery, not at end of round.** A dead end found in hour 3 saves an hour-8 agent.
4. **Never delete an entry.** If a route is revived, add a new block referencing the old ID and
   explaining what changed.
5. **Do not add a 21st stale progress document.** This file is the index; long form goes in
   `research/routes/`.
## B-13. ~~A dedicated RR reaction-arc builder must be written from scratch~~ — **CORRECTED, IT IS NOT NEEDED** **[V]**

- **found-by:** `arch-sr-case2` · **round 1** · **correction to an earlier orchestrator claim.**
- I told the Hole B group that `arcFwd`/`arcBwd` exist only in the species flavour, so
  `exists_second_evenCycle_of_offCycle_escape` "cannot even be typed" without a new RR
  builder. **That was an over-read of a grep.** Building `reactionArc`/`reactionArcBwd` as
  `TrueSRPathRR` values from scratch, with hand-rolled index arithmetic and hand-proved `RRGluable`
  witnesses, would be a significant waste of round-2 budget.
- The RR arc is available as **`C.speciesArc … .toPath.prepend (…)`**, and the `RRGluable` witnesses
  follow from cycle-edge injectivity — the species arc is already proved (`TrueSRSpeciesPath.lean:902-990`).

## A-16. `exists_positive_omegaPoint_of_upperRegion` is a **dead target** **[V]**

- **found-by:** `papers-craciun` / `adv-audit.DriftA` · **round 1** · **revive-when:** never.
- Its two nominal unbuilt inputs are not equally hard. `hsplit` and `hopenLow`/`hopenUp`/`hdisj`
  are **discharged by construction** — you supply the region decomposition. The entire burden is
  `hfloor : ∀ y ∈ Zupper, ∀ s, ε ≤ y s`, a uniform coordinate floor.
- `hsep_fails_of_boundaryPoint_mem_sublevel` (`:184`) proves that once `x₀` and the boundary
  ω-point `wmax` are both in a convex sublevel, the segment between them takes value `(x₀ s)/n → 0`
  at any `s ∈ Pmax`. **So `hfloor` cannot be established for any convex region containing both
  endpoints** — which is exactly what the hole's hypotheses give.

## A-17. But that refutation does **not** transfer to the live target **[V]**

- **found-by:** `papers-craciun` · **round 1** · **revive-when:** never.
- In `exists_positive_omegaPoint_of_faceRelevantCore` (`:417`) the clause is
  `hsep : ∀ s : S, ∃ ε, 0 < ε ∧ ∀ x, x.Positive → StoichCompatible (γ x₀ 0) x →
  ⟪-m, euclideanStoichState x⟫ ≤ c → ε ≤ x s`.
- The quantifier ranges over **positive, compatible `x` on one side of a single affine
  hyperplane** — not over an ω-limit set containing a boundary point. The segment-to-`wmax`
  refutation needs `wmax` in the sublevel, and **`wmax` is not `Positive`, so `hsep`'s hypothesis
  `x.Positive` excludes it. The refutation does not transfer.**
- **This is the crack, and it is the entire reason the landing site is real.**

## A-18. **Every terminal criterion for Hole A is refuted or goal-equivalent** — VERDICT **[V]**

- **found-by:** `papers-cracuin` (analysis), verified by the orchestrator against the source.
- **Claim 1 — the `PersistentFrom` / `upperRegion` family is goal-equivalent, not weaker.**
  `PersistentOrbit.omegaLimit_positive` (`CRNT/Dynamics/GlobalPersistence.lean:159-162`) is

  ```lean
  theorem PersistentOrbit.omegaLimit_positive (hpers : PersistentOrbit ϕ x₀) :
      ∀ w ∈ omegaLimit atTop ϕ {x₀}, w.Positive
  ```

  **Universally** quantified over ω — not `∃`. Since `hwmax : wmax ∈ ω` and `hzeroMax` +
  `hPmaxne` give `¬ wmax.Positive`, **`PersistentOrbit` is refuted by the hole's own hypotheses.**
  `exists_positive_omegaPoint_of_upperRegion` composes precisely this theorem (`:1534-1536`), and
  `wmax` enters its `K` through `subset_closure (hstay t ht)` — by limits of `γ x₀ t`, forced by
  `hmaps` + `hK`, not by any membership test a supplied region can avoid. **No choice of `Zupper`
  avoids it.** Independently corroborated by `not_persistentFrom_of_mem_omegaLimit_notPositive`
  (`HighCodimensionSiphonFace.lean:407`).

- **Claim 2 — `ComparableGrowthDescent` is the goal renamed.**
  `CRNT/Dynamics/SiphonDimensionDescent.lean:368-377`:

  ```lean
  theorem comparableGrowthDescent_iff_omegaPointPositive
      (hP₀crit : N.IsCriticalSiphon P₀) (hP₀carr : N.SiphonCarried ϕ x₀ P₀) :
      N.ComparableGrowthDescent ϕ x₀ ↔ (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive)
  ```

  with `←` filled by `⟨fun _P _hne _hcrit _hcarr => Or.inl h⟩`. The module's own header at
  `:360-367` says it: "**no proof can assemble the structure** ... as a strictly weaker stepping
  stone to the goal."

- **Claim 3 — the `hsep` / `hfloor` family is refuted outright.** `form-barrier`'s compiled
  `CRNT/Dynamics/BlueprintRouteRefutation.lean` takes the hypotheses of
  `exists_positive_omegaPoint_of_blueprintData` plus hole A's ω-limit hypotheses and concludes
  `False`. Every rung — `blueprintData`, `selfConsistent_normals`, `convex_tiles`,
  `tiled_faceCores`, `faceRelevantCore`, `toric_blueprint`, `toric_halfspace` — routes through
  `exists_positive_omegaPoint_of_coordinate_floors` with `T = S`.

**WHAT THIS MEANS.** The fan exists and the embedding exists, and they are genuine assets. But
**"wire up the existing pieces" cannot close Hole A**: every terminal criterion in the tree is
either refuted or equivalent in difficulty to the hole's own conclusion. A researcher landing
`hm`, `hstart`, `hface`, `hcore`, or a `ComparableGrowthDescent` instance would be landing a
theorem equivalent to Hole A under another name, and reporting it as progress.

Hole A needs a genuinely new idea. That is a negative result about round 1's plan, **not** about
the hole. The hole may still be open and closable; what is closed is the family of routes this
round spent its budget exploring.

**Adversary note (carried to round 2):** the danger now is precisely that someone lands a
goal-equivalent theorem and the metric reads it as progress. `measure.py` counts `sorry`s, which
is honest, but the *round score* must apply the **−200 "provable only via a vacuous or
goal-equivalent step"** penalty from `research/README.md` §5 to any such landing.

## A-19. **The unifying structural fact: `Permanent` is refuted, so the whole ladder dies at once** **[V, compiled]**

- **found-by:** `form-barrier` (compiled), `arch-delta` and `papers-craciun` (independent analyses),
  all converging. **Orchestrator-side correction: the fork was contested and is now settled —
  `form-barrier` conceded after compiling the `False`-level theorem; its four refutation theorems
  stand, only its endgame verdict was wrong.**

- `def Permanent` (`CRNT/Dynamics/EndotacticPermanence.lean:58-60`) is
  `∃ K, IsCompact K ∧ (∀ y ∈ K, y.Positive) ∧ ∃ v ∈ atTop, closure (image2 ϕ v {x₀}) ⊆ K`, and
  `omegaLimit_meets_positive_of_permanent` derives `hpK : p ∈ K` via
  `omegaLimit_subset_closure_image2`. Since `v = univ` in `exists_positive_omegaPoint_of_upperRegion`'s
  call, **`ω ⊆ closure (orbit image) ⊆ K`**, and `hKpos : ∀ y ∈ K, y.Positive` is **universal**.
  So `Permanent` yields **`∀ w ∈ ω, w.Positive`**, while the hole asks only for
  `∃ p ∈ ω, p.Positive` *while permitting* boundary ω-points (`hwmax`, `hzeroMax`, `hPmaxne`).
  **The hole's hypotheses assert the negation of the universal form.**

- This is the same fact as `PersistentOrbit.omegaLimit_positive`
  (`GlobalPersistence.lean:159-162`, also universal), and it subsumes A-11…A-18 and every individual
  `hsep` refutation. **The structural statement:** every certificate in this tree that traps the
  orbit in a region floored away from the boundary *also traps the entire ω-limit set there*, and is
  therefore incompatible with the existence of a boundary ω-point. No choice of region, barrier or
  tile data avoids it.

- **Not a defect of Craciun.** Theorem D (every trajectory converges to `x*`) is consistent with `wmax`:
  `wmax` is a transient point on a ω-orbit. Craciun delivers `∀`; the hole needs `∃`. Different
  statements — which is why the packaged criteria cannot be instantiated here at all.

- **Every pre-packaged criterion is refuted:** `_of_upperRegion` (:1596),
  `_of_blueprintData`/`_selfConsistent_normals`/`_convex_tiles`,
  `_of_tiled_faceCores`/`_of_faceRelevantCore`, `_of_toric_blueprint`/`_of_toric_halfspace`, and
  anything concluding through a `PersistentFrom` certificate containing the orbit image.

- **The surviving target is `Network.omegaLimit_positive_of_descend`** (`SiphonDimensionDescent.lean:137`),
  whose single hypothesis `N.ComparableGrowthDescent ϕ x₀` is **not** touched by the above — it never
  passes through `Permanent`. But its sole field is
  `(∃ p ∈ ω, p.Positive) ∨ (∃ Q, … Q.card < P.card …)`, i.e. the goal disjoined from a strictly
  smaller siphon. Discharging it is exactly as hard as the hole, as the module's own header
  (`SiphonDimensionDescent.lean:360-367`) admits. **Hole A requires a genuinely new idea.**

## A-20. Craciun's Lemma 9.7 does **not** construct the surfaces **[V, transcribed from the PDF]**

- **found-by:** `papers-craciun` · **round 1** · **revive-when:** never.
- Lemma 9.7 is a **sufficient condition given** a family `{Z_ε̂}` per `ε̂`; it concludes
  `T₃` *cannot cross within `(0,1)³`*. §8 Step 2 needs it within `[0,M]^{n+1}` and bridges by
  "reason like in Subsection 6.1.3" — an unquantified proximity argument. So **"supply the blueprint
  data" was never something Lemma 9.7 did for anyone.**
- Clause 9.7(ii) is **simultaneous over all cones**: one normal `n_P` must lie in *every* applicable
  `C`. That is strictly stronger than the repo's `x.Positive`-guarded `hsep`, and it is the source of
  the `relint`-of-`K_C` condition that `CraciunZSH.hinterior` mistranscribes as `⊆ interior`.

## B-14. The RR arc builder already exists as **public** `glueArc` — do not lift the privacy modifier **[V]**

- **found-by:** `form-fanface-core.EmbeddingAudit` · **round 1** · **revive-when:** never.
- `arch-sr-case2`'s self-correction is right that `prepend` is `private noncomputable def`
  (`TrueSRParityRR.lean:276`) and unreachable. **But it is not the only route**: `prepend` is consumed
  internally by the **public** `glueArc {x y} (X : TrueSRPathRR x) (Y : TrueSRPathRR y)
  (h : RRGluable X Y) : TrueSRPath (2 * (y + 1) + 1)` at `:388-392`, which also carries the
  edge-disjointness and species-disjointness side conditions a hand-rolled builder would have to
  re-establish.
- Species-flavour public entry points: `glueWalk` (`TrueSRGlueMaps.lean`:233) and `glueCycle` (:245).
- **The work is constructing `RRGluable`/`Gluable` instances, not building paths. Do not lift the
  `private` modifier — that is the larger and less clean change.**

## B-15. All four port items are **absent** from `holes`, and so is the target **[V]**

- **found-by:** `form-fanface-core.EmbeddingAudit` · **round 1** · **revive-when:** never.
- Repo-wide grep for `lemmaA6_case2|offCycle_escape|SignDirected|sToRIntersectionOfTwoPaths` over
  `CRNT/` returns **no matches**. `exists_second_evenCycle_of_offCycle_escape` itself does not exist
  anywhere in the tree.
- So Hole B is **not a repair** — it is authoring five declarations from scratch (four ported items
  plus the target). The missing prerequisite is `SignDirected` (the sign condition that is
  B-12's `hSR.2`) together with the `RRGluable`/`Gluable` instances.

## A-21. "Frontier membership ⇒ sorry-bearing" is **FALSE**, and it was my error **[V]**

- **found-by:** `infra-build` (correction), attributed correctly by `FormScaffold.ScDefZero` to an
  **orchestrator assertion**, not to the agents.
- I asserted in a broadcast: "`HighCodimensionSiphonFace` is on the frontier (line 2), which is
  consistent with it carrying the tree's one executable `sorry` at :135." **That inference is
  wrong.** The frontier set is the set of modules Lean has *ever failed* to elaborate. A
  hole-bearing module still **elaborates** — with `sorryAx`. So frontier membership carries **no**
  information about holes, and "consistent with" was doing dishonest work.
- **How it propagated:** three agents treated my assertion as corroboration for their own
  independent claim, which laundered a bad orchestrator premise into an apparently-triangulated fact.
  **Record this because it is the swarm's characteristic failure mode in miniature: a confident
  orchestrator premise, accepted by three careful agents, is more dangerous than an agent's own
  error, because nobody re-derives it.**
- **What it licensed:** the claim "closing Hole A closes the GAC chain, one edge wide." On the
  correct method — `form-barrier`'s **transitive-import closure computation** from
  `GlobalAttractorTheorem` (326 modules) finding **exactly one** executable `sorry` at
  `HighCodimensionSiphonFace.lean:135` — that claim **stands**. It was derived from the right
  method. The frontier-membership remark was decoration on top of it, not its basis. But it must be
  **re-derived from `scripts/dump_sorries.py`**, never from frontier membership, whenever it is
  repeated.
- **Standing rule added to `research/README.md` §7:** a green `lake build` carries no information
  about holes, and neither does frontier membership. **Only `scripts/dump_sorries.py` and a
  transitive `#print axioms` carry information about holes.**

## A-22. **CORRECTION TO A-19 — the obstruction is the ∀/∃ mismatch, not `Permanent`** **[V]**

- **found-by:** `papers-cracuin` (correcting me), verified by the orchestrator.
- **I misattributed the mechanism.** `Permanent` is a *hypothesis* of the theorems at
  `EndotacticPermanence.lean:81` and `:116`; the hole never assumes it. Showing `Permanent` is
  *refutable* under the hole's hypotheses is therefore **not** by itself a refutation of Hole A —
  to bite, `Permanent` would have to be *derivable*, which it is not.
- **The obstruction that actually bites** is `PersistentOrbit.omegaLimit_positive`
  (`GlobalPersistence.lean:159-162`), whose conclusion is **`∀ w ∈ ω, w.Positive`**. The hole's
  hypotheses (`hwmax`, `hzeroMax`, `hPmaxne`) **assert its negation**. So any criterion concluding
  the universal form is unsatisfiable here. That — not `Permanent` — is why `_of_upperRegion` and
  the whole `hsep` family die.
- **Recording this so round 3 does not chase it:** A-entries citing `Permanent` send the next
  round after a criterion that was never the problem. The real statement is the `∀`/`∃` mismatch.

## A-23. **Hole A is NOT dead — it reduces to ONE unproved dynamical estimate** **[V, corrected]**

- **found-by:** `form-fanface-core.HoleContext`, verified by the orchestrator against the signature.
- **I over-stated A-19.** "Hole A needs a genuinely new idea" was wrong. What is dead is *every
  pre-packaged criterion in the tree*. That is a fact about the criteria, **not** about the hole.
- `CodimTwoFaceModel.lean` shows the hypotheses are satisfiable-with-false-conclusion **except
  `hsol`** — so it refutes *static* arguments only. `hsol` is the orbit-ODE premise, which is
  exactly what an Anderson-style descent consumes and what every refuted criterion ignores.
- **The reduction, verified:** `Network.omegaLimit_positive_of_boundary_point`
  (`SiphonDimensionDescent.lean:159`) has signature
  `hϕγ hK hmaps hωnn hgenω hωaff hx0pos hdesc hw hs₁ → ∃ p ∈ ω, p.Positive`
  — **the hole's hypotheses minus all the `Pmax` data, plus `hdesc`.** Hence

  ```lean
  exists_positive_omegaPoint_of_highCodimension_siphonFace
    = fun … hdesc => omegaLimit_positive_of_boundary_point … hdesc hwmax
        (hzeroMax ⟨s₀, hPmaxne⟩).2
  ```

  a three-line wrapper. `hxs`/`hcb` then go unused, and `hcodim`, `hcard`, `hrank`, `hmaxExact`,
  `hzcard` are derivable or redundant (:1034, :1053, :1090).
- **The single unformalised object is `ComparableGrowthDescent.descend`**
  (`SiphonDimensionDescent.lean:125-132`): `∀ P, P.Nonempty → IsCriticalSiphon P → SiphonCarried P →
  (∃ p ∈ ω, p.Positive) ∨ (∃ Q, … Q.card < P.card …)`. Its **right disjunct is the analytic
  estimate** the file itself flags as blocked at :531-534; the conservation mechanism
  `eq_zero_on_pmax_of_conservation_eq` (:569) is the missing half.
- **So the honest entry is: "Hole A is closed under all packaged criteria; its residue is a single
  unproved descent estimate, reachable by a three-line wrapper."** That is a *dynamical* estimate,
  which is why `CodimTwoFaceModel` does not touch it.

## A-24. `HighCodimensionSiphonFace.lean:73-76` makes a **false axiom-hygiene claim** **[V]**

- **found-by:** `adv-audit.DriftA`. The "Trust status" block asserts: *"`#print axioms …` reports
  `sorryAx`, and so do exactly its downstream consumers … **No other declaration in the tree does.**"*
- **False.** A tree-wide scan for `^\s*sorry\b` returns exactly two sites —
  `HighCodimensionSiphonFace.lean:135` **and** `TrueChemistrySRCriterion.lean:8607`. It is false in
  the one file whose subject matter is axiom hygiene.
- Docstring-only, cannot break a build, and the cheapest real fix available anywhere. **Round 2
  should land it regardless of what happens to either hole.**

## B-16. The RR arc needs **no** privacy lift and no bespoke builder **[V]**

- `RRGluable` (`TrueSRParityRR.lean:260`) has fields `same_start` :262, `same_end` :264,
  `species_disjoint` :266, `reaction_disjoint` :268, `edge_disjoint` :270.
  `Gluable` (`TrueSRGlueInterface.lean:59`) has `same_start` :60, `same_end` :61,
  `species_disjoint` :62, `reaction_disjoint` :64, `edge_disjoint` :66, plus **public**
  `Gluable.symm` :69.
- `glueArc` (:388) calls the *private* `prepend` internally — legal within the file — so **no
  privacy lift is needed**. Typing note: `prepend`'s receiver is `TrueSRPathRR`, so the
  `speciesArc.toPath.prepend` route is **type-invalid**; build `TrueSRPathRR` from public
  accessors (`vertexAt`/`edgeAt`/`startReaction`/`endReaction`, simp lemmas :99-123), then glue.
- `TrueSRGlueInterface.lean` does **not** import `TrueChemistrySRCriterion` — so the ported file can
  avoid the `sorryAx` coupling (B-11).
- `TrueSRGlueInterface.lean:55-57` notes the `edge_disjoint` clause is what Banaji–Craciun's
  Lemma 10 supplies directly, and that **interior disjointness for a *simple* cycle is not carried
  out there** — a known residual to flag, not to assume away.

## A-25. **`hm` is VACUOUS — `m := 0` satisfies it** **[V]**

- **found-by:** `arch-fanface` · **round 1** · **revive-when:** never as stated.
- `hm : m ∈ N.faceRelevantCore P δ B hcore` is the **only** constraint on `m`, and `faceRelevantCore`
  is a `ProperCone` — a `ClosedSubmodule ℝ≥0 E` (Mathlib `Analysis/Convex/Cone/Basic.lean:61`) —
  which **always contains `0`**. So `m := 0` satisfies `hm`.
- **Do not read progress into instantiating `hm`.** It needs strengthening to `m ≠ 0` **plus** the
  dominance clause. **This trap survives the death of the criteria** and will bite whoever rebuilds
  them: the input that looks like the geometric content of the blueprint is satisfied by zero.

## B-17. **CORRECTION TO B-14 — `glueArc` is NOT the RR arc builder** **[V]**

- **found-by:** `arch-sr-case2` · **round 1** · **retracts B-14's first claim.**
- `glueArc {x y} (X : TrueSRPathRR x) (Y : TrueSRPathRR y) (h : RRGluable X Y) : TrueSRPath (…)`
  (`TrueSRParityRR.lean:388`) takes **two `TrueSRPathRR` values and their `RRGluable` as INPUT** and
  returns a `TrueSRPath`. **It cannot build either of its own inputs, so it is circular as an arc
  builder.**
- **What still stands from B-14/B-16:** the `private` modifier on `prepend` still needs **no** lift —
  `glueArc` calls it internally at :390, which is legal within the file. And `TrueSRPathRR` is a
  plain structure whose `tail` is an ordinary `TrueSRPath`, so an arc is a **structure literal**,
  needing no `prepend` at all. There is no `take`/`init` on `TrueSRPath` (`TrueSRPath.lean:34-37`),
  so a tail must be a literal of length `2*(m-1)+1`.
- **The real prerequisite is unchanged:** constructing `RRGluable` (fields at `:262` `same_start`,
  `:264` `same_end`, `:266` `species_disjoint`, `:268` `reaction_disjoint`, `:270` `edge_disjoint`)
  and `Gluable` (`TrueSRGlueInterface.lean:59`, plus public `Gluable.symm` at `:69`). **That is
  authoring, not building.**

## Durable Tier C work, true regardless of any fork **[V]**

- **The min-max analogue of `barrier_le_of_mem_omegaLimit` is absent.** `HighCodimensionSiphonFace.lean:272`
  has the single-barrier version; grep finds no `minMaxBarrier` there. The union-barrier
  ω-limit closure step is missing. `isClosed_minMaxSublevel` (`PolyhedralBarrier.lean:444`) already
  exists, so this should be mechanical. **True regardless of how the criteria fare.**
- **`(N.faceRelevantCones Pmax δ B).Nonempty` for the source-order fan is not established.** It
  should follow from `Network.deltaCore_mem` / `nearCones_nonempty` plus `IsPolyhedralFan.covers`,
  by the same argument as `CRNT.IsPolyhedralFan.nearCones_nonempty` (`FanFaceLattice.lean`). Cheap
  and mechanical.
- **`Fan E` is an axiom-free `abbrev`** for `Finset (ProperCone ℝ E)` (`ToricFan.lean:50`), so
  `toricField` needs no predicate. `IsPolyhedralFan` (`ConeFace.lean:196`) carries `faces_mem`,
  `inter_common`, `covers`, and `.negated` is proved at `:242`. `Refines` (`FanRefinement.lean:94`)
  is `⊆`-only (A-5). `HasDualFGCells` at `:981`.
- **Check whether `docs/gac-bridge-gap-analysis.lean`'s `ContinuousOn` discharge covers
  `hΓcont : ContinuousOn (γ x₀) (Ici 0)`.** This is a fact about the hole's *own* hypotheses, not a
  criterion input, so the freeze does not apply. The hole supplies `hsol` (`HasDerivAt` for all
  `t ≥ 0`) and `hgenω` (ω-points only); if the bridge closes the forward-ray case, one of the three
  orbit-level gaps is already gone.

## A-26. **ADJUDICATED AND MACHINE-CHECKED — the upper-region criterion is inapplicable** **[V, compiled]**

- **found-by:** `infra-scaffold-crnt`, branch `research/infrascaffold`, commit `ffc02b2`.
  New file `CRNT/Dynamics/UpperRegionFloorRefutation.lean`, imported from `CRNT.lean`.
- **Independently verified by the orchestrator:** `research/scripts/checkmod.sh` reports
  `=== OK (sorry-warnings: 0) ===`. No `sorry`, no `axiom`.
- `false_of_upperRegion_and_boundaryOmegaPoint` (:107) takes **every** hypothesis of
  `exists_positive_omegaPoint_of_upperRegion` — **including `hfloor`** — plus the hole's `hwmax`,
  `hPmaxne`, `hzeroMax`, and concludes `False`. **So `hfloor` is not an unbuilt input awaiting
  discharge; it is unsatisfiable.**
- `positive_omegaLimit_of_confinedToFlooredRegion` (:171) is the bare mechanism with **no**
  reaction-network structure: orbit confined to a floored region ⟹ every ω-point is positive.
- **Why the fork looked contested and was not:** `hfloor` *looks* like a region floor, so it seems to
  escape orbit-level obstructions — but the criterion consumes it through `closure_minimal`, i.e. as
  a statement about `closure Zupper`, and ω-limit points lie in the closure of the orbit image
  (`omegaLimit_subset_closure_image2`), which lies in `Zupper` (`orbit_stays_in_upperRegion`).
  **Steps 1–3 alone give `∀ s, ε ≤ wmax s`.** Neither the entropy level nor compactness is needed.
- **This supersedes the contested verdict of A-19/A-22 and is now the settled one.** `hm`,
  `hstart`, `hface`, `hcore` for `exists_positive_omegaPoint_of_faceRelevantCore` are **known-dead**.
  Do not spend budget on them. And note **A-25**: even before death, `hm` was vacuous (`m := 0`).

## A-27. **151 proved, hole-free modules sit in Hole A's import closure and are never used** **[V, computed]**

- **found-by:** `infra-scaffold-crnt`, `docs/hole-reachability.md` on `research/infrascaffold`.
- Computed from `import` lines plus short-name occurrence — **not curated, so it is checkable**.
  Headline entries: `ComplexBalanceStoichFan` (20 declarations, the source-order polyhedral fan),
  `ComplexBalanceStoichFanInclusion` (38 declarations, the Theorem 4.3 embedding),
  `FaceDirectionCone`.
- **This is the durable Tier C payoff and it survives every refutation above.** The fan and the
  embedding are real, proved, and compiled into Hole A's dependency cone without being called.
  Whatever replaces the dead criteria will need them.

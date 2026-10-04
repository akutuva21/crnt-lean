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

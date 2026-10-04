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
  comment at :3675 says the raw image family "need not satisfy the fan intersection axioms itself".
  So `π_n(B^ff_n) = B^ff_{n-1}` cannot be extracted from it.

## A-6. `IsCompletePointedPolyhedralFan` does not exist **[V]**

- **found-by:** `arch-fanfill` · **round 1** · **revive-when:** `infra-mathlib-fan` lands one.
- **Evidence:** `docs/gac-v3-face-fill-plan.md` records it missing; `ToricFan.lean:47-51` defines a fan
  type omitting the face-lattice and covering axioms entirely.
- **Consequence:** every consumer needing completeness/pointedness has nothing to consume. Tier C
  prerequisite, not Tier B.

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
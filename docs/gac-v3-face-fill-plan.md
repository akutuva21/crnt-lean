# GAC v3 Face-Fill Proof Plan

Goal: remove the remaining `sorry` in `CRNT/Dynamics/GlobalAttractorTheorem.lean`
by completing the Craciun v3 zero-separating construction and connecting it to the
codimension-greater-than-one branch of `Network.complexBalanced_genuinePermanent`.

Canonical checkout: `/Users/akutuva/.codex/worktrees/c259/crnt-lean`, branch
`codex/gac-global-attractor`. Preserve preexisting changes in
`CRNT/Geometry/ZeroSeparatingInduction.lean`, the untracked
`CRNT/Examples/TrueSRNetCoeffCounterexample.lean`, and `scripts/__pycache__/`.

## Paper-to-Lean ledger

| Craciun v3 step | Existing Lean representation | State / remaining work |
| --- | --- | --- |
| §7.3 binary-word scales and projected pre-blueprint neighborhoods | `craciunBinaryWordFiberBox`, `CoordinateProjectedFaceChain.preBlueprintNeighborhood`, scale-separation lemmas | Implemented for a face chain. The dirty theorem proves only the distinct-projection case of Theorem 7.1; retain it. |
| §7.4.3 Case 1.1: lift projected basepoints | `CompactZeroBitFiberPatchCover`, center/basepoint incidence | Local incidence lemmas exist. Need use them in a complete face-indexed construction. |
| §7.4.3 Case 1.2: fill between inherited boundary neighborhoods and subdivide strips | `CompactOneBitFiberPatchCover`, endpoint-graph seam lemmas | Shared strip tiling and compact seams exist. Missing the actual recursive face filler and its boundary-compatibility invariant. |
| §7.4.3 Step 2 / Remarks 7.5–7.7: faithful refinement and approximation | `projectionFiberSubdivisionCenterGraph_*`, compact projective tile refinement | Local tile/basepoint facts exist. Need a global faithful blueprint whose projection and seam data agree across the face lattice. |
| §8 Steps 1–4: arrangement atlas, face filling, exhaustive separating surfaces, invariant region | `FanRefinement` common-face/rank-drop data; `ToricUniformWallMargin` local wall atlas and finite overlap gluing; `ZeroSeparatingSurfaceExists` consumer | Atlas/gluing are local. Missing coherent recursive assembly into a global smooth zero-separating surface, followed by the target consumer. |

## Checklist

- [x] Verify canonical branch, HEAD, target, and preexisting dirty state.
- [x] Read the specified v3 PDF, including §7.3 Theorem 7.1, §7.4.3 Cases 1.1/1.2 and Step 2, and §8 construction outline.
- [x] Build the current geometry-to-target chain; record that the build still accepts the target only because of its `sorry`.
- [ ] Formalize the face-indexed pre-blueprint/faithful-blueprint data required by §7.4.3, reusing current projection chains, shared strips, common-face witnesses, and rank decrease.
- [ ] Prove and apply the rank-decreasing extension step: construct a strip/face piece from all inherited proper-face and endpoint data while preserving exact projection, coverage, disjoint interiors, and seam agreement.
- [ ] Recursively assemble a coherent barrier across the whole finite arrangement; local tile offsets and pointwise overlap smooth-max witnesses alone do not establish a global surface.
- [ ] Construct the `ZeroSeparatingSurfaceExists` witness consumed by the trajectory persistence argument and apply it in the target's higher-codimension branch.
- [ ] Build affected modules in dependency order, then `CRNT.Dynamics.GlobalAttractorTheorem`.
- [ ] Confirm the target source has no `sorry`/`admit`; run `#print axioms` on the exact target and ensure no `sorryAx` or new axiom.
- [ ] Commit only verified, task-related changes; preserve unrelated dirty/untracked work; push and verify the remote SHA.

## Current checkpoint

- Baseline HEAD: `2c19d32b8c613fcdd33d65bafe5e694acf6699be`.
- A targeted `lake build` completed 3,401 jobs. It emitted
  `CRNT/Dynamics/GlobalAttractorTheorem.lean:1442:8 declaration uses 'sorry'`;
  this is not proof completion.
- Added the missing proper-face endpoint edge to `OneBitFanFaceDependency` and
  `hyperplaneArrangementFamily_commonEndpoint_tasks_at`, so endpoint seam data
  can recurse through common exposed faces as strip data already could. This
  formalizes one dependency required by the face fill; the generic recursor is
  still not yet used to produce geometric output.
- Extended each task with a base-tile label. The arrangement atlas indexes
  patches by both a fan cell and a projected small tile; the former task index
  could not distinguish those local patches. Adjacent seam certificates now
  retain the respective incident patch labels.
- `lake build CRNT.Geometry.FanRefinement` could not replace the cached `.olean`
  in `.lake/build` (`operation not permitted`). Compiled the modified module to
  `/tmp/FanRefinement.olean`, overlaid it in a temporary Lean search tree, then
  directly compiled `CRNT/Dynamics/GlobalAttractorTheorem.lean` against that
  tree. Both compilations succeeded; the target still warns that it uses
  `sorry`.
- Ran `#print axioms CRNT.Network.complexBalanced_genuinePermanent`; output
  includes `sorryAx`.
- Axiom audit of the new dependency order and common-endpoint theorem contains
  only Lean's standard axioms; neither introduces `sorryAx`.
- Re-read the actual PDF text for §7.3 Theorem 7.1 and §7.4.3 Case 1.1,
  Case 1.2, and Step 2. The paper's construction requires both (a) lifting each
  inherited lower-dimensional basepoint when the face projection preserves
  dimension, and (b) filling between already-built boundary-face neighborhoods
  when dimension drops, followed by a subdivision satisfying the next-stage
  scale inequalities. The PDF then uses that faithful blueprint recursively to
  build the polyhedral ZSH family in §8.
- Current Lean boundary: `CoordinateProjectedFaceChain` and
  `preBlueprintNeighborhood` carry one projected face chain, not a finite
  subdivision face lattice with a jointly compatible family of chains.
  `CompactZeroBitFiberPatchCover` and `CompactOneBitFiberPatchCover` prove
  local Case 1.1 / Case 1.2 coverage, basepoint, compactness, and seam facts.
  `OneBitFanFaceDependency` plus `oneBitFanFaceDependency_recursion` provide
  only the well-founded index relation and a generic recursor. No caller uses
  that recursor to construct geometric data. The fan atlas provides local
  barrier functions and seam derivatives, but not a face-recursive global
  faithful blueprint or a global surface assembled from it.
- The source-level construction theorem that must be formalized next is a
  face-indexed recursive filler: for each arrangement cell and one-bit strip,
  construct the Case 1.1 lift or Case 1.2 filled strip from all proper exposed
  face and adjacent endpoint predecessors, with exact projection, coverage,
  disjoint interiors, and the higher-stage spanning/scale invariant. The
  current `OneBitFanFaceTask` is the index, but there is not yet a type carrying
  this task's geometric output and compatibility invariant. That output must
  then be consumed to construct `ZeroSeparatingSurfaceExists`; it cannot be
  discharged by `InductionStepHypothesis`, which is an implication supplied as
  an assumption.
- Exact target axiom audit run with `#print axioms
  CRNT.Network.complexBalanced_genuinePermanent`: it currently depends on
  `sorryAx` (as well as Lean's standard `propext`, `Classical.choice`, and
  `Quot.sound`).
- The preexisting dirty `CRNT/Geometry/ZeroSeparatingInduction.lean` lemma and
  unrelated untracked artifacts are preserved. The verified checkpoint was
  committed locally as `05900e8`; the target remains open. Push was rejected by
  automatic review because it treats this private repository payload as
  external source-code egress and says general push authorization does not
  authorize that specific destination. Do not retry by an alternate route
  without destination-specific approval.
- After that commit, corrected the product seam task index to retain only the
  projected small-tile label (the fan cell is a separate index), and added
  proper-face endpoint-to-endpoint and strip-to-strip dependency witnesses.
  Compiled `FanRefinement.lean` directly to `/tmp/FanRefinement.olean`, overlaid
  that artifact into the temporary Lean search tree, and compiled
  `GlobalAttractorTheorem.lean` against it. The exact target axiom audit still
  reports `sorryAx`; the well-founded dependency and common-endpoint lemmas
  report only standard Lean axioms.
- Added `oneBitFanFaceTaskPatch`, whose strip and endpoint cases now return the
  actual restricted strip patch and endpoint-graph patch, plus a face-mono
  lemma under projected-tile containment. Recompiled the geometry module and
  target successfully; the target warning and `sorryAx` remain unchanged.
- Added untagged projected cone tiles, proved exposed-face tile nesting, and
  specialized task-patch nesting to the arrangement tile crossed with each
  small blueprint tile. The endpoint graph is now proved to lie in either
  adjacent closed strip, and `oneBitFanFaceDependency.taskPatch_subset` proves
  every dependency constructor gives an inclusion between its actual task
  patches. The target recompiles, and audits of these new lemmas report only
  standard Lean axioms.
- Added `CompactOneBitFiberPatchCover.arrangementTaskPatch_cover`, identifying
  the actual finite arrangement/small-tile cover with the corresponding task
  strip outputs. The geometry module and target compile against this change;
  the coverage and edge-inclusion audits have no `sorryAx`, while the exact
  target audit still does.
- Extended `fanSmallProductTile_adjacentStrip_seam` to identify an adjacent
  strip intersection with the endpoint task over the actual common fan face
  and the pairwise small-tile intersection. Updated its two consumers, then
  compiled `FanRefinement.lean`, `ToricUniformWallMargin.lean`, and the target
  through the temporary Lean search tree. The seam, coverage, and edge
  inclusion audits contain only standard Lean axioms; the target still has
  `sorryAx`.
- Proved that this pair-labelled endpoint seam output is contained in each of
  its incident strip task outputs, using exposed-face tile nesting and the
  adjacent closed-strip endpoint calculation. Updated the two wall-atlas
  consumers to the current task indices. Recompiled all three affected
  modules and audited the exact target; the new seam inclusion lemmas remain
  `sorryAx`-free, but `Network.complexBalanced_genuinePermanent` still reports
  `sorryAx`.
- The current face-mono lemma still assumes tile containment, and it does not
  itself assemble the inherited outputs or barriers. The arrangement atlas
  gives exact common-face patch intersections, while the radial atlas's smooth
  maximum controls derivatives only at points incident to every listed patch.
  The generic face-task recursion still has no caller that returns those
  covers/barriers. Next refactor the recursive task domain so it consumes these
  pair-labelled endpoint outputs and preserves the scale/faithfulness
  invariant, then derive a global
  `ZeroSeparatingSurfaceExists` witness and apply it in the target branch.
  Keep the checklist open until its exact theorem and kernel axiom audit are
  clean.

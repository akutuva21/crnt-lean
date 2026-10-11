import CRNT
import CRNTFrontier

/-!
# Frontier axiom audit, reconciled with this source tree

`test/FrontierAudit.lean` is excluded from the `test` library and **cannot run against this
snapshot**: eight of the nine declarations it audits do not exist here (all of
`completeOscillationKernelBundle_of_tube`, `planarKernelBundle_proved`,
`vassenaKernelBundle_proved`, `parameterRichCoreKernelBundle_proved`,
`stabilityInheritanceKernelBundle_of_tube`, `recipeZeroKernelBundle_proved`,
`nondegenerateDependentReactionPersistence_proved` and
`stableDependentReactionPersistence_proved` have zero references in `CRNT/`).  It belongs to a
different snapshot than the source.  It is left untouched, because deleting its checks would
silently weaken an acceptance test; reconciling the two is a task for whoever knows where the
oscillation bundle lives.

This file is the gating audit that *does* match the tree.  Both `CRNT` (700 modules) and
`CRNTFrontier` (473 modules) build cleanly, so it can run.

## Why the incomplete results are pinned too

Both former holes are now pinned **clean**.  If a `sorryAx` reappears in either chain, this file
fails and forces the ledger and handoffs to be updated in the same commit.

Regenerate expectations by running the corresponding `#print axioms` and pasting the output.
-/

/-! ## Closed: the Global Attractor Conjecture

The former residual `exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex`
(`CRNT/Dynamics/HighCodimensionSiphonFace.lean`) is proved from
`Network.complexBalanced_forward_floor` (`CRNT/Persistence/ComplexBalancedFloor.lean`).  The whole
chain, up to `complexBalanced_globalAttractor`, is pinned clean.  See `HANDOFF_gac_closed.md`. -/

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex

/-- info: 'CRNT.Network.false_of_vertex_omegaPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.false_of_vertex_omegaPoint

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace

/-- info: 'CRNT.Network.complexBalanced_genuinePermanent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_genuinePermanent

/-- info: 'CRNT.Network.complexBalanced_permanent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_permanent

/-- info: 'CRNT.Network.complexBalanced_globalAttractor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_globalAttractor

/-! ## Closed: the Shinar--Feinberg true-SR criterion

`stronglyConcordant_fullyOpen_of_trueSRCriterion` is now proved by the Banaji--Craciun
determinant argument (`CRNT/Multistationarity/BCFullyOpen.lean`), so it and its consumers must
audit clean.  `test/BanajiCraciunAudit.lean` pins the route itself. -/

/-- info: 'CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion

/-- info: 'CRNT.Network.stronglyConcordant_of_trueSRCriterion_of_weaklyNormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stronglyConcordant_of_trueSRCriterion_of_weaklyNormal

/-- info: 'CRNT.Network.injective_of_trueSRCriterion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.injective_of_trueSRCriterion

/-! ## Clean frontier endpoints

Everything else reachable from `CRNTFrontier` must audit as
`[propext, Classical.choice, Quot.sound]`.  `floquetOrbitalStability_of_tube` is the one check of
`test/FrontierAudit.lean` whose target still exists, and it passes; the three Floquet constructions
that file reports as undeclared (`constructTransverseFloquetSectionData`,
`constructParameterizedPoincarePersistence`, `massActionFloquetData_of_branchMonodromy`) now have
zero references anywhere in `CRNT/`, so that gap is closed. -/

/-- info: 'CRNT.Network.floquetOrbitalStability_of_tube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.floquetOrbitalStability_of_tube

/-! ## The GAC reduction chain must stay clean

If any of these acquires `sorryAx`, the reduction has been short-circuited through the open
obligation rather than proved. -/

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_blueprintData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_blueprintData

/-- info: 'CRNT.Network.orbit_pos_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.orbit_pos_forward

/-- info: 'CRNT.Network.stoichCompatible_of_forward_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stoichCompatible_of_forward_solution

/-- info: 'CRNT.Network.highCodimension_of_not_facet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.highCodimension_of_not_facet

/-- info: 'CRNT.PolyhedralBarrier.minMaxBarrier_le_of_local_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PolyhedralBarrier.minMaxBarrier_le_of_local_descent

/-- info: 'CRNT.ConvexBarrierObstruction.not_exists_weights_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.ConvexBarrierObstruction.not_exists_weights_vector

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

The two open holes are pinned **with** their `sorryAx`.  That makes them gated rather than merely
known: if a third incomplete endpoint appears, or if one of these is closed, this file fails and
forces the ledger and handoffs to be updated in the same commit.  A test that only pins the clean
results cannot notice a new hole.

Regenerate expectations by running the corresponding `#print axioms` and pasting the output.
-/

/-! ## Open: the Global Attractor Conjecture

The residual case is `exists_positive_omegaPoint_of_highCodimension_siphonFace`
(`CRNT/Dynamics/HighCodimensionSiphonFace.lean`), the only `sorry` in the GAC chain.  See
`HANDOFF_gac_hole.md` and `docs/gac-bridge-gap-analysis.md`. -/

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace

/-- info: 'CRNT.Network.complexBalanced_genuinePermanent' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_genuinePermanent

/-- info: 'CRNT.Network.complexBalanced_permanent' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_permanent

/-- info: 'CRNT.Network.complexBalanced_globalAttractor' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_globalAttractor

/-! ## Open: the Shinar--Feinberg true-SR criterion

The remaining `sorry` is the ear-decomposition argument at
`CRNT/Multistationarity/TrueChemistrySRCriterion.lean`. -/

/-- info: 'CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion

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

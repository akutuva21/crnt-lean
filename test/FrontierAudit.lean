import CRNTFrontier

/-!
# Axiom audit for the frontier target

This file is **excluded from the `test` library** (see `scripts/gen_lakefile.py`,
`UNVERIFIED_TESTS`) because `CRNTFrontier` does not elaborate yet.  It is checked in anyway, as the
acceptance test for the oscillation development: the moment `lake build CRNTFrontier` is clean,
delete `test.FrontierAudit` from `UNVERIFIED_TESTS`, regenerate the lakefile, and this becomes a
gating check.

Why it matters: `OSCILLATION_FINAL_HANDOFF.md` claims that
`completeOscillationKernelBundle_proved` is a "zero-input assembly of the repository theorem
routes".  One `#print axioms` on that single definition settles the claim -- it reports every axiom
the whole tower rests on, including `sorryAx` if anything anywhere in it is incomplete.  That check
had never been run.  At the time of writing it would fail, because three load-bearing
constructions in the Floquet chain are referenced but never declared:

    constructTransverseFloquetSectionData      -- FloquetOrbitalStability.lean:162
    constructParameterizedPoincarePersistence  -- FloquetPersistenceGeneral.lean:174
    massActionFloquetData_of_branchMonodromy   -- FloquetPersistenceGeneral.lean:144

so `floquetOrbitalStability_proved`, and with it the `stabilityInheritance` field of the bundle,
has no proof.  See `scripts/frontier_gaps.txt` and LEDGER.md.
-/

/-! ## The closure claim -/

/-- info: 'CRNT.completeOscillationKernelBundle_of_tube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.completeOscillationKernelBundle_of_tube

/-! ## Its five fields, pinned individually so a failure localizes -/

/-- info: 'CRNT.planarKernelBundle_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.planarKernelBundle_proved

/-- info: 'CRNT.vassenaKernelBundle_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.vassenaKernelBundle_proved

/-- info: 'CRNT.parameterRichCoreKernelBundle_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.parameterRichCoreKernelBundle_proved

/-- info: 'CRNT.stabilityInheritanceKernelBundle_of_tube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.stabilityInheritanceKernelBundle_of_tube

/-- info: 'CRNT.recipeZeroKernelBundle_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.recipeZeroKernelBundle_proved

/-! ## The three results the handoff singles out as the deliverables -/

/-- info: 'CRNT.Network.floquetOrbitalStability_of_tube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.floquetOrbitalStability_of_tube

/-- info: 'CRNT.Network.nondegenerateDependentReactionPersistence_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.nondegenerateDependentReactionPersistence_proved

/-- info: 'CRNT.Network.stableDependentReactionPersistence_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stableDependentReactionPersistence_proved

/-!
## Non-vacuity of the tower

An axiom-clean `Prop`-valued bundle still proves nothing if the propositions it bundles are never
inhabited on a real network.  The repository currently contains no network shown to have
`OscillatoryCapacity` unconditionally: `Examples.HopfNetwork3` gets as far as a Hurwitz-boundary
crossing with transversal eigenvalue motion, and stops there.

The check below is the one that would turn the architecture into a result.  It is commented out
because the witness does not exist yet; writing it is the highest-value remaining task.

```
example : CRNT.Examples.HopfNetwork3.N.OscillatoryCapacity := ...
example : CRNT.Examples.HopfNetwork3.N.NondegenerateOscillatoryCapacity := ...
example : CRNT.Examples.HopfNetwork3.N.LinearlyStableOscillatoryCapacity := ...
```

Until one of those type-checks, every `*Target` in the oscillation tree is a statement about
networks that may or may not exist, and a subtly-too-weak `Target` cannot be detected.
-/

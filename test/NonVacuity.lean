import CRNT
import CRNT.Examples.Minimal
import CRNT.Examples.ReversiblePair
import CRNT.Examples.IrreversibleChain
import CRNT.Interop.Analysis

/-!
# Non-vacuity / negative controls

Every check in `Smoke.lean` is a *positive* control: it confirms that some predicate holds where it
should.  Positive controls cannot detect a predicate that holds everywhere, which is exactly the
failure this repository had:

* `HasNoDrainableSiphon`, `HasNoSelfReplicableSiphon` and `MinimalCriticalSiphonDichotomy` were
  defined as `∃ (_ : Unit), True` with `Decidable` instances given by `isTrue`, so the analyzer's
  corresponding flags were `true` for every network and the "proof-producing" bridges into
  `BoundaryOmegaCertificate` fired unconditionally.
* Six certificate structures were `structure C where dummy : True`, so every certificate carried no
  information.
* `StructurallyPersistent`, `StructurallyPermanent` and `IsMassActionFlow` were `:= True`.

A single test asserting that one of those flags is `false` on one network would have failed
immediately.  This file is that test, generalized: for every Boolean the analyzer exposes and every
structural predicate the library exposes, there is a witness on which it is **false**.

Rule for new predicates: a predicate is not finished until this file contains a network where it
fails.  `scripts/check_stubs.py` catches the syntactic shapes above; this file catches semantic
vacuity that is syntactically invisible.
-/

open CRNT
open scoped NNReal

namespace CRNT.Test.NonVacuity

/-! ## Structural predicates: witnesses where they fail

Lines below reuse `decide` only on analyzer fields that `Smoke.lean` already reduces
(`weaklyReversible`, `srSignConsistent`, `acrSpecies`, `numACRSpecies`, `hopfBoundaryMargin`,
`noPositivePeriodicOrbitCertified`).  Compound flags go through their bridge lemmas instead. -/

-- Weak reversibility fails on the irreversible chain and on the minimal network.
example : ¬ Examples.IrreversibleChain.N.WeaklyReversible :=
  Examples.IrreversibleChain.not_weaklyReversible

example : ¬ Examples.Minimal.N.WeaklyReversible := Examples.Minimal.not_weaklyReversible

/-! ## Analyzer flags: witnesses where they are `false`

Each line below pins a flag to `false` on a concrete `NetworkData`.  If a flag ever becomes
unconditionally `true` -- because its underlying predicate was weakened, or because someone
supplied an `isTrue` decider -- the corresponding line stops reducing and this file fails. -/

/-- The data-driven reversible pair `A ⇌ B`, as in `Smoke.lean`. -/
def revPair : NetworkData :=
  { numSpecies := 2,
    reactions := #[ { source := #[1, 0], target := #[0, 1] },
                    { source := #[0, 1], target := #[1, 0] } ] }

/-- The irreversible chain `A → B → C`: weak reversibility must report `false`. -/
def chain : NetworkData :=
  { numSpecies := 3,
    reactions := #[ { source := #[1, 0, 0], target := #[0, 1, 0] },
                    { source := #[0, 1, 0], target := #[0, 0, 1] } ] }

example : chain.analyze.weaklyReversible = false := by decide

-- Both persistence flags are `false` on the chain.  These go through the field bridges rather than
-- `decide` on the flag itself, because `decide` on weak reversibility is not guaranteed to
-- kernel-reduce inside the compound flag (see the note in `Smoke.lean`).  With the old hollow
-- siphon predicates the analogous `noDrainableSiphon` flag could not be made `false` by *any*
-- input, so no proof in this style existed.
example : chain.analyze.persistenceStructural = false := by
  rw [NetworkData.analyze_persistenceStructural_eq,
    show chain.analyze.weaklyReversible = false from by decide]
  simp

example : chain.analyze.persistenceCertified = false := by
  rw [NetworkData.analyze_persistenceCertified_eq,
    show chain.analyze.weaklyReversible = false from by decide]
  simp

-- The SR-sign-consistency verdict is `false` on the reversible pair, so the P-matrix route is
-- genuinely conditional rather than always available.
example : revPair.analyze.srSignConsistent = false := by decide

-- Structural ACR is not universal: the reversible pair reports no ACR species.
example : revPair.analyze.acrSpecies = #[] := by decide
example : revPair.analyze.numACRSpecies = 0 := by decide

-- The Hopf-boundary margin is `none` outside dimension three, so the field is not a constant.
example : revPair.analyze.hopfBoundaryMargin = none := by decide

/-! ## The oscillation exclusion route is conditional

`noPositivePeriodicOrbitCertified` is the disjunction of the deficiency-zero and low-rank routes.
It must be `true` where a route applies and `false` where none does -- a flag that were always
`true` would make `neverPositivePeriodic_of_analyze` an unconditional non-oscillation theorem. -/

-- Rank ≤ 1 route applies to the reversible pair (rank 1), so the flag is `true`.
example : revPair.analyze.noPositivePeriodicOrbitCertified = true := by decide

-- And the certified conclusion really follows from the flag, for this concrete network.
example : revPair.toNetwork.NeverPositivePeriodic :=
  NetworkData.neverPositivePeriodic_of_analyze revPair (by decide)

/-! ## Negative controls that live in the frontier

The strongest available negative control is the Lotka network, which genuinely oscillates and on
which both exclusion routes must therefore fail. It is in `test/LotkaNonVacuity.lean` rather than
here, because `CRNT.Examples.Lotka` has never been elaborated and this file gates the core build.
Move it here once the example compiles. -/

end CRNT.Test.NonVacuity

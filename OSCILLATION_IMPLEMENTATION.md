# Oscillation expansion checkpoint

This checkpoint expands `crnt-lean` with a unified deterministic mass-action oscillation layer.

## Closed in Lean source

- Exact `PeriodicTrajectory` and positive CRN periodic-orbit semantics.
- Exact global-attraction target `HasGloballyAttractingPositivePeriodicOrbit`, quantified over every
  forward mass-action solution in a chosen basin and convergence to the cycle up to phase.
- `OscillatoryCapacity` (existential in positive rate constants) and `NeverPositivePeriodic`
  (all positive rate constants), with their logical equivalence.
- Generic strict-Lyapunov exclusion of a nonconstant periodic trajectory.
- Weakly reversible deficiency-zero -> `NeverPositivePeriodic`, reusing the existing Horn--Jackson
  periodic-orbit theorem.
- Stoichiometric rank at most one -> `NeverPositivePeriodic`, independent of weak reversibility and
  deficiency.  Rank one is proved with a stoichiometric chart, Rolle's theorem, and local ODE
  uniqueness; the equilibrium-intersection step is generalized to arbitrary admissible kinetics.
- Generic periodic + point-convergent -> constant and locally-Lipschitz solution-hits-equilibrium ->
  constant lemmas, so future global convergence theorems can feed the exclusion API directly.
- Proof-carrying tri-state `OscillationCertificate` / proof-erased `OscillationStatus`.
- Total `NetworkData.oscillationCertificate`: currently returns a proved all-parameter exclusion for
  either weakly reversible deficiency-zero networks or stoichiometric-rank-at-most-one networks, and
  `unknown` otherwise; failed sufficient tests never become negative evidence.
- Poincare-return-map fixed point -> common `PeriodicTrajectory` bridge.
- Reaction restriction, minimal oscillatory subnetwork, and explicit inheritance interface.
- `P^-`, real Hurwitz, D-stability, and complementary structural matrix-pattern vocabulary.
- CRN-native child selections, child-selection matrices, strict right-half-plane instability,
  minimal unstable cores, and positive/negative-feedback determinant classification.
- Planar trapped-orbit and Dulac certificate data, with the missing global analytic implications
  represented as explicit propositions rather than axioms.
- Analyzer contract v16 fields:
  - `noPositivePeriodicOrbitCertified` (weakly-reversible deficiency-zero **or** stoichiometric rank ≤ 1)
  - `stoichRankTwo`
  plus kernel bridge theorems and smoke-test coverage.

## Deliberately not faked

The following remain mathematical proof frontiers rather than `axiom`, `sorry`, or heuristic verdicts:

- Poincare--Bendixson in Lean at the required generality.
- Bendixson--Dulac / Green-theorem bridge.
- The full kinetic realization theorem for the 2025--2026 Vassena/Blokhuis/Stadler structural
  oscillation criteria.
- Periodic-orbit inheritance under specific CRN enlargement operations.
- Floquet/Poincare-multiplier orbital stability.
- Global attraction to a limit cycle.
- Stochastic/NFsim oscillation semantics (which are not deterministic periodic orbits).

## Validation status in this environment

The repository was statically checked for internal `CRNT.*` import resolution and for newly introduced
`sorry`/`axiom` declarations.  No Lean or Lake executable is installed in this container, so this
checkpoint could not be elaborated with `lake build` / `lake test` here.  Run the repository's normal
Lean 4.31 / Mathlib 4.31 CI before merging; any elaboration issues should be treated as implementation
bugs, not weakened by replacing proofs with assumptions.

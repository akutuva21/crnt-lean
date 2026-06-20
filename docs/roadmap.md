# Roadmap

The stable core is intentionally narrow. The items below extend it without disturbing
the existing API.

## Verified Boolean decision procedures

Provide computable companions to the propositional graph predicates, related by
equivalence theorems:

- `reachableBool : Network S → Complex S → Complex S → Bool` with
  `reachableBool_iff : reachableBool N c d = true ↔ N.Reaches c d`;
- `weaklyReversibleBool` with `weaklyReversibleBool_iff`.

The natural implementation is a verified finite-reachability closure over the
network's complex carrier (a fixed-point iteration bounded by the complex count, with a
stabilization proof). This makes `decide` close reachability goals directly and lets
`numLinkageClasses` be computed rather than only proved per example.

## Exact rank certificates

Define the stoichiometric matrix over `ℤ`/`ℚ` and check externally supplied row-
reduction certificates, yielding exact rational rank for `stoichRank` without the
noncomputable `Module.finrank`.

## The `crnt_check` tactic

A tactic that discharges the common certificate goals (complex equality, membership in
the complex set, finite reachability, weak reversibility, small deficiency
computations), so generated files need only write `by crnt_check`.

## Deficiency-zero theorem

Prove `∀ N, N.SatisfiesDeficiencyZeroHypotheses → N.DeficiencyZeroConclusion`. This is
substantial algebra; the statement interface in
`CRNT/Theorems/DeficiencyZero/Statement.lean` is already in place.

## Further theory

Deficiency-one theory and multistationarity criteria; absolute concentration robustness
(Shinar–Feinberg); detailed balance; stochastic CRN (CTMC) semantics; and SBML/SBOL
codegen bridges as separate external tools.

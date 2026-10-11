# Handoff: field-map leaves, session 2026-10-11c

## What changed

Eight new modules, each elaborated by `lean` with exit code 0, no `sorry`, and every
named theorem audited to `[propext, Classical.choice, Quot.sound]` by `test/NewLeavesAudit.lean`
(which also contains non-vacuity examples). All eight are imported by `CRNT.lean`.

| Leaf | Old → new | Module | Main declarations |
|---|---|---|---|
| A5 | missing → proved | `CRNT/Identifiability/RateConstants.lean` | `rateConstants_identifiable_iff` (Craciun–Pantea 2008), `massActionVectorField_eqOn_positive_iff`, `Complex.sum_massActionMonomial_eq_zero` |
| F11 | partial → proved | `CRNT/Kinetics/Hill.lean` | `hillKinetics` (an admissible `Kinetics`), `hillKinetics_rate_le`, `hillKinetics_rate_pos`, `michaelisMentenKinetics_rate` |
| E2 | missing → partial | `CRNT/Extensions/Turing.lean` | `Turing.diffusionDrivenInstability_iff`, `exists_nonHurwitz_mode_iff`, `no_instability_of_equal_diffusion`, `opposite_signs`, `exists_growing_mode` |
| S18, A3 | missing → partial | `CRNT/Equilibria/OneSpeciesDescartes.lean` | `card_positiveSteadyStates_le_signVariations`, `positiveSteadyState_unique_of_signVariations_le_one` |
| S17 | missing → partial | `CRNT/Equilibria/ToricSteadyStates.lean` | `toricSteadyState_iff_log_orthogonal`, `toricSteadyState_iff_exp_parametrization`, `HasToricSteadyStates.geomMean` |
| C2 | missing → partial | `CRNT/Computation/StableComputation.lean` | `stablyComputes_of_terminating`; `min`, `+`, `k·`, `max` networks |
| C3 | partial (extended) | `CRNT/Design/Antithetic.lean` | `stochastic_maxRPA_mean`, `Antithetic.closedLoop_deterministic_setpoint`, `Antithetic.closedLoop_stochastic_setpoint` |
| D14 | missing → partial | `CRNT/Dynamics/Contraction.lean` | `Contraction.dist_le_exp_of_contracting`, `tendsto_of_contracting`, `tendsto_equilibrium_of_contracting` |

`docs/field-map.md` (and the copy at the archive root) is updated: tree statuses, leaf rows with
declaration names, and notes saying what each partial leaf still lacks.

## Statement-fidelity notes

* A5 is stated for indexed reactions: parallel reactions and self-loops count as linearly
  dependent, matching the fact that they destroy identifiability. Identifiability means
  agreement of vector fields on the positive orthant implies equal rate constants.
* S17 assumes the binomial description of the steady-state set (the definition of "toric steady
  states"); the criteria that *produce* such a description (Pérez Millán et al., Theorem 3.8's
  hypothesis on the kernel) are not formalized.
* C3 stochastic theorem takes the first-moment stationarity identity `E_π[A q] = 0` as a
  hypothesis; Briat–Gupta–Khammash derive it from ergodicity plus moment bounds. The pointwise
  generator identity `observableGenerator_maxRPACharge` is unconditional.
* D14 is on a real inner product space with the Euclidean one-sided Lipschitz condition; the
  logarithmic-norm (non-Euclidean) contraction used for reaction networks is not formalized.

## Not done

* `test/FieldMapAudit.lean` was **not** regenerated: `scripts/field_map_pins.py` imports `CRNT` and
  `CRNTFrontier`, which could not be built in this environment (1 core, 3 GB RAM). The new names
  are pinned in `test/NewLeavesAudit.lean` instead. Rerun `python3 scripts/field_map_pins.py`
  after a full build.
* `CRNT.lean` itself was not elaborated (needs the whole library); the new modules were built
  individually with `scripts/offline_build.py`.

## Environment notes

* `deriving Fintype` fails in this Mathlib (v4.34.0): the generated instance has a type mismatch
  in `enumList_nodup`. The new example networks use `Fin n` species and reactions instead.
* `Polynomial.eval_finset_sum` is deprecated (`eval_finsetSum`); `MvPolynomial.coeff` takes the
  polynomial first (`p.coeff m`); `Summable.tsum_sub` replaces `tsum_sub`.

## Suggested next steps

1. S18: bound `signVariations` by (number of distinct source complexes − 1) to get the
   Joshi–Shiu one-species corollary.
2. D14: Kamke/cooperative monotone systems.
3. C3: derive the first-moment stationarity identity from a finite-support or Foster–Lyapunov
   moment bound.
4. M11: inheritance of nondegenerate multistationarity (needs the implicit function theorem).

## Addendum (snapshot d)

Added after the first packaging, all compiled with exit code 0 and audited in
`test/NewLeavesAudit.lean` (41 declarations, all `[propext, Classical.choice, Quot.sound]`):

* S18: `card_positiveSteadyStates_le_numSources`, `positiveSteadyState_unique_of_numSources_le_two`
  (in `CRNT/Equilibria/OneSpeciesDescartes.lean`).
* F10/S16: `CRNT/Kinetics/SignVectorCriterion.lean` — `logAffine_affine_injective_iff`,
  `signCondition_iff_signCompatible`, `exists_two_points_of_not_signCompatible`.
* S15 (now proved): `CRNT/Translation/LinearConjugacyCharacterization.lean` —
  `massActionLinearlyConjugate_iff`, `dynamicallyEquivalent_iff_sourceWeightedSum_eq`.

In progress at the time of this snapshot:
* `CRNT/Open/DeficiencyZeroOpen.lean` compiles (exit code 0) but is not yet audited or imported.
* `CRNT/Open/DeficiencyOneOpen.lean` is written but **not yet compiled**.

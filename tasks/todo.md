# Expansion tasks

- [ ] Stochastic: identify a nonduplicate theorem family, implement a complete slice in owned files,
  focused-check principal proofs and record their axioms.
- [x] Realization: `SourceCoefficientCompleteness.lean` proves coefficient extraction, necessity
  from equality on all or positive concentrations, complete finite-union certificates and mismatch
  witnesses. Focused check and six principal axiom guards pass.
- [x] Deficiency/decomposition: `RelationSpace.lean` constructs both block-relation spaces, proves
  rank-nullity, signed deficiency balance, independence characterizations, exact additivity and
  sharp inequality cases. Focused check and eight principal axiom guards pass.
- [x] First partial integration: `lake build +CRNT test.AxiomAudit CRNTFrontier Scaffold` passes
  (4,660 jobs); source-integrity checks pass and the reserved hole file is unchanged.
- [ ] Checkpoint: independent mathematical review, public import integration, axiom audit.
- [ ] Checkpoint: integration builds, unchanged reserved hole, integrity scripts, verified commit/push.
- [ ] Next round: select broader results from the resulting mathematical dependency map.

## Broader slices now selected

- [ ] `RelationMap.lean`: construct the canonical complex-map action between the two relation
  spaces, characterize its kernel, and state faithful injectivity/surjectivity criteria.
- [ ] `FixedComplexRealization.lean`: construct a network on prescribed complexes from positive
  supported channel weights and prove its coefficient formula/realization criterion.
- [ ] After `DirichletForm.lean`: characterize zero energy by enabled-edge increments and
  communicating-class constancy, with positivity discharged from rates and concentrations.

The partial integration builds the public core import closure; the ongoing stochastic draft
is outside that closure until checked. The full-library expansion build remains a later gate.

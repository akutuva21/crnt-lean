# Floquet chain: what is missing, precisely

`CRNT/Oscillation/FloquetOrbitalStability.lean` and `CRNT/Oscillation/FloquetPersistenceGeneral.lean`
carry the claim that closes the oscillation development: a linearly stable positive mass-action
periodic orbit is orbitally asymptotically stable, and that property is inherited across a
stoichiometrically dependent added reaction. `completeOscillationKernelBundle_proved` takes both as
fields, so the "zero-input" closure claim in `OSCILLATION_FINAL_HANDOFF.md` rests on them.

Neither is proved. This file is the inventory, because the gap is much wider than the three
undeclared constructions visible to `scripts/check_undefined_names.py`.

## 1. Two imported modules did not exist

```
CRNT.Dynamics.FlowSmoothDependence     <- FloquetOrbitalStability.lean:4, PlanarFlowRegularity.lean:3
CRNT.Oscillation.ReturnMapContraction  <- FloquetOrbitalStability.lean:3
```

Both are now present as **interface modules**: statements in the repository's `…Target : Prop`
idiom, with the genuinely mechanical parts written out and the mathematics left explicitly open. No
axioms, no `sorry`. `scripts/check_imports.py` now fails on any import of a nonexistent module, so
this cannot recur silently.

## 2. Eight helper declarations existed nowhere

| used as | status |
|---|---|
| `Matrix.ofLinearMap` | now defined (`ReturnMapContraction.lean`) — matrix in `Module.finBasis` |
| `ContractingMap.iterates_tendsto_fixedPoint` | now routed to Mathlib's `ContractingWith.tendsto_iterate_fixedPoint` |
| `ContinuousLinearMap.spectralRadius_lt_iff` | open: `SpectralRadiusLtIffTarget` |
| `ContinuousLinearMap.ContractionEquivalentNormData` | now defined as a structure |
| `ContinuousLinearMap.exists_equivalentNorm_opNorm_lt_one` | open: `EquivalentContractionNormTarget` |
| `ContDiffAt.exists_local_contraction_in_equivalentNorm` | open: `LocalContractionTarget` |
| `Polynomial.simpleRoot_cannot_occur_in_both_factors` | open: `SimpleRootFactorTarget` |
| `Network.massAction_flow_smoothDependence` | open: `MassActionFlowSmoothDependenceTarget` |

Three of those names are in Mathlib-looking namespaces (`Matrix.`, `Polynomial.`,
`ContinuousLinearMap.`) but are not Mathlib declarations. That is the one class of hole no static
check in this repository can find, because Mathlib is not available to the checkers: only
`lake build` settles it. Expect more of them elsewhere in the frontier — a strict scan of frontier
files turns up 303 distinct undeclared qualified references, the overwhelming majority of which
*are* genuine Mathlib names, which is exactly why the vocabulary-gated check is the one that runs in
CI and `lake build` is the one that decides.

## 3. Three constructions are still undeclared

These are the load-bearing ones; the fields they have to discharge are listed here so the work is
scoped rather than guessed at.

### `constructTransverseFloquetSectionData` (FloquetOrbitalStability.lean:162)

Required signature, from the call site:

```lean
noncomputable def constructTransverseFloquetSectionData
    {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (P : N.LinearlyStablePositivePeriodicOrbit κ)
    (hfloquet : P.floquet)                                  -- the linear Floquet data
    (hsmooth  : ContDiff ℝ ⊤ (N.massActionVectorField κ))
    (hdep     : N.MassActionFlowSmoothDependence κ)          -- FlowSmoothDependence.lean
    (hsimple  : ...)                                         -- `1` a simple Floquet multiplier
    : N.TransverseFloquetSectionData P
```

`TransverseFloquetSectionData` is a 20-field `Type`-valued bundle. The fields split into three
groups:

*Bookkeeping, immediate once the section is chosen:* `E`, the four instance fields, `fixedPoint`,
`ambient`, `ambient_fixed`, `flow_zero`, `reference_flow`. Take `E := floquetSectionSpace P`, the
orthogonal complement of the phase velocity `periodicTangent P` — already defined in the file.

*Implicit function theorem on the flow:* `returnMap`, `returnTime`, `returnTime_pos`, `fixed`,
`flow_return`, `c1`, `derivative`, `hasDerivative`, `ambient_continuousAt`,
`interpolation_continuous`. All of these come from applying the IFT to
`(x, t) ↦ ⟪Φ x t − P.orbit 0, periodicTangent P⟫` at `(P.orbit 0, P.orbit.period)`, where
transversality is `⟪v, v⟫ ≠ 0` for `v` the phase velocity — nonzero because the orbit is
nonconstant. This needs `hdep` for differentiability of `Φ` in `x`, and Mathlib's
`HasStrictFDerivAt.implicitFunction`. The repository already has a worked analogue in
`CRNT/Dynamics/TransversalCrossingTime.lean` and `CRNT/Dynamics/PoincareReturnMap.lean`
(`TransversalSection.crossingTime`, `hasFDerivAt_returnMap`), both in the verified core — that is
the template, and reusing it rather than starting fresh is the obvious route.

*The monodromy factorization:* `charpoly_relation`, i.e.

```lean
P.floquet.floquetPolynomial
  = (Polynomial.X - 1) * ((Matrix.ofLinearMap derivative).map (algebraMap ℝ ℂ)).charpoly
```

This is the mathematical heart. The monodromy operator `M = V.fundamental (P.orbit 0) period`
fixes the phase velocity (`M v = v`, because `t ↦ P'(t)` solves the variational equation and is
periodic), so `M` preserves the splitting `ℝ ∙ v ⊕ (ℝ ∙ v)ᗮ` only after quotienting; the return-map
derivative is the induced map on the quotient. The factorization then follows from
`charpoly` of a block-triangular matrix. Note the statement as written asserts the split is exact,
which requires the section to be *invariant* rather than merely transverse — worth checking against
a reference before proving it, since the usual formulation is a similarity rather than an equality
of polynomials.

### `constructParameterizedPoincarePersistence` (FloquetPersistenceGeneral.lean:174)
### `massActionFloquetData_of_branchMonodromy` (FloquetPersistenceGeneral.lean:144)

The parameterized version of the above: a family of transverse sections over a parameter interval,
with the return-map IFT applied uniformly so that a nondegenerate fixed point persists, plus
continuity of the monodromy in the parameter to preserve the stable Floquet spectrum. It depends on
`constructTransverseFloquetSectionData`; there is no point starting it first.

## 4. The refactor the call sites need

`FloquetOrbitalStability.lean` currently calls the four open kernels as though they were theorems:

```lean
D.derivative.exists_equivalentNorm_opNorm_lt_one D.spectralRadius_lt_one
D.c1.exists_local_contraction_in_equivalentNorm ...
```

With the kernels stated as `Prop`s, each such consumer takes
`CRNT.ReturnMapContraction.ContractionKernelBundle` as a hypothesis and threads it through —
`spectralRadius_lt_one`, `contractionNormData`, `exists_localContraction`,
`sectionIterates_tendsto`, `locallyAttracts`, `floquetOrbitalStability_proved`. That is a
mechanical edit to about six declarations, and it makes the dependency visible in the type of
`floquetOrbitalStability_proved` instead of hiding it behind a name that does not resolve.

Doing it also means `OscillationKernelBundle.lean` must stop advertising a zero-input bundle: the
honest statement is that `completeOscillationKernelBundle_proved` needs the contraction kernels and
the flow smooth-dependence obligation. The earlier generation of that file did exactly this — it
carried `notPMinusZeroScaling`, `fisherFullerScaling` and similar as fields, with the comment "it is
intentionally a *bundle of propositions*, not an axiom; users may instantiate only the fields needed
for the route they use". The rewrite that collapsed those fields into `…_proved` definitions is what
turned a visible dependency into an invisible one.

## Suggested order of work

1. Run `lake build CRNTFrontier` and get the real error inventory. Everything above is static
   analysis; the class-2 holes (invented Mathlib names) can only be enumerated by the compiler, and
   there are likely more of them in the planar/Green chain.
2. Do the refactor in §4. It is mechanical, it makes the remaining obligations appear in type
   signatures, and it lets the rest of the oscillation tree build against honest hypotheses.
3. Prove `SimpleRootFactorTarget` — a short root-multiplicity argument, and the only one of the four
   that is genuinely small.
4. Prove `MassActionFlowSmoothDependenceTarget` from `ODE.norm_flow_variational_error_le`, which is
   already proved in the core. Steps are listed in the header of `FlowSmoothDependence.lean`.
5. Build `constructTransverseFloquetSectionData` on the `TransversalSection` machinery in
   `CRNT/Dynamics/PoincareReturnMap.lean`, leaving `charpoly_relation` last and checking its exact
   form against a reference first.
6. `EquivalentContractionNormTarget` and `LocalContractionTarget` are standard and can be done in
   either order; the first is the Householder norm construction, the second a mean-value argument.
7. Only then the parameterized versions and the Banaji inheritance route.

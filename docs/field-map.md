# Field map of chemical reaction network theory

This file maps the field of chemical reaction network theory (CRNT) onto this repository. Each
result of the field is a leaf with an identifier, its primary reference, the Lean
declarations that prove or state it, and a status. The map is the measure of what "all of
CRNT" means here: a leaf is covered when its declarations exist and are pinned axiom-clean.

The map is checked against the code: `scripts/field_map_pins.py` extracts every declaration
named in the tables below and writes `test/FieldMapAudit.lean`, which pins each one to
`[propext, Classical.choice, Quot.sound]` (or a subset). If a declaration is renamed, removed, or
acquires `sorryAx`, that test fails.

Status of the map: 2026-10-11, updated against `crnt-lean-2026-10-11c` (leaves F11, S17, S18, D14, A3, A5, E2, C2, C3 advanced; see `HANDOFF_field_map_c.md`).

## Status legend

| Status | Meaning |
|---|---|
| **proved** | The result, in the form stated in the reference, is a pinned theorem. |
| **partial** | Some of the result is proved (a special case, a direction, or the main lemmas), and the rest is missing. The *Notes* column says which. |
| **stated** | The statement is a named `Prop` (a contract), with no proof. |
| **missing** | No formal counterpart. |
| **open** | Open in the literature; the map tracks a formal statement. |

## 1. The tree

```
CRNT
├── F  Foundations
│   ├── F1  networks, complexes, reactions                         proved
│   ├── F2  linkage classes                                        proved
│   ├── F3  strong and terminal classes, weak reversibility        proved
│   ├── F4  stoichiometric subspace, conservation laws             proved
│   ├── F5  deficiency and its kernel characterization             proved
│   ├── F6  linkage-class deficiencies                             proved
│   ├── F7  siphons and traps                                      proved
│   ├── F8  mass-action kinetics, invariance of the orthant        proved
│   ├── F9  general kinetic systems                                partial
│   ├── F10 generalized mass action / power law                    partial
│   ├── F11 Michaelis–Menten and Hill kinetics                     proved
│   ├── F12 complex-space factorization, matrix-tree theorem       proved
│   ├── F13 open systems (CFSTR)                                   partial
│   ├── F14 elementary flux modes, flux cone                       proved
│   └── F15 circulation decomposition                              proved
├── S  Steady states
│   ├── S1  detailed balance, Wegscheider conditions               proved
│   ├── S2  complex balance: log-linear (toric) structure          proved
│   ├── S3  one complex-balanced equilibrium per class             proved
│   ├── S4  complex balanced ⇒ weakly reversible                   proved
│   ├── S5  complex balanced for all κ ⟺ WR ∧ δ = 0                proved
│   ├── S6  quasi-thermostatic characterization                    proved
│   ├── S7  tree-constant (binomial) criterion for complex balance proved
│   ├── S8  steady-state ideal, positive-torus equivalence          proved
│   ├── S9  Birch's theorem                                        proved
│   ├── S10 deficiency zero theorem                                proved
│   ├── S11 deficiency one theorem                                 proved
│   ├── S12 WR ⇒ positive steady state                             proved
│   ├── S13 absolute concentration robustness                      proved
│   ├── S14 network translation, generalized complex balance       proved
│   ├── S15 linear conjugacy                                       proved
│   ├── S16 generalized mass action: complex balance, Birch        partial
│   ├── S17 steady-state parametrizations and invariants           partial
│   └── S18 counting positive steady states                        partial
├── M  Multistationarity
│   ├── M1  injectivity ⇒ at most one steady state per class        proved
│   ├── M2  P-matrices, Gale–Nikaido univalence                    proved
│   ├── M3  species–reaction graph theorem                         proved
│   ├── M4  DSR graph                                              partial
│   ├── M5  concordance                                            proved
│   ├── M6  strong concordance                                     proved
│   ├── M7  Deficiency One Algorithm                               partial
│   ├── M8  Advanced Deficiency Algorithm                          partial
│   ├── M9  degree theory                                          partial
│   ├── M10 multistationarity-capacity tests                       proved
│   ├── M11 inheritance and atoms of multistationarity             missing
│   ├── M12 composition of monostationary networks                 proved
│   └── M13 parameter regions for multistationarity                missing
├── D  Deterministic dynamics
│   ├── D1  positivity and well-posedness                          proved
│   ├── D2  relative-entropy Lyapunov function                     proved
│   ├── D3  LaSalle invariance principle                           proved
│   ├── D4  local asymptotic stability of complex balance          proved
│   ├── D5  Global Attractor Theorem                               proved
│   ├── D6  single linkage class GAC                               proved
│   ├── D7  siphon criteria for persistence                        proved
│   ├── D8  endotactic networks                                    partial
│   ├── D9  strongly endotactic permanence                         stated
│   ├── D10 facet repulsion                                        partial
│   ├── D11 drainable and self-replicable siphons                  stated
│   ├── D12 persistence conjecture                                 open
│   ├── D13 compact compatibility classes, boundedness             proved
│   ├── D14 monotone systems, contraction                          partial
│   ├── D15 Routh–Hurwitz                                          proved
│   ├── D16 Hopf bifurcation                                       partial
│   ├── D17 no oscillation for WR deficiency zero                  proved
│   ├── D18 existence of oscillations, chaos                       missing
│   ├── D19 quasi-steady-state reduction, Tikhonov–Fenichel        partial
│   └── D20 intermediates and their elimination                    partial
├── P  Stochastic CRNT
│   ├── P1  chemical master equation, generator                    proved
│   ├── P2  product-form stationary distributions                  proved
│   ├── P3  stochastic detailed balance                            proved
│   ├── P4  ergodicity on finite closed regions                    proved
│   ├── P5  absorbing states                                       proved
│   ├── P6  Foster–Lyapunov criteria                               partial
│   ├── P7  recurrence and explosivity on infinite state spaces    missing
│   ├── P8  Kurtz law of large numbers                             partial
│   ├── P9  CLT and diffusion approximation                        missing
│   └── P10 extinction and stochastic ACR                          missing
├── A  Algebraic and geometric CRNT
│   ├── A1  siphons as prime supports                              proved
│   ├── A2  elimination, Gröbner bases                             missing
│   ├── A3  real root bounds, mixed volumes                        partial
│   ├── A4  tropical methods                                       missing
│   └── A5  identifiability of rate constants                      proved
├── E  Extensions
│   ├── E1  thermodynamics: entropy production                     partial
│   ├── E2  reaction–diffusion, Turing instability                 partial
│   └── E3  non-isothermal and delay systems                       missing
└── C  Computation and design
    ├── C1  decision procedures and certificates                   proved
    ├── C2  chemical computation                                   partial
    └── C3  design: robust perfect adaptation, integral feedback   partial
```

## 2. Leaves

Declarations are written with their full names. Every declaration listed is pinned by
`test/FieldMapAudit.lean`.

### F. Foundations

| ID | Result | Reference | Lean | Status | Notes |
|---|---|---|---|---|---|
| F1 | Networks, complexes, reactions; the complex set | Feinberg 2019, ch. 2 | `CRNT.Network.source_mem_complexes`, `CRNT.Network.target_mem_complexes` | proved | |
| F2 | Linkage classes are the connected components of the reaction graph | Feinberg 2019, ch. 2 | `CRNT.Network.numLinkageClasses_eq_card_connectedComponent` | proved | |
| F3 | Weakly reversible iff every strong linkage class is terminal | Feinberg 2019, ch. 2 | `CRNT.Network.weaklyReversible_iff_allStrongClasses_terminal` | proved | |
| F4 | Conservation laws: dimension of the orthogonal complement of the stoichiometric subspace | Feinberg 2019, ch. 3 | `CRNT.Network.finrank_conservationLawSpace` | proved | |
| F5 | Deficiency `δ = n − ℓ − s ≥ 0`; `δ = dim(ker Y ∩ im ∂)` | Feinberg 1987; Feinberg 2019, ch. 6 | `CRNT.Network.deficiencyInt_nonneg`, `CRNT.Network.deficiencyInt_eq_finrank_deficiencySubspace` | proved | |
| F6 | `∑ δᵢ ≤ δ`, with equality characterized | Feinberg 1995a | `CRNT.Network.sum_linkageDeficiency_le_deficiency`, `CRNT.Network.sum_linkageDeficiency_eq_deficiency_iff` | proved | |
| F7 | Siphons; the zero set of an ω-limit point is a siphon | Angeli–De Leenheer–Sontag 2007 | `CRNT.Network.isSiphon_zeroSet_of_mem_omegaLimit` | proved | |
| F8 | Mass action; the closed orthant is forward invariant | Feinberg 2019, ch. 2 | `CRNT.Network.forwardInvariant_nonnegOrthant` | proved | |
| F9 | General kinetic systems; deficiency-zero conclusions without mass action | Feinberg 1972; Feinberg 2019, ch. on general kinetics | `CRNT.Network.deficiencyZero_not_weaklyReversible_no_positive_steadyState_or_cycle` | partial | Non-mass-action versions of the deficiency one theorem and of concordance consequences are not stated separately. |
| F10 | Generalized mass action / power-law systems | Müller–Regensburger 2012 | `CRNT.Network.GeneralizedMassActionData.generalized_deficiency_zero_theorem`, `CRNT.logAffine_affine_injective_iff`, `CRNT.signCondition_iff_signCompatible` | partial | Deficiency zero theorem; the sign-vector characterization of when affine classes meet log-affine sets in at most one point (both directions, abstract subspaces). The network-level statement "unique complex-balanced equilibrium for every κ iff sign condition" (which needs constructing rate constants) is missing. |
| F11 | Michaelis–Menten and Hill kinetics | Michaelis–Menten 1913; Briggs–Haldane 1925; Hill 1910 | `ODE.qssa_error_bound`, `CRNT.Network.hillKinetics`, `CRNT.Network.hillKinetics_rate_le`, `CRNT.Network.hillKinetics_rate_pos`, `CRNT.Network.michaelisMentenKinetics_rate` | proved | Hill kinetics (and its Michaelis–Menten case) is an admissible `Kinetics`, so every kinetics-agnostic theorem applies; the QSSA derivation of Michaelis–Menten is `ODE.qssa_error_bound`. |
| F12 | `ẋ = Y A_κ Ψ(x)`; the matrix-tree theorem for the kinetic Laplacian | Horn–Jackson 1972; Gunawardena 2003 | `CRNT.Network.kineticCofactor_eq_treeConstant_combinatorial` | proved | |
| F13 | Open systems (CFSTR): zero complex and inflow/outflow pseudo-reactions | Feinberg 2019, ch. on open systems | `CRNT.Network.linked_singletonComplex_fullyOpen` | partial | Structural facts are proved; the deficiency theorems for open systems are not stated in their open-system form. |
| F14 | Elementary flux modes are the extreme rays of the flux cone | Schuster–Hilgetag 1994 | `CRNT.Network.elementaryFluxMode_iff_extremeRay`, `CRNT.Network.fluxCone_generated_by_elementaryFluxModes` | proved | |
| F15 | Circulations on the reaction graph decompose into cycles | — (graph theory) | `CRNT.Network.graphCirculation_decomposes_into_cycles` | proved | |

### S. Steady states

| ID | Result | Reference | Lean | Status | Notes |
|---|---|---|---|---|---|
| S1 | Detailed balance and the Wegscheider conditions | Wegscheider 1901; Feinberg 1989 | `CRNT.Network.satisfiesWegscheider_iff`, `CRNT.Network.reversible_of_positiveDetailedBalanced` | proved | |
| S2 | Positive complex-balanced equilibria form a log-linear (toric) set | Horn–Jackson 1972 | `CRNT.Network.mem_positiveComplexBalancedSet_iff_toric` | proved | |
| S3 | Exactly one complex-balanced equilibrium in each positive class | Horn–Jackson 1972 | `CRNT.Network.isComplexBalanced_unique_in_positiveClass` | proved | |
| S4 | A positive complex-balanced equilibrium forces weak reversibility | Horn 1972 | `CRNT.Network.weaklyReversible_of_positive_complexBalanced` | proved | |
| S5 | Complex balanced for every κ iff weakly reversible and `δ = 0` | Horn 1972; Feinberg 1972 | `CRNT.Network.forall_complexBalanced_iff` | proved | |
| S6 | For `δ = 0`, every positive steady state is complex balanced | Feinberg 1987 | `CRNT.Network.positiveSteadyState_iff_complexBalanced` | proved | |
| S7 | Complex balance iff the tree-constant binomials vanish | Craciun–Dickenstein–Shiu–Sturmfels 2009 | `CRNT.Network.complexBalanced_iff_treeConstantBinomials` | proved | |
| S8 | The steady-state ideal of a WR `δ = 0` network agrees on the positive torus with the binomial ideal | Craciun–Dickenstein–Shiu–Sturmfels 2009 | `CRNT.Network.deficiencyZero_steadyStateIdeal_positiveTorusEquivalent_complexBalanceIdeal` | proved | |
| S9 | Birch's theorem | Birch 1963 | `CRNT.birch` | proved | |
| S10 | Deficiency zero theorem | Horn 1972; Feinberg 1972, 1987 | `CRNT.Network.deficiencyZeroTheorem` | proved | |
| S11 | Deficiency one theorem (existence and uniqueness) | Feinberg 1995a | `CRNT.Network.deficiencyOne_uniqueness`, `CRNT.Network.deficiencyOneUniqueness_multiClass`, `CRNT.Network.weaklyReversible_deficiencyOne_exists_positive_steadyState` | proved | |
| S12 | Weakly reversible mass action has a positive steady state in every class | Boros 2019 | `CRNT.Network.exists_positiveSteadyState_of_weaklyReversible` | proved | |
| S13 | Absolute concentration robustness for deficiency one | Shinar–Feinberg 2010 | `CRNT.Network.shinarFeinberg_ACRAt`, `CRNT.Network.shinarFeinberg_standardACR` | proved | Hypotheses match the paper: deficiency one, a positive steady state at `κ`, two non-terminal complexes differing only in `s`. |
| S14 | Network translation and generalized complex balance | Johnston 2014 | `CRNT.Network.ReactionTranslation.steadyState_iff_generalizedComplexBalanced_of_faithful` | proved | |
| S15 | Linear conjugacy of mass-action systems | Johnston–Siegel 2011 | `CRNT.Network.jacobian_similarity_of_linearConjugacy`, `CRNT.Network.massActionLinearlyConjugate_iff`, `CRNT.Network.dynamicallyEquivalent_iff_sourceWeightedSum_eq` | proved | Conjugacy by `x ↦ c ∘ x` holds iff `c^y W'_y = c ∘ W_y` at every complex (`W_y` the source-wise rate-weighted reaction vectors); agreement on the positive orthant suffices. The algorithmic search for conjugate networks (MILP) is not formalized. |
| S16 | Generalized mass action: complex balance and a Birch-type theorem | Müller–Regensburger 2012 | `CRNT.Network.GeneralizedMassActionData.unique_complexBalanced_in_positiveClass`, `CRNT.exists_two_points_of_not_signCompatible` | partial | Uniqueness under `SignCompatible`; conversely, failure of `SignCompatible` yields two distinct positive points with difference in the stoichiometric subspace and log-difference in the given subspace. Realizing these as complex-balanced equilibria for some κ (the network-level converse) and the existence half for every κ are missing. |
| S17 | Linear elimination; MESSI systems; toric steady states; rational parametrizations; steady-state invariants | Feliu–Wiuf 2012; Pérez Millán–Dickenstein 2018; Pérez Millán et al. 2012; Thomson–Gunawardena 2009 | `CRNT.Network.toricSteadyState_iff_log_orthogonal`, `CRNT.Network.toricSteadyState_iff_exp_parametrization`, `CRNT.Network.HasToricSteadyStates.geomMean` | partial | Toric steady states (Pérez Millán et al. 2012): the positive steady states are log-affine with the monomial parametrization `x* · exp v`, `v ⊥ aᵢ - bᵢ`, and closed under weighted geometric means. The criterion for having toric steady states, linear elimination, MESSI systems and steady-state invariants are missing. |
| S18 | Bounds on the number of positive steady states | Bihan–Dickenstein–Giaroli 2020; Joshi–Shiu 2017 | `CRNT.Network.card_positiveSteadyStates_le_signVariations`, `CRNT.Network.card_positiveSteadyStates_le_numSources`, `CRNT.Network.positiveSteadyState_unique_of_numSources_le_two` | partial | One-species networks: Descartes' rule of signs bounds the number of positive steady states, hence at most (distinct reactant coefficients − 1) of them, and no multistationarity with at most two reactant coefficients. Multi-species bounds (mixed volumes, circuits) are missing. |

### M. Multistationarity

| ID | Result | Reference | Lean | Status | Notes |
|---|---|---|---|---|---|
| M1 | An injective network has at most one steady state per class | Craciun–Feinberg 2005 | `CRNT.Network.massAction_subsingleton_steadyState_of_injective` | proved | |
| M2 | P-matrix Jacobians and Gale–Nikaido univalence | Gale–Nikaido 1965 | `CRNT.isLocalHomeomorph_of_pmatrix_fderiv` | proved | |
| M3 | The species–reaction graph theorem | Craciun–Feinberg 2006 | `CRNT.Network.injective_of_trueSRCriterion`, `CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion_bc` | proved | |
| M4 | DSR graph criteria | Banaji–Craciun 2009 | — | partial | The determinant cycle-cover expansion (`CRNT.det_eq_sum_cycleCover_terms`) is proved; the DSR theorem itself is not stated. |
| M5 | Concordance iff injectivity for every weakly monotonic kinetics | Shinar–Feinberg 2012 | `CRNT.Network.concordant_iff_all_weaklyMonotonic_injective` | proved | |
| M6 | Strong concordance for fully open and weakly reversible networks | Shinar–Feinberg 2012 | `CRNT.Network.stronglyConcordant_of_fullyOpen_of_weaklyReversible` | proved | |
| M7 | Deficiency One Algorithm | Feinberg 1995b | `CRNT.Network.stoichSubspace_ne_bot_of_doaAffirmsCapacity`, `CRNT.Network.exists_signCompatible_of_hasMultistationarityCapacity` | partial | The forward step to a sign-compatible log-ratio is proved; the correctness equivalence (capacity iff the algorithm affirms it) is proved in neither direction. |
| M8 | Advanced Deficiency Algorithm | Ellison 1998 | `CRNT.Network.stoichSubspace_ne_bot_of_adaAffirmsCapacity` | partial | As for M7. |
| M9 | Brouwer degree and steady-state existence | Conradi–Feliu–Mincheva–Wiuf 2017 | `CRNT.Network.exists_isMassActionSteadyState_of_reducedDegree_ne_zero` | partial | Structural criteria for a nonzero degree are missing. |
| M10 | Capacity tests: two positive zeros, sign-indefinite reduced Jacobian | Conradi–Feliu–Mincheva–Wiuf 2017 | `CRNT.Network.hasMultistationarityCapacity_of_two_positive_zeros`, `CRNT.Network.hasMultistationarityCapacity_of_signIndefinite` | proved | |
| M11 | Inheritance of multistationarity; atoms of multistationarity | Joshi–Shiu 2013; Banaji–Pantea 2016 | — | missing | |
| M12 | Interconnection of networks injective on their classes | — | `CRNT.Network.Kinetics.InjectiveOnClass.sum_subsingleton_steadyState` | proved | |
| M13 | Parameter regions for multistationarity | Conradi–Feliu–Mincheva–Wiuf 2017; Bihan–Dickenstein–Giaroli 2020 | — | missing | |

### D. Deterministic dynamics

| ID | Result | Reference | Lean | Status | Notes |
|---|---|---|---|---|---|
| D1 | Bounded forward solutions from positive states stay positive | — | `CRNT.Network.orbit_pos_forward` | proved | |
| D2 | The relative entropy decreases along solutions | Horn–Jackson 1972 | `CRNT.Network.relEntropy_antitone_along_solution` | proved | |
| D3 | LaSalle's invariance principle | LaSalle 1960 | `Flow.laSalle` | proved | |
| D4 | Local asymptotic stability of the complex-balanced equilibrium in its class | Horn–Jackson 1972 | `CRNT.Network.omegaLimit_eq_singleton_of_local` | proved | |
| D5 | Global Attractor Theorem for complex-balanced systems | Horn 1974 (conjecture); Craciun, arXiv:1501.02860 (route) | `CRNT.Network.complexBalanced_globalAttractor`, `CRNT.Network.complexBalanced_genuinePermanent`, `CRNT.Network.complexBalanced_forward_floor` | proved | See `HANDOFF_gac_closed.md`. |
| D6 | GAC for a single linkage class | Anderson 2011 | `CRNT.Network.singleLinkageClass_gac` | proved | Now also a corollary of D5. |
| D7 | No critical siphon ⇒ persistence | Angeli–De Leenheer–Sontag 2007 | `CRNT.Network.boundaryOmegaExcluded_of_hasNoCriticalSiphon`, `CRNT.Network.structurallyPersistent_of_deficiencyZero_hasNoCriticalSiphon` | proved | |
| D8 | Endotactic networks; weakly reversible ⇒ endotactic | Craciun–Nazarov–Pantea 2013 | `CRNT.Network.WeaklyReversible.endotactic` | partial | Persistence and permanence of two-dimensional endotactic systems are missing. |
| D9 | Strongly endotactic networks are permanent | Gopalkrishnan–Miller–Shiu 2014 | `CRNT.Network.stronglyEndotacticStd_iff_tierDescending_of_directionLemmas` | stated | The two tier lemmas are named claims (`StrongEndotacticTierCharacterizationClaim`, `TierDescendingPermanenceClaim`). |
| D10 | Weakly reversible processes near facets | Anderson–Shiu 2010 | — | partial | The influx estimate for a singleton critical siphon is proved (see `docs/persistence-gac.md`); the full facet result is not stated. |
| D11 | No drainable siphon ⇒ persistence; autocatalysis | Deshpande–Gopalkrishnan 2014 | `CRNT.Network.noDrainableSiphonOmegaPersistence` | stated | |
| D12 | Persistence conjecture | Feinberg 1987; Craciun–Nazarov–Pantea 2013 | `CRNT.Network.PersistenceConjectureStrong` | open | Bounded weakly reversible trajectories would follow from extending D5 (see Phase 4). |
| D13 | Conservative networks have compact compatibility classes | — | `CRNT.Network.isCompact_nonnegativeCompatibilityClass_of_strictPSemiflow` | proved | |
| D14 | Monotone systems and contraction for reaction networks | Angeli–Sontag 2008; Banaji 2009; Russo–di Bernardo–Sontag 2010 | `CRNT.Contraction.dist_le_exp_of_contracting`, `CRNT.Contraction.tendsto_of_contracting`, `CRNT.Contraction.tendsto_equilibrium_of_contracting` | partial | Contraction under a one-sided Lipschitz condition on a real inner product space: exponential convergence of solutions and a unique globally attracting equilibrium. Monotone systems (Kamke condition, Angeli–Sontag) and non-Euclidean (logarithmic-norm) contraction for reaction networks are missing. |
| D15 | Routh–Hurwitz criteria (degree ≤ 4) | Routh 1877; Hurwitz 1895 | `CRNT.hurwitz_quadratic_iff`, `CRNT.hurwitz_cubic_root_iff`, `CRNT.hurwitz_quartic_root_iff` | proved | |
| D16 | Hopf bifurcation | Errami et al. 2015 | `CRNT.hopf_crossing_gate` | partial | The crossing condition is proved; the sustained-oscillation verdict waits on center-manifold averaging. |
| D17 | Weakly reversible deficiency zero networks have no positive periodic orbits | Horn–Jackson 1972 | `CRNT.Network.neverPositivePeriodic_of_weaklyReversible_deficiencyZero` | proved | |
| D18 | Existence of oscillations; chaos | — | — | missing | |
| D19 | Quasi-steady-state reduction; Tikhonov–Fenichel | Tikhonov 1952; Fenichel 1979 | `ODE.qssa_error_bound`, `ODE.fenichel_persistence` | partial | The transverse contraction bound for the enzyme field is a hypothesis. |
| D20 | Intermediates and their elimination | Feliu–Wiuf 2012 | `CRNT.Network.SingleIntermediateKineticData.intermediateSteadyConcentration_pos` | partial | Single intermediates only. |

### P. Stochastic CRNT

| ID | Result | Reference | Lean | Status | Notes |
|---|---|---|---|---|---|
| P1 | The chemical master equation generator | Gillespie 1977; Anderson–Kurtz 2015 | `CRNT.Network.cmeGenerator_eq_ackResidual` | proved | |
| P2 | Product-form Poisson stationary distributions iff complex balance | Anderson–Craciun–Kurtz 2010 | `CRNT.Network.productPoisson_isStationary_of_complexBalanced`, `CRNT.Network.productPoisson_masterStationary_iff_complexBalanced` | proved | |
| P3 | Stochastic detailed balance from the Wegscheider conditions | Whittle 1986 | `CRNT.Network.exists_microscopicDetailedBalance_of_Wegscheider` | proved | |
| P4 | Convergence to stationarity on a finite closed strongly connected region | — | `CRNT.Network.regionMatrix_pow_mulVec_tendsto_stationaryVec` | proved | |
| P5 | Absorbing states | — | `CRNT.Network.zero_absorbing_iff_no_zero_source` | proved | |
| P6 | Foster–Lyapunov criteria | Meyn–Tweedie 1993 | `CRNT.Network.LinearFosterLyapunovCertificate.drift_neg_above` | partial | No recurrence conclusion yet. |
| P7 | Positive recurrence and non-explosivity on infinite state spaces | Anderson–Cappelletti–Kim–Nguyen 2020 | — | missing | |
| P8 | Kurtz's law of large numbers | Kurtz 1972 | `CRNT.Network.tendsto_scaledGenerator`, `CRNT.Network.fluidLimit_dist_le` | partial | Generator convergence and a conditional fluid-limit bound; the sample-path process is missing (Mathlib lacks compensated-Poisson martingales). |
| P9 | Central limit theorem; diffusion (chemical Langevin) approximation | Kurtz 1971, 1976 | — | missing | |
| P10 | Extinction in networks with absolute concentration robustness | Anderson–Enciso–Johnston 2014 | — | missing | |

### A. Algebraic and geometric CRNT

| ID | Result | Reference | Lean | Status | Notes |
|---|---|---|---|---|---|
| A1 | Siphons correspond to prime supports | Shiu–Sturmfels 2010 | `CRNT.Network.isSiphonPrimeSupport_iff` | proved | |
| A2 | Elimination and Gröbner bases for steady-state ideals | — | — | missing | |
| A3 | Real root bounds and mixed volumes | Bihan–Dickenstein–Giaroli 2020 | `CRNT.Network.card_positiveSteadyStates_le_signVariations` | partial | Descartes' rule of signs (Mathlib `Polynomial.roots_countP_pos_le_signVariations`) for one-species networks. Mixed volumes and multivariate Descartes bounds are missing. |
| A4 | Tropical model reduction | Samal et al. 2015 | — | missing | |
| A5 | Identifiability of rate constants | Craciun–Pantea 2008 | `CRNT.Complex.sum_massActionMonomial_eq_zero`, `CRNT.Network.massActionVectorField_eqOn_positive_iff`, `CRNT.Network.rateConstants_identifiable_iff` | proved | Rate constants are determined by the vector field on the positive orthant iff, for every complex, the reaction vectors out of it are linearly independent (reactions indexed, so parallel reactions and self-loops count as dependent). |

### E. Extensions

| ID | Result | Reference | Lean | Status | Notes |
|---|---|---|---|---|---|
| E1 | Entropy production is nonnegative for detailed-balanced systems | — | `CRNT.Network.entropyProduction_nonneg` | partial | Gibbs free energy and thermodynamic potentials beyond detailed balance are missing. |
| E2 | Reaction–diffusion systems; Turing instability | Turing 1952; Murray 2003 | `CRNT.Turing.diffusionDrivenInstability_iff`, `CRNT.Turing.exists_nonHurwitz_mode_iff`, `CRNT.Turing.no_instability_of_equal_diffusion`, `CRNT.Turing.opposite_signs`, `CRNT.Turing.exists_growing_mode` | partial | Linear Turing analysis for two species: the instability criterion, the equal-diffusion and activator–inhibitor corollaries, and an explicit exponentially growing Fourier-mode solution of the linearized PDE. Nonlinear reaction–diffusion PDEs (well-posedness, pattern selection) are missing. |
| E3 | Non-isothermal and delay systems | — | — | missing | |

### C. Computation and design

| ID | Result | Reference | Lean | Status | Notes |
|---|---|---|---|---|---|
| C1 | Decision procedures (linkage, weak reversibility, deficiency, single-linkage GAC) | — | `CRNT.Network.gac_of_singleLinkage_decide` | proved | See `docs/foundations.md` for the full list. |
| C2 | Chemical computation | Chen–Doty–Soloveichik 2014 | `CRNT.Computation.stablyComputes_of_terminating`, `CRNT.Computation.minCRN_stablyComputes`, `CRNT.Computation.addCRN_stablyComputes`, `CRNT.Computation.scaleCRN_stablyComputes`, `CRNT.Computation.maxCRN_stablyComputes` | partial | Count semantics and stable computation; terminating networks compute their terminal output; `min`, `+`, `k·` and `max` are stably computed. The semilinear characterization of stably computable functions is missing. |
| C3 | Robust perfect adaptation; antithetic integral feedback | Briat–Gupta–Khammash 2016 | `CRNT.Network.maxRPA_output_eq_between_steadyStates`, `CRNT.Network.stochastic_maxRPA_mean`, `CRNT.Antithetic.closedLoop_deterministic_setpoint`, `CRNT.Antithetic.closedLoop_stochastic_setpoint` | partial | Deterministic and stochastic setpoints of the antithetic controller. The stochastic theorem assumes the first-moment stationarity identity for the charge observable; deriving it from ergodicity and moment bounds (as Briat–Gupta–Khammash do) is missing. |

## 3. Gaps by tier

**Tier A — classical canon, settled mathematics.**
F9, F10, F13, S16, M4, M7, M8, D8, D9, D10, D11, D16.

**Tier B — modern standard results.**
S17, M9, M11, M13, D14, D20, P6, P7, P10, A2–A4 (A1 and A5 done), C3.

**Tier C — needs general mathematics Mathlib lacks.**
S18 and A3 (real algebraic geometry); A2 (Gröbner bases); P8 and P9 (compensated-Poisson
martingales, sample-path processes); D16 (center-manifold averaging); D19 (transverse contraction
bounds); E2 (parabolic PDEs).

**Tier D — open.**
D12 (persistence conjecture), D18 (general existence of oscillations), E3.

## 4. Plan

Each phase lists the leaves it closes.

**Phase 0 — this file.** Write the map, pin every declaration it names
(`test/FieldMapAudit.lean`), and keep the two in step.

**Phase 1 — Tier A, in dependency order.**

1. Non-mass-action and open-system forms of the classical theorems: F9, F13 (small–medium;
   mostly re-parametrizing existing proofs).
2. Generalized mass action and conjugacy: F10, S15, S16 (medium; sign-vector conditions of
   Müller–Regensburger, Johnston–Siegel characterization).
3. Persistence classes with the new floor machinery (`exists_zsh`, band invariance): D8
   (two-dimensional endotactic), D9 (strongly endotactic permanence), D10, D11 (medium–large).
4. DSR graph theorem: M4 (medium; the cycle-cover expansion is in place).
5. Deficiency One and Advanced Deficiency Algorithms: M7, M8 (large, several sessions;
   check against the published examples computationally before formalizing).
6. Hill kinetics as a kinetic system: F11 (small).

**Phase 2 — Tier B.**

1. Steady-state parametrizations: S17 (linear elimination, MESSI, toric steady states,
   invariants).
2. Multistationarity: M9 (structural nonzero degree), M11 (inheritance, atoms), M13
   (parameter regions).
3. Dynamics: D14 (monotone systems, contraction), D20 (general intermediates).
4. Stochastic: P6, P7 (recurrence, non-explosivity), P10 (extinction).
5. Algebraic: A5 (identifiability); C3.

**Phase 3 — Tier C, each a general-mathematics project first.** Compensated-Poisson martingales
(P8, P9); center-manifold averaging (D16); transverse contraction (D19); Gröbner bases and real
root bounds (A2, A3, S18); a reaction–diffusion layer (E2). Each starts with a scoping document
that separates the general mathematics from its CRNT use.

**Phase 4 — Tier D.** D12 for bounded trajectories: embed weakly reversible mass action into a
toric differential inclusion, and prove the two-sided validity condition in `exists_zsh` (the
current proof uses only the half that complex balance provides). Validate numerically on known
hard examples before formalizing. D18 and E3 are tracked as formal statements with partial
results.

## 5. Maintaining the map

* A change that proves, renames, or removes a declaration named here updates this file in the
  same commit, then reruns `python3 scripts/field_map_pins.py` and `lean test/FieldMapAudit.lean`.
* A leaf moves to **proved** only when its statement has been checked against the reference
  (quantifiers, hypotheses, vacuity) and its declarations are pinned.
* New leaves get the next free identifier in their branch; identifiers are never reused.

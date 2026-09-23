# Mathematical review of the oscillation statements

Static checks find missing names, hollow shapes and unresolved imports. They cannot find a
statement that is *well-formed, axiom-free, and says the wrong thing*. This is a review of the
load-bearing statements in the oscillation development for that failure mode, done before the
first build because it does not need one.

Four findings, in descending order of seriousness.

## 1. `FloquetOrbitalStabilityTarget` was vacuous

This is the headline theorem of the whole Floquet chain and the `stabilityInheritance` field of
`completeOscillationKernelBundle_*`. It read:

```lean
def FloquetOrbitalStabilityTarget : Prop :=
  ∀ … (P : N.LinearlyStablePositivePeriodicOrbit κ),
      ∃ basin : Set (Concentration T),
        Set.range P.orbit.orbit ⊆ basin ∧ P.orbit.GloballyAttractsSolutions basin
```

Take `basin := Set.range P.orbit.orbit`. The first conjunct is `subset_rfl`. For the second, unfold
`GloballyAttractsSolutions`: given `x ∈ basin`, so `x = P.orbit s` for some `s`, and given any
forward solution `γ` with `γ 0 = x`, we must produce for each `ε > 0` a time `T` beyond which
`∃ phase, dist (γ t) (P.orbit phase) < ε`. Forward uniqueness of mass-action solutions (the field
is locally Lipschitz; `ODE.dist_le_of_isIntegralCurve` is in the core) gives
`γ t = P.orbit (s + t)` for `t ≥ 0`, so taking `phase := s + t` makes the distance `0 < ε`, with
`T := 0`.

So the statement is provable in a few lines with no Floquet theory, no spectral radius, and no
Poincaré section. A basin that is merely a *superset* of the orbit carries no information; orbital
asymptotic stability requires it to be a *neighbourhood*.

**Fixed.** `CRNT/Oscillation/Floquet.lean` now defines

```lean
def orbitTube (P : N.PositivePeriodicOrbit κ) (δ : ℝ) : Set (Concentration S) :=
  {x | ∃ phase : ℝ, dist x (P.orbit phase) < δ}

def FloquetOrbitalStabilityTarget : Prop :=
  ∀ … (P : N.LinearlyStablePositivePeriodicOrbit κ),
      ∃ δ : ℝ, 0 < δ ∧ P.orbit.GloballyAttractsSolutions (P.orbit.orbitTube δ)
```

The old weak form is kept as `hasAttractingBasin`, derived from the strong one, with a docstring
saying it is trivially true on its own.

**Consequence for the intended proof.** The basin that `locallyAttracts` constructs is
`{x | ∃ y ∈ U, ∃ τ ∈ [0, returnTime y], x = flow y τ}` with `U` an *open* section neighbourhood, so
the strengthened statement is still what that proof structure delivers — but the last step,
extracting a uniform tube radius, is now visible as an obligation (`TubeBasinTarget`) instead of
being skipped. It is bookkeeping rather than mathematics: `ambient_continuousAt` and
`interpolation_continuous` give a radius near one phase, and `[0, P.orbit.period]` is compact, so
the radius can be made uniform in phase. Someone should still write it.

**Knock-on.** `floquetOrbitalStability_proved` is now `floquetOrbitalStability_of_tube`, taking the
obligation, and the bundle is `completeOscillationKernelBundle_of_tube`. The "zero-input assembly"
claim in `OSCILLATION_FINAL_HANDOFF.md` does not survive contact with the corrected statement, and
that is the right outcome: the dependency is in the type now rather than hidden behind a name that
does not resolve.

## 2. `charpoly_relation` is correct — my earlier caveat was wrong

In `MERGE_REPORT.md` I flagged the field

```lean
charpoly_relation :
  P.floquet.floquetPolynomial
    = (Polynomial.X - 1) * ((Matrix.ofLinearMap derivative).map (algebraMap ℝ ℂ)).charpoly
```

as suspect, on the grounds that the standard statement is a similarity rather than an equality of
polynomials. That was over-cautious. The equality is right, and here is why, so nobody weakens it:

Let `M` be the monodromy operator (`floquetPolynomial = charpoly M`) and `v := periodicTangent P`
the phase velocity at `P.orbit 0`. Then `M v = v`: the map `t ↦ P.orbit' t` solves the variational
equation along the orbit (differentiate the ODE in `t`) and is periodic with the orbit's period, so
it is a `+1`-eigenvector of the time-`period` fundamental matrix. Since the orbit is nonconstant,
`v ≠ 0`.

Choose any basis whose first vector is `v`. Because `M v = v`, the first column of the matrix of
`M` is `e₁`, so the matrix is block upper-triangular with blocks `(1)` and `M̄`, where `M̄` is the
map induced by `M` on the quotient `ℝⁿ / ℝv`. Hence

```
charpoly M = (X − 1) · charpoly M̄
```

exactly, as polynomials. It remains that `derivative` — the return-map derivative on the section
`E = (ℝ ∙ v)ᗮ` — has the same characteristic polynomial as `M̄`. It does: differentiating
`P(x) = Φ(x, τ(x))` gives `DP = M + v · Dτ`, and the section derivative is `π ∘ DP|_E` where `π` is
the projection onto `E` along `v`. The rank-one correction `v · Dτ` has image in `ℝv`, so `π` kills
it and `π ∘ DP|_E = π ∘ M|_E`, which is conjugate to `M̄` under the isomorphism `E ≅ ℝⁿ / ℝv`.
Characteristic polynomials are conjugation-invariant, so the two agree.

So the field is stated correctly and its proof has three separable pieces: `M v = v`, the
block-triangular factorization, and the conjugacy of `π ∘ M|_E` with `M̄`. The first is a
differentiation, the second is `Matrix.charpoly_blockTriangular`-style, the third is linear algebra.

## 3. `SimpleRootFactorTarget` — proved

The smallest of the four contraction kernels, now discharged in
`CRNT/Oscillation/ReturnMapContraction.lean` as `simpleRoot_not_mem_both`:

if `(p * q).roots.count a = 1` then `p * q ≠ 0` (otherwise the count is `0`), so `p ≠ 0` and
`q ≠ 0`, so `Polynomial.roots_mul` gives
`(p*q).roots.count a = p.roots.count a + q.roots.count a`. If `a` were a root of both, each
summand is `≥ 1` and the total is `≥ 2`, contradiction.

This is what rules out the transverse return derivative inheriting the autonomous multiplier `1`:
linear stability makes `1` a simple root of the Floquet polynomial, and the factorization in §2
then forces `1 ∉ charpoly(derivative).roots`. `ContractionKernelBundle` lost the field accordingly.

## 4. The remaining three kernels: proof strategies

Stated in `ReturnMapContraction.lean`; here is how each should go, so that the Lean can be written
against a settled argument.

### `EquivalentContractionNormTarget` — decomposed, partly proved

Spectral radius `ρ(T) < 1` gives an equivalent norm with operator norm `< 1`. Pick `r` with
`ρ(T) < r < 1`. Gelfand's formula (`‖Tⁿ‖^{1/n} → ρ(T)`) gives `C` with `‖Tⁿ‖ ≤ C rⁿ` for all `n`.
Define

```
‖x‖' := ⨆ n, r^{-n} ‖Tⁿ x‖
```

The supremum is finite: `r^{-n}‖Tⁿ x‖ ≤ r^{-n} C rⁿ ‖x‖ = C‖x‖`. It is a norm (a sup of norms,
each absolutely homogeneous and subadditive), it is equivalent (`‖x‖ ≤ ‖x‖' ≤ C‖x‖`, the lower
bound from the `n = 0` term), and

```
‖T x‖' = ⨆ n, r^{-n} ‖T^{n+1} x‖ = r · ⨆ n, r^{-(n+1)} ‖T^{n+1} x‖ ≤ r ‖x‖'
```

so the rate is `r < 1`. This is cleaner in Lean than the usual finite-sum Householder norm, because
the sup form makes the contraction estimate a one-line index shift rather than a telescoping
argument. `ContractionEquivalentNormData` wants the constants explicitly: `lo := 1`, `hi := C`.

**Now partly done.** `ReturnMapContraction.lean` defines `adaptedNorm` and proves the two facts
that need the decay input: `adaptedNorm_bddAbove` (the family is bounded by `C‖x‖`, so the
supremum is a real number rather than the junk value) and `norm_le_adaptedNorm` (the `n = 0` term
gives `lo := 1`). The obligation is reduced to `GeometricDecayTarget`:

```
ρ(T) < 1  →  ∃ r C, 0 < r ∧ r < 1 ∧ 0 ≤ C ∧ ∀ n, ‖Tⁿ‖ ≤ C rⁿ
```

which is a statement about operator powers only, with no norms on `E` in sight. Mathlib has the
Gelfand limit as `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`, so of the four
original kernels this is the one most likely to fall out in a few lines at a terminal. What remains
after it is `ciSup`-manipulation over a bounded family: the norm axioms and the index shift.
`ReducedContractionKernelBundle` is the bundle in this shape, and new consumers should prefer it.

### `LocalContractionTarget`

`f` is C¹ at the fixed point `x₀`, `D = Df(x₀)` has `‖·‖'`-rate `c₀ < 1`. Let
`c := (1 + c₀)/2 < 1`. Continuity of `x ↦ Df(x)` in the adapted norm gives a ball `B` around `x₀`
on which `‖Df(x) − D‖' ≤ (c − c₀)/1`. On the convex set `B` the mean value inequality gives

```
‖f x − f y‖' ≤ (sup_{z ∈ B} ‖Df(z)‖') ‖x − y‖' ≤ c ‖x − y‖'
```

and `f x₀ = x₀` plus `c < 1` makes `B` invariant after shrinking. Two cautions: the mean value
inequality has to be applied in the adapted norm, so the equivalence constants enter the radius
choice; and `MapsTo f U U` needs the invariance step, which is where `f x₀ = x₀` is used.

### `SpectralRadiusLtIffTarget`

`ρ(T) < 1` iff every root of the characteristic polynomial has modulus `< 1`. In finite dimension
the spectrum is the root set of the characteristic polynomial of the complexification, and
`ρ` is the max modulus over the spectrum. The only real content is the passage between the real
operator's `spectralRadius ℝ` and the complex root set, i.e. that the spectrum of `T` viewed over
`ℝ` and the eigenvalues of `T ⊗ ℂ` have the same moduli. This is the most Mathlib-dependent of the
three and worth searching for before proving: if the relevant `Matrix.charpoly` / spectrum bridge
exists, this collapses to a rewrite.

## 4b. The tube obligation is now a compactness argument, and mostly proved

Strengthening `FloquetOrbitalStabilityTarget` (§1) created a new obligation: get a *uniform* tube
radius out of the section argument. That turns out to be free, and `Floquet.lean` now proves it:

* `orbitTube_eq_thickening` — the tube is `Metric.thickening δ (Set.range orbit)`, so Mathlib's
  thickening API applies;
* `continuous_orbit` — each component is differentiable by `P.solution`, hence continuous, hence
  continuous into the pi type;
* `isCompact_range_orbit` — by periodicity every value is attained on `[0, period]`
  (`Function.Periodic.exists_mem_Ico₀`), so the range is a continuous image of a compact interval;
* `exists_orbitTube_subset_of_isOpen` — `IsCompact.exists_thickening_subset_open` then gives a
  uniform radius inside any open set containing the orbit;
* `exists_tube_attraction_of_open_basin` — with basin monotonicity, an open attracting basin yields
  the tube form outright.

So the obligation shrank from "produce a uniform metric radius, uniformly in phase" to
`OpenBasinTarget`: *the basin produced by the section argument is open*. That is a statement about
one set with no quantifier over phases and no metric estimate, and its inputs
(`interpolation_continuous`, `returnTime_pos`, openness of `U`) are already fields of
`TransverseFloquetSectionData`. `floquetOrbitalStability_of_openBasin` is the route in this shape.

## 4c. Smooth dependence, decomposed

`MassActionFlowSmoothDependenceTarget` is now split into three named pieces with the assembly
proved (`massActionFlowSmoothDependence_of_steps`), which is what shows the split is faithful —
there is no hidden fourth step:

* `UniformModulusTarget` — compactness bookkeeping over `ContDiff ℝ ⊤` of the field, which is
  proved in the core;
* `FundamentalMatrixTarget` — the real content: solve the variational equation with identity
  initial value, continuously in the base point. `ODE.exists_isIntegralCurve` gives the pointwise
  solution; continuity in `x` is a second Grönwall;
* `DerivativeAssemblyTarget` — bookkeeping again, consuming the already-proved
  `ODE.norm_flow_variational_error_le`, whose driving term is linear in the increment and vanishes
  with the modulus from step 1, which is exactly the `o(‖y − x‖)` condition.

## 5. Non-vacuity: the Lotka network

`CRNT/Examples/Lotka.lean` (new) sets up the cheapest concrete network with positive periodic
orbits. `A → 2A`, `A + B → 2B`, `B → 0` has mass-action field

```
ẋ = k₁ x − k₂ x y ,   ẏ = k₂ x y − k₃ y
```

which is Lotka–Volterra, and

```
V(x, y) = k₂ x − k₃ log x + k₂ y − k₁ log y
```

is a first integral. The conservation identity is pure cancellation:

```
(k₂ − k₃/x)(k₁x − k₂xy) + (k₂ − k₁/y)(k₂xy − k₃y)
  = k₁k₂x − k₂²xy − k₁k₃ + k₂k₃y + k₂²xy − k₂k₃y − k₁k₂x + k₁k₃ = 0
```

Four cancelling pairs; nothing survives.

Why this and not `HopfNetwork3`: the orbit comes from a conserved quantity, so it needs no centre
manifold, no normal form, and no first Lyapunov coefficient — all of which `HopfNetwork3` would
need, and all of which are in the unverified frontier. The route is:

1. the identity above (`field_simp; ring` after unfolding the field);
2. constancy along solutions — chain rule plus (1), same shape as the core's
   `relEntropy_antitone_along_solution` with equality in place of `≤`;
3. compactness of level sets — `V` is strictly convex on the open quadrant and coercive both at the
   boundary (`−log` blows up) and at infinity (linear terms dominate); this is the same coercivity
   argument as the core's `birchDual_coercive`;
4. a period — the level set is a compact regular closed curve on which the field does not vanish,
   so take a transversal at a non-equilibrium point and use the crossing time. The core already has
   `CRNT/Dynamics/TransversalCrossingTime.lean` and `CRNT/Dynamics/PoincareReturnMap.lean`
   (`TransversalSection.crossingTime`, `isPeriodic_returnMap_fixedPoint`) for exactly this.

Only step 4 touches planar machinery, and only the transversal-return part of it — not
Poincaré–Bendixson. Steps 1–3 all have proved analogues in the verified core.

**Step 1 is now done, along with more than planned.** `CRNT/Examples/Lotka.lean` proves:

* `field_A` and `field_B` — both components of the mass-action field in closed form. Everything
  else in the file depends only on these two, so they are the single place to adjust if the `simp`
  set needs tuning on a real build;
* `conservation_identity` — `⟪∇V, F⟫ = 0` at every positive concentration, by `field_simp; ring`
  after the field computation. The four cancelling pairs above;
* `hasDerivAt_firstIntegral_A` / `_B` — that `firstIntegralGrad` really is the gradient, which is
  what turns the identity into constancy along solutions by the chain rule;
* `equilibrium_isSteadyState` — the positive equilibrium `(k₂/k₁, k₀/k₁)` really is one;
* `not_weaklyReversible` and `two_le_stoichRank` — so neither compiled exclusion route applies.
  This is the consistency check: if either applied, the file would be asserting a contradiction.

Steps 2–4 remain, as `FirstIntegralConstantTarget`, `LevelSetCompactTarget` and
`HasPositivePeriodicOrbitTarget`, each with the core theorem that supplies it named in its
docstring. The network is indexed by `Fin 2` / `Fin 3` rather than custom inductives purely so that
`Fin.sum_univ_three` and `Fin.prod_univ_two` do the enumeration — enumerating `Finset.univ` for a
`deriving Fintype` inductive needs a hand-written `Finset.sum_insert` chain, and that is exactly the
kind of thing that fails on a first build.

Worth noting what this witness would buy: it is the first time any `…Target` in the tree gets
composed end to end on a concrete network. Until that happens a target that is too weak to compose
— exactly the defect in §1 — cannot be detected by anything except reading.

## 6. Statements checked and found correct

For the record, so this is not re-litigated:

* `NondegenerateDependentReactionPersistenceTarget` and its stable twin quantify capacity
  existentially over rate constants on the *enlarged* network, so the "sufficiently small added
  rate" in Banaji's theorem is absorbed by the `∃ κ`. Correct as stated.
* `GlobalLimitCycleOnClass.attracts` uses `positiveCompatibilityClass (orbit.orbit 0)` as the
  basin, which is a genuine nontrivial set — the §1 defect does not recur here.
* `OscillatoryCapacity` / `NeverPositivePeriodic` are exact negations of one another modulo the
  parameter quantifier, and `PositivePeriodicOrbit` carries `period_pos` and a nonconstancy field,
  so "periodic orbit" does not degenerate to an equilibrium. Correct.
* `LinearlyStable` requires `1` simple *and* all other multipliers inside the unit circle, which is
  the right notion for a periodic orbit of an autonomous system (the trivial multiplier can never
  be removed). Correct.

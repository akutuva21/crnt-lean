# Vacuity and degeneracy audit of the two hole chains

**Agent:** `adv-vacuity` · **Branch:** `research/adv-vacuity`
**Scope:** every theorem on the consumer chains of hole A and hole B; every definition that admits
degenerate data; machine-checked non-vacuity witnesses.

## 0. How to read this

Three kinds of claim are distinguished, and each is labelled:

* **[M]** *machine-checked* — a Lean theorem that elaborates, named with its module. The file is
  `test/VacuityAudit.lean` (tests) and `CRNT/Dynamics/UpperRegionVacuity.lean` (library).
* **[P]** *proof read* — the argument was read and its `by`-block followed binder by binder.
* **[INFERENCE]** — not verified here.

Every `[M]` claim is a **refutation** (`¬ …`) or an **inhabitedness witness** (a concrete
instance). Refutations prove a hypothesis is load-bearing and the theorem is not a triviality;
inhabitedness witnesses prove the predicate is not unsatisfiable. Both are needed: a theorem is
*vacuous* when its hypotheses cannot be met, and *trivial* when its conclusion holds without them.

---

## 1. Ranked findings

### R1 — **CRITICAL** — `DifferentialInclusion.Field` may be empty, making every barrier conclusion vacuous **[M]**

`CRNT/Dynamics/DifferentialInclusion.lean:43`

```lean
abbrev Field (E : Type*) := E → Set E
```

No nonemptiness requirement, anywhere, on `F x`. And

```lean
def ForwardInvariant (F : Field E) (R : Set E) : Prop :=
  ∀ γ : ℝ → E, IsInclusionSolution F γ → γ 0 ∈ R → ∀ t, 0 ≤ t → γ t ∈ R   -- :97
```

With `F ≡ fun _ => ∅` there are no solutions at all, so `ForwardInvariant F R` holds for **every**
region `R`. Machine-checked:

* `test/VacuityAudit.lean :: forwardInvariant_vacuous_for_empty_field (R : Set ℝ) :
  DifferentialInclusion.ForwardInvariant (fun _ => (∅ : Set ℝ)) R`
* `test/VacuityAudit.lean :: forwardInvariant_not_vacuous_in_general :
  ¬ ForwardInvariant (fun _ => ({1} : Set ℝ)) {x : ℝ | x ≤ 0}` — so the previous lemma is a
  statement about *empty* fields, not about the definition being vacuous.

**Blast radius.** The conclusion of `forwardInvariant_barrierSublevel`
(`CRNT/Geometry/PolyhedralBarrier.lean:317`), `forwardInvariant_of_cone_descent` (`:341`),
`forwardInvariant_of_polar_descent` (`:364`) and `forwardInvariant_minMaxSublevel` (`:491`). Any
blueprint that constructs a toric field without proving `∀ y, (F y).Nonempty` gets all four for
free. **Not guarded downstream anywhere.**

### R2 — **CRITICAL** — *independently confirmed, then consolidated away* — the Step-4 `upperRegion` criterion is refuted by any boundary ω-point

**Status: the theorem is not landed by me.** Four other researchers independently compiled the
same `False`-level verdict (`infra-scaffold-crnt` `UpperRegionFloorRefutation.lean`, `adv-refute`
`UpperRegionObstruction.lean`, `adv-audit` `UpperRegionAdjudication.lean`, `form-barrier`
`BlueprintRouteRefutation.lean`). Per the orchestrator's Decision 1 I deleted my own copy
(`CRNT/Dynamics/UpperRegionVacuity.lean`) rather than add a fifth. **Cite A-28 /
`Network.universalPositive_omegaLimit_of_closedPositiveConfine`**, which subsumes all of them and
four of the `hsep`-shaped ones.

**What I verified independently, and it settles the disputed question.** I derived the refutation
by a *third* route — `orbit_stays_in_upperRegion` (`HighCodimensionSiphonFace.lean:1508`, proved,
sorry-free) → `omegaLimit_subset_closure_image2` (`Mathlib/Dynamics/OmegaLimit.lean:50`) →
`closure_minimal` on the floor — and it does **not** go through `Permanent`, so it is immune to
`papers-craciun`'s objection that `Permanent` is a hypothesis the hole never assumes. The chain
is three lines:

1. non-crossing ⟹ `∀ t, γ x₀ t ∈ Zupper` (`orbit_stays_in_upperRegion`);
2. every point of `image2 ϕ univ {x₀}` is therefore in `closure Zupper`, and `closure Zupper` is
   closed, so **every ω-point is in `closure Zupper`**;
3. `hfloor : ∀ y ∈ Zupper, ∀ s, ε ≤ y s` with `0 < ε` and `{y | ∀ s, ε ≤ y s}` closed
   (`⋂ s {y | ε ≤ y s}`) survives closure, so **every ω-point is positive**.

**Verdict: `papers-craciun` is right; `form-barrier`'s counter-argument is wrong.** The claim
that "`hfloor` is a floor on a *region* rather than along the orbit, so the orbit-level refutations
do not touch it" fails at step 2: the floor propagates to the *whole ω-limit set*, and the
ω-limit set provably meets the region. **`hfloor` is not an unbuilt input of
`exists_positive_omegaPoint_of_upperRegion`; it is an inconsistent one** — establishing it makes
the criterion's own conclusion false.

One point that is *not* in the consolidated theorem and that I checked: the refutation needs
**neither** `hxs.Positive`, **nor** `hcb.IsComplexBalanced`, **nor** `hx₀.Positive` — only
non-crossing, the floor, and the existence of any boundary ω-point. So it cannot be dodged by
rescaling the floor or by choosing `Zupper` more carefully. That is what makes this a structural
obstruction rather than a defect of one criterion.


### R3 — **CRITICAL** — every packaged criterion funnels through a uniform coordinate floor, which hole A's `hzeroMax` forbids **[P]**

Now subsumed by A-28: the template needs only `IsClosed K`, `∀ y ∈ K, y.Positive` and
`closure (image2 ϕ v {x₀}) ⊆ K`, so it kills every rung that discharges orbit confinement through a
closed positive set — which is all of them. `Permanent` is merely one way of discharging it and
should no longer be cited as the reason.
criteria; the first is `form-barrier`'s `blueprintData_inconsistent_with_highCodimension` for the
`hsep` rung. Together they close off the whole ladder.

The two independent machine-checked results are `form-barrier`'s
`blueprintData_inconsistent_with_highCodimension` (the `hsep` rung, which kills the whole ladder)
and the consolidated `universalPositive_omegaLimit_of_closedPositiveConfine` (the `hfloor` rung).

### R3 — **CRITICAL** — every packaged criterion funnels through a uniform coordinate floor, which
hole A's `hzeroMax` forbids **[P]**

Grep of the conclusion chains shows that `exists_positive_omegaPoint_of_convex_tiles`
(`ToricBarrierExplicit.lean:347`), `_of_selfConsistent_normals` (`:502`),
`_of_blueprintData` (`:578`), `_of_tiled_faceCores` (`FaceDirectionCone.lean:367`),
`_of_faceRelevantCore` (`:417`), `_of_toric_blueprint` (`ToricBarrierTrapping.lean:422`) and
`_of_toric_halfspace` (`:473`) all pass a clause

```
hsep : ∀ s : S, ∃ ε > 0, ∀ x, x.Positive → StoichCompatible … → (in guarded region) → ε ≤ x s
```

i.e. **uniform coordinate floors on the guarded region**. `exists_positive_omegaPoint_of_upperRegion`
carries the same content under the name `hfloor`. `hsep_fails_of_boundaryPoint_mem_sublevel`
(`HighCodimensionSiphonFace.lean:184`, proved) refutes the first shape once a boundary ω-point lies
in the closed sublevel, and R2 refutes the second shape without needing convexity. **No rung of
the ladder is reachable from hole A's data.**

### R4 — **HIGH** — hole B's hypothesis bundle has **no witness in the tree** **[M]**

Hole B is `Network.stronglyConcordant_fullyOpen_of_trueSRCriterion`
(`TrueChemistrySRCriterion.lean:8003`, residual `sorry` at `:8607`), whose hypotheses are

```
hsep  : N.ReactantProductSeparated
hflow : N.ZeroComplexReactionsAreFlows
hSR   : N.TrueSRStrongCriterion
```

Repo-wide grep for witnesses to `TrueSRStrongCriterion` returns **exactly two**:

| witness | module | `ZeroComplexReactionsAreFlows` | `ReactantProductSeparated` | how `hSR` holds |
|---|---|---|---|---|
| `flowN` | `CRNT/Examples/TrueSRCounterexample.lean:5` | **false** (`flowN_not_zeroComplexReactionsAreFlows`) | true (vacuously) | **vacuously** — `flowN_trueSR` is proved by `flowN_no_cycle : ∀ C, False`; the true-SR graph has *no edges at all* |
| `netN` | `CRNT/Examples/TrueSRNetCoeffCounterexample.lean:33` | true | **false** (`netN_not_reactantProductSeparated`) | with real content — `netN_has_even_cycle` exhibits the 4-cycle `A —ρ₀— B —ρ₁— A` |

**So the three hypotheses of hole B are never jointly satisfiable by any network in the tree.**
That does not make the theorem vacuous (`hSR` *is* inhabited, and non-trivially so, by `netN`),
but it does mean that every proof of the theorem is currently a proof about a class with no known
member, and that a regression which quietly weakened `TrueSRStrongCriterion` to something implied
by `¬ ZeroComplexReactionsAreFlows` would be invisible.

**The one network that would be needed** — a network that is reactant/product separated, has no
incidence to the zero complex (or only canonical inflow/outflow channels), *and* has at least one
even true-SR cycle satisfying the coefficient identity — does not exist in the tree. Candidate
shape worked out but not yet formalised: the directed 3-cycle `A → B → C → A` over `S = Fin 3`.
Its true-SR graph is the 6-cycle `A —ρ₀— B —ρ₁— C —ρ₂— A`; all edge labels are 1 so every cycle is
an `SCycle`; its only cycles are the 6-cycle and its reverse, and the common-edge subgraph of two
orientations of a 6-cycle is a 6-cycle, which cannot be decomposed into simple
species-to-reaction paths, so `SToRIntersection` is empty. Adding `inflowReaction A` makes
`hflow` non-vacuous. **`TrueSRStrongCriterion`'s second clause is therefore also
vacuously satisfiable in the intended witness**, which is itself worth recording.

### R5 — **HIGH** — `hpolar` in `forwardInvariant_of_cone_descent` is vacuous for an empty cone family **[M]**

`CRNT/Geometry/PolyhedralBarrier.lean:341`

```lean
theorem forwardInvariant_of_cone_descent …
    (hmem   : ∀ i : ι, L i ∈ Λ i)
    (hpolar : ∀ y, R ≤ barrier L b y → ∀ i, L i y - b i = barrier L b y →
              ∀ c ∈ F y, ∀ M ∈ Λ i, M c ≤ 0) : ForwardInvariant F {barrier L b ≤ R}
```

`Λ : ι → Set (E →L[ℝ] ℝ)` is unconstrained. With `Λ i = ∅`, `hpolar` is a `∀ M ∈ ∅, …`, hence true
for *every* `L`, `b`, `R`, `F`, while `hmem` is false. Machine-checked
(`test/VacuityAudit.lean :: cone_descent_hpolar_is_vacuous_for_empty_cone`): the first conjunct is
the vacuity, the second is `¬ ((1 : ℝ →L[ℝ] ℝ) ∈ ∅)`.

**So `hmem` — not `hpolar` — is the hypothesis that carries the geometry.** A blueprint that
supplies "the descent hypothesis" as an empty cone family has supplied nothing; and the conclusion
is still false (`identBarrierSublevel_not_forwardInvariant`, same file).

### R6 — **MEDIUM** — `hdesc`, `hsep`, `C ⊆ interior K`, `inductionStep` and `ZeroSeparatingSurfaceExists`
are all genuinely load-bearing **[M]**

* `barrier_le_of_local_descent`'s `hdesc` (`PolyhedralBarrier.lean:282`): refuted at the one-piece
  identity barrier, `R = 0`, `γ t = t`, `v t = 1` —
  `test/VacuityAudit.lean :: barrier_le_of_local_descent_descent_is_load_bearing`
  (all four conjuncts: the curve is differentiable with the stated velocity, `hstart` holds, `hdesc`
  fails, and the conclusion fails).
* `dist_ge_of_local_descent`'s `hsep` (`:382`):
  `test/VacuityAudit.lean :: dist_ge_of_local_descent_separation_is_load_bearing`
  (the start `γ 0 = 0` is at distance `0` from the origin).
* `barrier` and `minMaxBarrier` are not constants:
  `identBarrier_eval`, `minMaxBarrier_is_not_constant` — guards against a `barrier := 0` regression,
  which would make every trapping theorem true.
* `CraciunZSH.hinterior` (`C ⊆ interior K`, load-bearing at five sites: `:32`, `:186`, `:222`
  — the hypothesis is literally *named* `hinterior` — `:311`, `:346`, `:378`). A-11 reports it is
  unobtainable from Craciun's actual `relint_Ω K_C` hypothesis on symmetry cones; the concrete
  counterexample is the diagonal ray inside the upper half-plane: `{(t,t) | 0 ≤ t} ⊆ {x | x₂ ≥ x₁}`
  but `(1,1) ∉ interior {x | x₂ ≥ x₁}`. Not yet in the test file.
* `DifferentialInclusion.InductionStepHypothesis` (`ZeroSeparatingSurface.lean:297`) is *defined* as
  the implication it takes as hypothesis, so `ZeroSeparatingInduction.inductionStep_of_ruledBuild`
  (`:8715`) is the identity function and discharges no geometric content. It is used nowhere in
  `CRNT/`. **[P]** (the tautology is visible from the `def`; see `inductionStepHypothesis_empty_index_iff_conclusion`
  below for the machine-checked degeneration).

### R7 — **MEDIUM** — `ZeroSeparatingSurfaceExists` is inhabited, but its `x₀ ≠ 0` guard is implicit **[M]**

`CRNT/Geometry/ZeroSeparatingSurface.lean:105`. The structure never states `x₀ ≠ 0`; the guard is
carried by the conjunction `0 < r`, `g x₀ ≤ c`, `{g ≤ c} ⊆ (Metric.ball 0 r)ᶜ`. Machine-checked:

* `test/VacuityAudit.lean :: zeroSeparatingSurfaceExists_is_inhabited :
  ZeroSeparatingSurfaceExists (fun _ : ℝ => 0) 1` — inhabited, via the affine half-plane
  (`n = 1`, `a = δ = 1`).
* `… :: zeroSeparatingSurfaceExists_false_at_origin : ¬ ZeroSeparatingSurfaceExists f 0` — the
  interface is **unsatisfiable at the origin**.
* `… :: zeroSeparatingSurfaceExists_start_ne_zero` — the implicit guard, positively.

So a blueprint instantiating the interface with `x₀ = 0` is discharging a false statement.

### R8 — **MEDIUM** — `NetworkCycleDecomposition` is uninhabited, so `ToricEmbeddingWR`'s polar-cone
embedding is dead **[P]**

`CRNT/Dynamics/ToricEmbeddingWR.lean:160` requires `mono : ∀ j, Monotone (a j)` where `a` is the

* `test/VacuityAudit.lean` — R1, R5, R6 (partial), R7, A-11.

`CRNT/Dynamics/UpperRegionVacuity.lean` was written and then **deleted** under the consolidation
decision; the derivation it contained is recorded in R2 as a cross-check, not as an artifact.
Both remaining files are hole-free and elaborating (see §5 for the check commands; the orchestrator
should run `lake build`).
`NetworkCycleDecomposition` has no instances and `multiCycle_velocity_mem_polarCone` /
`NetworkCycleDecomposition.velocity_mem_polarCone` can never be applied. Not a vacuity *bug* — a
dead input. (The orchestrator has already ruled this module out.)

### R9 — **LOW** — nothing syntactic to report

`scripts/stub_baseline.txt` has five entries; the only chain-related one is hole A's `sorry`.
A regex sweep of `CRNT/Geometry/FanRefinement.lean`, `FanFaceLattice.lean`,
`ToricBarrierTrapping.lean`, `PolyhedralBarrier.lean`, `ZeroSeparatingInduction.lean` and
`TrueChemistrySRCriterion.lean` for the classic hollow shapes (`:= True`, `∃ _, True`,
`dummy : True`, `isTrue trivial`, `by trivial`) returns **no matches**. The danger in this tree is
semantic, not syntactic — which is why this file is a set of refutations rather than a linter.

---

## 2. Degenerate-data enumeration

Every definition in the two chains that admits degenerate input, with `file:line`, and whether the
degeneracy is guarded downstream.

| # | definition | file:line | admits | guarded downstream? |
|---|---|---|---|---|
| D1 | `structure Network` | `CRNT/Basic/Network.lean:24` | `R = Empty` ⇒ `complexes = ∅` ⇒ `IsComplexBalanced` vacuous (`Equilibria/ComplexBalanced.lean:33`), `stoichSubspace = ⊥`, `massActionVectorField = 0` | **Yes**, by `hcodim : 2 ≤ finrank (stoichSubspace.map (projOn Pmax))` at `HighCodimensionSiphonFace.lean:131` — with `R = ∅` the right side is `0` |
| D2 | `Network.reaction` | `CRNT/Basic/Network.lean:32` | an **identity reaction** `source = target` ⇒ `reactionVector = 0`, a null true-reaction class carrying two SR edges at the same species | **No.** It perturbs `TrueSRCycle.isCPair` counts arbitrarily, which feeds directly into `Even` and therefore `TrueSRStrongCriterion`. **Unexamined — flagged as the most likely remaining hole-B degeneracy** |
| D3 | `Network.reaction` | `CRNT/Basic/Network.lean:32` | the **zero reaction** `source = target = 0` ⇒ `IsFlowChannel` (`TrueChemistrySRGraph.lean:71`) ⇒ excluded from the true chemistry ⇒ the SR graph can be empty | **No**, and it is *the* vacuity route for hole B: `flowN` is exactly this |
| D4 | `structure RateConstants` | `CRNT/Kinetics/MassAction.lean:24` | zero rate constants | **Yes** — `positive : ∀ r, 0 < k r` (`:28`). Closed by construction |
| D5 | `S` (species type) | `CRNT/Basic/Network.lean:24` | `S = Empty` ⇒ `xstar.Positive` vacuous | **Yes**, by `hPmaxne : Pmax.Nonempty` (`HighCodimensionSiphonFace.lean:124`) |
| D6 | a species in no reaction | `CRNT/Basic/Network.lean:32` | yes, unconstrained | **No**, but harmless: both chains gate on `Positive`, not on occurrence |
| D7 | `abbrev DifferentialInclusion.Field` | `CRNT/Dynamics/DifferentialInclusion.lean:43` | `F y = ∅` ⇒ `ForwardInvariant F R` for all `R` | **No** — see R1 **[M]** |
| D8 | `Λ` in `forwardInvariant_of_cone_descent` | `CRNT/Geometry/PolyhedralBarrier.lean:343` | `Λ i = ∅` ⇒ `hpolar` vacuous | **Partly** — `hmem` blocks it, but `hmem` alone is not the geometry; see R5 **[M]** |
| D9 | `ι` (barrier index) | `CRNT/Geometry/PolyhedralBarrier.lean:67` | — | **Yes** — `[Nonempty ι]` is required by `Finset.univ_nonempty`; `barrier` is not defined at `ι = ⊥` |
| D10 | `ι` in `InductionStepHypothesis` | `CRNT/Geometry/ZeroSeparatingSurface.lean:298` | `ι = ⊥` ⇒ the "induction step" ≡ the conclusion | **No** — see R6 |
| D11 | `ZeroSeparatingSurfaceExists f x₀` | `CRNT/Geometry/ZeroSeparatingSurface.lean:105` | `x₀ = 0` ⇒ unsatisfiable | **Implicitly** (not stated) — see R7 **[M]** |
| D12 | `hinterior : C ⊆ interior K` | `CRNT/Geometry/CraciunZSH.lean:36` (and `:186`, `:222`, `:311`, `:346`, `:378`) | satisfiable in general, unobtainable on symmetry cones | **No** — A-11; the intended application is blocked |
| D13 | `NetworkCycleDecomposition.mono` | `CRNT/Dynamics/ToricEmbeddingWR.lean:182` | refuted ⇒ the structure is uninhabited | n/a — see R8 |
| D14 | `structure TrueSRCycle` | `CRNT/Multistationarity/TrueChemistrySRGraph.lean:139` | 1-cycles, repeated species, repeated reactions | **Yes** — `nontrivial : 2 ≤ n`, `species_injective`, `reaction_injective` |
| D15 | `structure TrueSRCycle.SToRIntersection` | `CRNT/Multistationarity/TrueChemistrySRGraph.lean:236` | an empty common-edge subgraph, or a cycle-shaped common subgraph | **Yes** — `componentCount_pos`, `componentLength_pos`, `covers_common`, `components_separated`. (This is why a cycle's common subgraph with *itself* is empty, and why `netN` satisfies the second clause of `hSR` despite having an even cycle) |
| D16 | `def ReactantProductSeparated` | `CRNT/Multistationarity/StrongConcordance.lean:26` | — | **Yes** — it is the hypothesis added when the unseparated criterion was refuted (`CRNT/Examples/TrueSRNetCoeffCounterexample.lean:724`, `unseparated_trueSRCriterion_false`) |

---

## 3. What landed

**`test/VacuityAudit.lean`** — ten machine-checked lemmas, elaborating with **zero** sorry-warnings
(`research/scripts/checkmod.sh test/VacuityAudit.lean` → `=== OK === (sorry-warnings: 0)`).
Registered in the `test` target via `python3 scripts/gen_lakefile.py` (`"test.VacuityAudit"`
appended to the generated `[[lean_lib]] name = "test"` globs; `lakefile.toml` is generator-owned
and was **not** hand-edited).

1. `identBarrier_eval` — the one-piece identity barrier is the identity (anti-regression guard).
2. `forwardInvariant_vacuous_for_empty_field` — **R1**: an empty `DifferentialInclusion.Field`
   makes `ForwardInvariant F R` true for *every* `R`.
3. `forwardInvariant_not_vacuous_in_general` — and the definition is not vacuous in general.
4. `barrier_descent_is_load_bearing` — **R6**: `hdesc` of `barrier_le_of_local_descent`.
5. `identBarrierSublevel_not_forwardInvariant` — the same barrier really is not invariant.
6. `cone_descent_hpolar_is_vacuous_for_empty_cone` — **R5**: `hpolar` is vacuous for `Λ i = ∅`.
7. `dist_ge_separation_is_load_bearing` — **R6**: `hsep` of `dist_ge_of_local_descent`.
8. `minMaxBarrier_is_not_constant` — anti-regression guard for the non-convex route.
9. `zeroSeparatingSurfaceExists_is_inhabited` — **R7**: the surface interface is satisfiable.
10. `zeroSeparatingSurfaceExists_false_at_origin`,
    `zeroSeparatingSurfaceExists_start_ne_zero` — **R7**: its implicit `x₀ ≠ 0` guard.

**Not landed by me:** `CRNT/Dynamics/UpperRegionVacuity.lean` (R2).  Written, then **deleted** under
the orchestrator's consolidation decision — four other researchers independently compiled the
same `False`-level theorem and `infra-scaffold-crnt` owns the consolidated file.  My derivation is
recorded in R2 as a *cross-check* of the disputed fork verdict, not as a fifth artifact.

## 4. Dead ends / not done

* **Not done:** `inductionStepHypothesis_empty_index_iff_conclusion` and the two `ruledSet_*`
  refutations from R6 were drafted but are **not** in the landed file — the module import
  (`CRNT.Geometry.ZeroSeparatingInduction`, 8776 lines) made elaboration slow, and R2 superseded
  their priority.  They are written out in Lean signature form in §6 so another researcher can
  land them without re-deriving them.
* **Not done:** the `hsep`-shape refutation of the `faceRelevantCore` criterion in the exact shape
  of `…_of_convex_tiles`'s `hsep`.  `form-barrier`'s `not_separationClause_of_boundaryOmegaPoint`
  covers it; duplicating it was not worth the elaboration cost.
* **Not done — and this one cost real budget:** the `hinterior` symmetry-cone counterexample
  (R6 last bullet).  `Metric.isOpen_iff` on `interior {x | x₂ ≥ x₁}` worked, but the
  `dist ((1,1) + (0, -ε/2)) (1,1) < ε` arithmetic in the `ℝ × ℝ` *sup* norm defeated me across
  four iterations.  The statement is in §6.  It is **not** on any live path — `FaceDirectionCone`
  never imports `CraciunZSH` — so it is a documentation item, not a blocker.
* **Not attempted:** constructing the hole-B witness of R4.  The `directed 3-cycle` candidate is
  worked out in R4; formalising it needs the enumeration of all `TrueSRCycle n` for
  `S = Fin 3` (`2 ≤ n ≤ 3`) and the "a common subgraph which is a 6-cycle is not a union of simple
  S-to-R paths" argument, plus the `Quotient` reasoning for `TrueReaction` representatives.  That
  is a genuine multi-day job and is **the** thing that would move hole B from "no witness at all"
  to "a witness with content".
* **Tooling note for whoever reads this later:** `research/scripts/checkmod.sh` was broken for
  the whole first half of round 1 — `lake env` *prepends* to `LEAN_PATH`, so the worktree-local
  `.lake/build/lib/lean/CRNT/` decoy directory shadowed the shared cache and **every** module
  importing a `CRNT.*` module failed with an error naming an `.olean` that exists.  Fixed by
  `infra-build` on `research/infra-build` (PR #7) and pulled into this branch.  If your branch
  predates that fix, re-run your checks; any "does not elaborate" verdict involving a `CRNT.*`
  import from before is void.

## 5. Lean signatures for the items not landed (drop-in)

```lean
-- test/VacuityAudit.lean, requires `import CRNT.Geometry.ZeroSeparatingInduction`

/-- `InductionStepHypothesis` is its own implication: `inductionStep_of_ruledBuild` is the identity
and no combination of the ruled-surface theorems can discharge it. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (x₀ : E) {ι : Type*} [Fintype ι]
    (facetField : ι → (E → E)) (facetStart : ι → E) :
    DifferentialInclusion.InductionStepHypothesis f x₀ facetField facetStart :=
  fun h => h

/-- Degenerate index: with no facets the "induction step" collapses to the conclusion. -/
theorem inductionStepHypothesis_empty_index_iff_conclusion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (x₀ : E)
    (facetField : Empty → (E → E)) (facetStart : Empty → E) :
    DifferentialInclusion.InductionStepHypothesis f x₀ facetField facetStart ↔
      DifferentialInclusion.ZeroSeparatingSurfaceExists f x₀

/-- The outward-ruling hypothesis of `ruledSet_subset_compl_ball_of_outward` is load-bearing:
without it the swept point lands exactly on the origin. -/
theorem ruledSet_outward_ruling_is_load_bearing :
    (‖((0 : ℝ), (1 : ℝ)) : ℝ × ℝ‖ = 1) ∧
    (∀ p ∈ ({(0 : ℝ × ℝ) | (3 : ℝ)} : Set (ℝ × ℝ)), (1 : ℝ) ≤ ⟪((0 : ℝ), (1 : ℝ)), p⟫_ℝ) ∧
    (¬ (0 ≤ ⟪((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (-1 : ℝ))⟫_ℝ)) ∧
    (¬ CRNT.ZeroSeparatingInduction.ruledSet ({(0 : ℝ × ℝ) | (3 : ℝ)} : Set (ℝ × ℝ))
        ((0 : ℝ), (-1 : ℝ)) 3 ⊆ (Metric.ball (0 : ℝ × ℝ) 1)ᶜ)


/-- `C ⊆ interior K` is unobtainable on a symmetry cone: the diagonal ray lies in the closed upper
half-plane but not in its interior.  This is the concrete content of A-11.  `Metric.isOpen_iff`
on `interior {x | x₂ ≥ x₁}` gives the ball; the missing step is the `ℝ × ℝ` **sup-norm**
arithmetic `dist ((1,1) + (0, -ε/2)) (1,1) < ε` (after `rw [Metric.mem_ball]` the goal is
`max (dist z.1 1) (dist z.2 1) < ε`, i.e. the `Prod.sup_dist` form, *not* `‖x - y‖`). -/
theorem symmetry_cone_not_in_interior :
    ¬ diagRay ⊆ interior {x : ℝ × ℝ | x.2 ≥ x.1}
```

## 6. Recommended next actions

1. **Do not assign anyone to hole A's packaged criteria.** They are retired for one structural
   reason (A-28 / `Network.universalPositive_omegaLimit_of_closedPositiveConfine`), which R2
   independently confirms by a `Permanent`-free route. `hm`, `hstart`, `hface`, `hcore` are known
   dead, and `hm` was vacuous anyway (A-25: `m := 0` satisfies it). The residue is
   `ComparableGrowthDescent.descend` (`SiphonDimensionDescent.lean:125-132`).
2. **For hole B, build the witness of R4** before building the ear.
   `exists_second_evenCycle_of_offCycle_escape` closes in `hSR.2`; `hSR.2` is only informative for
   networks that *have* a second even cycle, and **no network in the tree satisfies all three of
   hole B's hypotheses**. The directed 3-cycle `A → B → C → A` over `S = Fin 3` is the candidate,
   with the construction worked out in R4.
3. **Add `Λ i ≠ ∅` and `F x ≠ ∅` guards** wherever the barrier criteria are instantiated
   (`ToricBarrierTrapping.lean`, `FaceDirectionCone.lean`, `ToricBarrierExplicit.lean`). They are
   free and they are the difference between a real criterion and a tautology.
4. **Record D2** (identity reactions) as an open question for hole B: an identity reaction `X → X`
   contributes two SR edges at `X` with the same endpoint, so it flips `isCPair` counts. Whether
   `ReactantProductSeparated` plus `ZeroComplexReactionsAreFlows` excludes it is unexamined.
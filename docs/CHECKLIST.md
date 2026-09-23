# crnt-lean working checklist

Companion to `docs/theorem-index.md` (generated) and `docs/session-addendum.md` (findings).
This file is hand-maintained: **update it at the end of every session.**

---

## 0. Pre-flight — run before writing any lemma

Skipping step 2 is how `crossClassRatio_eq_iff_robust` got reinvented. It was already proved
in `Design/ACRCrossClass.lean` *and* described in prose in
`docs/multistationarity-robustness.md:286`. Names diverge; statements don't.

- [ ] 1. `python3 scripts/decl_index.py --build` (refresh; declarations move)
- [ ] 2. `python3 scripts/decl_index.py --like '<the statement you are about to write>'`
- [ ] 3. `python3 scripts/decl_index.py --find <keyword>`
- [ ] 4. Check the name in mathlib source before relying on it:
      `grep -rn "theorem <name>\b" /path/to/mathlib4-4.31.0/Mathlib/`
- [ ] 5. If the plan is to reuse a proof from another module, confirm that module **builds**.
      A `PROVED`-looking statement in a non-elaborating module is `UNCHECKED`, not proved.

## 0b. Environment (see addendum §1 for detail)

- `zstd` absent, network off; use `zdec.py` (ctypes over `libzstd.so.1`), pipe into `tar`.
- Disk is the constraint (~9.8 GB). Skip `*.ilean`. One bash command caps at ~300 s, hence
  `scripts/batch_build.py` with its resumable `.build_state.json`.
- `LEAN_PATH` must list every `$CRNT_CACHE/*/.lake/build/lib/lean` plus the project build dir.

---

## 1. The headline number nobody was tracking

| | count |
|---|---|
| theorems/lemmas | 4688 |
| PROVED (no sorry **and** module elaborates) | 3514 |
| **UNCHECKED (no sorry, module never elaborated)** | **895** |
| SORRY | 278 |

Ledger 201 -> 185. Tree sorry lines 295 -> 286.

**957 statements look proved but Lean has never seen their proofs.** This is not a
bookkeeping nicety: of the ones inspected this session, one referenced struct fields that do
not exist (`shinarFeinberg_pinnedRatioAt_via_linkageScalars`) and one was vacuous
(`nonterminal_complex_detects_deficiency_coordinate`, conclusion `a = b + (a - b)`).

So the real remaining work is **285 sorries + 957 unverified proofs**, and the cheapest way
to shrink the second number is to get ledgered modules to elaborate — which is the
mechanical tier that was already the priority.

- [ ] Re-run `decl_index.py --build` after each promotion wave and watch UNCHECKED fall.

---

## 2. Done — verified this session

Every item below was confirmed by elaborating the file. All four gates pass; `import CRNT`
green; 293 tree sorries.

### Modules taken to zero errors (12)
- [x] `Oscillation.VassenaCriteria` — gates 35 modules
- [x] `Oscillation.PlanarRecurrentSection` — gates 31
- [x] `Oscillation.PlanarMinimalSet`
- [x] `Oscillation.PlanarTransversalGeometry`
- [x] `Oscillation.PlanarCanonicalReturn`
- [x] `Oscillation.RankTwoPlanar`
- [x] `Oscillation.Analyze`
- [x] `Flux.Cone`
- [x] `Flux.Elementary`
- [x] `Reduction.Intermediates`
- [x] `Deficiency.TerminalKernelDimension` — the `Quotient` problem from HANDOFF §6.3
- [x] `Deficiency.TerminalKernelCone`
- [x] `Deficiency.DeficiencyOneScalarReduction`
- [x] `Deficiency.DeficiencyOneLinkageScalars`

### Mathematical corrections
- [x] **`Phase2` was the wrong type.** `Fin 2 → ℝ` carries the sup norm, which is not induced
      by any inner product, so the "missing `InnerProductSpace`" instance can never exist.
      Now `EuclideanSpace ℝ (Fin 2)`. Unblocked four Planar gates.
- [x] **`complexBalanced_iff_toricLeaf` was false as stated** — needed `x.Positive`;
      `IsComplexBalanced` carries no positivity. Its `sorry` was unfillable.
- [x] **`nonterminal_complex_detects_deficiency_coordinate` was vacuous** — proved with α = 1
      and `ring`, and flagged, because the statement cannot carry its intended content.
- [x] **Same-linkage-class case of `nonterminal_linkageScalars_eq` discharged** —
      `by_cases hcls : N.classOf c = N.classOf d` then `rw [hcls]`.
- [x] Deduplicated the cross-class reduction into `Deficiency/LogMonomialRatio.lean`; both
      names kept, no consumer broken.

### Tooling added
- [x] `scripts/decl_index.py` — generated declaration index + `--like` duplicate check
- [x] `scripts/batch_build.py` — resumable budgeted build driver
- [x] `scripts/dump_sorries.py` — every sorry with its real statement
- [x] `scripts/find_transferable.py` — normalized-statement match (+ delegation filter)
- [x] `scripts/promotable.py`, `scripts/rank_targets.py`, `zdec.py`

---

## 3. Next — in priority order

### 3.1 Free wins
- [x] **DONE — promoted 10 modules; ledger 201 -> 191.** Use `scripts/promote.py --all`,
      which snapshots all five coupled files, applies, regenerates the lakefile, runs all
      four gates, and **rolls back** on any failure. Never do this by hand.
- [ ] `Oscillation.PlanarSectionCoordinates` — next Planar gate, at 9 errors.
      Remaining: `quarterTurn_zero`/`_one` must see through `toLp`; one goal wants
      `inner_smul_left` + `real_inner_quarterTurn_self`.

### 3.2 Shinar–Feinberg — the one open goal, now isolated
Chain: `shinarFeinberg_pinnedRatioAt` ← `standardShinarFeinberg_crossClassRatioPinned`
← `logMonomialRatio_eq_of_nonterminal_SF_pair` ← `nonterminal_linkageScalars_eq`.

- [ ] **Extend `StandardShinarFeinbergHypotheses`** (`Design/ACRStandard.lean:61`) to carry a
      `ShinarFeinbergHypotheses` and the deficiency-one hypotheses. It is currently a
      standalone struct with `nonTerminalC`/`nonTerminalD` and no `extends`, which is why
      `ShinarFeinbergCrossClass` (referencing `H.toShinarFeinbergHypotheses`,
      `H.deficiencyOneHypotheses`, `H.c_nonterminal`, `H.d_nonterminal`) has never compiled.
      **Mechanical.**
- [ ] **Prove the cross-class case of `nonterminal_linkageScalars_eq`.** Reduced (verified) to
      `x s = y s` for two nonterminal complexes in *distinct* linkage classes.
      - Circular, do not attempt: anything consuming `CrossClassRatioPinned`
        (`ACRUnconditional`, `ACRCrossClass`, `shinarFeinberg_ACRAt`). The reduction is an
        `iff`, so the coupling lemma and ACR at `s` are the *same* statement.
      - Everything proved gives Φ constant *within* a class only:
        `logMonomialRatio_const_of_deficiencyZeroClass`,
        `logMonomialRatio_eqOn_deficientClass`, `logMonomialRatio_eqOn_linked`,
        `proportional_of_restrictedKineticImage` (`MultiClass.lean:114` — sorry-free and
        building, but concludes `Ψx = K·Ψy` on the deficient class θ **only**).
      - Viable route: deficiency-one structure theory — `h.oneTerminal`, nonterminality of
        both complexes, and uniqueness of the deficient class via `deficientLinkageClass` /
        `linkageDeficiency_eq_zero_of_ne_deficientClass` (both proved). The step to find is
        one that crosses from a deficiency-**zero** class to the deficient class.

### 3.3 The four unchecked "transferable" pairs
`find_transferable.py` flags these as sorried-with-a-proved-twin, but **every proving module
is `UNCHECKED`**, and the fifth of the set turned out to be a sketch against a nonexistent
API. Get the proving module to elaborate *first*, then judge.
- [ ] `treeConstant_kineticKernel` ← `…_via_cofactor` (5 live consumers)
- [ ] `deficiencyOne_existence_of_weaklyReversible` ← `…_via_degree` (1)
- [ ] `exp_treePotential_satisfies_treeBinomials` ← `…_complete` (1)
- [ ] `det_bdc_principal_expansion` ← `…_via_cauchyBinet` (2)

### 3.4 Sweep for more vacuous / false statements
The two found this session were visible from the statement alone.
- [ ] `python3 scripts/dump_sorries.py` over all 285; look for conclusions that are ring
      identities, `∃` with no real constraint, or hypotheses the goal cannot possibly need.
- [ ] `python3 scripts/decl_index.py --dups` for proved statements duplicated across modules.
- [ ] Add a build-status filter to `find_transferable.py` so `UNCHECKED` twins are labelled.

### 3.5 Known not-mechanical — do not count as repair work
- [ ] `Translation.SourceComplexes` — sketch against the nonexistent `N.ReactionTranslation`.
- [ ] `Dynamics.TierStrictUpwardPartner` — goal is false under its own hypotheses.
- [ ] `exists_zero_of_deficiencyOneDegreeCertificate` — needs Brouwer degree theory, which
      mathlib 4.31 does not have in usable finite-dimensional form.

---

## 4. Standing corrections to HANDOFF.md

- §2.2 is wrong: a `.olean`-only cache **does** import fine (the 519 companion-less oleans work).
- §6.3's `VassenaCriteria` diagnosis is wrong: `Finset.sum_ite_eq'` cannot fire because
  `mul_ite` leaves `(…) * 0`, not a syntactic `0`. Use `Matrix.mul_diagonal`.
- The "21 major theorems" figure is a keyword artefact of `sorry-triage.md`; it classifies by
  keyword match on the enclosing declaration and its comment. Do not quote it as a count.
- New defect classes: `⟪x, y⟫_ℝ` lives in the `InnerProductSpace` scope (not
  `RealInnerProductSpace`); `Mathlib.Data.Matrix.Notation` → `Mathlib.LinearAlgebra.Matrix.Notation`;
  the `section`→`xsection` rename is half-finished (but `HopfRealizes` uses a distinct
  `.section'` that builds — leave it); `congrField` is `subst`-defined so `change` cannot see
  through it.


---

## 5. Triage-first workflow (added after the promotion wave)

Reading files one at a time to rediscover the same defect is the slow path. Analyze the whole
target set first, then fix by *class*:

```
python3 scripts/triage.py --targets scripts/unverified_modules.txt          # classify
python3 scripts/triage.py --targets scripts/unverified_modules.txt --apply  # batch-fix
python3 scripts/batch_build.py --targets scripts/unverified_modules.txt --retry-all
python3 scripts/promote.py --all
python3 scripts/decl_index.py --build
```

`--apply` only touches classes whose fix the error itself determines (`noncomputable`,
`notation-scope`, `bigop-binder`, `noncomputable-thm`, and `missing-import` when the name
resolves to exactly one module with no cycle risk). Every fix is verified by re-elaborating,
and reverted if the error count does not drop.

**Results of the first run:** 11 modules auto-fixed, 89 -> 62 errors, no human file-reading.
`Equilibria.BoundarySiphon` went 7 -> 1 from a single inferred import;
`Equilibria.LinkageComplexBalance` reached 0.

### Current defect distribution across the ledger

| count | bucket | auto |
|---|---|---|
| 51 | invalid-field | |
| 27 | type-mismatch | |
| 22 | unsolved-goals | |
| 22 | noncomputable | yes |
| 13 | simpa-mismatch | |
| 12 | rewrite-no-match | |
| 8 | unknown-ident | |
| 86 | blocked-unbuilt-dep | (build first) |

`invalid-field` at 51 is the largest non-auto bucket and is worth attacking next as a class:
each instance is either a missing import (auto-fixable once the name resolves uniquely) or an
invented name. Extending `triage.py` to split those two apart would likely convert a large
share of the 51 into auto-fixes.

### Biggest remaining targets (error counts after auto-fix)

- `Oscillation.VassenaContinuation` — 30, gates the D-Hopf chain (~28 modules)
- `Oscillation.FloquetOrbitalStability` — 30
- `Oscillation.ReturnMapFamilyPersistence` — 28
- `Deficiency.ExactSequence` — 18
- `Oscillation.PlanarSectionCoordinates` — 8, next Planar gate
- `Basic.Isomorphism` — 9 (all `rewrite-no-match` / `type-mismatch`)


---

## 6. Merging an external tree (never trust "compiles cleanly")

`scripts/compare_tree.py` diffs another CRNT tree against ours and **elaborates both versions
of every differing file** under an identical `LEAN_PATH` and identical dependency `.olean`s,
adopting a file only when the other side is strictly better on `(errors, holes)`.

Elaborating their file inside their own tree is not comparable -- their build state differs.
The script therefore tests each candidate in place: save ours, write theirs, elaborate,
restore.

```
python3 scripts/compare_tree.py --other /path/to/tree                    # survey
python3 scripts/compare_tree.py --other /path/to/tree --verify           # + Lean
python3 scripts/compare_tree.py --other /path/to/tree --verify --port    # + adopt
```

### First merge (2026-09-19, external branch)

736 files: 681 identical, 45 differing, none unique to either side.
**7 adopted, 6 rejected, all decided by Lean:**

| adopted | ours | theirs |
|---|---|---|
| `Deficiency.ExactSequence` | 18 err, 1 hole | **0 err, 0 holes** |
| `Design.Localization` | 5 err, 1 hole | 0, 0 |
| `Kinetics.GeneralizedNondegeneracy` | 4 err, 1 hole | 0, 0 |
| `Design.EmergentCycles` | 4 err, 1 hole | 0, 0 |
| `Equilibria.TreeConstantKernelBasis` | 3 err, 1 hole | 0, 0 |
| `Equilibria.TreeConstantBinomials` | 2 err, 1 hole | 0, 0 |
| `Subnetwork.EmbeddedNetwork` | 0 err, 1 hole | 0, 0 |

`ExactSequence` and `TreeConstantBinomials` were the two highest-leverage one-hole roots
(~20 downstream modules each), so this was a real unblock.

**Rejected, kept ours** -- and the two the external branch itself flagged as unfinished are
exactly the two that measured worse, so its self-reporting was accurate:
`Translation.SourceComplexes` (ours 13 err vs theirs 16),
`LinearAlgebra.OrientedMatroidNondegeneracy` (2 vs 3), `Equilibria.DetailedBalanceToric`
(5 vs 6), `Deficiency.TerminalKernelFaces` (1 vs 2), `Translation.LinearConjugacy` (3 vs 5),
`Kinetics.GeneralizedNetwork` (4 vs 5). The last four are cases where our `triage.py`
auto-fixes had already beaten the hand repairs.

Ours also stayed ahead on `Deficiency.DeficiencyOneLinkageScalars` (1 hole vs 2) and
`Equilibria.GeneralizedComplexBalanceToric` (4 vs 5) -- the vacuous-lemma proof, the
same-class discharge, and the false-statement correction.

### Two independent findings that agree

Both branches independently concluded, without coordination:
* `Translation/SourceComplexes` targets an obsolete `N.ReactionTranslation` API and needs a
  migration, not a proof.
* `OrientedMatroidNondegeneracy` states something **not true** under its current witness
  definition (a nonzero witness with no positive coordinates makes the positive-block
  covering condition vacuous). Fix: require nonempty positive support. Ours is at 2 errors,
  theirs 3; neither compiles yet. **This is the next false-statement correction to land.**

### Merge hygiene
- [ ] Always `--verify` before `--port`; hole count alone is not sufficient (a file can drop a
      `sorry` and gain errors, which is a regression).
- [ ] After porting: `triage --apply` -> `batch_build --retry-all` -> `promote --all` ->
      `decl_index --build`.
- [ ] Re-check the ours-better list after each merge; our auto-fixes drift ahead of hand
      repairs quickly.


---

## 7. The `invalid-field` class: resolved as a question, not as 51 repairs

Ran every unresolved name from `.build_state.json` against a map of every declaration in the
tree. Result: **all 22 distinct unresolved names are declared nowhere — zero are
auto-importable, zero ambiguous.** So `invalid-field` / `unknown-ident` is not a
missing-import bucket at all; it is entirely "written against an API that does not exist".
That kills the idea of converting it to auto-fixes, and it is worth knowing rather than
re-deriving.

Two of the 22 were nonetheless *near-misses* and are now fixed:

* **`isCompact_of_isBounded`** (`Geometry/ConservativeCompatibility`) — there is no
  `IsClosed.isCompact_of_isBounded`. The 4.31 lemma is
  **`Metric.isCompact_of_isClosed_isBounded`**, taking both facts as explicit arguments, and
  it is in the `Metric` namespace (`Mathlib/Topology/MetricSpace/Bounded.lean:320`).
* **`section` as a structure field** — the real root cause of a whole cluster. **Four**
  structures declared a field literally named `section`
  (`ReturnMapFamilyPersistence:34`, `ScalarReturnMapFamilyPersistence:27`,
  `FloquetPersistenceGeneral:34`, `PlanarReturnOrdering:30`). `section` is a Lean command
  keyword, so the parser reads the field declaration as a `section` command and the entire
  structure silently fails to be created — which is why the error surfaces far away as
  "invalid field" on *other* names. Renamed the field to `xsection` across the declarations,
  the structure-instance assignments, the unqualified in-structure uses, and every `.section`
  projection, with per-file verification and automatic revert if a file got worse.
  `HopfRealizes` uses a distinct `.section'` that builds — excluded.

**`Oscillation.ReturnMapFamilyPersistence`: 28 -> 0 errors.** After the rename, the only
residue was a universe error: `structure BranchPeriodicTrajectory ... : Type where` cannot
hold a `PeriodicTrajectory` over `E : Type*` (that lands at `u_1 + 1`, not `Type 0`).
Dropping the `: Type` ascription and letting Lean infer closed it. Promoted; ledger -> 185.

### Remaining `section`-field structures
The other three renamed structures still show 1 error each, all blocked behind unbuilt
dependencies rather than the rename. Re-run `batch_build --retry-all` then `triage` on
`ScalarReturnMapFamilyPersistence`, `FloquetPersistenceGeneral`, `PlanarReturnOrdering` once
their closures build — they are likely cheap now.

### Genuinely-missing API (not proofs) — needs a design decision, not a repair
`BranchPeriodicTrajectory`(now built), `CrossLinkageTreeRatioPinned`, `robustExponent`,
`sameLinkageACRValue`, `sameLinkage_ACR_treeConstant_equation`,
`weaklyReversible_of_complexBalanced` (all `Design/ShinarFeinbergTreeFormula`),
`DeficiencyOneBranchStrictlyMonotone`, `DeficiencyOneScalarBranch`
(`Deficiency/DeficiencyOneMonotonicity`), `DifferentiablyMonotonicAt`
(`Multistationarity/WeakNormality`), `LocalC1SensitivityBranch`
(`Design/LocalizationDifferential`), `TransverseFloquetSectionData`
(`Oscillation/FloquetOrbitalStability`), `ReactionTranslation`
(`Translation/SourceComplexes`), `toShinarFeinbergHypotheses`
(`Design/ShinarFeinbergCrossClass`), plus
`conservationCoordinates_eq_of_stoichCompatible` /
`stoichCompatible_iff_conservationCoordinates_eq` (`Equilibria/ConservationCoordinates`),
`concordanceKineticsRealization_noninjective` (`Multistationarity/ConcordanceConverse`),
`exists_positive_kineticKernel_of_weaklyReversible` (`Deficiency/TerminalKernelFaces`).

`ShinarFeinbergTreeFormula` alone accounts for five of these, so it is one coherent missing
API rather than five defects.


## 8. Second merge pass — and a flaw in my own comparison metric

Verified the remaining 29 differing files (last pass had only Lean-checked 16). **1 adopted,
27 keep-ours, 1 tie.** Two claims did not survive verification under an identical
`LEAN_PATH`:

* `Oscillation.VassenaContinuation` — reported as "compiles cleanly"; measured **ours 30
  errors vs theirs 38**. Kept ours.
* `Oscillation.VassenaCriteria` — ours 0 vs theirs 4.

Also ours-better: `Reduction.Intermediates` (0 vs 2), `Flux.Elementary` (0 vs 3),
`Flux.Cone` (0 vs 1), `SingleIntermediateElimination` (6 vs 8),
`ConservativeCompatibility` (4 vs 5). The pattern holds: `triage.py` auto-fixes keep
overtaking hand repairs, so the other branch should re-pull before touching these.

### **Metric flaw — fix before the next merge**
`compare_tree.py` ranks on `(errors, holes)`, but **a module that fails at *import* time
reports only 1 error while hiding every defect behind it.** `PlanarSectionCoordinates` was
adopted on a measured `1` that was really `12` (their version reintroduced the stale
`Mathlib.Data.Matrix.Notation` path I had already fixed; mine was at 8). I had to reapply my
own `open scoped InnerProductSpace` and `WithLp.toLp` fixes on top of the adopted file.

- [ ] Make `compare_tree.py` refuse to adopt when either side's diagnostics contain
      `object file ... does not exist` — that is an unresolved-import short circuit, not a
      comparable error count. Re-measure after building deps.

## 9. `PlanarSectionCoordinates`: 12 -> 4 errors

Fixes that landed (next Planar gate):
* `⟪x, y⟫_ℝ` on `EuclideanSpace` needs **`PiLp.inner_apply`** in the simp set, not
  `RCLike.inner_apply` alone — the inner product goes through the `PiLp` layer first. This
  broke both `real_inner_quarterTurn_self` and `norm_sq_quarterTurn`.
* `canonicalSectionPoint` needed `noncomputable` (depends on `quarterTurn`).
* `canonicalSectionPoint_mem`: `simp` could not cancel `q + X - q`; an explicit
  `have ... := by abel` plus `real_inner_smul_left` then `real_inner_quarterTurn_self` closes it.
* `canonicalSectionPoint_injective`: the `simpa` lands on `u • t = v • t`; convert to
  `(u - v) • t = 0` explicitly via `sub_smul` rather than hoping simp finds it.

**Remaining: 4 errors, all inside `canonicalSectionPoint_scalar`** (two `linarith` failures,
one kernel-metavariable). That is the surjectivity direction — genuine proof work, one
theorem, and the last thing standing between the Planar chain and its next promotion.


## 10. Theorem-formalization pass (sorry-directed)

Switched from error-count targeting to **promotion leverage**: for each sorried module, how
many ledger modules would become closure-clean if that module's sorries were filled. Baseline
was 74 closure-clean ledger modules. Top built targets were
`Design.EmergentConservation` (6 sorries, gain 4) and `Equilibria.TreeConstants` (2, gain 3).

### Proved this pass (4 sorries closed, all Lean-verified)

**`Equilibria/LinkageComplexBalance.isComplexBalanced_iff_forall_linkage`** — global complex
balance is exactly classwise complex balance. Proved two new helper lemmas
`linkageInflow_eq_inflow` / `linkageOutflow_eq_outflow`: at a complex of its own class the
class constraint `classOf (sourceIdx r) = q` is automatic, because
`classOf_sourceIdx_eq_targetIdx` (`Deficiency/KineticBlock.lean:32`) says no reaction joins
two classes. Needed an import of `Deficiency.KineticBlock` (no cycle). Module now 0 errors,
0 sorries; **promoted, ledger -> 184.**

**`LinearAlgebra/OrthogonalComplement.sup_inf_orthSum_of_le`** (new, reusable) — for `U ≤ V`,
`U ⊔ (V ⊓ orthSum U) = V`. Dot-product form of Mathlib's
`Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection`, transported across `toEuclid`.
Note: `Submodule.comap_sup` **does not exist** (comap does not distribute over `⊔`), so the
proof compares *images* and closes with `Submodule.map_injective_of_injective` plus
`Submodule.map_inf _ hinj`.

**`Design/EmergentConservation`** — 6 sorries -> 3, module at 0 errors:
* new `sum_speciesRestriction_mul`: dot-product adjointness of restriction and zero-padding
  (both sums collapse to the part supported on `V`);
* `inheritedLocalConservation_le_local`, via that adjointness plus
  `Submodule.mem_sup_right (Submodule.mem_map_of_mem hz)`;
* `localConservation_eq_inherited_sup_emergent` — one line from `sup_inf_orthSum_of_le`, since
  `emergent` is *by definition* `local ⊓ inheritedᗮ`;
* `globalConservation_eq_augmented_sup_lost` — same lemma, rewriting
  `(orthSum augmentedStoich)ᗮ` back via `orthSum_orthSum`.

Tree sorry lines **286 -> 282**. All four gates PASS, umbrella green.

### DONE — that companion lemma closed all three
Added to `LinearAlgebra/OrthogonalComplement.lean`, both compiling first attempt:
* **`inf_orthSum_eq_bot`** — `U ⊓ orthSum U = ⊥`. Direct from the definition: `w` in both
  gives `∑ i, wᵢ * wᵢ = 0`, and `Finset.sum_eq_zero_iff_of_nonneg` + `mul_self_eq_zero`
  forces `w = 0`. No inner-product machinery needed.
* **`finrank_add_finrank_inf_orthSum_of_le`** — for `U ≤ V`,
  `finrank U + finrank (V ⊓ orthSum U) = finrank V`, from `sup_inf_orthSum_of_le`,
  `Submodule.finrank_sup_add_finrank_inf_eq`, and the disjointness above
  (`U ⊓ (V ⊓ orthSum U) = ⊥` via `← inf_assoc, inf_eq_left.mpr h`).

With those, the three remaining sorries fell in one pass:
`localConservationDim_eq_inherited_add_emergent` (one line),
`globalConservationDim_eq_augmented_add_lost` (same lemma + `orthSum_orthSum`),
`emergentConservationDim_eq_zero_iff` (`Submodule.finrank_eq_zero` then the subspace
decomposition both ways).

**`Design/EmergentConservation`: 6 sorries -> 0, 0 errors.** Promoted together with
`Design.Localization`; ledger -> 182. The build pass that followed built **45** modules.

### Note
`Equilibria.TreeConstants` (gain 3) is NOT cheap: its two sorries are the directed
Matrix--Tree theorem and "every finite strongly-connected digraph has an in-arborescence
toward each vertex". Real graph theory, not repair.


## 11. High-risk target scoped: the in-arborescence existence theorem

`Equilibria.TreeConstants` is the top remaining leverage (gain 3, builds). Its two sorries:

1. `treeConstant_kineticKernel` — the directed Matrix--Tree theorem.
2. `exists_rootedInArborescence_of_weaklyReversible` — every finite strongly-connected
   digraph has an in-arborescence toward each vertex.

I scoped (2) rather than half-building it. **Feasible, and the prerequisite exists**, but it
is a genuine construction, not a repair:

* `IsRootedInArborescence root T` is a four-part conjunction: every non-root class vertex has
  **exactly one** selected outgoing reaction (`∃!`), the root has none, no selected reaction
  comes from outside the class, and every class vertex `SelectedReaches` the root.
* `SelectedReaches = Relation.ReflTransGen (SelectedEdge T)`, so mathlib's `ReflTransGen`
  induction applies.
* **Prerequisite already proved:** `WeaklyReversible.reaches_comm`
  (`Graph/CycleCover.lean:89`) makes reachability symmetric, which is exactly the strong
  connectivity of each linkage class. Also available: `reaches_self_through`,
  `onDirectedCycle`.
* `Decision/Reachability.ReachesWithin : ℕ → Complex S → Complex S → Prop` gives a
  **bounded-depth** reachability, which is what a distance function and well-founded
  recursion need.

### Construction plan
1. `dist c := Nat.find` of `ReachesWithin n c root` (nonempty by `reaches_comm` + a
   `Reaches → ∃ n, ReachesWithin n` bridge — check whether that bridge exists; if not it is
   the first lemma to write).
2. For `c ≠ root` in the class, `dist c > 0`, so there is `r` with `sourceIdx r = c` and
   `dist (targetIdx r) < dist c` (strict decrease is the whole point).
3. Choose such an `r_c` per vertex (`Classical.choice`), set
   `T := (class.erase root).image (fun c => r_c)`.
4. The `∃!` clause: existence by construction; uniqueness because every element of `T` has
   `sourceIdx (r_c) = c`, so two elements with the same source come from the same `c`
   (`Finset.image` + injectivity on the index).
5. The reachability clause: strong induction on `dist c`, stepping along `r_c`.

Realistically 150+ lines with several elaboration rounds — a session of its own, not a
turn. Whoever picks it up: **write step 1's bridge lemma first and verify it in isolation**,
since everything else depends on the distance being well-defined.

`treeConstant_kineticKernel` (Matrix--Tree) should wait until (2) lands, since the kernel
computation needs the arborescence set to be nonempty.


## 12. Where the sorries actually live — and the Equilibria bottleneck

Distribution (279 lines / 96 modules):

| area | sorries | modules | built |
|---|---|---|---|
| **Equilibria** | **64** | 19 | 3 |
| Kinetics | 31 | 9 | 0 |
| Multistationarity | 27 | 12 | 3 |
| Translation | 23 | 9 | 1 |
| Basic | 22 | 3 | 0 |
| Flux | 17 | 4 | 1 |
| Deficiency | 16 | 7 | 3 |
| Stochastic / Design | 13 each | 5 / 6 | 2 / 1 |
| Graph | 12 | 3 | 0 |

**Equilibria is the densest, but "attack the biggest area" was the wrong first move**: only
3 of its 19 sorried modules elaborated, so 61 of the 64 sorries were not even iterable, and
their counts could be masked by elaboration errors. The productive move was to make them
*reachable* first. Root-blocker analysis found six roots, four of which shared one defect.

### New defect class: bad generalized field notation
**"Invalid field notation: Function `f` does not have a usable parameter of type
`Network ...`"** — `logRatio`, `conservationCoordinate`, `kineticMonomial`,
`logRatio_toricParam` are plain functions in the `Network` namespace that take **no**
`Network`/`GeneralizedMassActionData` argument, so `N.f` / `G.f` cannot resolve. Stripping
the receiver fixed the class:
`ComplexBalanceGeometry` 2 -> 0, `ConservationCoordinates` 11 -> 2,
`DetailedBalanceToric` 5 -> 1. (`GeneralizedNetwork` got *worse* and was auto-reverted —
its `G.kineticMonomial` needs a real argument, not just receiver removal.)

### Also fixed
* **`Mathlib.LinearAlgebra.Quotient` is now a directory** -> `...Quotient.Basic`. One more
  4.31 stale path. Its "1 error" was an import short-circuit hiding **10** real errors —
  the same metric trap as §8, so the guard reverted a *correct* fix. Applied deliberately.
* `DetailedBalanceToric`: `StoichCompatible x y` unfolds to `(y - x) ∈ stoichSubspace`, but
  the goal wanted `x - y`; closed with `Submodule.neg_mem` + `simpa [neg_sub]`. **0 errors.**

**Equilibria modules building: 3 -> 17 of 33.** Two build passes compiled 45 modules each.

### The chain this unlocked
`DetailedBalanceToric` (now 0) -> `DetailedBalanceEntropy` (2 sorries) ->
`DetailedBalanceLinearStability` (**7 sorries, and only 1 error, which was this import
chain**). That is 11 sorries that just became iterable — the best-conditioned block left in
Equilibria, and the next thing to work.

### Clusters inside Equilibria (attack as clusters, not modules)
* **Matrix--Tree**: `DirectedMatrixTreeProof` 6, `MatrixTreeCofactor` 4,
  `GeneralizedTreeConstantCriterion` 4, `TreeConstantCriterion` 3, `TreeConstants` 2 = **19**.
  All gated on the in-arborescence construction in §11 — do that first.
* **Lyapunov / linear stability**: `ComplexBalanceLinearStability` 7 (8 errors) +
  `DetailedBalanceLinearStability` 7 (now unblocked) = **14**. Checked: these are *not*
  duplicates — entropy-Hessian quadratic form vs log-form reaction flux, genuinely the
  complex-balanced and detailed-balanced theories. But they are structurally parallel
  (`*_eq_secondVariation`, `*_nonpos`, `*_eq_zero_iff*`), so a shared
  "negative-semidefinite quadratic form vanishing exactly on the tangent" lemma would likely
  serve both — the §10 pattern again.
* **Wegscheider**: `WegscheiderGenerators` 4, `WegscheiderInteger` 3,
  `WegscheiderDeficiency` 1 = **8**.


## 13. Auto-fixer extended, then manual work down the Equilibria stability chain

### `bad-dot-notation` is now an AUTO class in `triage.py`
Lean names the offending function in the message ("Function `f` does not have a usable
parameter of type ..."), so stripping the receiver is *determined by the error* -- the same
bar as `noncomputable`. Added as an auto-fixer, verified per module and reverted if the
error count does not drop. First tree-wide run: **4 modules, 25 -> 12 errors**, including
`Deficiency.DeficiencyOneMonotonicity` 8 -> 3 and
`Equilibria.ComplexBalanceLinearStability` 8 -> 4.
(It correctly declined `Kinetics.GeneralizedNetwork`, where `G.kineticMonomial` needs a real
argument rather than receiver removal.)

### Manual: the detailed-balance chain is now fully clean
* **`Equilibria.DetailedBalanceEntropy` -> 0 errors.** `positivity` cannot see inside a sum;
  replaced with `mul_nonneg` + `Finset.sum_nonneg` using the per-reaction lemma. Recurring
  shape: **`positivity` fails on `∑`/flux terms; go term-wise.**
* **`Equilibria.DetailedBalanceLinearStability` -> 0 errors, 7 sorries -> 5.**
  - `massActionMonomial_directional_derivative_logform`: proved from
    `massActionMonomialGrad_mul_coord` with `Finset.mul_sum` + `field_simp` +
    `linear_combination h j * hg`.
  - **Relocated `massActionMonomialGrad_mul_coord`** from `Oscillation/VassenaCriteria.lean`
    to `Kinetics/MassActionJacobian.lean`, next to the definition of
    `massActionMonomialGrad`. It was only reachable from `Oscillation/*`, so the
    `Equilibria/*` stability modules could not use it without a cycle. Both files still
    elaborate; a pointer comment marks the old site.
  - `detailedBalanceJacobianQuadratic_strict_on_stoich`: closed the sum-positivity `sorry`
    with `Function.ne_iff` to get a nonzero coordinate, then `Finset.sum_pos'` with
    `div_mul_eq_mul_div` + `div_nonneg` / `div_pos`.
  - Last error was `linarith` unable to connect `hpair` and `hsumpos`: they were the same sum
    written two ways. `simp only [invDiagonalApply] at hpair` makes the definition syntactic.
    **`unfold ... at h` did nothing here — `simp only [def]` is the reliable form.**

### State
Tree sorry lines **279 -> 277**; PROVED **3527 -> 3547**; UNCHECKED **895 -> 877**;
decl-level SORRY 271 -> 269. **Equilibria building: 17 -> 19 of 33.** A build pass compiled
39 modules. All four gates PASS, umbrella green.

### Next in this cluster
`Equilibria.ComplexBalanceLinearStability` is now at 4 errors with 7 sorries and is the
mirror of the module just finished — same theorem shapes
(`*_eq_secondVariation`, `*_nonpos`, `*_eq_zero_iff_tangent`, `*_strict_on_stoich`). The four
techniques above should transfer almost directly:
term-wise `Finset.sum_nonneg` instead of `positivity`, `Function.ne_iff` + `Finset.sum_pos'`
for strictness, `simp only [def]` to align sums, and `linear_combination` against the
gradient identity (now reachable from `Kinetics/MassActionJacobian`). **Do that next.**


## 14. Division of labour with the parallel branch, and the Basic isomorphism cluster

The other branch has claimed: Matrix--Tree / cofactor machinery, persistence & permanence,
Shinar--Feinberg / ACR, global oscillation & Hopf, and terminal kernels. **Do not work those**
-- it has already re-done `TerminalKernelDimension` and `TerminalKernelCone`, which this
branch had also cleared, so that was duplicated effort on both sides.

Areas it has named nothing in, and which this branch should own:

| area | sorries | modules | note |
|---|---|---|---|
| **Basic (isomorphism)** | 22 | 3 | foundational; worked this pass |
| **Kinetics (generalized)** | 31 | 9 | 0 were building |
| **Multistationarity** | 27 | 12 | |
| **Translation** | 23 | 9 | |
| Graph (condensation/circulation) | 12 | 3 | adjacent to their Matrix--Tree, coordinate first |

Note on their hole count: they report 270 vs our 286 and call ours stale. Counts are not
comparable across branches (line vs declaration, comment stripping, and each branch has
proofs the other lacks). `compare_tree.py --verify` is the only reliable comparison -- use it
rather than arguing headline numbers.

### `Basic.Isomorphism`: 10 errors -> 0

All four defects were distinct and none was auto-fixable:
* **Composite equiv not unfolded.** `rw [G.map_reaction, F.map_reaction]` cannot fire on
  `(F.reactionEquiv.trans G.reactionEquiv) r`; `simp only [Equiv.trans_apply]` first.
* **`Submodule.span_le` leaves a Set-coerced membership**, so `rw [Submodule.mem_comap]`
  never matches -> `simp only [SetLike.mem_coe, Submodule.mem_comap]`.
* `LinearEquiv.finrank_map_eq` was applied in the wrong direction (needed `.symm`).
* **Reaction-vs-complex projection.** The goal is about `(N.reaction r).source`, but
  `map_reaction` is about the whole renamed reaction. `(Reaction.rename f R).source` is
  *definitionally* `Complex.rename f R.source`, so bridge with `congrArg` or a `have ... rfl`.

**The real find: `complex_mem_iff` was circular.** Its reverse direction read
`(F.symm.complex_mem_iff _).mp h` -- the theorem invoking itself. Replaced with a direct
argument: pull the complex out of `Finset.mem_union`/`mem_image`, transport along
`map_reaction`, then cancel the renaming with **`(Complex.renameEquiv F.speciesEquiv).injective`**
(`renameEquiv` already existed and gives injectivity for free). Module now **0 errors**.

### `Basic.IsomorphismKinetics`: 1 error -> 0
`simpa [← F.invConcentration_mapConcentration x, ← ...y]` hit **maximum recursion depth**:
reversed rewrites keep re-expanding `x` into `invConcentration (mapConcentration x)` forever.
**Rule: never give `simp` a reversed rewrite whose RHS contains its own LHS** -- rewrite
forwards in the hypothesis (`congrArg` then `rwa [...] at h`).

### State
PROVED **3547 -> 3570**; UNCHECKED **877 -> 854**; sorry lines 277; all four gates PASS,
umbrella green. `Basic.IsomorphismStructural` (10 sorries) is now blocked only by
`Dynamics.Trap` -- fix that and the remaining 15 sorries of the cluster become iterable.

### Next for this branch
1. `Dynamics.Trap` -> unblocks `Basic.IsomorphismStructural` (10 sorries).
2. `Kinetics.GeneralizedCycleExactSequence` (9 sorries) and the generalized-kinetics cluster
   (31 total, none building) -- entirely ours.
3. `Multistationarity.StrongConcordance` / `WeakNormalityCriterion` (4 each).


## 15. `Dynamics.Trap` cleared; `WeakNormality` is the real gate on the Basic cluster

### `Dynamics.Trap`: 5 errors -> 0, promoted (ledger -> 181)
* **`DecidablePred` on a `Finset.filter`.** `minimalTraps` filtered on `N.IsMinimalTrap`,
  which is not decidable. Fixed with the pattern the repo already uses for
  `rootedInArborescences`: `noncomputable def ... := by classical; exact ...`, and the
  companion `mem_minimalTraps` becomes `classical; simp [minimalTraps]`.
* **New defect shape: `unfold A B at h ⊢` errors when *either* location lacks one of the
  names.** Four sites had `unfold IsReactant IsProduct at hreact ⊢` where the hypothesis has
  one and the goal the other. **`simp only [A, B] at h ⊢` tolerates absence; `unfold` does
  not.** Worth adding to `triage.py` as an auto class -- it is a pure textual substitution
  and the error names the offending constant.

### `Multistationarity.WeakNormality` — bad dot notation in disguise
`rateDerivativeFunctional` has `{N : Network S}` **implicit**, so `N.rateDerivativeFunctional`
cannot resolve. Unlike the usual case this does *not* produce
"does not have a usable parameter"; it surfaces as **"typeclass instance problem is stuck:
Fintype ?m"**, which is why the auto-fixer missed it. Stripping the receiver was correct but
uncovered three deeper errors, so the module is at 4:
* a `simpa ... using W.nonsingular` that genuinely does not match (the two operators differ by
  scalar rearrangement -- needs a real proof, not a bigger simp set);
* `DifferentiablyMonotonicAt` is *declared in this file* yet referenced as
  `N.DifferentiablyMonotonicAt` -- same receiver problem, at a structure;
* a `rewrite` with no matching pattern.

**This is the sole gate on `Basic.IsomorphismStructural` (10 sorries)**, so it is the next
thing to finish, not a side quest. Recommended order: fix the two remaining receiver errors
first (mechanical), then the `simpa`, then re-measure.

- [ ] Add to `triage.py`: treat "typeclass instance problem is stuck" **together with** a
      receiver-prefixed call to a `{N : ...}`-implicit function as the same auto class.
- [ ] Add `unfold A B at h ⊢` -> `simp only [A, B] at h ⊢` as an auto class.

### State
PROVED **3570 -> 3578**; UNCHECKED **854 -> 846**; sorry lines 277; ledger **182 -> 181**.
All four gates PASS, umbrella green.

### Standing queue for this branch (all disjoint from the other branch)
1. `Multistationarity.WeakNormality` (4 errors) -> unblocks `Basic.IsomorphismStructural`
   (10 sorries).
2. `Kinetics` generalized cluster — 31 sorries over 9 modules, none building.
   `GeneralizedCycleExactSequence` (9 sorries) is blocked by one unbuilt dependency; clear
   that first and the cluster becomes measurable.
3. `Multistationarity.StrongConcordance` / `WeakNormalityCriterion` (4 each).
4. `Translation.ParallelStructural` (7) and `Translation.Improper` (5).


## 16. `autoImplicit` is a root cause worth hunting tree-wide

`Multistationarity.WeakNormality`: **5 errors -> 1.** Three of them had a single root cause,
and it is not a tactic problem:

```
variable {S : Type} [DecidableEq S] [Fintype S]        -- N is NOT here
...
structure DifferentiablyMonotonicAt (K : Kinetics N) (x : Concentration S) where
```

`N` is not in the `variable` block, so Lean's `autoImplicit` bound it as `{N : ?}` with an
unknown type. `Kinetics N` then could not determine `S`, which surfaced as
**"typeclass instance problem is stuck: Fintype ?m.5"** — and because the structure failed to
be created, `DifferentiablyMonotonicAt` and `KineticNondegeneracyWitness` became *unknown
identifiers* several lines later. Three errors, one cause, none of them looking like the
cause. Binding it (`structure DifferentiablyMonotonicAt {N : Network S} (K : N.Kinetics) ...`)
cleared all three.

**This is a high-value hunt:** `autoImplicit` turns a typo or a missing `variable` into a
stuck-metavariable error *far* from the real site, and the repo's `variable` blocks are
inconsistent about including `N`. Cheap detector: for each file, list identifiers used in
declaration *signatures* that are neither in its `variable` block nor declared anywhere —
those are silent autoImplicits.

- [ ] Write `scripts/find_autoimplicit.py` doing exactly that, and consider
      `set_option autoImplicit false` per file to make these hard errors.

Also fixed: `Degenerate` is `¬ Nondegenerate`, so
`rw [← weaklyNormal_iff_nondegenerate] at hdeg` could not see the pattern —
`simp only [Degenerate] at hdeg` first. (Recurring: **`rw` needs the definition unfolded;
`simp only [def]` is the reliable opener.**)

### Two new auto classes added to `triage.py`
* `unfold-absent` (AUTO): rewrites `unfold A B at h ⊢` to `simp only [A, B] at h ⊢`, since
  `unfold` errors when either location lacks one of the names.
* `stuck-instance` (report-only, deliberately **not** auto): the error never names the
  offending receiver, so a textual fix cannot be derived from it — but flagging it points at
  the `autoImplicit` class above.

### Remaining error in `WeakNormality` (1)
`simpa [...] using W.nonsingular` at line 107: the weak-normality and normality operators
differ by scalar rearrangement inside a `LinearMap.codRestrict`, so no simp set will align
them. Needs the operators proved *equal as functions* first (`LinearMap.ext`), then
injectivity transported. That is the last thing gating
`Basic.IsomorphismStructural` (10 sorries).

### State
sorry lines 277; PROVED 3578; UNCHECKED 846; ledger 181. All four gates PASS, umbrella green.


## 17. `WeakNormality` closed; the Kinetics cluster unblocked from the top

### A measurement bug of mine — guard against it
I reported `Kinetics.GeneralizedNetwork` as "0 errors" when it had 2. Cause: I ran
`timeout 100 lean $f | grep -c error` in a loop; the timeout **killed** the process, output
was empty, and `grep -c` returned 0. **An empty diagnostic stream is indistinguishable from
success unless you check the exit code.** Never read "0 errors" from a timed-out run; either
drop the timeout for single-file checks or test `${PIPESTATUS}`.

### `Multistationarity.WeakNormality`: 1 error -> 0  (gates 10 sorries)
The `simpa ... using W.nonsingular` could never work: the weak-normality and normality
operators differ by scalar rearrangement **inside a `LinearMap.codRestrict`**, so the simp
set is rewriting under a coercion it cannot see through. The fix is to stop trying to match
and instead prove the operators *equal*, then transport injectivity:

```lean
have hop : N.weakNormalityOperatorOnStoich P
    = N.normalityOperatorOnStoich W.speciesWeights W.reactionWeights := by
  refine LinearMap.ext fun σ => Subtype.ext ?_
  simp only [..., LinearMap.codRestrict_apply, LinearMap.domRestrict_apply, ...]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring
rw [hop]; exact W.nonsingular
```
**General pattern: when two restricted operators "should" be equal, `LinearMap.ext` +
`Subtype.ext` + `congr 1` beats any `simpa`.** This is the third instance this session of
"replace a failing `simpa` with an explicit equality".

### `Kinetics.GeneralizedNetwork`: 2 -> 0, and it was the top of the cluster
* **Proved `kineticOrderRank_le_incidenceRank`** (was a `sorry`): `kineticOrderMap` is
  `kineticComplexMap ∘ incidenceMap`, so `LinearMap.range_comp` plus
  `Submodule.finrank_map_le` gives it in three lines — a linear image cannot raise dimension.
* That unblocked the `omega` at `incidenceRank_eq_kineticOrderRank_add_kineticDeficiency`:
  **ℕ subtraction is truncated**, so `omega` needed the rank bound as a hypothesis.
* `kineticMonomial (α) (x)` takes no `G`, so every `G.kineticMonomial` was invalid. The
  auto-fixer cleared the identifier-receiver cases (6 -> 1); the survivor had a
  **parenthesized** receiver `(GeneralizedMassActionData.classical N).kineticMonomial`, which
  the regex does not match. *TODO: extend `bad-dot-notation` to parenthesized receivers.*

### Cluster state after unblocking the root
`GeneralizedNetwork` 0 errors. The other four are now each blocked by exactly **one upstream
module**, all outside Kinetics:
| module | blocked on |
|---|---|
| `GeneralizedCycleExactSequence` (9 sorries) | `Deficiency.CycleExactSequence` |
| `GeneralizedComplexBalanceObstruction` (4) | `Equilibria.ComplexBalanceObstruction` |
| `GeneralizedDeficiencyZeroCRNT` (4) | `Equilibria.GeneralizedComplexBalanceToric` |
| `GeneralizedDeficiencyZero` (2) | 3 own errors (noncomputable + 2 "Function expected") |

So the 31-sorry Kinetics cluster reduces to **three upstream modules**. Note
`Equilibria.GeneralizedComplexBalanceToric` is one the other branch reports having finished —
worth pulling their version via `compare_tree.py --verify` before doing it here.

### State
sorry lines **277 -> 276**; PROVED **3578 -> 3588**; UNCHECKED **846 -> 837**. All four gates
PASS, umbrella green.


## 18. End-to-end: `Basic.IsomorphismStructural` (isomorphism invariance of structural CRNT)

Took one module as a body of mathematics instead of chasing errors. **5 of 10 sorries closed,
module at 0 errors**, plus two pre-existing *broken* proofs repaired and one upstream blocker
cleared. 12 new verified declarations.

### The technique that made it cheap: prove one direction, get the other from `F.symm`
Every statement here is an `iff` between `N` and `M`. Proving both directions doubles the
work and lets them drift. Instead prove the forward map only, add two inverse-cancellation
simp lemmas, and derive the `iff`:

```lean
@[simp] theorem symm_mapSpeciesFinset (F) (P) : F.symm.mapSpeciesFinset (F.mapSpeciesFinset P) = P
@[simp] theorem symm_mapSpeciesCovector (F) (w) : F.symm.mapSpeciesCovector (F.mapSpeciesCovector w) = w

theorem isSiphon_iff (F) (P) : N.IsSiphon P ↔ M.IsSiphon (F.mapSpeciesFinset P) :=
  ⟨fun h => F.isSiphon_map h, fun h => by simpa using F.symm.isSiphon_map h⟩
```
Same shape for traps, minimal siphons, conservation laws, consistency. **This is the pattern
for the whole file** — the five remaining sorries should use it too.

### Closed
* `isSiphon_iff`, `isTrap_iff` — transport incidence witnesses through both equivalences,
  using `reactionEquiv.surjective` / `speciesEquiv.surjective` to name preimages.
* `isMinimalSiphon_iff` — needed three new `@[simp]` bridge lemmas
  (`mapSpeciesFinset_subset`, `_nonempty`, `_inj`); the content is that every candidate
  strict subset downstairs is the renaming of one upstairs.
* `conservationLaw_iff` — the key observation is that `mapSpeciesCovector` **is** the action
  of `speciesLinearEquiv` (`rfl`), so `Equiv.sum_comp` plus `map_reactionVector` closes it.
* `consistent_iff` — push the positive flux along `reactionEquiv`; `map_sum` + `map_smul` +
  `map_reactionVector` turn the transported sum into `speciesLinearEquiv 0`.

### Pre-existing proofs that were simply wrong
`isReactant_iff` and `isProduct_iff` both ended in `rfl`, which cannot see through
`Complex.rename`: `rename e y (e s)` is `y (e.symm (e s))`, and reducing that needs
`Equiv.symm_apply_apply`. `simp [Reaction.rename, Complex.rename]` closes both. **They were
never true as written**, and everything in the file depends on them.

### Blocker cleared
`Multistationarity.StrongConcordance` had `rw [show y - x = (y - x₀) - (x - x₀) by ext s; ring]`
— `ext s; ring` does **not** close a Pi-type subtraction. Replaced by the group identity
`rw [← sub_sub_sub_cancel_right y x x₀]`. Module -> 0 errors.

### Correct names (the file used non-existent ones)
`N.Conservative` -> **`N.IsConservative`** (`Flux/PSemiflow.lean:37`);
`N.Consistent` -> **`N.IsConsistent`** (`Deficiency/Consistent.lean:43`).

### Remaining 5 in this module, with the route
| sorry | route |
|---|---|
| `conservative_iff` | `IsConservative = ∃ w, IsStrictPSemiflow w`; transport `w` by `mapSpeciesCovector`, same shape as `consistent_iff` |
| `normal_iff` | rename the positive weights, then conjugate `normalityOperatorOnStoich` by `speciesLinearEquiv`; use the **`LinearMap.ext` + `Subtype.ext`** pattern from §17, not `simpa` |
| `weaklyNormal_iff` | same as `normal_iff` with `SourceInfluenceFamily` |
| `concordant_iff` | both are `¬ ∃ (α, σ), Witness`; contrapose and transport the witness fields one by one |
| `stronglyConcordant_iff` | as `concordant_iff` plus the `reactionDirectionSign` clauses, all renaming-invariant |

### State
sorry lines **276 -> 271**; PROVED **3588 -> 3613**; UNCHECKED **837 -> 829**; declarations
4693 -> 4705. All four gates PASS, umbrella green.


## 19. `Basic.IsomorphismStructural` finished end-to-end: 8 of 10 sorries, 0 errors

Isomorphism invariance of structural CRNT is now a proved theory rather than a stub file.
**23 new verified declarations**, module at 0 errors, only the two normality statements left.

### Closed this pass (on top of §18's five)
* **`concordant_iff`** — Concordance is `¬ ∃ witness`, so the `iff` comes from contraposing a
  *witness transport* in both directions. `concordanceWitness_map` transports all five fields:
  `mem_kerL` via the new `inKerL_map`, `mem_stoich` via `mem_stoichSubspace_map`,
  `sigma_ne` via `mapSpeciesCovector_ne_zero`, and both sign clauses via `isReactant_iff`
  (the source-support conditions are literally reactant incidence).
* **`stronglyConcordant_iff`** — same shape. Needed `reactionDirectionSign_map` (the sign is
  `source s - target s`, so renaming-invariant by `map_reaction`), then `promotes_map` /
  `opposes_map`, then the six-field `strongConcordanceWitness_map`.
* **`conservative_iff`** — `IsPInvariant w` is `w ∈ orthSum stoichSubspace`. `isPInvariant_map`
  works because every stoichiometric vector downstairs is the renaming of one upstairs
  (`← map_stoichSubspace`, then `obtain ⟨u, hu, rfl⟩`), reducing the pairing to `Equiv.sum_comp`.

### Reusable lemmas this produced (worth knowing about before touching any transport proof)
`inKerL_map`, `mem_stoichSubspace_map`, `mapSpeciesCovector_ne_zero`,
`mapSpeciesCovector_apply`, `mapSpeciesCovector_eq` (`= speciesLinearEquiv`, by `rfl`),
`isPInvariant_map`, `reactionDirectionSign_map`, `promotes_map`, `opposes_map`,
`mapSpeciesFinset_subset` / `_nonempty` / `_inj`, `symm_mapSpeciesFinset`,
`symm_mapSpeciesCovector`.

`inKerL_map` and `isConsistent_map` share one sum-transport argument
(`Equiv.sum_comp` + `map_sum` + `map_smul` + `map_reactionVector`); that argument is the
workhorse of the whole file.

### Gotcha worth remembering
A `@[simp]` lemma declared *later* in the file is not available earlier — `mapSpeciesCovector_apply`
sits in the concordance block, so the conservativity proof above it must use
`simpa [mapSpeciesCovector]` instead. Cheap to trip over, cheap to fix.

### The last 2 (`normal_iff`, `weaklyNormal_iff`) — route
Both are `Nonempty ...Witness` whose content is `Function.Injective` of an operator
*restricted to the stoichiometric subspace*. So the proof is not field-by-field transport;
it needs the induced equivalence `N.stoichSubspace ≃ₗ M.stoichSubspace` coming from
`map_stoichSubspace`, then the two restricted operators shown **conjugate** by it, then
injectivity transported across the conjugation. Use the §17 pattern
(`LinearMap.ext` + `Subtype.ext` + `congr 1`) — a `simpa` will not align them, exactly as in
`weaklyNormal_of_normal`. Renaming the weights is the easy part
(`q' t = q (symm t)`, `η' q = η (symm q)`).

### State
sorry lines **271 -> 268**; PROVED **3613 -> 3627**; declarations 4705 -> 4716;
UNCHECKED 829. All four gates PASS, umbrella green.


## 20. Third merge with the parallel branch — 7 adopted, and a warning

741 files: 658 identical, 68 differing. **7 adopted after Lean verification, 5 kept ours,
1 skipped.** Sorry lines **266 -> 241** (the single biggest drop of the project).

### Adopted (all verified in *our* tree with dependencies pre-built)
| module | ours was | theirs |
|---|---|---|
| `Graph.Condensation` | 1 err, 7 holes | **0, 0** |
| `Kinetics.GeneralizedNetwork` | 0 err, 5 holes | 0, 0 |
| `Deficiency.TerminalKernelFaces` | 1 err, 4 holes | 0, 0 |
| `Equilibria.TreeConstantCriterion` | 0 err, 3 holes | 0, 0 |
| `Deficiency.TerminalKernelCone` | 0 err, 3 holes | 0, 0 |
| `Deficiency.TerminalKernelDimension` | 0 err, 2 holes | 0, 0 |
| `Equilibria.TreeConstants` | 0 err, 2 holes | 0 err, 1 hole |

`TreeConstants` is the notable one: their **rooted in-arborescence existence theorem** is
real and verified, which is the §11 construction I had scoped at 150+ lines and declined to
start. That leaves `treeConstant_kineticKernel` (directed Matrix--Tree) as the sole hole
there, matching their own account.

### Rejected — the "zero holes" trap, now with hard numbers
Three of their claimed closures have **no sorries but many errors**, i.e. the holes were
replaced with text Lean rejects:

| module | ours | theirs |
|---|---|---|
| `Equilibria.GeneralizedTreeConstantCriterion` | 0 err, 4 holes | **16 err**, 0 holes |
| `Translation.SourceComplexes` | 13 err, 1 hole | **16 err**, 0 holes |
| `Equilibria.GeneralizedComplexBalanceToric` | 3 err, 4 holes | **7 err**, 0 holes |
| `Design.ShinarFeinbergTheorem` | 0 err, 1 hole | 3 err, 0 holes |
| `LinearAlgebra.OrientedMatroidNondegeneracy` | 2 err, 1 hole | 3 err, 0 holes |

**A hole count is meaningless without the error count.** This is the same asymmetry as
`UNCHECKED`: removing a `sorry` from a module that does not elaborate proves nothing. Any
future merge must compare `(errors, holes)` jointly, which `compare_tree.py` does.
It also means their reported "270 vs our 286" was not a like-for-like comparison.

### Unblocking the Kinetics chain after the merge
Fixing three defects cleared the whole upstream chain:
* `Equilibria.GeneralizedComplexBalanceToric` 3 -> 0: two `noncomputable` (auto-fixed) plus
  **`N.SameStoichClass` cannot resolve** — the def sits inside
  `namespace GeneralizedMassActionData`, so its real name is
  `…GeneralizedMassActionData.SameStoichClass`. Use `SameStoichClass N x y`.
  *New sub-case of the bad-dot-notation class: the receiver is fine, the **namespace** is wrong.*
* `Kinetics.GeneralizedDeficiencyZero` 2 -> 0: **`GeneralizedNondegenerate` is declared
  nowhere in the tree** (autoImplicit again). The intended hypothesis is the
  Müller--Regensburger sign condition `SignCompatible N.stoichSubspace (orthSum
  G.kineticOrderSubspace)`, exactly as used in `GeneralizedComplexBalanceToric`. Substituted
  and flagged in-source, since this is an inferred statement rather than a transcription.

### State
sorry lines **241** (from 295 at session start); PROVED **3674**; UNCHECKED **820**;
ledger **179**. All four gates PASS, umbrella green.

### Division of labour going forward
Theirs (confirmed by their own plan): directed Matrix--Tree, cross-class Shinar--Feinberg,
persistence/permanence, global Hopf / planar end-to-end, generalized toric.
Ours: Equilibria stability cluster (14), Kinetics generalized cluster (19 remaining),
Multistationarity (27), Translation (23), Flux (17), and converting `UNCHECKED` to verified.

**Message back to them:** re-pull before touching `GeneralizedTreeConstantCriterion`,
`SourceComplexes`, `GeneralizedComplexBalanceToric`, `ShinarFeinbergTheorem`,
`OrientedMatroidNondegeneracy` — our versions elaborate and theirs do not, despite having
fewer holes. And `Basic.IsomorphismStructural` is now complete (10/10 proved) on our side.


## 21. Auditing all 820 UNCHECKED statements

Built `scripts/audit_unchecked.py`. All 820 cannot be *elaborated* (their 156 modules do not
compile), but the two defect shapes that caught the known fakes are detectable statically.
Result of auditing every one:

| check | result |
|---|---|
| references a name declared nowhere | **already covered — use `check_undefined_names.py`, which reports 4** |
| named mathematical hypothesis never used (possible vacuity) | **16** |
| no static red flag | 804 |

### Two false starts of mine, recorded so they are not repeated
1. I reimplemented the undeclared-name audit and got **347** hits — almost all Lean-core
   names (`congrArg`, `Subtype`, `Function`) missing from my Mathlib-only scan. The repo's
   `check_undefined_names.py` already does this properly by restricting to
   `scripts/repo_vocabulary.txt`, and the true answer is **4** (all in
   `scripts/frontier_gaps.txt`). I deleted my version. *Same mistake as the duplicated
   `crossClassRatio_eq_iff_robust` lemma: check for existing machinery first.*
2. The first vacuity pass reported 27, including `kineticDeficiency_eq_deficiency_of_rank_eq`
   ("unused `hrank`"). False positive: the proof is `omega`, which **consumes the local
   context without naming anything**. Excluding context-consuming tactics (`omega`,
   `linarith`, `simp_all`, `aesop`, `assumption`, `positivity`, ...) took 27 -> 16 and made
   the list trustworthy.

### Validation: the detector independently rediscovered two known-false statements
* `Dynamics.TierStrictUpwardPartner.strictBelow_original_of_truncated` — unused `hy'`;
  HANDOFF §7.3 already records this goal as **false under its own hypotheses**.
* `LinearAlgebra.OrientedMatroidNondegeneracy.equalCoordinateNondegenerate_congr_right` —
  unused `hBC`; **both branches independently found this module states something false**.

Finding two known-false statements without being told about them is decent evidence the
other 14 deserve a read.

### The 16 vacuity candidates — highest priority first
| module:line | declaration | unused |
|---|---|---|
| `Kinetics.GeneralizedDeficiencyZeroExistence:76` | `generalized_deficiency_zero_theorem` | `hδ` |
| `Algebra.DeficiencyIdeal:65` | `positive_steadyState_iff_complexBalanced_of_deficiencyZero` | `hx` |
| `Equilibria.ComplexBalanceObstruction:58` | `treeAffinity_mem_incidenceRowSpace` | `hwr` |
| `Theorems.DeficiencyZero.TreeConstantConstruction:36` | `treeLogDifference_mem_incidenceRowSpace` | `hwr` |
| `Translation.DeficiencyImprovement:72` | `original_uniqueSteadyState_via_translation` | `hsign` |
| `Design.LocalizationDifferential:173` | `localized_C1_steadyState_branch_of_nonsingular` | `hinj` |
| `Stochastic.DetailedBalance:48` | `productPoisson_reactionFlux_detailedBalance` | `hc` |
| `Oscillation.PlanarLocalReturnLoops:135` | `orbitArc_injective` | `ht` |
| `Oscillation.PlanarReturnMonotonicity:146` | `periodicOrbit_subset_minimal` | `horigin` |
| + `TierStrictUpwardPartner`, `OrientedMatroidNondegeneracy` (both already known false) | | |

`generalized_deficiency_zero_theorem` not using its **deficiency-zero hypothesis** is the
most alarming: either it is proved by a route that does not need `hδ` (then the statement
should be strengthened), or it is vacuous. Read it first.

An unused hypothesis is not proof of vacuity — a proof can legitimately not need one — but
each of these is either a **weaker theorem than advertised** or a genuinely vacuous
statement, and both are worth knowing before the module is counted as done.

### What the audit does NOT show
**804 of the 820 carry no static red flag.** They are not validated — Lean has still never
seen them — but they are not obviously fake either. The only way to settle them is to make
their modules elaborate, and they concentrate heavily:
`Oscillation.*` planar/Hopf machinery dominates the top of the list
(`GlobalHopfSpectralCrossing` 10, `PlanarAdjacentReturnLoop` 10, `PlanarLocalReturnLoops` 10,
`PlanarFlowBox`/`PlanarFlowRegularity`/`PlanarNoCrossing` 8 each), plus
`Design.StrongBufferingFluxRPA` 10 and `Algebra.PositiveTorusIdeals` 9.

That concentration is actionable: the planar/Hopf block is the other branch's declared lane,
so **they should run this audit on it**, while ours is `Design.*`, `Algebra.*`,
`Stochastic.*`, `Translation.*`.


## 22. Elaborating the 804: it is 44 problems, not 156 — and 2 modules gate half

`scripts/rank_unchecked_roots.py` (resumable; state in `.elab_state.json`) elaborated every
non-elaborating module and classified it:

| class | count | meaning |
|---|---|---|
| **DEP-BLOCKED** | **102** | every error is `object file ... does not exist`. **Zero work** — compiles free once its roots do. |
| **ROOT** | **44** | real errors of its own, all dependencies already built → actionable now. |
| DEEP | 0 | (nothing is stuck behind an unbuilt root *and* broken) |

So "elaborate 804 statements" is really "fix 44 modules", and it is extremely top-heavy.
Each ROOT below is scored by the UNCHECKED statements in its transitive downstream closure:

| gates | errs | root |
|---|---|---|
| **242** | 28 | `Oscillation.VassenaContinuation` |
| **159** | 4 | `Oscillation.PlanarSectionCoordinates` |
| 59 | 4 | `Oscillation.Inheritance` |
| 59 | 10 | `Deficiency.CycleExactSequence` |
| 30 | 1 | `Equilibria.MatrixTreeCofactor` |
| 20 | 3 | `Kinetics.GeneralizedBirchExistence` |
| 20 | 5 | `Oscillation.ScalarReturnStability` |
| 20 | 13 | `Translation.SourceComplexes` |
| 18 | 2 | `LinearAlgebra.OrientedMatroidNondegeneracy` |
| 15 | 4 | `Dynamics.GlobalPersistenceFrontier` |

**Two modules gate 401 of the 803.** `VassenaContinuation` (28 errors) and
`PlanarSectionCoordinates` (4 errors) are both `Oscillation.*`, i.e. the other branch's
declared lane — they should be told this, because nothing else in the tree comes close to
that leverage.

### Cleared this pass (4 roots, all 1-error, gating 64)
* `Equilibria.MatrixTreeCofactor` (gates 30) — `Fintype (N.WithoutLinkageRoot root)` could
  not be synthesised: it is `{c : LinkageComplex root // c ≠ linkageRoot root}` and deciding
  the predicate needs choice. Added a `noncomputable instance ... := by classical; exact
  Subtype.fintype _`.
* `Theorems.DeficiencyOne.Theorem` (gates 9) — a stray `.symm`;
  `deficiencyOne_uniqueness` already yields the required direction.
* `Stability.BDCPrincipalMinors` (gates 7) — the goal groups `(-1)^card * (coef * monomial)`
  while `mul_nonneg` splits after `coef`; `rw [← mul_assoc]` first.
* `Stochastic.ConservativeClasses` (gates 6) — `Finset.single_le_sum` left its function as a
  metavariable; pin it with `(f := fun t => w t * m t)`.

Result: PROVED **3674 -> 3691**, UNCHECKED **820 -> 803**, non-elaborating modules 162 -> 152.

### The efficient order from here
1. `PlanarSectionCoordinates` — **4 errors, gates 159.** Best ratio in the tree by far. The
   remaining errors are all inside `canonicalSectionPoint_scalar` (surjectivity).
2. `VassenaContinuation` — 28 errors, gates 242. Biggest prize, most work.
3. `Oscillation.Inheritance` (4 err / 59) and `Deficiency.CycleExactSequence` (10 err / 59).
4. Then the long tail: 34 more roots, mostly 1-7 errors each.

Do **not** work DEP-BLOCKED modules: 102 of them need no attention at all.


## 23. Implementation pass on the top UNCHECKED roots

### `Oscillation.PlanarSectionCoordinates` — 4 errors -> 3 (gates 159)
Proved two real coordinate lemmas inside `canonicalSectionPoint_scalar`:
* `hn2 : ‖field q‖^2 = f₀^2 + f₁^2`, from `real_inner_self_eq_norm_sq` + `PiLp.inner_apply`
  (**note**: `rw [← real_inner_self_eq_norm_sq]` does not fire here; take the equation as a
  `have` and `rw [← h]; ring`).
* `hd : (x₀-q₀)f₀ + (x₁-q₁)f₁ = 0`, the section condition in coordinates. Needed
  `WithLp.ofLp_sub` + `Pi.sub_apply` in the simp set and `linear_combination this` to fix
  the factor orientation.

`nlinarith` was the wrong tactic: each coordinate is a **linear** combination of `hd`
(coefficient `-f₀` on coordinate 0, `f₁` on coordinate 1).

**Remaining obligation (Lean plumbing, not mathematics), recorded in-source.** After
`ext i; fin_cases i` the goal retains `(q + c • !₂[-f₁, f₀]).ofLp ⟨0, ⋯⟩`; none of
`WithLp.ofLp_add`, `ofLp_smul`, `ofLp_toLp`, `Pi.add_apply`, `Matrix.cons_val_zero`,
`Fin.mk_zero`, `Fin.isValue` pushes `ofLp` through the sum at that Fin literal, so
`field_simp` never reaches scalar form. **Route to close:** skip `ext` — prove the two
scalar identities `(x-q) 0 = u * (-(field q) 1)` and `(x-q) 1 = u * (field q) 0` first (each
`field_simp` + `linear_combination · * hd`), then finish with `sub_eq_iff_eq_add'`.

### `Deficiency.CycleExactSequence` — 10 errors -> 9 (gates 59)
* The **Set-coercion-blocks-`mem_ker`** class again (third occurrence):
  `rw [LinearMap.mem_ker]` cannot match `_ ∈ ↑(ker _)`; use
  `simp only [SetLike.mem_coe, LinearMap.mem_ker]`.
* Near-miss name: `LinearMap.finrank_range_of_injective` -> **`LinearMap.finrank_range_of_inj`**
  (`Mathlib/LinearAlgebra/Dimension/Finrank.lean:128`).
* Open: two `unsolved goals` on `codRestrict` kernels (78, 100), a
  `HasQuotient ↥stoichCycleSpace Type` failure at 114 (the `⧸` elaborates only once the
  `comap` argument resolves), and a `Function expected` at 161.

### `Oscillation.Inheritance` (gates 59) — diagnosed, not yet repaired
All three errors are `rw` pattern mismatches against `addSelfReactions` /
`extendSelfReactions` sums: the rewrite targets a `∑ x_1, (N.addSelfReactions Q c)...` shape
that the goal does not literally contain. These need the goal printed and the rewrite
replaced by `Finset.sum_congr` / `simp only [def]`, same as §17.

### Cleared earlier this pass (4 roots, gating 64)
`Equilibria.MatrixTreeCofactor` (Fintype instance via `classical` + `Subtype.fintype`),
`Theorems.DeficiencyOne.Theorem` (stray `.symm`), `Stability.BDCPrincipalMinors`
(`rw [← mul_assoc]` before `mul_nonneg`), `Stochastic.ConservativeClasses`
(`Finset.single_le_sum (f := ...)`).

### State
PROVED **3691**, UNCHECKED **803**, sorry lines 241, ledger 179.
All four gates PASS, umbrella green.

### Next actions, in order
1. `PlanarSectionCoordinates` via the recorded route (gates 159, one theorem).
2. `Oscillation.Inheritance` — print goals, replace the three `rw`s (gates 59).
3. `CycleExactSequence` 78/100/114 (gates 59).
4. `VassenaContinuation` — 28 errors, gates 242; the largest single lever in the tree.

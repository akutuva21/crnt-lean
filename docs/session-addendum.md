# Session addendum — corrections to HANDOFF.md

Everything here was measured against the tree, not estimated. Where it contradicts
`HANDOFF.md`, this file is the later measurement.

## 1. Build environment corrections

**§2.2 is wrong about the cache.** It says a cache with only `.olean` files fails with
`missing data file for module …`. That is false *for importing*. The repo ships
`.lake/build/lib/lean` with 519 `.olean` files and **zero** `.olean.private`, and they import
fine — `import CRNT` was green in 42 s with no cold rebuild. Treat `.olean.private` /
`.olean.server` as required only when a module actually needs private declarations from a
dependency.

**`offline_build.py` has a staleness hole.** `up_to_date` only compares `.olean` mtimes, so it
treats companion-less oleans as current. It worked out here but will silently skip a module
that needs rebuilding.

**`zstd` is not installed and the network is disabled**, but `libzstd.so.1` ships with the
image. `zdec.py` (ctypes streaming wrapper) decompresses the split archives; pipe the
concatenated parts straight into `tar` so the intermediate archive is never written.
Disk is the binding constraint: ~9.8 GB quota against 2.6 GB toolchain + 5.8 GB cache.
Skip `*.ilean` (0.28 GB, editor-only). Also: a single command is capped at ~300 s, which is
why `scripts/batch_build.py` exists.

## 2. `Phase2` was the wrong type — this was the session's main unlock

`abbrev Phase2 := Fin 2 → ℝ` cannot work. `TransversalSection` is stated over
`InnerProductSpace ℝ E` and uses the inner product essentially (`sectionCoord`, the
`transversal` field). The pi type carries the **sup norm, which is not induced by any inner
product**, so the "missing `InnerProductSpace ℝ Phase2` instance" in §6.3 is not a missing
instance — no such instance can exist.

Fixed by `abbrev Phase2 := EuclideanSpace ℝ (Fin 2)` in `Oscillation/PlanarFrontier.lean`.
Ripple cost is small and mechanical: vector literals need `WithLp.toLp 2 ![…]`, because Lean
auto-inserts the `ofLp` coercion but cannot wrap the result back.

This unblocked four consecutive gates of the Planar / Poincaré–Bendixson chain.

## 3. New defect classes for the §6.2 catalogue

**The `⟪x, y⟫_ℝ` notation scope.** It lives in the `InnerProductSpace` scope, **not**
`RealInnerProductSpace` (which supplies the unsuffixed `⟪x, y⟫`). Mathlib 4.31:
`scoped[InnerProductSpace] notation:max "⟪" x ", " y "⟫_" 𝕜:max => inner 𝕜 x y`.
Without the open the bracket is not a valid token, so it surfaces as a bare
`expected token` **parse** error that hides every later defect in the file.
36 files use it (288 occurrences); 8 were missing the open, 7 of them the blocked Planar chain.

**Stale Mathlib path:** `Mathlib.Data.Matrix.Notation` does not exist in 4.31 →
`Mathlib.LinearAlgebra.Matrix.Notation`.

**The `section`→`xsection` rename was left half-finished.** The structure field was renamed but
call sites were not. Note `Dynamics/HopfRealizes` uses `.section'` — a *different* field that
builds; do not rewrite it.

**`congrField` does not reduce.** It is defined by `subst`/`exact`, so `change` cannot see
through it. Use its own simp lemmas (`congrField_orbit`, `congrField_period`).

## 4. `complexBalanced_iff_toricLeaf` was false as stated

`Equilibria/GeneralizedComplexBalanceToric.lean`. The forward direction needs `x.Positive`,
and the proof tried to obtain it with a `sorry`. But `IsComplexBalanced` is
`∀ c, inflow c = outflow c` — a pure balance condition carrying no positivity (the zero state
satisfies it vacuously). **That `sorry` was unfillable.** Now takes `(hx : x.Positive)`
explicitly and the forward direction is discharged. Belongs in §7.3.
*Not yet Lean-verified*: its dependency closure (`TreeConstantBinomials`,
`GeneralizedNetwork`, `GeneralizedNondegeneracy`) does not build.

## 5. The "21 major theorems" figure is a keyword artefact — but the duplicates are not transferable

`docs/sorry-triage.md` classifies by keyword match on the enclosing declaration and its
comment, so a one-line corollary gets filed as `major-theorem` because "toric" or
"deficiency" appears nearby. Do not quote 21 as a considered count.
`scripts/dump_sorries.py` prints every sorry with its real statement.

`scripts/find_transferable.py` implements the §7.1 normalized-statement match. Result:
**6 candidate groups, 0 actually transferable.** Recorded so nobody repeats this:

| sorried | proved twin | why not transferable |
|---|---|---|
| `finrank_complexBalanceObstructionSpace` | `number_independent_complexBalance_constraints` | same file; the "proof" just **cites the sorried one** (tool false positive) |
| `treeConstant_kineticKernel` | `treeConstant_kineticKernel_via_cofactor` | proving module **imports** the sorried one → cycle |
| `deficiencyOne_existence_of_weaklyReversible` | `deficiencyOne_existence_via_degree` | cycle |
| `exp_treePotential_satisfies_treeBinomials` | `…_complete` | cycle |
| `det_bdc_principal_expansion` | `…_via_cauchyBinet` | cycle |
| `shinarFeinberg_pinnedRatioAt` | `…_via_linkageScalars` | cycle |

The five downstream proofs do not cite their sorried twin, so they *look* independent. **Do not
trust that.** All five proving modules are on the frontier ledger and have **never
elaborated**, so their proof text has never been checked by Lean. Verified concretely for
Shinar–Feinberg: `shinarFeinberg_pinnedRatioAt_via_linkageScalars` reads
`H.toShinarFeinbergHypotheses`, `H.deficiencyOneHypotheses`, `H.c_nonterminal` and
`H.d_nonterminal` — **none of these fields exist**. `StandardShinarFeinbergHypotheses`
(`Design/ACRStandard.lean:61`) is a standalone structure with `nonTerminalC` / `nonTerminalD`
and no `extends`. It is a sketch against a nonexistent API (HANDOFF §8), so the mathematics is
*not* present downstream.

I relocated that proof upstream, cleared the four intervening blockers to get it to elaborate,
and it failed on the missing fields — so I reverted it and left the `sorry` with the diagnosis
recorded in the module docstring.

**Rule to carry forward: a "proof" in a ledgered module is unverified text, not a proof.**
Before treating any of the remaining four as transferable, first get its module to elaborate.
`find_transferable.py` should be extended to mark whether the proving module builds.

**The four still-unchecked pairs** are `treeConstant_kineticKernel`,
`deficiencyOne_existence_of_weaklyReversible`, `exp_treePotential_satisfies_treeBinomials`,
`det_bdc_principal_expansion`. Each upstream sorry also has live consumers
(5 / 1 / 1 / 2 respectively), so they cannot simply be deleted either.

**Improve the tool before trusting it again:** `find_transferable.py` must reject a "proved"
member whose proof body mentions the sorried member's name. That single check would have
caught the `finrank_complexBalanceObstructionSpace` false positive.

## 6. Modules taken to zero errors this session

`Oscillation.VassenaCriteria` (4 errors; gates 35), `Oscillation.PlanarRecurrentSection`
(8; gates 31), `Oscillation.PlanarMinimalSet`, `Oscillation.PlanarTransversalGeometry` (8),
`Oscillation.PlanarCanonicalReturn`, `Oscillation.RankTwoPlanar`, `Flux.Cone`,
`Flux.Elementary`, `Reduction.Intermediates`, `Oscillation.Analyze`.

Plus the four blockers cleared while chasing the Shinar-Feinberg transfer -- these stand on
their own even though the transfer itself failed:

* `Deficiency.TerminalKernelDimension` (3 errors; the `Quotient N.stronglyLinkedSetoid`
  problem named in HANDOFF 6.3).  `Quotient.mk''` takes the setoid as an **instance**, but
  `stronglyLinkedSetoid` is a plain `def`, so it must be named:
  `Quotient.mk N.stronglyLinkedSetoid c`.  Likewise `Quotient.sound` needs
  `(s := N.stronglyLinkedSetoid)` plus folding through `Quotient.out_eq`.  Third error was
  `rw [LinearMap.mem_ker]` against a goal of shape `_ in (ker _ : Set _)` -- the coercion
  blocks the pattern, so apply `LinearMap.mem_ker.mpr` instead.
* `Deficiency.TerminalKernelCone` (2 errors): a `rw` whose goal was already in
  `terminalKernelCoordinates` form, and `nonneg_of_mul_nonneg_right` ->
  `mul_nonneg_iff_of_pos_right`, after collapsing the sum with `Finset.sum_eq_single`.
* `Deficiency.DeficiencyOneScalarReduction` (3 errors): `StoichCompatible` is **real but
  unimported** (`Equilibria/CompatibilityClass.lean:25`); a spurious `noncomputable theorem`;
  `exists G : T` with no body, where the intent was `Nonempty T`; and `<<_>>` anonymous-hypothesis
  syntax that cannot resolve unnamed arrow binders during statement elaboration -- name them.
* `Deficiency.DeficiencyOneLinkageScalars` (1 error): missing `noncomputable`.

On `VassenaCriteria`, §6.3's diagnosis is wrong: `Finset.sum_ite_eq'` cannot fire because
`mul_ite` leaves the else-branch as `(…) * 0`, not a syntactic `0`. `Matrix.mul_diagonal`
collapses it in one rewrite. Error 2 needs `linear_combination` (the product `grad * x j` is
not syntactically present, so `rw` cannot fire); error 3 follows from error 2 by cancelling
`diag(x) * diag(1/x) = 1`.

Promotable (builds **and** closure sorry-free) went 6 → 10. Tree sorries 295 → 294.

## 7. Immediate next steps

1. **Promote the 10** (`scripts/promotable.py`): drop from `scripts/unverified_modules.txt`,
   add to `CRNT.lean` *before* the module docstring at line 577, drop from
   `CRNTFrontier.lean`, rerun `gen_lakefile.py`, lower `unverified_baseline.txt`, run all four
   gates. This is bookkeeping on work that already elaborates.
2. `Oscillation.PlanarSectionCoordinates` — next Planar gate, 11 → 9 errors. Remaining:
   `quarterTurn_zero`/`_one` must see through `toLp`; one goal needs `inner_smul_left` plus
   `real_inner_quarterTurn_self`.
3. Add the delegation check to `find_transferable.py`, then rerun over all 294.
4. Do **not** count as mechanical: `Translation.SourceComplexes` (sketch against the
   nonexistent `N.ReactionTranslation`) and `Dynamics.TierStrictUpwardPartner` (goal false
   under its own hypotheses, §7.3).


## 8. The Shinar--Feinberg kernel: what is actually open

Chasing this to the bottom, the whole cross-linkage argument rests on exactly two lemmas in
`Deficiency/DeficiencyOneLinkageScalars.lean`.  Findings:

**`nonterminal_complex_detects_deficiency_coordinate` (was line 100) -- VACUOUS, now proved.**
Its conclusion was

    exists a, a != 0 and  v = a * d + (v - a * d)

which is `a = b + (a - b)`: true for *every* `a`, so the only content was `exists a, a != 0`.
Proved with `a := 1` and `ring`.  None of `hdelta`, `h`, `hx`, `hxs`, `hnt` is used -- in
particular nonterminality of `c` plays no role whatsoever, despite the name and the
docstring ("the sign/cut lemma at the heart of the cross-linkage part of the Deficiency One
Theorem").  This is a real `sorry` removed *and* a real defect exposed: the statement needs
restating to pin `a` down before it can carry the sign/cut step.  Anything downstream relying
on this name for mathematical content is relying on nothing.

**`nonterminal_linkageScalars_eq` (line 115) -- genuinely open.**

    linkageLogRatio x y (classOf c) = linkageLogRatio x y (classOf d)

for nonterminal `c`, `d` differing in exactly one species.  This is the actual
Shinar--Feinberg cut/kernel argument.  I searched the tree for machinery to route it through;
the only proved statement in this family is `linkageRatioGap_self` (`gap q q = 0`, a
tautology).  There is nothing to transfer, and `linkageLogRatio` is defined through
`Classical.choose (Quotient.exists_rep q)`, so any proof must go via
`logMonomialRatio_eqOn_linkageClass` to escape the arbitrary representative.

So the dependency chain is:
`shinarFeinberg_pinnedRatioAt` <- `standardShinarFeinberg_crossClassRatioPinned` (sketch
against a nonexistent structure API, see 5) <- `logMonomialRatio_eq_of_nonterminal_SF_pair`
<- `nonterminal_linkageScalars_eq` (**the one open theorem**).

Closing Shinar--Feinberg means (a) extending `StandardShinarFeinbergHypotheses` to actually
carry a `ShinarFeinbergHypotheses` and the deficiency-one hypotheses, and (b) proving
`nonterminal_linkageScalars_eq`.  (a) is mechanical.  (b) is the theorem.


## 9. Shinar--Feinberg: two new Lean-verified theorems, and the sorry sharpened to ACR

Added to `Deficiency/LogMonomialRatio.lean` (both compile, zero errors):

**`logMonomialRatio_sub_of_differOnlyAt`** -- if `c` and `d` agree away from `s`, then

    Phi(c) - Phi(d) = (c s - d s) * (log (x s) - log (y s))

i.e. linearity of `Phi` in the complex vector, specialised to a Shinar--Feinberg pair.
Proof: `logMonomialRatio_eq` on both sides, `Finset.sum_sub_distrib`, then
`Finset.sum_eq_single s` since every off-`s` term cancels.

**`logMonomialRatio_eq_iff_of_differOnlyAt`** -- for such a pair with `c s != d s`,

    Phi(c) = Phi(d)  <->  x s = y s

(forward via `mul_eq_zero` + `Real.log_injOn_pos`; reverse immediate).

### Consequence

`nonterminal_linkageScalars_eq` now reduces, in verified Lean, to `x s = y s`:

    rw [<- logMonomialRatio_eq_linkageLogRatio .., <- logMonomialRatio_eq_linkageLogRatio ..,
        logMonomialRatio_eq_iff_of_differOnlyAt hx hy hcd (by exact_mod_cast hne)]

so the one remaining `sorry` in the Shinar--Feinberg chain is now *literally* the ACR
conclusion rather than an opaque class-scalar identity.

**Because the second lemma is an `iff`, this is not a weakening -- it is a structural result:
the cross-class scalar coupling lemma and absolute concentration robustness at `s` are the
same statement.** Neither is weaker than the other. So this `sorry` can never be discharged
by anything that itself consumes `CrossClassRatioPinned` (`ACRUnconditional`,
`ACRCrossClass`, `shinarFeinberg_ACRAt`) -- that route is circular by construction, which is
very likely why the chain has stalled here. It must come from the deficiency-one structure
theory: nonterminality of `c` and `d`, `oneTerminal`, and uniqueness of the deficient linkage
class.

`CRNT.Design.ShinarFeinbergTheorem` and the whole `DeficiencyOneLinkageScalars` chain now
elaborate (5 modules built, 0 failures).


## 10. Correction: I duplicated an existing theorem -- and the cross-class case is now isolated

**My mistake, recorded so it is not repeated.** The `iff` I added in section 9
(`logMonomialRatio_eq_iff_of_differOnlyAt`) already existed as
`crossClassRatio_eq_iff_robust` (`Design/ACRCrossClass.lean:118`), sorry-free, with
essentially the same proof down to the `Finset.sum_eq_single s` collapse. I wrote it without
first searching for an equivalent statement -- in a session whose whole subject was
statement matching. `find_transferable.py` only compares *sorried* against *proved*
declarations, so it cannot catch a human adding a fresh duplicate of a proved one.

Resolved by deduplicating rather than reverting: the argument now lives once, at its natural
home next to `logMonomialRatio_eq` in `Deficiency/LogMonomialRatio.lean`, and
`crossClassRatio_eq_iff_robust` is a one-line citation of it. Both names survive, so no
consumer breaks, and `Deficiency/*` can now reach the reduction without importing `Design/*`.
`ACRCrossClass` still elaborates at zero errors.

### What is genuinely left of Shinar--Feinberg

Verified this session inside `nonterminal_linkageScalars_eq`:

* **same linkage class -- DISCHARGED.** `by_cases hcls : N.classOf c = N.classOf d` closes
  by `rw [hcls]`, because the goal is an equality of *class* scalars and
  `logMonomialRatio_eqOn_linkageClass` already supplies constancy of `Phi` on a class.
  Compiles.
* **different linkage classes -- open**, and now reduced to `x s = y s`.

I searched the tree exhaustively for cross-class machinery. Everything proved gives constancy
of `Phi` *within* a class and nothing across:
`logMonomialRatio_const_of_deficiencyZeroClass`, `logMonomialRatio_eqOn_deficientClass`,
`proportional_of_restrictedKineticImage` (`MultiClass.lean:114`, sorry-free and building --
but it concludes `Psi x = K * Psi y` **on the deficient class theta only**),
`logMonomialRatio_eqOn_linked`. So the missing step is genuinely cross-class and cannot be
assembled from what exists.

Combined with the `iff`, the situation is sharp: the open goal is ACR at `s` for two
nonterminal complexes in *distinct* linkage classes, and any route through
`CrossClassRatioPinned` is circular. It has to come from the deficiency-one structure theory
-- `oneTerminal`, nonterminality of `c` and `d`, and uniqueness of the deficient linkage class
(`deficientLinkageClass`, `linkageDeficiency_eq_zero_of_ne_deficientClass`, both proved).

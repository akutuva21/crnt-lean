# Session report — 2026-10-10

**Branch:** `resolve-holes` · **Worktree:** `tmp/holes-resolve` · **Base:** `bfa5b12` (master)

---

## Executive summary

| hole | status | why |
|---|---|---|
| **A** — `CRNT/Dynamics/HighCodimensionSiphonFace.lean:147` | **NOT CLOSABLE** | The statement *is* the Global Attractor Conjecture. The source paper (Craciun v3) asserts the Step-4 assembly but **does not write it down** (verified against the source by `GacLit`, cited at HCSF:390-400). The literature treats the GAC as open (Wiuf 2026). The statement is faithful and non-vacuous (17 of 18 hypotheses jointly satisfiable with a false conclusion). No legitimate route to `sorry`-free is available. |
| **B** — `CRNT/Multistationarity/TrueChemistrySRCriterion.lean:9435` | **REDUCED to one clean proposition** | The residue ≡ `no_offCycle_negFlux`. A proved, axiom-clean discharger (`no_escape_from_cycleSpecies`) already exists in `TrueSRCycleSpeciesDegree.lean` — blocked only by an import cycle. **Import cycle now broken** (SHALLOW verdict: 11 declarations, depth 2, ~300 lines, 3 de-privatisations, 0 new lemmas). Remaining work: prove `no_offCycle_negFlux` from Shinar–Feinberg source-block analysis. This is a well-posed published problem. |

---

## What was achieved (all independently verified)

### Tooling fix (blocked all prior work in new worktrees)
- `.lake/packages` symlink must be created **before** any `lake env` call, otherwise an unbuilt cache is created and all modules fail with "unknown module prefix 'Mathlib'".
- Fix: `rm -rf .lake/packages && ln -s /Users/akutuva/Documents/Proofs/crnt-lean/.lake/packages .lake/packages`

### Hole B — import cycle broken (obstacle 1 DONE)
- `research/drafts/CycleSpeciesDegreeInverted.lean` (560 lines) — the 11 declarations from TSC that `TrueSRCycleSpeciesDegree` needed, lifted and de-privatised.
- **Verified:** `checkmod.sh OK`, `sorry-warnings: 0`, no forbidden tokens.
- Corrects status doc: none of the four named decls was `private`; the real closure is 11 decls, depth 2, 3 genuinely private (all de-privatised), zero new lemmas.
- `no_offCycle_negFlux` is now the **only** obstacle.

### Hole B — `EarNonseparability.lean` ported
- `research/drafts/portfig8/EarNonseparability.lean` (828 ln) — the Shinar–Feinberg ear nonseparability theory from `backup-fig8`.
- Root cause: branch predated commit `fe613e2` (`SeparatesWithin` gained a support-containment premise). Repair added the premise using the file's existing helper.
- **Verified:** `checkmod.sh OK`, `sorry-warnings: 0`, all 4 theorems axiom-clean, **no statement changes**.

### End-block leaf theory (§5.5) formalised
- `research/drafts/EndBlockLeaf.lean` (200 ln, 18 theorems) — the leaf property `SourceBlocks.lean` deferred by name.
- **Verified:** `checkmod.sh OK`, `sorry-warnings: 0`, no forbidden tokens.

### `RelPathAppend.lean` ported
- `research/drafts/portfig8/RelPathAppend.lean` (186 ln) — `appendPath` + `start`/`end`/`noRepeat`.
- **Verified:** `checkmod.sh OK`, `sorry-warnings: 0`.

### Faithfulness audit (both holes)
- Hole A: 17/18 hypotheses machine-checked jointly satisfiable with false conclusion (`CodimTwoFaceModel.codimTwoModel_all_but_hsol`). `hsol` is the sole load-bearing hypothesis. The `_of_upperRegion` refutation needs 7 hypotheses the hole lacks — it infects only dead criteria.
- Hole B: three consumers pass `hsep`/`hflow`/`hSR` verbatim. Hypothesis class non-empty but degenerate (canonical-inflow networks satisfy all three with `hSR` vacuous).
- **Verdict:** both FAITHFUL, NOT VACUOUS.

### Consolidated status document
- `research/Hole-Status-2026-10-10.md` — supersedes scattered route docs. Records:
  - Precise obstacle table for Hole B (obstacle 1 DONE, obstacle 2 remains)
  - Hole A's exact gap: one unused hypothesis at `ConeFaceIncidence.lean:110` (`exposedFace_antitone`) needing packaging as a normal-fan family
  - Mathlib/repo convexity API inventory — `HasDualFGCells`, `coneDual` bipolar, well-founded §7 face induction **all exist** in repo; `CraciunV3BlueprintScales` is nearly empty (2 theorems, no δ-slack)
  - `backup-fig8` port status (RelPathAppend clean, EarNonseparability repaired)
  - Hole A's **final verdict**: not a formalization gap; it is the open GAC; source paper does not prove it.

### One surviving route for Hole A (for the record)
- `exists_positive_omegaPoint_of_relInteriorFace` (HCSF:350) — floors on `S \ Pmax` only, not refuted. But it still requires the Step-4 assembly the paper does not provide.

---

## What is NOT achieved (and why)

| target | reason |
|---|---|
| Close Hole A | The statement = Global Attractor Conjecture, open in literature; source paper claims but does not prove the needed Step 4. Any closure would require a breakthrough, an axiom, or a silent weakening — all forbidden by charter. |
| Close Hole B | Reduced to `no_offCycle_negFlux` (Shinar–Feinberg §5.5/§A.3 source-block datum). The analog `hrest` is refuted by in-scope data (HCSF:200). Agents probed but hit rate limits; the search script was running exact exhaustive/random phases and had refuted its own docstring caveat — useful infrastructure but no verdict yet. |
| Block existence / directed ear decomposition / normal-fan polytope | Agents hit rate limits mid-work. Partial progress was made (NormalFanPolytope was rewriting; DirectedEarDecomp found the general existence theorem false for the representation). |

---

## Artifacts delivered (all in `resolve-holes` branch, pushed)

| path | description | verification |
|---|---|---|
| `research/Hole-Status-2026-10-10.md` | Consolidated status, supersedes route docs | — |
| `research/drafts/CycleSpeciesDegreeInverted.lean` | 11 declarations, import cycle broken | `checkmod.sh` OK, 0 sorries |
| `research/drafts/EndBlockLeaf.lean` | 18 theorems, §5.5 leaf property | `checkmod.sh` OK, 0 sorries |
| `research/drafts/portfig8/RelPathAppend.lean` | 186 ln, appendPath | `checkmod.sh` OK, 0 sorries |
| `research/drafts/portfig8/EarNonseparability.lean` | 828 ln, 4 theorems, repaired | `checkmod.sh` OK, 0 sorries |
| `research/routes/HoleB-Residue-Reduction.md` | Residue = `no_offCycle_negFlux` | — |
| `research/scripts/offcycle_negflux_search.py` | (partial, from OffCycleNegFluxSearch) | self-test passes |

---

## Honest disposition

| hole | recommendation |
|---|---|
| **A** | Leave the `sorry`. Document why (this report + `Hole-Status-2026-10-10.md`). Do not waste effort. |
| **B** | Focus all remaining effort here. The math is published (Shinar–Feinberg). The import cycle is broken. The remaining proposition `no_offCycle_negFlux` is well-posed. Build the source-block / block-tree / ear-decomposition theory that `SourceBlocks.lean` defers; the pieces exist in `backup-fig8` (Case 1/2 ear modules, ear nonseparability) and the `TrueSREarCase1/2` modules already in `master`. |

---

## Suggested next session priorities

1. **Finish the source-block theory for Hole B** — use `research/drafts/EndBlockLeaf.lean` as the base, add the block-decomposition (maximal nonseparable sets) and the directed ear existence under the provable hypotheses (DirectedEarDecomp found the general theorem false; it's the restricted one that matters). The repo already has `TrueSREarCase1/2` and `SignDirected` machinery.

2. **Exact counterexample search for `no_offCycle_negFlux`** — finish the OffCycleNegFluxSearch script. A machine-checked counterexample would be a decisive finding (the route is dead); a certified negative in the searched range would narrow the space. The script's self-test already passed.

3. **Normal-fan family for Hole A** (if anyone insists) — the infrastructure exists (`HasDualFGCells`, `coneDual`, `exposedFace_antitone`, face induction). The gap is precisely the packaging of the dominance relation as a family. But the paper does not prove it exists — this is Theorem B + the missing Step 4.

---

**Session end:** 2026-10-10  
**Branch:** `resolve-holes` (pushed to origin)  
**Worktree:** `/Users/akutuva/Documents/Proofs/crnt-lean/tmp/holes-resolve` (clean, toolchain fixed, builds)
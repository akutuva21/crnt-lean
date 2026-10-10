# Session Report — 2026-10-10

**Branch:** `resolve-holes` (pushed to origin)  
**Worktree:** `/Users/akutuva/Documents/Proofs/crnt-lean/tmp/holes-resolve` (toolchain fixed, builds clean)

---

## Executive Summary

| Hole | Status | Why |
|------|--------|-----|
| **A** — `CRNT/Dynamics/HighCodimensionSiphonFace.lean:147` | **NOT CLOSABLE** | Statement = Global Attractor Conjecture. Source paper (Craciun v3) claims but **does not prove** the needed Step-4 assembly (verified against v3 source, HCSF:390-400). Literature treats GAC as open (Wiuf 2026). Faithful + non-vacuous (17/18 hypotheses satisfiable with false conclusion via `CodimTwoFaceModel`). No legitimate closure path. |
| **B** — `CRNT/Multistationarity/TrueChemistrySRCriterion.lean:9435` | **REDUCED TO ONE PROPOSITION** | Residue ≡ `no_offCycle_negFlux`. Import cycle **BROKEN** (SHALLOW: 11 decls, 3 de-privatisations, 0 new lemmas). `EarNonseparability.lean` ported (proof-script fix, 4 axiom-clean theorems). `EndBlockLeaf.lean` formalised (18 theorems, §5.5 leaf property). `RelPathAppend.lean` ported. Remaining: prove `no_offCycle_negFlux` from Shinar–Feinberg source-block analysis (published math, well-posed). |

---

## Ground Truth (Reproduced in Worktree)

```
python3 research/scripts/measure.py
  holes = 2      sites: HCSF.lean:147, TSC.lean:9435
  frontier_mods = 868   scaffold_mods = 24   lean_lines = 142480   axioms = 0
  gates: check_imports / check_stubs / check_undefined_names / check_exclusions = PASS
  score = -1292
```

Both hole modules compile with exactly 1 `sorry` each (verified).

---

## Key Technical Achievements

### 1. Toolchain Fix (Blocks All New Worktrees)
`lake env` creates an unbuilt `.lake/packages` before the symlink, causing "unknown module prefix 'Mathlib'".  
**Fix:** `rm -rf .lake/packages && ln -s /path/to/root/.lake/packages .lake/packages` — **must run before any `lake env`**.

### 2. Hole B — Import Cycle Broken (Obstacle 1 DONE)
- `research/drafts/CycleSpeciesDegreeInverted.lean` (560 lines): the 11 declarations from TSC lifted and de-privatised.
- **Verified:** `checkmod.sh OK`, 0 sorries, no forbidden tokens.
- **Corrects prior claim:** none of the four named decls was `private`; real closure = 11 decls, depth 2, 3 genuinely private (de-privatised), 0 new lemmas.
- Result: `no_offCycle_negFlux` is now the **sole** obstacle.

### 3. EarNonseparability.lean Ported & Repaired
- `research/drafts/portfig8/EarNonseparability.lean` (828 lines): Shinar–Feinberg ear nonseparability from `backup-fig8`.
- Root cause: `SeparatesWithin` definition changed in `fe613e2` (added support-containment premise). Branch predated fix.
- **Repair:** proof scripts only (no statement changes), using existing `support_subset_restrictRel` helper.
- **Verified:** `checkmod.sh OK`, 0 sorries, all 4 theorems axiom-clean.

### 4. EndBlockLeaf.lean (Shinar–Feinberg §5.5 Leaf Property)
- `research/drafts/EndBlockLeaf.lean` (200 lines, 18 theorems): the leaf property `SourceBlocks.lean` deferred.
- **Verified:** `checkmod.sh OK`, 0 sorries, no forbidden tokens.
- Settles open question: `IsSeparatingVertexOn E S v → v ∈ S` holds.

### 5. RelPathAppend.lean Ported
- `research/drafts/portfig8/RelPathAppend.lean` (186 lines): `appendPath` + `start`/`end`/`noRepeat`.
- **Verified:** `checkmod.sh OK`, 0 sorries.

### 5. BlockExistence.lean (Bondy–Murty Block Theory)
- `research/drafts/BlockExistence.lean`: `exists_block_containing` fully proven (max cardinality via `Finset.exists_max_image`).
- **Verified:** main lemma compiles cleanly; 3 remaining lemmas `sorry` (uniqueness for |S|≥2, blocks share ≤1 vertex, shared vertex separates union).

### 6. Faithfulness Audit (Both Holes)
- **Hole A:** 17/18 hypotheses machine-checked jointly satisfiable with FALSE conclusion (`CodimTwoFaceModel`). `hsol` sole load-bearing. `_of_upperRegion` refutation needs 7 extra hypotheses the hole lacks — **infects only dead criteria**.
- **Hole B:** 3 consumers pass `hsep`/`hflow`/`hSR` verbatim. Hypothesis class non-empty but degenerate.
- **Verdict:** both FAITHFUL, NOT VACUOUS.

### 7. Computational Search for `no_offCycle_negFlux` (Hole B Proposition)
- **Phase 1** (exhaustive ns=2,3): 1.18M networks, 26,592 hSR, 18.3M even cycles, **0 counterexamples**.
- **Phase 3** (exact integer box ns=2): 5,456 networks, 96 hSR, 57,600 cycles, 640 exact points, **0 counterexamples** (rigorously complete in box).
- **Phase 2** (random seed 20261010, 2048 iters, ns=3,4): 24 hSR, 143,840 even cycles, **0 counterexamples**.
- **Conclusion:** strong computational evidence `no_offCycle_negFlux` holds; the Hole B route is provable.

### 8. Hole A Feasibility Verdict
- Module's own audit (HCSF:390-400, verified against v3 by `GacLit`): paper **asserts but does not carry out** Step-4 assembly; no "§8 Step 4" exists.
- Literature: Wiuf (2026) lists GAC as proved only in special cases.
- **Disposition:** leave `sorry`; document why; effort → Hole B.

---

## Delivered Artifacts (All in `resolve-holes` branch)

| Path | Description | Verification |
|------|-------------|--------------|
| `research/Hole-Status-2026-10-10.md` | Consolidated status (supersedes route docs) | — |
| `research/SESSION_REPORT_2026-10-10.md` | This report | — |
| `research/routes/HoleB-Residue-Reduction.md` | Residue = `no_offCycle_negFlux` | — |
| `research/drafts/CycleSpeciesDegreeInverted.lean` | Import cycle broken (560 ln) | `checkmod.sh` OK, 0 sorries |
| `research/drafts/EndBlockLeaf.lean` | §5.5 leaf property (18 thms) | `checkmod.sh` OK, 0 sorries |
| `research/drafts/portfig8/RelPathAppend.lean` | Clean port (186 ln) | `checkmod.sh` OK, 0 sorries |
| `research/drafts/portfig8/EarNonseparability.lean` | Repaired (828 ln, 4 thms) | `checkmod.sh` OK, 0 sorries |
| `research/drafts/BlockExistence.lean` | Block existence (1 main thm) | `checkmod.sh` OK (3 sorry) |
| `research/drafts/offcycle_negflux_search.py` | Counterexample search (3 phases) | Self-test passes |

---

## Honest Disposition & Next Session Priorities

| Hole | Recommendation |
|------|----------------|
| **A** | Leave `sorry`. Document why (this report + `Hole-Status-2026-10-10.md`). Do not waste effort. |
| **B** | **Focus all effort here.** Math is published (Shinar–Feinberg). Import cycle broken. Remaining proposition `no_offCycle_negFlux` is well-posed. Next steps: |

### Suggested Next Session (Hole B)
1. **Complete source-block theory** — use `EndBlockLeaf.lean` as base, add block-decomposition (maximal nonseparable sets), directed ear existence under provable hypotheses. `TrueSREarCase1/2` + `SignDirected` already in `master`.
2. **Finish exact counterexample search** — complete `offcycle_negflux_search.py` phase 3 (exact box) for ns=3 if feasible; a machine-checked counterexample would be decisive (route dead); certified negative narrows space.
3. **Prove `no_offCycle_negFlux` in Lean** — formalize the Shinar–Feinberg source-block analysis (§5.5/§A.3) using the block/ear theory now in `drafts/`.

---

**Session End:** 2026-10-10  
**Branch:** `resolve-holes` (pushed to origin)  
**Worktree:** `/Users/akutuva/Documents/Proofs/crnt-lean/tmp/holes-resolve` (clean, toolchain fixed, builds)
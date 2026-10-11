# HANDOFF — true-SR hole (Hole B) CLOSED, session of 2026-10-10

Target: `CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion` in
`CRNT/Multistationarity/TrueChemistrySRCriterion.lean`.

**Status: closed.**  The statement is unchanged:

```lean
theorem stronglyConcordant_fullyOpen_of_trueSRCriterion
    (N : Network S) (hsep : N.ReactantProductSeparated)
    (hflow : N.ZeroComplexReactionsAreFlows)
    (hSR : N.TrueSRStrongCriterion) :
    N.fullyOpen.StronglyConcordant
```

`#print axioms` on it and on `stronglyConcordant_of_trueSRCriterion_of_weaklyNormal`,
`stronglyConcordant_of_trueSRCriterion_of_weaklyReversible` and `injective_of_trueSRCriterion`
reports `[propext, Classical.choice, Quot.sound]`.  `scripts/dump_sorries.py` reports **1** sorry
(Hole A, `HighCodimensionSiphonFace.lean`).

## Route: Banaji–Craciun determinant argument, not Shinar–Feinberg sign causality

The previous proof body (≈ 725 lines of sign-causality case analysis) ended in a residue that the
in-scope hypotheses could not exclude (DEAD-ENDS B-39, B-40).  It was replaced by a one-line call to
`stronglyConcordant_fullyOpen_of_trueSRCriterion_bc`.  The old body is not in the tree any more; the
lemmas it used are still there and still build.

Mathematics, in order:

1. **Reduction** (`det_bcProduct_eq_zero_of_witness`).  Let `A = [Γ | I] : Matrix S (N.R ⊕ S) ℝ`.
   A strong-concordance witness `(α, σ)` of `N.fullyOpen` gives weights `w ≥ 0` with
   `w (inr t) _ = d t > 0` and `(A * B) σ = 0`, `B k t = w k t * A t k`.  The outflow clauses force
   `sign α_out(s) = sign σ s` exactly (`outflow_sign`), the inflow clauses give the same sign or zero
   (`inflow_sign`), so the net outflow is `d s * σ s` with `d > 0` (`flowDiag`).  Each internal
   `α r ≠ 0` is witnessed by one species `s₀` with `0 < α r / (dir r s₀ * σ s₀)`, which defines
   `w r ·` (`chanWeight`, `sum_chanWeight`).  The zero-rate clause is never needed for internal
   channels.
2. **Column expansion** (`DetCycle.det_mul_eq_sum_columns`).
   `det (A * B) = ∑ f : S → K, (∏ t, B (f t) t) * det (A.submatrix id f)`, from
   `MultilinearMap.map_sum` and `map_smul_univ` on the rows of the transpose.  With
   `B k t = w k t * A t k` every term is a nonnegative monomial times
   `(∏ t, G t t) * det G`, `G = A.submatrix id f`; the term `f = inr` equals `∏ d > 0`
   (`det_mul_pos_of_coeff_nonneg`, `det_bcProduct_pos`).
3. **Coefficients** (`bc_coeff_nonneg`).  Zero diagonal ⇒ coefficient 0.  Two columns from one
   true-reaction class ⇒ proportional columns ⇒ `det G = 0` (`det_bcG_eq_zero_of_sameClass`).
   Otherwise normalize to `H = G · diag(1/G_tt)`; `(∏ G_tt) det G = (∏ G_tt)² det H`.
4. **Cancellation lemma** (`DetCycle.det_nonneg_of_negCycles`, pure algebra).  Unit diagonal,
   every negative cycle of weight exactly `−1`, distinct negative cycles disjoint ⇒ `0 ≤ det H`.
   Sign-reversing involution on `Perm ι` toggling the least negative cycle disjoint from the
   nonnegative cycle factors (`toggle`, `admissible`, `Finset.sum_involution`).
5. **Bridge** (`BCCycleBridge`).  A cyclic permutation of nonzero `H`-weight uses only internal
   channels (identity columns and, by `hflow`, singleton flows cannot carry a cycle).  It becomes a
   `TrueSRCycle` (`CycleChannels.toCycle`: species `c^j x₀`, reaction the class of `f` at species
   `j`).  `signed_weight_eq`: weight `= -(-1)^numCPairs · ∏ right labels / ∏ left labels` under
   `hsep`.  Hence negative ⇒ even, and even + s-cycle (`hSR.1`) ⇒ weight `−1`.
6. **Condition (ii)** (`BCIntersection`, `BCIntersectionCert`).  Two distinct cycles `c ≠ d` with
   one channel assignment that share a species have an S-to-R intersection: every shared species
   carries the same left edge, so each common component runs from an *entry* species `z`
   (`c⁻¹ z ≠ d⁻¹ z`) forward along `c` while `c = d`, ending at a reaction.  The full
   `TrueSRCycle.SToRIntersection` certificate is built, all twelve fields
   (`CyclePair.sToRIntersection`).  With `hSR.2` this gives the disjointness hypothesis of step 4.

Reference: M. Banaji, G. Craciun, *Graph-theoretic approaches to injectivity and multiple equilibria
in systems of interacting elements*, Commun. Math. Sci. 7 (2009) 867–900.  The argument there is the
`P₀`-matrix statement; here it is specialized to `det(D + ΓW) > 0`, which is all the fully open
extension needs.

## Files

| file | content |
| --- | --- |
| `CRNT/Multistationarity/BCDetCycleCancellation.lean` | step 4 (Mathlib only) |
| `CRNT/Multistationarity/BCColumnExpansion.lean` | step 2 (Mathlib only) |
| `CRNT/Multistationarity/BCCycleBridge.lean` | step 5 |
| `CRNT/Multistationarity/BCIntersection.lean` | step 6, cycle-level facts (entries, first disagreement `M`, backward walk) |
| `CRNT/Multistationarity/BCIntersectionCert.lean` | step 6, the certificate |
| `CRNT/Multistationarity/BCFullyOpen.lean` | steps 1–3 and `stronglyConcordant_fullyOpen_of_trueSRCriterion_bc` |
| `test/BanajiCraciunAudit.lean` | 10 `#guard_msgs` pins, clean axiom set; builds in about a minute |

`FlowsAreSingletons` in `BCFullyOpen.lean` is the body of `ZeroComplexReactionsAreFlows`, inlined
because the latter is defined inside `TrueChemistrySRCriterion.lean`; the two are definitionally
equal and the main theorem passes `hflow` straight through.

## Reconciliation done in this commit

* `TrueChemistrySRCriterion.lean` imports `BCFullyOpen`; body replaced.
* `CRNT.lean` now imports `CRNT.Multistationarity.TrueChemistrySRCriterion` (the module is
  sorry-free, so it graduates into the default import).  **This is a decision, revert it if you
  disagree**; nothing else depends on it.
* `test/AxiomAudit.lean`: two stale `sorryAx` expectations updated to clean, two pins added; the
  file passes.
* `test/FrontierAuditCurrent.lean`: true-SR section moved to "closed", three clean pins; passes.
* `scripts/stub_baseline.txt` regenerated (1 entry); `research/Audit/known_holes.txt` lists only
  `HighCodimensionSiphonFace`; `research/Audit/orphan_baseline.txt` lowered from 145 to 126.
* Prose in `HighCodimensionSiphonFace.lean` (trust status), `research/README.md`, `BRIEF-B.md`.

## Verification performed (offline driver `scripts/offline_build.py`, Lean 4.34.0, Mathlib v4.34.0)

* `CRNT` — all **751** modules, zero failures.
* `CRNTFrontier` — all **525** modules, zero failures.
* `test/AxiomAudit.lean`, `test/FrontierAuditCurrent.lean`, `test/BanajiCraciunAudit.lean` pass.
* `check_exclusions.py`, `check_stubs.py`, `research/Audit/ledger_coverage.py`, `check_imports.py`
  pass.

Pre-existing: before this change `ledger_coverage.py` already failed on the orphan count (168 > 145);
it passes now because the graduation lowers the count to 126.

## Environment notes for the next session

* The quota is about 19 GB.  Pruned safely: `*.ilean`, toolchain `*.a`, `libLLVM`, `libclang-cpp`,
  AppleDouble `._*`.  **Do not delete the toolchain's `lib/lean/Lake*`**: `Mathlib.Tactic`
  transitively imports `Lake.Util.Casing` (`TrueSRFirstHop` failed until it was restored).
* Background processes started with `setsid nohup` are killed unpredictably; run builds in the
  foreground under `timeout 290` and rerun (the driver is incremental).

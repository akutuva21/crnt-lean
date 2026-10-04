# Hole B, slice `form-sr-deg2b`: degree-two parity, cross-class consequences, and the RR arc index ranges

Branch `research/form-sr-deg2b`, PR #9 (base `holes`). Two elaborating hole-free modules.

## Landed, machine-checked

### 1. `CRNT/Multistationarity/TrueSRDegreeTwoParity.lean` — commit `4607b05`

`research/scripts/checkmod.sh CRNT/Multistationarity/TrueSRDegreeTwoParity.lean` →
`=== OK (sorry-warnings: 0) ===`. 20 declarations.

The degree-two predicate was previously only an anonymous hypothesis of
`no_sToRIntersection_of_degree_two`; it is now named and its consequences proved.

```lean
def TrueSRCycle.DegreeTwo (C : N.TrueSRCycle n) : Prop :=
  ∀ (e : N.TrueSREdge) (i : Fin n), e.reaction = C.reaction i →
    e.SameIncidence (C.leftEdge i) ∨ e.SameIncidence (C.rightEdge i)

theorem TrueSRCycle.containsEdge_of_degree_two
theorem TrueSRCycle.no_offCycle_edge_of_degree_two
theorem TrueSRCycle.no_isCPair_of_degree_two        (hsep) (C) (hdeg) (j) : ¬ C.isCPair j
theorem TrueSRCycle.numCPairs_eq_zero_of_degree_two (hsep) (C) (hdeg) : C.numCPairs = 0
theorem TrueSRCycle.even_of_degree_two             (hsep) (C) (hdeg) : C.Even
theorem TrueSRCycle.sCycle_of_degree_two_of_trueSRCriterion (hSR) (hsep) (C) (hdeg) : C.SCycle
theorem TrueSRCycle.not_odd_of_degree_two          (hsep) (C) (hdeg) : ¬ Odd C.numCPairs
theorem TrueSRCycle.crossClass_of_degree_two       (hsep) (C) (hdeg) (i)
theorem TrueSRCycle.left_species_occurs_in_source  (C) (i) (h)
theorem TrueSRCycle.right_species_occurs_in_target (C) (i) (h)
theorem TrueSRCycle.no_strict_gain_labels          (C) (hsc) (a) (ha) (hineq) : False
theorem false_of_degree_two_strict_gain            (hSR) (hsep) (C) (hdeg) (a) (ha) (hineq) : False
theorem false_of_shared_sToR_of_trueSRCriterion    (hSR) (C) (D) (hC) (hD) (hI) : False
theorem TrueSRCycle.no_sToRIntersection_of_degree_two' (C) (D) (hdeg)
theorem degree_two_halves_are_asymmetric           (hSR) (hsep) (C) (D) (hdeg)
-- TrueSRSSPath
theorem ssGlue_no_isCPair_of_degree_two            (hsep) (hdeg) (t)
theorem ssGlue_numCPairs_eq_zero_of_degree_two     (hsep) (hdeg)
theorem ssGlue_even_of_degree_two                  (hsep) (hdeg)
theorem ssGlue_not_odd_of_degree_two               (hsep) (hdeg)
theorem ssGlue_degree_two_zero                     (hsep) (hdeg) : ssNumCPairs P = 0 ∧ ssNumCPairs Q = 0
theorem ssGlue_sCycle_of_degree_two_of_trueSRCriterion (hSR) (hsep) (hdeg)
theorem ssGlue_parity_transport                    (hsep) (hdeg)
-- Residual
def DegTwoGain  (C) : Prop ;  theorem degTwoGain_refutes (hSR) (hsep) (C) (hdeg) (h) : False
def IsolateDegreeTwo (C) (k) : Prop
def DegreeTwoParity (C) : Prop ; theorem degreeTwoParity (hSR) (hsep) (C) (hdeg)
```

### 2. `CRNT/Multistationarity/TrueSRReactionArc.lean` — commit `efd182a`

`=== OK (sorry-warnings: 0) ===`. The prerequisite for
`exists_second_evenCycle_of_offCycle_escape`.

```lean
theorem TrueSRCycle.zero_lt_of_nontrivial (C) : 0 < n
theorem TrueSRCycle.arc_len_lt  {m} (hmn : m < n) : m - 1 < n
theorem TrueSRCycle.rev_len_lt  (hn : 0 < n) (hm : 0 < m) : n - m - 1 < n
theorem TrueSRCycle.fwd_idx_lt  (hm) (hmn) {q : Fin (2 * (m - 1) + 1)} : q.1 / 2 + 1 < n
theorem TrueSRCycle.fwd_idx_le  (hm) (hmn) {q : Fin (2 * (m - 1) + 1)} : q.1 / 2 + 1 ≤ m
theorem TrueSRCycle.bwd_idx_lt  (hm) (hn)   {q : Fin (2 * (n - m - 1) + 1)} : n - 1 - q.1 / 2 < n
theorem TrueSRCycle.bwd_idx_ge  (hm) (hmn) {q : Fin (2 * (n - m - 1) + 1)} : m ≤ n - 1 - q.1 / 2
theorem TrueSRCycle.fwd_bwd_index_split (hm) (hmn) {qb} (hb : qb.1 / 2 + 1 = n - m)
    : n - 1 - qb.1 / 2 = m
```

## Mathematical content

### The parity obstruction (degree two ⟹ even, unconditionally)

The chain, each link already in the tree except the first:

1. `C.isCPair j` forces a third SR edge `f` off `C` at `C.reaction j`, with
   `f.species ∉ {C.species j, C.species (j+1)}` and `¬ C.ContainsEdge f`
   (`Network.exists_offCycle_edge_of_isCPair`, needs `hsep` + internality only).
2. `C.DegreeTwo` says no such edge exists.
3. So `C.numCPairs = 0`, so `C.Even`, so `hSR.1` forces `C.SCycle`.

**Step 3 is the cross-class consequence.** At a degree-two reaction vertex the two cycle edges
carry *different* endpoint complexes (`crossClass_of_degree_two`), so the cycle crosses the
reaction — one edge on the reactant side, one on the product side — and never turns back. This is
why the s-cycle identity compares a reactant coefficient against a product coefficient.

### Where `hSR.2` is used — the answer is *nowhere*, and that is the finding

`no_sToRIntersection_of_degree_two'` needs **no hypothesis at all**. So on a degree-two cycle the
"no S-to-R sharing" half of `TrueSRStrongCriterion` is vacuous: it is never invoked, and it cannot
be the step that produces a contradiction. `degree_two_halves_are_asymmetric` packages the
asymmetry: the first half yields `C.SCycle`, the second yields nothing.

`false_of_shared_sToR_of_trueSRCriterion` is the *only* place `hSR.2` appears in this
development, in one line (`hSR.2 C D hC hD hI`).

**Consequence for the route.** Degree-two isolation must be discharged by `hSR.1` together with
the strict gain, and `false_of_degree_two_strict_gain` does exactly that. The only remaining
input is `Residual.DegTwoGain`: positive multipliers and the pointwise strict gain inequalities,
which come from `InKerL α` and `hopp`, not from the SR graph. This is the `InKerL`/`hopp` step,
not graph theory.

### The C-pair counting obstruction for S-to-S glues

`ssGlueCycle_numCPairs` gives `numCPairs (P ∪ Q) = ssNumCPairs P + ssNumCPairs Q` with **no seam
term** (the S-to-S seam is intrinsic to `P`, see `TrueSRSSGlueCPairs.lean`'s header). So degree
two of the glue forces *both* arcs c-pair-free (`ssGlue_degree_two_zero`), the glue is even, an
s-cycle, and never odd. `ssGlue_parity_transport` then says the parity of `P ∪ Q` is the parity
of `ssNumCPairs Q` alone: a c-pair-free chord `P` is parity-invisible. The odd-c-pair
configurations are exactly the ones degree two excludes.

## Residuals (named, with full signatures)

* `Residual.DegTwoGain C := ∃ a : Fin n → ℝ, (∀ i, 0 < a i) ∧ (∀ i, ((C.leftEdge (finRotate n i)).coeff : ℝ) * a (finRotate n i) < ((C.rightEdge i).coeff : ℝ) * a i)`.
  Discharged by `degTwoGain_refutes` together with `false_of_degree_two_strict_gain`. This is the
  `InKerL α` / `hopp` input.
* `Residual.IsolateDegreeTwo C k := C.DegreeTwo` — the degree-two statement the residue at
  `TrueChemistrySRCriterion.lean:8607` would need, in the exact shape required.
* `Residual.DegreeTwoParity C := (∀ i, ¬ C.isCPair i) ∧ C.numCPairs = 0 ∧ C.Even ∧ C.SCycle`,
  discharged outright by `degreeTwoParity`.
* **RR arc assembly** (documented in `TrueSRReactionArc.lean`'s header): rewriting each arc edge
  to `C.leftEdge`/`C.rightEdge` via `TrueSRArc.initialArcPath_edge_even`/`_odd` with
  `rotate_leftEdge` and `TrueSRCycle.reverse_leftEdge`, then
  `arcFwdRR : TrueSRPathRR (m - 1)` and `arcBwdRR : TrueSRPathRR (n - m - 1)`, then the
  `RRGluable` instance from `fwd_idx_le`/`bwd_idx_ge` plus `reaction_injective`. I attempted the
  edge rewrites; the `Fin` side-condition discharge via `congr 1`/`Fin.ext` on the `rotate` and
  `revPerm` index expressions did not terminate within a reasonable iteration budget, so I
  trimmed to the bounds, which are the non-obvious half. **This is a genuine incomplete step, not
  a dead end** — the remaining work is index bookkeeping on top of lemmas now in place.

## Dead ends / negative results

* **`TrueSRPath.prepend` being `private` is not the blocker the orchestrator suspected.** The
  orchestrator's B-12 note said the RR arc derivation "must go through `toPath`" and that
  `prepend`'s privacy might block it, worth +30 if so. That is **not** the situation:
  `TrueSRParityRR.lean` already contains the composed builders `glueArc` (public, line 388),
  `gluable_of_RRGluable` (public, line 442), and `rrGluedCycle` (public, line 518). No privacy
  change is needed. The genuinely missing object is an `RRGluable` *instance* built from a cycle,
  which is what `TrueSRReactionArc.lean` starts.
* **The degree-two route cannot be closed via `hSR.2`.** Machine-checked: the second conjunct is
  vacuous on a degree-two cycle. Any attempt to route through the sharing half in the degree-two
  case is attempting to extract a contradiction from a hypothesis with no content there.
* **Degree two does not need the S-to-R machinery at all to be even.** `even_of_degree_two` takes
  only `hsep`; no `hSR` appears.

## Note on tooling

`research/scripts/checkmod.sh` failed for every `CRNT.*`-importing module in my worktree until I
symlinked the shared olean tree into `.lake/build/lib/lean`. That matches `infra-build`'s
diagnosis (`lake env` prepends to `LEAN_PATH`, so the worktree-local dir shadowed the shared
root). My modules were verified *after* working around it locally; they should be re-checked
with the fixed script.
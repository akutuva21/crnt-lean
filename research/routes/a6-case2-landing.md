# A.6 Case 2 — locating, porting, and assessing the "source-block datum"

**Author:** `form-sr-case2` · **Branch:** `research/form-sr-case2` · **Target:** Hole B,
`CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8607`
(`Network.stronglyConcordant_fullyOpen_of_trueSRCriterion`).

---

## 0. Summary

The five "arrangement theorems" the round-1 brief asked me to thread exist only on the
**unmerged** branch `backup-fig8` (commit `637a970`). `git merge-base --is-ancestor backup-fig8
holes` → **false**: the branch was `reset: moving to ef8048c` and never merged (this is
orchestrator finding B-9). I re-authored a self-contained port of the four declarations that
Case 2 actually *consumes* into a fresh `CRNT/Multistationarity/TrueSREarCase2.lean` on my
branch; it does **not** import `CRNT.Multistationarity.TrueSREarCase1` or
`CRNT.Multistationarity.TrueChemistrySRCriterion` (orchestrator finding B-12), so its axiom
footprint stays clean of the file under repair.

**The five arrangement theorems cannot be threaded, and the reason is structural, not a matter
of finding the right lemma.** They are `False`-*consumers*, and three of their inputs have no
producer anywhere in this repository. §4 gives the precise blocker; §5 gives the minimal
restructuring.

---

## 1. Where the five theorems live

```
git log --oneline backup-fig8 -5
637a970 feat: Lemma A.6 Case 2 — five arrangement theorems (six Fig.8 drawings) feeding hSR
0880aca feat: Case 2 machinery — HasEdge predicates, SignDirected, glued-cycle ContainsEdge iffs …
886e1f0 merge: bring in SrEarTheory A.3 foundations + Case 1 for Case 2 work
4fd4ff2 feat: public liftRelPathToTrueSRPathRev wrappers over the private reversal lift
08e47eb feat: Lemma A.6 Case 1 — S-to-R pair construction from a fresh directed ear
36334e1 feat: restrictRel, IsDirectedCycleOn and nonseparable-stage propagation (A.3 foundations)
c9911d9 feat: RelPath.appendPath — glued directed paths with vertex/end/no-repeat lemmas

git merge-base backup-fig8 holes   #= ef8048c
git merge-base --is-ancestor backup-fig8 holes   #= exit 1  (NOT merged)
git log --oneline ef8048c..backup-fig8            # 7 commits, all unmerged
```

The five entry points, in `CRNT/Multistationarity/TrueSREarCase2.lean` on `backup-fig8`:

| Lean name | Fig. 8 order after `R_O` | closed pair | common edges |
|---|---|---|---|
| `lemmaA6_case2_arrangement1` | `R_I, S_O, S_I` | `C ∪ q`, `P ∪ v` | `arc(R_I,S_O) ∪ arc(S_I,R_O)` |
| `lemmaA6_case2_arrangement2` | `R_I, S_I, S_O` | `C ∪ q`, `P ∪ u` | `arc(R_I,S_I) ∪ arc(S_O,R_O)` |
| `lemmaA6_case2_interleaved`  | `S_O, R_I, S_I` / `S_I, R_I, S_O` | `C ∪ q`, `P ∪ v` | one piece |
| `lemmaA6_case2_arrangement4` | `S_O, S_I, R_I` | `C ∪ p`, `P ∪ v` | `arc(R_O,S_O) ∪ arc(S_I,R_I)` |
| `lemmaA6_case2_arrangement6` | `S_I, S_O, R_I` | `C ∪ p`, `P ∪ u` | `arc(R_O,S_I) ∪ arc(S_O,R_I)` |

Representative signature (`lemmaA6_case2_arrangement1`, verbatim):

```lean
theorem lemmaA6_case2_arrangement1 (N : Network S) (hSR : N.TrueSRStrongCriterion)
    {a b c d L₁ L₂ : ℕ} (σ : S → ℝ)
    (C : N.TrueSRPathRR a) (q : N.TrueSRPathRR b)
    (P : N.TrueSRSSPath (2 * c + 2)) (v : N.TrueSRSSPath (2 * d + 2))
    (c₁ : N.TrueSRPath L₁) (c₂ : N.TrueSRPath L₂)
    (hCq : RRGluable C q) (hPv : SSGluable P v)
    (harr : ∀ e : N.TrueSREdge, q.HasEdge e ∧ v.HasEdge e ↔
      (c₁.HasEdge e ∨ c₂.HasEdge e))
    (hCP : ∀ k l, ¬ (C.edgeAt k).SameIncidence (P.edge l))
    (hCv : ∀ k l, ¬ (C.edgeAt k).SameIncidence (v.edge l))
    (hqP : ∀ k l, ¬ (q.edgeAt k).SameIncidence (P.edge l))
    (hsep : ∀ i j, ¬ (c₁.edge i).ShareVertex (c₂.edge j))
    (hX : (rrGluedCycle C q hCq).SignDirected σ)
    (hY : (ssGlueCycle P v hPv).SignDirected σ) :
    False
```

---

## 2. What I landed: the four consumers, re-authored from scratch

New file **`CRNT/Multistationarity/TrueSREarCase2.lean`** (429 lines), imports
`TrueSRParityRR`, `TrueSRPath`, `TrueSRSSGlueCPairs` only.

```lean
def TrueSRCycle.SignDirected {n : ℕ} (C : N.TrueSRCycle n) (σ : S → ℝ) : Prop :=
  (∀ i, σ (C.species i) ≠ 0) ∧
    (∀ i, C.isCPair i ↔ σ (C.species i) * σ (C.species (finRotate n i)) < 0)

theorem TrueSRCycle.even_of_signDirected {n : ℕ} (C : N.TrueSRCycle n) {σ : S → ℝ}
    (h : C.SignDirected σ) : C.Even

def TrueSRPath.HasEdge    {L : ℕ} (P : N.TrueSRPath L)    (e : N.TrueSREdge) : Prop :=
  ∃ k : Fin L, e.SameIncidence (P.edge k)
def TrueSRSSPath.HasEdge  {L : ℕ} (P : N.TrueSRSSPath L)  (e : N.TrueSREdge) : Prop :=
  ∃ k : Fin L, e.SameIncidence (P.edge k)
def TrueSRPathRR.HasEdge  {j : ℕ} (A : N.TrueSRPathRR j)  (e : N.TrueSREdge) : Prop :=
  ∃ k : Fin (2 * j + 2), e.SameIncidence (A.edgeAt k)

noncomputable def TrueSRCycle.sToRIntersectionOfTwoPaths {m n L₁ L₂ : ℕ}
    (C : N.TrueSRCycle m) (D : N.TrueSRCycle n)
    (c₁ : N.TrueSRPath L₁) (c₂ : N.TrueSRPath L₂)
    (h₁C : ∀ i, C.ContainsEdge (c₁.edge i)) (h₁D : ∀ i, D.ContainsEdge (c₁.edge i))
    (h₂C : ∀ i, C.ContainsEdge (c₂.edge i)) (h₂D : ∀ i, D.ContainsEdge (c₂.edge i))
    (hcov : ∀ f : N.TrueSREdge, C.ContainsEdge f → D.ContainsEdge f →
      c₁.HasEdge f ∨ c₂.HasEdge f)
    (hsep : ∀ i j, ¬ (c₁.edge i).ShareVertex (c₂.edge j)) :
    C.SToRIntersection D

theorem lemmaA6_case2_twoComponents (N : Network S) (hSR : N.TrueSRStrongCriterion)
    {m n L₁ L₂ : ℕ} (X : N.TrueSRCycle m) (Y : N.TrueSRCycle n)
    (c₁ : N.TrueSRPath L₁) (c₂ : N.TrueSRPath L₂)
    (CE QE PE VE : N.TrueSREdge → Prop)
    (hXE : X.Even) (hYE : Y.Even)
    (hdecX : ∀ e, X.ContainsEdge e ↔ (CE e ∨ QE e))
    (hdecY : ∀ e, Y.ContainsEdge e ↔ (PE e ∨ VE e))
    (hCP : ∀ e, ¬ (CE e ∧ PE e))
    (hCV : ∀ e, ¬ (CE e ∧ VE e))
    (hQP : ∀ e, ¬ (QE e ∧ PE e))
    (harr : ∀ e, QE e ∧ VE e ↔ (c₁.HasEdge e ∨ c₂.HasEdge e))
    (hsep : ∀ i j, ¬ (c₁.edge i).ShareVertex (c₂.edge j)) : False

theorem lemmaA6_case2_oneComponent (N : Network S) (hSR : N.TrueSRStrongCriterion)
    {m n L : ℕ} (X : N.TrueSRCycle m) (Y : N.TrueSRCycle n) (c₁ : N.TrueSRPath L)
    (CE QE PE VE : N.TrueSREdge → Prop)
    (hXE : X.Even) (hYE : Y.Even)
    (hdecX : ∀ e, X.ContainsEdge e ↔ (CE e ∨ QE e))
    (hdecY : ∀ e, Y.ContainsEdge e ↔ (PE e ∨ VE e))
    (hCP : ∀ e, ¬ (CE e ∧ PE e))
    (hCV : ∀ e, ¬ (CE e ∧ VE e))
    (hQP : ∀ e, ¬ (QE e ∧ PE e))
    (harr : ∀ e, QE e ∧ VE e ↔ c₁.HasEdge e) : False
```

Re-elaborated from scratch rather than copied (B-12): the sign-change counting lemma
`cyclic_sign_changes_even` and its two helpers `prod_pm_one_eq_neg_one_pow_card_neg`,
`even_card_neg_of_prod_one` are private in my file, because the in-tree
`N.trueSRCycle_even_of_signChange` (`TrueChemistrySRCriterion.lean:6885`) is itself `private`
and I must not import that module (it would put `sorryAx` in my footprint and couple the port
to the file being repaired).

One deliberate deviation from the branch text: the branch's `sToRIntersectionOfTwoPaths` proves
`componentLength_pos` with `hlen0`/`hlen1` plus `if_pos`/`if_neg`; I replaced it by a single
`hlenpos` that goes through `hcases`. Behaviourally identical, one lemma instead of three.

---

## 3. Where they would have to enter hole B's proof

The `sorry` sits in the residue branch of
`theorem stronglyConcordant_fullyOpen_of_trueSRCriterion` (`…:8607` pre-merge), inside

```
by_cases hnc : ¬ ∃ a b : Fin n, a.1 ≠ b.1 ∧ b.1 ≠ (a.1+1)%n ∧
    N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) ≠ 0
```

goal `False`, with in scope: `C : N.TrueSRCycle n`, `hCeven`, `hSCycleNet`, `hSR`, `hsep`,
`hflow`, `α : N.fullyOpen.R → ℝ`, `σ : S → ℝ`, `T : Finset (TrueInternalAggregateVertex α σ)`,
`q`, `s`, `hattachment`, `htail`, `qC`, and (in the `inl s0` arm) `s0 : AggregateActiveSpecies σ`,
`hv0 : Q0.vertex ⟨0⟩ = Sum.inl s0`, `hs0C : C.HasSpecies s0.1`, `m : ℕ`, `Q0 : RelPath _ T m`,
`hg0`, `hqm`, `hQ0inj`, `hQ0late`, `hm1s : ¬ (m = 1 ∧ s0 = s)`.

The natural entry point would be `lemmaA6_case2_oneComponent N hSR C Y c₁ CE QE PE VE …` at the
`sorry`, with `harr` supplied by the arrangement identity. But the shapes do not line up: the
`sorry` has an aggregate `RelPath Q0` and one `TrueSRCycle C`; it has **no second cycle `Y`**, no
edge predicates `CE/QE/PE/VE`, no `hdecX/hdecY` decompositions, and no `TrueSRPathRR`/`TrueSRSSPath`
ears. This is orchestrator finding B-10, confirmed: `grep -n 'harr\|hdecX\|CE e' …` finds nothing
above line 8607.

---

## 4. Why threading is impossible — the precise blocker

Three of the five theorems' inputs have **no producer anywhere in this repository**.

**(a) There is no constructor for `N.TrueSRPathRR`.** It is a structure
(`TrueSRParityRR.lean:57`) with four fields, three of which are obligations:

```lean
structure TrueSRPathRR (N : Network S) (j : ℕ) where
  first : N.TrueSREdge
  tail : N.TrueSRPath (2 * j + 1)
  first_species : Sum.inl first.species = tail.vertex ⟨0, by omega⟩
  first_ne_tail_edge : ∀ i : Fin (2 * j + 1), ¬ first.SameIncidence (tail.edge i)
  first_ne_tail_vertex : ∀ i : Fin (2 * j + 1 + 1),
    Sum.inr ⟨first.reaction, first.internal⟩ ≠ tail.vertex i
```

Grep evidence:

```
$ grep -rn "TrueSRPathRR" CRNT/ --include=*.lean -l
CRNT/Multistationarity/TrueSREarCase2.lean        (backup-fig8 only)
CRNT/Multistationarity/TrueSRParityRR.lean        (definition site)
CRNT/Multistationarity/TrueChemistrySRCriterion.lean   -- one *comment*, line 5688

$ grep -rn "first_ne_tail_edge\|first_species\|first_ne_tail_vertex" CRNT/ --include=*.lean \
    | grep -v TrueSRParityRR.lean
(nothing)
```

So **nothing in the tree ever builds a `TrueSRPathRR`**. All five arrangement theorems take one
(`C q : N.TrueSRPathRR a`, resp. `C p q`) as their first path argument. Until someone writes the
aggregate lift `RelPath (TrueInternalAggregateCausalEdge) → TrueSRPathRR` (a reaction-to-reaction
causal path has even length `k = 2j+2`, `first` is the step-0 edge witness from
`aggregateSourceAdj_has_trueSREdge`, and `tail` is `relPathToTrueSRPath T (P.tail 1) …` of length
`k-1 = 2j+1`; the three side conditions follow from `P.vertex` injectivity plus the fact that
index `0` carries the start reaction), the five theorems are **unreachable** — there is no term
of the shape they need. This is the single most important structural fact about the Case-2
route.

**(b) `SignDirected σ` has no producer at the `sorry`.** It needs
`∀ i, C.isCPair i ↔ σ (C.species i) * σ (C.species (finRotate n i)) < 0`. The residue has
`hopp`/`hcausal` about `trueInternalClassFlux` and `¬hnc` about cycle-class flux — none of which
says anything about `TrueSRCycle.isCPair`, which is `(C.leftEdge i).endpoint = (C.rightEdge i).endpoint`,
a property of the *concrete* SR edges of the cycle. The only in-tree c-pair/sign-change theorem,
`trueInternalCausalEdges_cPair_iff_signChange` (`TrueChemistrySRCriterion.lean:2458`), is stated
for `trueInternalCausalLeftEdge`/`RightEdge` of a single reaction, not for a general
`TrueSRCycle` glued from arcs.

**(c) The arrangement identity `harr` and the gluability data have no producer.**
`harr : ∀ e, q.HasEdge e ∧ v.HasEdge e ↔ (c₁.HasEdge e ∨ c₂.HasEdge e)` is, per the branch file's
own header, "the *arrangement datum* … Discharging it is the cut-the-cycle-at-the-four-attachments
computation". That computation needs the stage's arc decomposition (`p`, `q` from `R_O`, `u`, `v`
from `S_O`) as `TrueSRPathRR`/`TrueSRSSPath` objects, plus `RRGluable`/`SSGluable` from
`IsDirectedCycleOn`/`DirectedEarDecomposition` instances for the source block. None of those
instances exists: `CRNT/Graph/EarNonseparability.lean` is fully abstract in `V E` and is
instantiated nowhere.

Consequently there is **nothing derivable from hole B's hypotheses** to add as a hypothesis, and
adding an unjustified one would be a fabrication. **I did not thread anything.**

---

## 5. Minimal restructuring that would make it possible

Dependency order, with the currently-missing pieces marked ✗:

1. ✗ **`N.relPathToTrueSRPathRR`** — reaction→reaction lift from an aggregate causal `RelPath`.
   Signature sketch:
   ```lean
   noncomputable def N.relPathToTrueSRPathRR (T : Finset (N.TrueInternalAggregateVertex α σ))
       {k : ℕ} (P : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α:=α) (σ:=σ)) T k)
       (hinj : Function.Injective P.vertex)
       {ρ ρ' : N.ActiveAggregateTrueReaction α σ}
       (h0 : P.vertex ⟨0, by omega⟩ = Sum.inr ρ)
       (hlast : P.vertex ⟨k, by omega⟩ = Sum.inr ρ') : ∃ (j : ℕ), N.TrueSRPathRR j
   ```
   Needs first: **alternation/parity** — `∀ i : Fin (k+1), (∃ ρ, P.vertex i = Sum.inr ρ) ↔
   i.1 % 2 = 0` — so that `k` is even and `j = k/2 - 1`. This parity lemma does not exist in the
   tree either (`grep -rn 'RelPath' CRNT` finds nothing about parity), and it is worth landing on
   its own: it is needed by any route that turns an aggregate path into an arc.
2. ✗ **`RRGluable` / `SSGluable` from a cycle.** `RRGluable` is a structure at
   `TrueSRParityRR.lean:260`; nothing builds one from a `TrueSRCycle`'s two arcs.
3. ✗ **`IsDirectedCycleOn` / `DirectedEarDecomposition` instances** for the aggregate source
   `T` at the residue (`EarNonseparability.lean` has the abstract results
   `directedEar_isNonseparableOn`, `isNonseparableOn_of_directedEarDecomposition`,
   `isNonseparableOn_of_isDirectedCycleOn`, but zero instantiations).
4. ✗ **The `SignDirected σ` bridge** for cycles glued out of arcs.
5. ⇒ then `fresh_rr_ss`, `ssGlueCycle_even_of_partner`, `TrueSRPathRR.rrGluedCycle_containsEdge_iff`,
   `TrueSRSSPath.ssGlueCycle_containsEdge_iff`, and the five `lemmaA6_case2_arrangement*` become
   reachable and can be ported verbatim from `637a970`.

Per orchestrator finding B-1 the ear can never close via `hnd`; it must terminate in `hSR.2`.
`lemmaA6_case2_twoComponents` / `lemmaA6_case2_oneComponent` are exactly the two `hSR.2` exits,
which is why they are the right thing to have landed first.

---

## 6. Dead ends

- **Threading any of the five arrangement theorems into the `sorry`.** Refuted by §4(a): no
  `TrueSRPathRR` value exists in the repository, and nothing at the residue produces the ear data
  the theorems ask for.
- **Cherry-picking `backup-fig8`.** Its 1992-line diff touches `CRNT/Graph/EarNonseparability.lean`,
  `CRNT/Graph/RelPathAppend.lean`, `CRNT/Multistationarity/TrueSREarCase1.lean` — none of which is
  on `holes`, and `TrueSREarCase1` itself imports the unmerged `sr-blocks` (`84e49f2`) and
  `sr-route-ear` (`9285de1`) content. (I did merge the branch locally to *read* it, then reset.)
- **Reusing `N.trueSRCycle_even_of_signChange`.** It is `private` in
  `TrueChemistrySRCriterion.lean:6885`; importing that module would put `sorryAx` in the port's
  axiom footprint and couple it to the file under repair (B-12). Re-proved instead.
- **`lemmaA6_case2_arrangement2` / `..._arrangement6` parity transfers**
  (`ssGlueCycle_even_of_partner`, `rr_three_glued_even_of_two`). `rr_three_glued_even_of_two`
  *is* on `holes` (`TrueSRParityRR.lean`); `ssGlueCycle_even_of_partner` needs
  `ssGlueCycle_numCPairs`, which on `holes` exists only as the `private`
  `ssGlueCycle_numCPairs` at `TrueChemistrySRCriterion.lean:7881`. Another B-12 casualty.

---

## 7. What a next researcher should do

Land item 1 of §5 — `relPathToTrueSRPathRR` together with the aggregate-path **alternation/parity**
lemma. It is self-contained, needs only the existing private
`aggregateSourceAdj_has_trueSREdge` / `relPathAdj` / `relPathToTrueSRPath` helpers inside
`TrueChemistrySRCriterion.lean`, and it is a strict prerequisite for every remaining Case-2 item.
Once it exists, items 2–5 become reachable and the five `lemmaA6_case2_arrangement*` can be
lifted verbatim.
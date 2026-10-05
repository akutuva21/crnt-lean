# The missing discharger at `TrueChemistrySRCriterion.lean:8607`: a species-to-species ear

**Status: target statement established; the S→S builder obstacle is CLEARED; the true blocker is
evenness of the glued cycle, which is a sum-versus-term gap in the σ-sign data. The proof is not
written.** All `file:line` citations were read in the tree at commit `5f4160a` (branch
`research/holeb-earcase-port`, PR #36).

## 1. Why this is the exact remaining gap

The `sorry` sits at the end of a `by_cases hvr` inside the `v`-is-a-species branch of the `hspan`
proof, where an `exfalso` has made the goal `False`. Read the three ear dischargers the file
already contains and compare their endpoint types:

| discharger | line | `hstart` endpoint | `hlast` endpoint | shape |
|---|---|---|---|---|
| `no_clean_directed_species_reaction_ear_of_trueSRCriterion` | 5299 | `Sum.inl s` | `Sum.inr ρ` | S → R |
| `no_species_reaction_ear_of_trueSRCriterion` | 5688 | `Sum.inl s` | `Sum.inr ρ` | S → R |
| `no_reaction_species_ear_of_trueSRCriterion` | 5735 | `Sum.inr ρ` | `Sum.inl s` | R → S |

**All three require an on-cycle *reaction* at one end.** The in-scope data at `:8607` has an
on-cycle **species** at *both* ends. No discharger in the tree has that shape. That is the
"A.6 Case-2 source-block datum" the in-file comment at `:8600-8607` names, and it is why
`research/DEAD-ENDS.md` B-6 and B-10 record that the ear route is "a different proof": the Case-2
dischargers of `CRNT/Multistationarity/TrueSREarCase2.lean` are stated for `TrueSRPathRR` /
`TrueSRSSPath` **on a stage cycle built inside a source block**, which is not what this proof
constructs.

## 2. The data actually in scope

From `Q0 := CRNT.exists_minimal_relPath … ` and `exists_minimal_escape` (`:7585`):

- `Q0 : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T m`, `0 < m`,
  `hQ0inj : Function.Injective Q0.vertex`;
- `hv0 : Q0.vertex ⟨0,_⟩ = Sum.inl s0` with `hs0C : C.HasSpecies s0.1`;
- `hqm : Q0.vertex ⟨m,_⟩ = Sum.inr q`, `hqT : Sum.inr q ∈ T`;
- `hQ0late : ∀ i, i.1 ≠ 0 → ¬ C.HasVertex (N.aggregateVertexToTrueSRVertex (Q0.vertex i))`;
- `W : (CRNT.relationGraphOn … T).Walk … (Sum.inr q) (Sum.inr v)` with `hvOn : C.HasVertex … v`
  where `v` is `Sum.inl`, i.e. an on-cycle species; `W.IsPath`; `hWoff : ∀ i, i < W.length,
  ¬ C.HasVertex …`; `hWpos : 0 < W.length`;
- `hm1s : ¬ (m = 1 ∧ s0 = s)`;
- `¬ hnc`, `hopp`, `hcausal`, `hsep`, `hCeven`, `hSR`, `hscc`, `hsource`.

### The concatenation is the ear, and its parity is forced

The causal-edge case table (`:4691-4699`) is

```
| Sum.inl s, Sum.inr ρ => (N.trueInternalClassFlux α ρ.1 s.1) * σ s.1 < 0
| Sum.inr ρ, Sum.inl s => 0 < (N.trueInternalClassFlux α ρ.1 s.1) * σ s.1
| Sum.inl _, Sum.inl _ => False
| Sum.inr _, Sum.inr _ => False
```

so consecutive vertices alternate species/reaction, and:

- `Q0.vertex 0 = Sum.inl s0` (species) and `Q0.vertex m = Sum.inr q` (reaction) force **`m` odd**;
- `W` starts at the reaction `q` and ends at the species `v`, so **`W.length` is odd**;
- hence `Q0 ++ W` has **even** total length and is species at both ends: the shape of
  `N.TrueSRSSPath (2 * j + 2)`, **not** `TrueSRPathRR`.

Consequently the applicable glue is `SSGluable` / `ssGlueCycle`
(`TrueSRSpeciesPath.lean:392`, `:548`), with evenness from `ssGlueCycle_numCPairs`
(`TrueSRSSGlueCPairs.lean:107`) and `ssGlueCycle_even_of_partner` (in the Case-2 port) — **not**
`rrGluedCycle`. Step 0 of `Q0` forces `Q0.vertex 1 = Sum.inr ρ₁` with
`N.trueInternalClassFlux α ρ₁.1 s0.1 * σ s0.1 < 0` and `ρ₁` off-cycle, which is exactly the
`no_offCycle_negFlux` refutation recorded by PR #20 and is why `no_escape_from_cycleSpecies` cannot
be used.

## 3. Target statement

To be stated inside `TrueChemistrySRCriterion.lean` (the three ingredients
`trueSREdge_endpoint_eq_of_same_class_and_species` `:1806`,
`exists_trueSREdge_of_nonzero_trueInternalClassFlux` `:4781` and
`nonAdjacent_cycleClassFlux_eq_zero` `:6979` are all `private` to that file, so nothing usable
lives outside it):

```lean
private theorem no_species_species_ear_of_trueSRCriterion (N : Network S)
    (hSR : N.TrueSRStrongCriterion) {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (C : N.TrueSRCycle n) (hC : C.Even)
    (T : Finset (N.TrueInternalAggregateVertex α σ)) {k : ℕ}
    (P : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T k)
    (hinj : Function.Injective P.vertex) (hk : 4 ≤ k)
    {s₀ s₁ : AggregateActiveSpecies σ}
    (hstart : P.vertex ⟨0, by omega⟩ = Sum.inl s₀)
    (hlast  : P.vertex ⟨k, by omega⟩ = Sum.inl s₁)
    (hs₀C : C.HasSpecies s₀.1) (hs₁C : C.HasSpecies s₁.1)
    (hne : s₀ ≠ s₁)
    (hinterior : ∀ i : Fin (k + 1), i.1 ≠ 0 → i.1 ≠ k →
      ¬ C.HasVertex (N.aggregateVertexToTrueSRVertex (P.vertex i))) : False
```

with `k` even forced by the case table, so `hk : 4 ≤ k` (rather than `3 ≤ k` as in the S → R
versions, which have odd length).

## 4. What the proof must do

Convert `P` to a `TrueSRSSPath` (both ends species ⇒ even length), obtain the two cycle arcs between
`s₀` and `s₁`, and exhibit one of the six arrangements of Fig. 8 as in the header table of
`TrueSREarCase2.lean`, then feed `lemmaA6_case2_interleaved` / `lemmaA6_case2_twoComponents`.
Three obstacles, in order of difficulty:

1. ~~**`P` is a `RelPath`, not a `TrueSRSSPath`.**~~ **CLEARED.** The S → S builder exists:
   `relPathToTrueSRSSPath` at **`TrueChemistrySRCriterion.lean:5475`**,

   ```lean
   private noncomputable def relPathToTrueSRSSPath (N : Network S)
       {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
       (T : Finset (N.TrueInternalAggregateVertex α σ)) {k : ℕ}
       (P : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T k)
       (hinj : Function.Injective P.vertex) (hk : 0 < k)
       {s s' : AggregateActiveSpecies σ}
       (h0 : P.vertex ⟨0, by omega⟩ = Sum.inl s)
       (hlast : P.vertex ⟨k, by omega⟩ = Sum.inl s') : N.TrueSRSSPath k
   ```

   It is `private`, hence in-file, and takes **species at both ends** — exactly the composite's
   shape. Every argument is available at the residue: `P` = the concatenation of `Q0` with the
   `RelPath` form of `W`; `hinj` from `hQ0inj` together with `W.IsPath`; `hk` from the parity
   argument above (composite length even and `> 0`); `h0 = hv0`; `hlast` from `hvOn` with `v` the
   species. Sibling builders `relPathToTrueSRPath` (`:5217`, S → R) and `relPathToTrueSRPathRev`
   (`:5584`, R → S) sit at the same level.
   **So the route does not stop at step 1.** Two obstacles remain.
2. **`harr`, the arrangement datum.** `CE/QE/PE/VE` appear nowhere above `:8607`
   (`DEAD-ENDS.md` B-10, confirmed by grep: zero hits for `harr`, `hdecX`, `hdecY` in the file).
   `research/routes/pr10-verification.md` §5 records that `harr` has no producer and that the
   reason is not merely a missing glue instance. The arrangement is the
   cut-the-cycle-at-four-attachments computation.
3. **Evenness of the glued cycle — THE REAL BLOCKER.** `hC : C.Even` is given for `C` only. The
   glued cycle's evenness comes from `TrueSRCycle.even_of_signDirected` (Case-2 port `:147`),
   which needs

   ```lean
   def TrueSRCycle.SignDirected {n : ℕ} (C : N.TrueSRCycle n) (σ : S → ℝ) : Prop :=
     (∀ i, σ (C.species i) ≠ 0) ∧
       (∀ i, C.isCPair i ↔ σ (C.species i) * σ (C.species (finRotate n i)) < 0)
   ```

   The ear's interior species are **off-cycle**, and the residue's hypotheses pin σ there in no way:

   - `hcausal`/`hopp` pin the class flux at *cycle* classes only (`DEAD-ENDS.md` B-5: "already
     sharp", no slack).
   - `hlocal` (`:6077-6080`) is a **sum** positivity,
     `0 < ∑_ρ (N.trueInternalClassFlux α ρ s.1) * σ s.1` over
     `N.trueInternalAggregateSourceClasses α σ T`. It bounds the *total* at each species and forces
     nothing about any individual term, hence nothing about an individual off-cycle σ-sign.
   - every other `σ s ≠ 0` in the file (`:1272`, `:1408`, `:1957`) occurs as a **precondition**
     `hs : σ s ≠ 0`, never as something derivable.

   So `SignDirected σ` on any cycle containing ear species is **not provable from the residue's
   hypotheses**. This is a sum-versus-term gap, the same species of obstruction as Hole A's
   A-64/A-68 — an analytic estimate nobody has made, not a missing lemma.

**Prioritisation.** Obstacles 1 and 2 are finite combinatorics over `C` and the ear's shape, and both
are writable now. But even if both succeed, `lemmaA6_case2_*` cannot be applied without evenness. **The
true target is therefore not `harr` but a new estimate relating the σ-sign pattern to the flux-sign
pattern on off-cycle species** — of the shape "the aggregate causal degree of an off-cycle species is
bounded, or its class flux is σ-sign-definite". Nothing in the tree, the 21 landed declarations, or
the research ledger supplies it. `harr` is the tractable second-order problem.

Corollary: `no_offCycle_negFlux` (landed, PR #20) is **refuted** at the residue, so any strategy
assuming it is dead; and a strategy needing σ-sign-definiteness for an off-cycle class asks for
something the hypotheses equally do not give.

## 5. Dead ends already excluded (do not re-walk)

- `no_spanning_path_of_trueSRCriterion` cannot be applied to `Q0`: `hqm` puts `q` at index `m` and
  `hQ0late` + `hmpos` force every index `≠ 0` off-cycle, so `Q0` is half-spanning (B-7).
- `hnd` in the `hspan` witness is unsatisfiable: every SR edge joining a cycle species to a cycle
  reaction is itself a cycle edge (B-1). Do not try to rebuild `hspan` in this branch.
- `hopp` does **not** force the first hop to be length 1 (B-8); the in-file comment at `:8600-8607`
  is wrong, and PR #20's `classFlux_trichotomy` machine-checks the correction.
- `hrest` is not in scope at `:8607` and its natural instance is refuted by `hattachment` (B-3).
- `hSR.2` is vacuous on a degree-two cycle (B-25), so degree-two isolation cannot be discharged
  through it.

## 6. Cited sources

- G. Shinar and E. D. Feinberg, *Sign-causality and concavity in chemical reaction networks*,
  arXiv:1203.6560, Appendix A.3, Lemma A.6 (Case 1 = S → R ear, Case 2 = S → S ear) and
  Appendix A.2 (parity transfer). Case 1 is formalised in
  `CRNT/Multistationarity/TrueSREarCase1.lean`; Case 2's discharge lemmas are in
  `CRNT/Multistationarity/TrueSREarCase2.lean`.
- The six arrangements and the `CE/QE/PE/VE` notation: header table of
  `CRNT/Multistationarity/TrueSREarCase2.lean`.

## 5b. SUPERSEDED ordering — read `holeB-literature.md` first

This note's §4 prioritised `harr` as obstacle 2 and named the σ-sign estimate as the true
blocker (§4b). **Both were superseded** by the primary-source work recorded in
`research/routes/holeB-literature.md`:

| this note said | the source says | status |
|---|---|---|
| blocker is a sum-versus-term σ gap (§4b) | Prop. 5.11 (`:869`) gives evenness of **every cycle in the source** under `hSR.2`, with **no σ-sign hypothesis at all** | §4b **wrong**; the paper never asks for a σ-sign estimate |
| build `no_species_species_ear_of_trueSRCriterion` | the target is a port of **Prop. 5.11** over the block decomposition | §3 target **mis-aimed** |
| `harr` is a real obstacle | `harr` is real but **second-order**: it only matters once evenness is in hand, and evenness is free under Prop. 5.11 | §4 ordering **wrong** |
| "Lemma A.6" | no such lemma; the content is **Prop. 5.8** (App. A.3) + **App. A.2** | citation wrong throughout |

What survives from this note and is still correct:

1. **The residue's ear is species→species.** The three existing dischargers (`:5299`, `:5688`,
   `:5735`) all need an on-cycle reaction at one end; the in-scope data has an on-cycle species at
   both ends (`Q0 : s0 ⇝ q`, then `W : q ⇝ v`). Verified, and unchanged by the literature work.
2. **The parity forcing.** `m` odd, `W.length` odd, composite even and species-terminated, so the
   applicable glue is `SSGluable`/`ssGlueCycle` rather than `rrGluedCycle`. Verified from the case
   table at `:4691-4699`.
3. **`relPathToTrueSRSSPath` exists** at `:5475` and takes species at both ends — obstacle 1
   cleared. Verified.
4. **The dead-end list in §5.** All still valid; B-8 in particular is now machine-checked by
   `classFlux_trichotomy` (landed in PR #36), which confirms the in-file comment at `:8600-8607`
   is wrong.
5. **`v ≠ s`** is already proved in the file: the `hsNotIn` argument at `:8306-8316` shows
   `⟨Sum.inl s, hsT⟩ ∉ W.support`, and it is branch-independent. **`v = s0` is neither forced nor
   excluded** — nothing in `:8572-8609` relates them, so a `by_cases` on it is required.

Corrected dependency order for whoever attempts this next:

1. `Walk → RelPath` lift + a whole-path `append` (`RelPath.concat` extends by ONE vertex only —
   verified at `CRNT/Graph/RelPath.lean:189-190`, so `Q0 ++ W` needs a new operation). In progress
   in `CRNT/Graph/RelPathWalk.lean`.
2. `relPathToTrueSRSSPath` on the composite; `by_cases` on `v = s0`.
3. **Port the weakest useful form of Prop. 5.11** — see `holeB-literature.md` §7-8 for why the block
   structure may be avoidable, and §11 for the full cost if it is not.
4. Only then `harr` / the six arrangements of `SixCases.eps` (recoverable — the tarball ships it).

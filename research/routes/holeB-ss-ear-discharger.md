# The missing discharger at `TrueChemistrySRCriterion.lean:8607`: a species-to-species ear

**Status: precise target statement, established by reading source. The proof is not written.**
All `file:line` citations were read in the tree at commit `4bb7049` (branch
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

1. **`P` is a `RelPath`, not a `TrueSRSSPath`.** There is `N.relPathToTrueSRPathRev`
   (`N.relPathToTrueSRPathRev T P hinj hkpos hlast hstart`, used at `:5735`) but that is the
   **S → R** builder. The S → S builder for a species-terminated `RelPath` must be located or
   written. **This is the first thing to check** — if it does not exist, the route stops here.
2. **`harr`, the arrangement datum.** `CE/QE/PE/VE` appear nowhere above `:8607`
   (`DEAD-ENDS.md` B-10, confirmed by grep: zero hits for `harr`, `hdecX`, `hdecY` in the file).
   `research/routes/pr10-verification.md` §5 records that `harr` has no producer and that the
   reason is not merely a missing glue instance. The arrangement is the
   cut-the-cycle-at-four-attachments computation.
3. **Evenness of the extracted cycles.** `hC : C.Even` is given for `C` only. The glued cycle needs
   `SignDirected σ`, which requires σ nonzero on the ear's species and the c-pairs to be exactly the
   σ-sign changes — an estimate about signs that `hopp`/`hcausal` provide for *cycle* classes only
   (`DEAD-ENDS.md` B-5). **This may be the real blocker**, independent of `harr`.

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

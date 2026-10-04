# The RR reaction-arc builder — route and residual

**agent:** `form-sr-parity` · **branch** `research/form-sr-parity` · **PR** #17
**status:** the arithmetic is proved and committed; the construction is *not* closed.

## 1. Why this is the right first step

DEAD-ENDS **B-12** and the surviving-route memo agree: the ear of Shinar–Feinberg A.6 Case 2
runs **reaction-to-reaction**, from `R_O` to `R_I`. The tree has cycle arcs only for the
*species* flavour:

| flavour | arc builder | gluability | file |
|---|---|---|---|
| species → species | `TrueSRCycle.speciesArc` / `speciesArcBwd` (`:645`, `:755`) | `ss_gluable_arcs` (`:902`) | `TrueSRSpeciesPath.lean` |
| reaction → reaction | **none** | **none** | — |

So `exists_second_evenCycle_of_offCycle_escape` could not even be *typed* before this slice.

## 2. A correction to the brief (checked, `[V]`)

The orchestrator's second brief said `prepend` being private is a blocker worth +30 and that
lifting `private` is "a legitimate, minimal, documented change". Reading the source:

* `TrueSRPath.prepend` (`TrueSRParityRR.lean:276`) is `private noncomputable def` — true.
* But **`glueArc` (`:388`) is public and already is the RR arc builder**, and it is *already
  exported*. The brief's own later correction says this.
* `glueArc X Y h` takes `h : RRGluable X Y` **as an input**.

**The genuinely missing artefact is therefore the `RRGluable` instance for two cycle arcs, not
the path data.** Constructing `reactionArcFwd` is still necessary (you must have `X` and `Y`
before you can glue them), but the *terminal* object `exists_second_evenCycle_of_offCycle_escape`
needs is the `RRGluable`. Recommend downstream work target `rr_gluable_arcs` directly.

I did **not** lift the `private` modifier on `prepend`. The construction below routes through the
public `TrueSRCycle.rotate` + `initialArcPath` instead, so no privacy change was required.

## 3. What is proved and committed

`CRNT/Multistationarity/TrueSRReactionArc.lean` — hole-free, **0 sorries**, axioms exactly
`[propext, Classical.choice, Quot.sound]` (verified with `#print axioms`).

```lean
private theorem one_lt_n {n : ℕ} (hn : 2 ≤ n) : 1 < n

private theorem rotate_speciesAt {n : ℕ} (C : N.TrueSRCycle n) (r : ℕ) {i : ℕ} (hi : i < n) :
    (C.rotate r).species ⟨i, hi⟩ = C.species ⟨(i + r) % n, Nat.mod_lt _ (by omega)⟩

private theorem rotate1_reaction {n : ℕ} (C : N.TrueSRCycle n) (m : ℕ)
    (hm : m < n) (hmpos : 0 < m) (hm1 : m - 1 < n) :
    (C.rotate 1).reaction ⟨m - 1, hm1⟩ = C.reaction ⟨m, hm⟩
```

**Why `rotate_speciesAt` is stated at an arbitrary index** rather than reusing
`TrueSRCycle.rotate_species` (`:67`, which is `rfl`): it is *insensitive to the `Fin` proof terms
in the caller*. That was, by a wide margin, the largest source of elaboration friction in this
slice — `rotate_species` is stated at `⟨i, ?⟩` and the goal often carries a different proof.
This one reformulation removed most of it.

## 4. The construction, and its exact residual

```lean
-- ρ_0 ⇝ ρ_m : first edge leaves ρ_0 on C.rightEdge 0, then runs
-- species 1 →leftEdge 1→ ρ_1 →rightEdge 1→ ⋯ →leftEdge m→ ρ_m.
-- The tail is the initial arc of the cycle ROTATED BY 1, so species 1 sits at
-- position 0 and no % n ever wraps: every index touched is in 1 … m, m < n.
reactionArcFwd (hm1 : m - 1 < n) : N.TrueSRPathRR (m - 1) where
  first := C.rightEdge ⟨0, by omega⟩
  tail  := (C.rotate 1).initialArcPath (m - 1) hm1
  first_species        := <PROVED>
  first_ne_tail_edge   := <RESIDUAL>
  first_ne_tail_vertex := <RESIDUAL>
```

Three of five obligations are discharged (including `first_species`, which took the
`rotate_speciesAt` reformulation above). The two residuals are **index arithmetic, not new
mathematics**:

**(a) `first_ne_tail_edge : ∀ i : Fin (2 * (m-1) + 1), ¬ first.SameIncidence (tail.edge i)`**

Split on `i.1 % 2 = 0`. In both cases rewrite with `TrueSRCycle.initialArcPath_edge_even/odd`
and `TrueSRCycle.rotate_leftEdge/rotate_rightEdge`; every cycle index the tail touches is
`t := i.1 / 2 + 1 ∈ [1, m] ⊂ [1, n)`, never `0`.

* *left-edge case: solved.* The pair is left-vs-right, which a cycle never has:
  `C.not_sameIncidence_left_right ⟨t⟩ ⟨0⟩`.
* *right-edge case: solved modulo one arithmetic lemma.* Both sides are
  `C.species ((t + 1) % n)`; `t ≥ 1` so `(t+1) % n` is `t + 1 ≥ 2` when `t + 1 < n`, and `0`
  when `t + 1 = n`. Either way it is `≠ 1`. Discharge with `C.species_injective` then a
  `by_cases hwrap : t + 1 = n`.

**(b) `first_ne_tail_vertex : ∀ i, Sum.inr ⟨first.reaction, first.internal⟩ ≠ tail.vertex i`**

Split on `i.1 % 2 = 0`.

* *even case: solved.* Such a vertex is `Sum.inl _`, and `Sum.inl _ ≠ Sum.inr _`.
* *odd case: solved modulo one arithmetic lemma.* The vertex is
  `(C.rotate 1).reaction ⟨i.1/2, _⟩`; apply `C.reaction_injective` and then
  `⟨t⟩ ≠ ⟨0⟩` in `Fin n` with `t = (i.1/2 + 1) % n`.

**The only obstacle is mechanical:** `TrueSRCycle.initialArcPath_vertex_odd` (`:212`) is stated
at `⟨p.1 / 2, by omega⟩`, and the goal elaborates that index with a *different* proof term, so
every `rw` must have the index written out in full. Two workarounds that worked:

```lean
-- 1. state the helper at an arbitrary index (done above), and
-- 2. avoid `congrArg Fin.val` on a `Fin` equality — it fails to elaborate because
--    the motive depends on the proof term.  Use `Fin.ext`, or introduce the index
--    as a named `Fin` first.
```

Do **not** try to `rw [TrueSRCycle.rotate_species]` directly in a goal; it is `rfl` and its
index proof will not match. Go through `rotate_speciesAt`.

## 5. Dependency order

1. `reactionArcFwd` (this file; 3/5 obligations done) — **blocking**.
2. `reactionArcBwd := (C.reverse).rotate (n-1) |> .reactionArcFwd (n - m)`; on that cycle
   `reaction 0 = C.reaction 0`, `rightEdge 0 = C.leftEdge 0`, `reaction (n-m) = C.reaction m`.
   Available from `TrueSRCycle.rotate_*` + `TrueSRCycle.reverse_*` (all public).
3. `rr_gluable_arcs : RRGluable (reactionArcFwd …) (reactionArcBwd …)` — **the real target.**
   Counterpart of `ss_gluable_arcs` (`TrueSRSpeciesPath.lean:902`). Each clause
   (`same_start`, `same_end`, `species_disjoint`, `reaction_disjoint`, `edge_disjoint`,
   `TrueSRParityRR.lean:260`) is a cycle-index injectivity argument of exactly the shape in §4.
4. Then `glueArc` (public, `:388`) and `gluable_of_RRGluable` (`:442`) give the two halves of
   each glued cycle for free, and `rr_three_glued_even_of_two` (`:783`) gives the evenness.

## 6. Dead ends hit (do not re-walk)

* **`C.reverse` alone does not give the backward arc.** `(C.reverse).reactionArcFwd (n - m)`
  starts at `C.reaction (n-1)`, not `C.reaction 0`. The `rotate (n-1)` in step 2 is required.
* **`initialArcPath_vertex_zero` does not exist.** Use
  `initialArcPath_vertex_even … ⟨0, _⟩ (by show (0:ℕ) % 2 = 0; omega)`.
* **`congrArg Fin.val` on a `Fin` equality** fails with "motive is not type correct" whenever
  the index carries a `⟨·, by omega⟩` term. Use `Fin.ext` inside `congrArg` on the *function*.
* **`Nat.mod_lt _ hlt` takes `hlt : 0 < n`**, not the bound you are proving. Write
  `Nat.mod_lt _ (by show 0 < n; omega)`.
* **Section variables are auto-bound and come first.** `(C : TrueSRCycle n) (m : ℕ) (hm : m < n)`
  auto-binds `C`, `m`, `n`, so a `private theorem` in that section takes only `hm` explicitly.
  Anything called from outside the section must re-declare its parameters, or live outside it.
* **`checkmod.sh` was broken all round** (`lake env` prepends to `LEAN_PATH`, so the worktree
  build dir shadowed the shared cache and *every* module importing a `CRNT.*` module failed).
  Workaround used here: `rm -rf .lake/build && ln -s <shared>/.lake/build .lake/build`.
  InfraBuild has the real fix on `research/infra-build`.
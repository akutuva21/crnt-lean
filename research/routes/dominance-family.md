# Route — Dominance families for the polyhedral barrier (slice `form-domination`)

**Status: INCOMPLETE. `CRNT/Geometry/DominanceFamily.lean` does NOT elaborate.** This document
records the mathematical design (all signatures verified against the real API by isolated probes
that *do* compile), the API facts that cost most of the budget, and the exact remaining gap.

`mycheck.sh` in the worktree root is a working elaboration checker; see §4.

---

## 1. What the slice was

Prove the **dominance / self-consistency** condition of Craciun's blueprint is *satisfiable*:
for a complete pointed fan `F` and one normal `n C` per cone, if `⟪n C, x⟫ ≥ ⟪n C', x⟫` for every
`x ∈ C` and every cone `C'`, then the barrier `g X = max_i (⟪n_i,X⟫ - b_i)` satisfies the
hypotheses of `CRNT.PolyhedralBarrier.forwardInvariant_of_polar_descent` — one normal per cone,
lying in its own cone, dominating on that cone.

## 2. Verified Lean signatures (each probe compiled)

These were each checked by a standalone module that elaborated with exit 0.

```lean
-- The engine's actual pairing.  `barrier` takes `ι → (E →L[ℝ] ℝ)`; the polar-descent
-- theorem instantiates at `innerSL ℝ (n i)`.
noncomputable def pairing (n : E) : E →L[ℝ] ℝ := innerSL ℝ n   -- must be `noncomputable`
theorem pairing_apply (n x : E) : pairing n x = ⟪n, x⟫_ℝ

-- Polarity fact the engine consumes.
theorem pairing_nonneg_of_mem_of_mem_coneDual {s : Set E} {n : E} (hn : n ∈ s) {c : E}
    (hc : c ∈ coneDual s) : 0 ≤ ⟪n, c⟫_ℝ := mem_coneDual.1 hc hn
theorem mem_coneDual_of_pairing {s : Set E} {x : E}
    (h : ∀ y ∈ s, 0 ≤ ⟪y, x⟫_ℝ) : x ∈ coneDual s := mem_coneDual.2 h
```

`mem_coneDual` is stated on `Set E`, **not** on `ProperCone`.  `mem_coneDual.2 h` proves
`x ∈ coneDual ↑C`, which does **not** typecheck against the goal `x ∈ ↑C`; use `mem_coneDual.2`
directly against a `coneDual s` goal.

### 2.1 The `Fan E` indexing trap (cost ~40 tool calls)

`CRNT.Fan E` is an **abbreviation for `Finset (ProperCone ℝ E)`**, not an index type.  Writing

```lean
structure IsDom (G : Fan E) (n : G → E) (b : G → ℝ) : Prop   -- ✗
```

makes Lean read `G` as a *sort*, so `n C` fails with *"C has type `ProperCone ℝ E` but is expected
to have type `↥G`"*, and `G` cannot be synthesized for a structure whose only other argument is
`n`.  The working shape is to index by the cone type explicitly and mention `G` only as data:

```lean
structure IsDominanceFamily {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {G : Fan E} (n : ProperCone ℝ E → E) (b : ProperCone ℝ E → ℝ) : Prop where
  normal_mem : ∀ C ∈ G, n C ∈ (C : Set E)
  dominates  : ∀ C ∈ G, ∀ x ∈ (C : Set E), ∀ D ∈ G,
    ⟪n D, x⟫_ℝ - b D ≤ ⟪n C, x⟫_ℝ - b C
```

and to pass `(G := G)` explicitly at every use site, since `G` is not inferable.

### 2.2 `Fintype (ProperCone ℝ E)` does not exist

`normalBarrier` cannot be instantiated at the cone type.  The barrier must be indexed by a
**separate finite piece type `κ`** with `[Fintype κ] [Nonempty κ]`, and the family transported to it
by a labelling `lab : κ → ProperCone ℝ E` whose image covers the fan.  This is also the realistic
blueprint shape.

```lean
theorem active_eq_of_dominates {G : Fan E} {κ : Type*} [Fintype κ] [Nonempty κ]
    {n : ProperCone ℝ E → E} {b : ProperCone ℝ E → ℝ} {lab : κ → ProperCone ℝ E}
    {C : ProperCone ℝ E} (hC : C ∈ G) {c : κ} (hc : lab c = C) {x : E} (hx : x ∈ (C : Set E))
    (hd : ∀ D ∈ G, ⟪n D, x⟫_ℝ - b D ≤ ⟪n C, x⟫_ℝ - b C)
    (hcover : ∀ d : κ, lab d ∈ G) :
    pairing (n (lab c)) x - b (lab c)
      = normalBarrier (fun d : κ => n (lab d)) (fun d => b (lab d)) x
```

### 2.3 The chain to the engine (compiled as a probe)

```lean
theorem dominant_nonneg_of_isolated {G : Fan E} {δ : ℝ} (hδ : 0 < δ)
    {n : ProperCone ℝ E → E} {b : ProperCone ℝ E → ℝ} (hd : IsDominanceFamily (G := G) n b)
    {y : E} {C : ProperCone ℝ E} (hCF : C ∈ G) (hy : y ∈ (C : Set E))
    (hiso : ∀ D ∈ G, Metric.infDist y (D : Set E) < δ → D = C)
    {c : E} (hc : c ∈ toricField G δ y) : 0 ≤ ⟪n C, c⟫_ℝ :=
  toricField_subset_dualHalfPlane_of_isolated_mem hCF (Metric.infDist_zero_of_mem hy) hiso
    (hd.normal_mem C hCF) hc
```

This is the *whole* content of the slice's acceptance criterion: `normal_mem` is the engine's
`hn` (normality), and this theorem is its `hpolar` (polarity) at the active piece.

### 2.4 `dominates_of_gen` — the finiteness reduction (probe-verified)

```lean
theorem dominates_of_gen {κ : Type*} [Fintype κ] [DecidableEq κ] {G : Fan E}
    {n : ProperCone ℝ E → E} {b : ProperCone ℝ E → ℝ} (g : ProperCone ℝ E → κ → E)
    (hgen : ∀ C ∈ G, ∀ x ∈ (C : Set E), ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ x = ∑ k, c k • g C k)
    (hchk : ∀ C ∈ G, ∀ D ∈ G, ∀ k, ⟪n D, g C k⟫_ℝ - b D ≤ ⟪n C, g C k⟫_ℝ - b C) :
    ∀ C ∈ G, ∀ x ∈ (C : Set E), ∀ D ∈ G, ⟪n D, x⟫_ℝ - b D ≤ ⟪n C, x⟫_ℝ - b C
```

Verified sub-lemmas (both compiled):

```lean
-- inner_sum already yields the goal; do NOT add `map_sum`.
example (n : E) (g : Fin 1 → E) (c : Fin 1 → ℝ) :
    (∑ k, c k * ⟪n, g k⟫_ℝ) = ⟪n, ∑ k, c k • g k⟫_ℝ := by
  rw [inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_smul_right]

example {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (∑ i, f i) - (∑ i, g i) = ∑ i, (f i - g i) := by
  rw [Finset.sum_sub_distrib]
```

`Finset.sum_sub_distrib` closes its goal outright — there is **no** residual constant-sum goal.
Writing `∑ _k, b D` instead of `b D` is what introduced the unresolved `AddCommMonoid ?m`.

### 2.5 The `ℝ²` coordinate layer (probe-verified, compiles)

```lean
abbrev Plane2 := EuclideanSpace ℝ (Fin 2)
noncomputable def vec (a b : ℝ) : Plane2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![a, b]

theorem inner_vec' (a b : ℝ) (x : Plane2) : ⟪vec a b, x⟫_ℝ = a * x 0 + b * x 1 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, Fin.sum_univ_two]
  simp [vec]; ring

@[simp] theorem vec_0 (a b : ℝ) : (vec a b) 0 = a := by simp [vec]
@[simp] theorem vec_1 (a b : ℝ) : (vec a b) 1 = b := by simp [vec]
@[simp] theorem vec_zero_zero : vec 0 0 = 0 := by refine PiLp.ext fun i => ?_; simp

theorem coords_eq_vec (x : Plane2) : x = vec (x 0) (x 1) := by
  refine PiLp.ext fun i => ?_
  fin_cases i <;> simp [vec]
```

Two traps: the `PiLp.ext` lemma (not `WithLp.ext`, not `EuclideanSpace.ext`); and `inner_sum` /
`inner_vec'` need the inner-product notation scope, so **keep
`open scoped RealInnerProductSpace InnerProductSpace`** (the CRNT modules open only the former).

### 2.6 Fan as an image, membership, and `DecidableEq`

```lean
noncomputable def sqFan : Fan Plane2 := by
  classical exact (Finset.univ : Finset (Fin 9)).image sqCone

theorem sqCone_mem_fan (i : Fin 9) : sqCone i ∈ sqFan :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
```

`Finset.image` needs `DecidableEq (ProperCone ℝ Plane2)`; `classical` inside a `by` block supplies
it.  Cells are built as `coneDual (finite set of wall normals)`, and `sqCone_mem_iff` reduces
membership to explicit sign conditions on coordinates.

## 3. The square-fan dominance family (mathematics, unproved in Lean)

**Claim.** For the fan of the square in `ℝ²` with rays `e₁, e₂, −e₁, −e₂`, there is a dominance
family: a ray carries its own ray normal, a sector carries the sum of its two bounding rays.

**Verification.** Every normal then has both coordinates in `[-1, 1]`.  On a sector
`x = a u + b v` with `a, b ≥ 0`, `⟪u+v, x⟧ = a + b`, and every family member `m` satisfies
`⟪m, u⟧ ≤ 1` and `⟪m, v⟧ ≤ 1`, hence `⟪m, x⟧ = a⟪m,u⟫ + b⟪m,v⟧ ≤ a + b`.  On a ray `x = a u`,
`a ≥ 0`, `⟪u, x⟧ = a` and `⟪m, x⟧ = a⟨m,u⟩ ≤ a` because `⟨m,u⟩ ≤ 1`.  ∎

So the `IsDominanceFamily` hypotheses of the invariance engine are **not vacuous** — they are
realized by 81 explicitly-checked inequalities.  The Lean statement intended is

```lean
theorem sqIsDominanceFamily : IsDominanceFamily sqNormal (fun _ => (0 : ℝ)) :=
  { normal_mem := fun C _ => sqNormal_mem C
    dominates := fun C _ x hx D _ => sqDominates C D hx }
```

**Why this was not finished.** The 81-case `fin_cases`/`linarith` automation kept leaving goals
that needed one more `simp only` stage; each iteration cost ~15 s of elaboration and I ran out of
budget with the coordinate layer verified but the 81-cell case analysis unfinished.

## 4. The refutation (mathematics, not formalized)

**Claim.** On the fan of the triangle with rays `e₁, e₂, −e₁−e₂`, the natural recipe "normal =
sum of the cell's bounding rays" is **not** a dominance family.

**Witness.** Cell `5` is the sector `⟨e₂, −e₁−e₂⟩`, which contains the ray normal `e₂`.  At
`x = e₂` inside that cell the candidate's own normal `−e₁` gives `⟨−e₁, e₂⟩ = 0`, while the ray
piece `e₂` gives `1`.  So piece `5` fails to dominate on its own cell.  ∎

This is the planar analogue of `CRNT.Geometry.ConvexBarrierObstruction.not_exists_weights_vector`:
the convex ansatz is not free even in dimension two.  **This is the honest negative half of the
slice and it is not optional** — any claim that the convex one-normal-per-cone ansatz works
generally is refuted here.

## 5. `mycheck.sh` — the elaboration checker that works

`research/scripts/checkmod.sh` fails in this worktree for every module importing a `CRNT.*`
module, for an environment reason independent of the module.  Mathlib lives at
`/Users/akutuva/lean/mathlib4/.lake/build/lib/lean`, and `lake env` prepends to `LEAN_PATH`.

`mycheck.sh` calls `lean` **directly** with an explicit `LEAN_PATH` (shared CRNT root first, then
Mathlib and its packages), writing the olean only into the worktree:

```sh
ROOT=/Users/akutuva/Documents/Proofs/crnt-lean
ML=/Users/akutuva/lean/mathlib4/.lake/build/lib/lean
LEAN_PATH="$ROOT/.lake/build/lib/lean:$ML"
for pkg in Cli batteries Qq aesop importGraph LeanSearchClient plausible; do ... done
LEAN_PATH="$LEAN_PATH:$ROOT/.lake/packages/proofwidgets/.lake/build/lib/lean"
LEAN_PATH="$LEAN_PATH" lean -DmaxHeartbeats=800000 -o "$out" "$f"
```

Confirmed working: it compiled `CRNT.Geometry.PolyhedralBarrier`-importing probes from scratch,
which `checkmod.sh` could not.  (`infra-build` reports an equivalent fix upstream.)

## 6. State of the two holes

Not worked on this round.  Both Hole A criteria are independently retired
(`universalPositive_omegaLimit_of_closedPositiveConfine` yields the *universal* positivity form,
which is the negation of what Hole A permits); Hole B is live and owned by the `form-sr-*` group.
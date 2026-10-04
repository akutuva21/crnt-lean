# Hole A, residue: the analytic estimate behind `ComparableGrowthDescent.descend`

**Agent:** `arch-sr-descent` · **round 2** · **branch** `research/arch-sr-descent-2`
**Target:** `Network.ComparableGrowthDescent.descend`, `CRNT/Dynamics/SiphonDimensionDescent.lean:128-131`
(structure at `:124-133`, left disjunct at `:129`, right disjunct at `:130-131`).
**Companion transcription:** `research/papers/anderson-1101-0761-transcription.md` (full read of
arXiv:1101.0761v6, 23 pages, this session).

Every `file:line` below was read in this session in this worktree unless explicitly marked.

---

## 0. Bottom line, first

**The residue is not an estimate that Anderson wrote down and nobody formalised. It is an
estimate Anderson did not use.** `arXiv:1101.0761` contains **no** siphon-cardinality descent, no
iteration over faces, and no "the zero set strictly shrinks" clause. It contains a *single global
dichotomy* (Lemma 4.7: `C1 ∨ C2`) whose conclusion is "the ω-limit set is a **single point**"
(Lemma 4.9), not "the siphon shrinks". The word *siphon* occurs once in the body, in the
historical background (transcription §1).

Three consequences, in decreasing order of usefulness:

1. **A checkable structural refutation of the residue's stated mechanism.** The escape face in
   hole A is a **critical** siphon. Anderson's Lemma 4.8 contradiction is *driven by* the
   conservation relation that `IsCriticalSiphon` asserts **does not exist**. So at exactly the
   configuration hole A occupies, the proof of Lemma 4.8 cannot be run. §4 below.
2. **The one hypothesis that would close the hole is `N.numLinkageClasses = 1`, and it is not
   derivable** from anything the hole supplies. Under it, the hole's hypotheses are in fact
   *inconsistent* (`hwmax` contradicts Anderson Thm 4.10). §5.
3. **Everything else is missing machinery, not missing analysis** — the projected/reduced network
   with time-dependent kinetics does not exist in the tree at all. §6.

So: **clean negative on the mechanism as the file describes it; no Anderson-type argument gives
the residue as stated.** What survives is a precise, small statement (the `C1` clause, §2) whose
proof is 4.5 pages of finite combinatorics on tiers plus one Stiemke argument — reachable in
principle, but it lands **Anderson Thm 4.10**, which is a *different and stronger* theorem than
the descent, and it still needs `SingleLinkageClass`.

---

## 1. The residue, exactly

```lean
structure ComparableGrowthDescent (N : Network S) (ϕ : Flow ℝ≥0 (Concentration S))
    (x₀ : Concentration S) : Prop where
  descend : ∀ P : Finset S, P.Nonempty → N.IsCriticalSiphon P → N.SiphonCarried ϕ x₀ P →
    (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) ∨
      (∃ Q : Finset S, Q.Nonempty ∧ N.IsCriticalSiphon Q ∧ Q.card < P.card ∧
        N.SiphonCarried ϕ x₀ Q)                                   -- :128-131
```

Supporting definitions, all read this session:

* `SiphonCarried` (`:61-63`): `∃ w ∈ omegaLimit atTop ϕ {x₀}, ∀ s, s ∈ P ↔ w s = 0`.
* `SiphonFace P` (`CRNT/Dynamics/Persistence.lean:59-60`):
  `{x | x.Nonnegative ∧ ∀ s ∈ P, x s = 0}`.
* `IsSiphon P` (`CRNT/Dynamics/Siphon.lean:54-55`):
  `∀ r : N.R, (∃ s ∈ P, N.IsProduct r s) → (∃ s ∈ P, N.IsReactant r s)`.
* `IsCriticalSiphon P` (`CRNT/Dynamics/Siphon.lean:84-87`):
  `P.Nonempty ∧ N.IsSiphon P ∧ ¬ ∃ v : S → ℝ, (∀ s, 0 ≤ v s) ∧ (∀ s, 0 < v s ↔ s ∈ P) ∧
    (∀ r : N.R, ∑ s, v s * N.reactionVector r s = 0)`.

Confirmed as DEAD-ENDS A-37 records (and re-verified here): the left disjunct `:129` is byte-identical
to the hole's conclusion, and `comparableGrowthDescent_iff_omegaPointPositive` (`:368-377`) makes the
whole structure equivalent to the goal given any carried critical siphon. **This document therefore
does not treat `descend` as a reduction step.** It treats it as: *what analytic statement would have
to be true for the file's stated mechanism to be a theorem at all?*

---

## 2. §1 of the brief — the analytic statement in Lean signature form

Three candidates, ordered by how much of the residue they actually are.

### 2.1 What `#grep relEntropy` says (I ran it; I did not assume)

`relEntropy` is `CRNT/Theorems/DeficiencyZero/Lyapunov.lean:58-59`:

```lean
noncomputable def relEntropy {ι : Type*} [Fintype ι] (xstar x : ι → ℝ) : ℝ :=
  ∑ i, (x i * Real.log (x i / xstar i) - x i + xstar i)
```

Anderson's `V_x̄` (eq. (4.5), transcription §2.7) is **this function with an arbitrary positive
reference `x̄`**. What the tree has is the **single-reference** version:

```lean
theorem dissipation_nonpos (N : Network S) (κ : RateConstants N) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    (∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) ≤ 0
```
(`CRNT/Theorems/DeficiencyZero/Dissipation.lean:191-193`)

**This is the single most important grep result of the assignment.** Anderson's estimate is
*strictness and universality* where the tree has *weakness and one reference*:

| | tree | Anderson C1 |
|---|---|---|
| reference | the complex-balanced `xstar` | **every** `x̄ ∈ ℝ^N_{>0}` |
| conclusion | `≤ 0` | `< 0`, for all `t > T_x` |
| where | every interior point | the escaping trajectory |

### 2.2 E1 — the family-of-Lyapunov estimate (Anderson's C1), in Lean signature form

The genuine "comparable-growth Lyapunov-family estimate", transcribed to the repo's coordinates.
`N.massActionRate κ r x` and `N.massActionVectorField κ x s = ∑ r, rate r x * reactionVector r s`
(`CRNT/Kinetics/MassAction.lean:49-51`), and `relEntropy x̄ x = ∑ s (x_s log(x_s/x̄_s) - x_s + x̄_s)`
so `relEntropy_hasDerivAt` (`CRNT/Theorems/DeficiencyZero/Stability.lean:37-40`) gives

```lean
/-- Anderson Lemma 4.7, condition C1, for the ORIGINAL (not projected) trajectory.
    Requires the reduced/projected network of §3 to be instantiated first. -/
def LyapunovFamilyStrictlyDecreases (N : Network S) (κ : N.RateConstants)
    {γ : Concentration S → ℝ → Concentration S} {x₀ : Concentration S} : Prop :=
  ∀ x̄ : Concentration S, x̄.Positive →
    ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t →
      ∑ s, (Real.log (γ x₀ t s) - Real.log (x̄ s)) *
        N.massActionVectorField κ (γ x₀ t) s < 0
```

*What growth comparison:* none locally — this is the **integrated** consequence of the growth
comparison. The growth comparison itself (Def 4.1, transcription §2.4) is a **tier partition of the
complexes along a subsequence**:

```lean
/-- Anderson Definition 4.1 (i). Within one tier, monomials are comparable up to a constant. -/
def TierComparableOn (N : Network S) (xs : ℕ → Concentration S) (y y' : Complex S) : Prop :=
  ∃ C : ℝ, 1 < C ∧ ∀ n, (C⁻¹ : ℝ) * CRNT.tierMonomial (xs n) y ≤ CRNT.tierMonomial (xs n) y' ∧
                     CRNT.tierMonomial (xs n) y' ≤ C * CRNT.tierMonomial (xs n) y

/-- Anderson Definition 4.1 (ii). Higher tier monomials dominate lower ones. -/
def TierStrictlyBelow (N : Network S) (xs : ℕ → Concentration S) (y y' : Complex S) : Prop :=
  Tendsto (fun n => CRNT.tierMonomial (xs n) y / CRNT.tierMonomial (xs n) y') atTop atTop
```
(`CRNT.tierMonomial` is `CRNT/Dynamics/TierPersistence.lean:30-31`; note the repo's
`TierStrictBelow` at `:34-35` encodes the *opposite* convention — `→ 0` — so it is Anderson's 4.1(ii)
with the tiers named the other way round. This is exactly the `A-2` sign hazard in a second guise;
**do not reuse the repo's `TierSame`/`TierStrictBelow` for Definition 4.1 without checking signs.**)

*Across what escape:* Anderson's `x_n = φ(t_n, x_0)` with `t_n → ∞`, `x_n → z ∈ ω(φ(·,x_0)) ∩
∂ℝ^N_{≥0}`, the **projected** trajectory of §3, with `U = {i : z_i = 0}` the reduced species set.

*At what rate:* **no uniform rate.** The domination constants are `q_{1,n}, q_{2,n} → ∞`
(transcription §2.8, eqs. 4.10/4.14), i.e. the estimate is "for all sufficiently large `n`, the
downward-tier terms dominate the upward-tier terms by an arbitrarily large factor", uniform over
`x̄` only through the bounded constants `|c_k| = |(y_k′ − y_k)·ln x̄| < ∞` (eq. after 4.7).
The **only** numeric bound consumed is the bounded-kinetics constant `η`
(`η < κ_k(t) < 1/η`, Definition 2.7 / eq. 4.17), used at eq. (4.12).

*For which Lyapunov family:* **all** of them — `V_x̄` for **every** `x̄ ∈ ℝ^N_{>0}` simultaneously.
This is what defeats the boundary-boundedness of `V_{xstar}` (`a1101.pdf:262`).

### 2.3 E2 — the exclusion of the bad tier configuration (Anderson Lemma 4.8)

```lean
/-- Anderson Lemma 4.8, general form. Only needs SINGLE LINKAGE CLASS in the printed proof. -/
def TopTierIsNotUnionOfLinkageClasses (N : Network S) (xs : ℕ → Concentration S) : Prop :=
  ¬ ∃ (P : ℕ) (T : Fin P → {c : Complex S // c ∈ N.complexes}), … T is a partition …
    (T 0 = ∪ (the complexes of some nonempty set of linkage classes))
```

### 2.4 E3 — the assembled theorem (Anderson Thm 4.10)

```lean
theorem anderson_theorem4_10 (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) (hslc : N.numLinkageClasses = 1)
    {xstar} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hK : IsCompact K) (hmaps : ∀ t, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, y.Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    -- Anderson's *condition 2*:
    (hcond2 : (∀ w ∈ omegaLimit atTop ϕ {x₀}, ¬ w.Positive) ∨
              (∀ w ∈ omegaLimit atTop ϕ {x₀}, w.Positive)) :
    ∀ w ∈ omegaLimit atTop ϕ {x₀}, w.Positive
```

Two observations that matter for the hole:

* **Condition 2 is free here.** `by_cases hex : ∃ p ∈ ω, p.Positive`; the `hex` branch is the hole's
  conclusion outright; the `¬hex` branch combined with `hωnn` makes *every* ω-point non-positive,
  i.e. condition 2 holds. So condition 2 costs one `by_cases` and is **not** part of the residue.
* **E3's conclusion is stronger than the hole's.** `∀ w ∈ ω, w.Positive` excludes `hwmax`
  entirely. So for `N.numLinkageClasses = 1`, **hole A's hypotheses are inconsistent** and the hole
  is provable — from `hwr`, which the tree supplies via
  `N.weaklyReversible_of_positive_complexBalanced κ hxs hcb`
  (`CRNT/Dynamics/HighCodimensionSiphonFace.lean:755`, read this session) — plus `hslc`.

---

## 3. The proof, cited

Full transcription with page anchors: **`research/papers/anderson-1101-0761-transcription.md`**.
The dependency chain, with the clause each step contributes:

| step | source | output |
|---|---|---|
| Def 3.1 + (3.7) | `a1101.pdf:153-160`, `:180` | reduced network `{S_U,C_U,R_U}` + kinetics `κ_k(t)` |
| Lemma 3.3 / 3.4 | `a1101.pdf:169` | ≤ℓ linkage classes; weakly reversible |
| eq. (4.17) | `a1101.pdf:381` | `η < κ_k(t) < 1/η` from (4.16) — **the one numeric bound** |
| Def 4.1 / Lemma 4.2 | `a1101.pdf:192-229` | tiers along a subsequence |
| Lemma 4.3 (Stiemke) | `a1101.pdf:231` | linear-algebra alternative |
| Thm 4.6 | `a1101.pdf:239-255` | `∃ w ≥ 0, supp w = U(z)`, `w ⊥` same-tier differences |
| eq. (4.5) | `a1101.pdf:258-262` | `V_x̄`, `∇V_x̄ = ln x − ln x̄` |
| Lemma 4.7 C1∨C2 | `a1101.pdf:264-341` | eqs. (4.8)/(4.9) split by tier; (4.10) & (4.12)–(4.15) domination |
| Lemma 4.8 | `a1101.pdf:341-345` | `¬C2` **under single linkage class** |
| Lemma 4.9 | `a1101.pdf:345-357` | C1 ⟹ ω a single point |
| Thm 4.10 | `a1101.pdf:357-383` | `ω ∩ ∂ = ∅`; origin-is-local-max kills `x(t) → 0` |
| Cor 4.11 | `a1101.pdf:383-385` | GAC for single-linkage complex-balanced |

**Marked `[NOT ACCESSIBLE]`, deliberately not paraphrased from memory:** Anderson, *Global asymptotic
stability for a class of nonlinear chemical equations*, SIAM J. Appl. Math. **68** (2008) 1464–1476
(reference [1] at `a1101.pdf:408-410`) — the "entry-time" paper cited by `research/README.md:175-176`
as bibliographic fact only. I did not fetch it this session, so nothing in §2 or §4 leans on it.
Likewise Anderson–Shiu arXiv:0903.0901 was not read this session.

---

## 4. The decisive part: which hypotheses each step consumes, and which the hole does NOT supply

The hole's hypotheses, verbatim from `CRNT/Dynamics/HighCodimensionSiphonFace.lean:111-133`:
`hxs hcb hϕγ hsol hK hmaps hωnn hgenω hωaff hx₀ hPmaxne hwmax hzeroMax hmaxExact hzcard hcodim hcard hrank`.

### 4.1 Consumed and available

| Anderson step | needs | available? |
|---|---|---|
| Thm 4.10 cond. 1, boundedness | bounded `φ(·,x₀)` | ✅ `hK`, `hmaps` |
| Thm 4.10 cond. 2 | all-boundary ∨ all-interior | ✅ **free**, one `by_cases` (§2.4) |
| Lemma 4.7 premise | `dist(φ(t),∂ℝ^N_{≥0}) → 0` | ✅ `hwmax` + `hωnn` (some `s`, `wmax s = 0`) |
| weak reversibility (Lemma 4.7 proof, eqs. 4.10/4.12; Lemmas 3.4) | `N.WeaklyReversible` | ✅ derivable: `weaklyReversible_of_positive_complexBalanced κ hxs hcb`, `HighCodimensionSiphonFace.lean:755` |
| eq. (4.17), `η < κ_k(t) < 1/η`, **upper** part | bounded `φ` | ✅ `hK` |
| eq. (4.17), **lower** part `κ_k(t) ≥ η` | `j ∉ U` ⇒ `lim inf φ_j > 0` | ✅ *from the definition of `U`*, not from the hole: `U = {i : z_i = 0 for some z ∈ ω}`, so `j ∉ U` ⇒ `ω_j > 0` ⇒ `lim inf φ_j ≥ ω_j > 0`, using `hK`+`hmaps` for the ω-limit-set construction. **This is the one genuinely free step of §3.** |
| positivity of the original trajectory (`∇V_x̄ = ln x − ln x̄` needs `x(t) > 0`) | `φ(t,x₀) > 0` ∀t | ✅ `Network.genuineOrbit_pos` from `hx₀` + `hsol` (used at `CRNT/Dynamics/GlobalAttractorTheorem.lean:140`, read this session) |

### 4.2 NOT supplied — the blocker list

| # | missing item | status in tree |
|---|---|---|
| **B1** | **`N.numLinkageClasses = 1`** | ✗ **not a hypothesis, not derivable.** `numLinkageClasses := Nat.card (Quotient N.linkedSetoid)` (`CRNT/Graph/LinkageClass.lean:93-94`). Nothing in the hole's list constrains it. §5.2 gives a witness that `IsCriticalSiphon` is compatible with `ℓ = 2`. |
| **B2** | **The projected/reduced network and its time-dependent kinetics** (§3.1, Def 3.1, eq. (3.7)) | ✗ **nothing in `CRNT/`**. I grepped `reducedNetwork|reducedReactionNetwork|projectedDynam|ProjOn|boundedMassAction|BoundedMassAction` over `CRNT/`: the **only** hit is `projOn` at `CRNT/Dynamics/FacetRepulsionAndersonShiu.lean:315-317`, the plain linear coordinate projection used for `hcodim` — not a reduced reaction network. `GeneralizedMassActionData` (`CRNT/Kinetics/GeneralizedDeficiencyZero.lean:47`) is a **static** structure, not a `κ_k(t)`. Every existing module is stated for a fixed `N` with fixed `κ`; Anderson's C1 and Lemma 4.8 are statements about a *different, non-autonomous* system. |
| **B3** | Tier partition of the complexes along a subsequence (Def 4.1, Lemma 4.2) | ✗ in hole's 179-module import closure. `CRNT/Dynamics/TierPersistence.lean` exists (476 lines, read this session) and is in `CRNT.lean:512`, but is **outside** the hole's closure (computed). It is also the *Cappelletti–Kim–Nguyen* tier route, not Anderson 1101.0761, and its `TierStrictBelow` (`:34-35`) has the **opposite** sign convention to Anderson's 4.1(ii). Its own open flag is `EveryTransversalTierSequenceHasDirectionWitness` (`:191-192`), which is *stronger* than Anderson's Lemma 4.2 (it asks for a single linear functional exactly realizing the whole preorder; Anderson only produces a partition). |
| **B4** | Stiemke (Lemma 4.3) | ✗ not present as a usable statement over `ℝ^S` with the strict-inequality alternative |
| **B5** | Theorem 4.6 (tier-respecting conservation relation) | ✗ |
| **B6** | Lemma 4.9 (C1 ⟹ ω a single point) | ✗; the tree's LaSalle route gives ω ⊆ `{xstar}` only from **one** `relEntropy`, not a family |
| **B7** | "origin is a local max of `V_x̄`" (last line of Thm 4.10's proof) | ✗ |

### 4.3 The structural refutation — B1 is not the only problem, and the others do not fix it

**Claim.** Let `z ∈ ω(φ(·,x₀)) ∩ ∂ℝ^N_{≥0}` with `U := zero set of z` a siphon. Then Anderson's
argument at `z` succeeds **only if** `U` is *not* a critical siphon.

**Proof.** Anderson's Lemma 4.8 contradiction has exactly two ingredients (transcription §2.9):
(i) `T_1 ≡ C` — one single tier; (ii) Theorem 4.6's `w ≥ 0` with `supp w = U` and
`w · (y_k′ − y_k) = 0` for **every** reaction, which makes `w · φ(t)` constant by (2.2), while
`w · φ(t_n) → 0`.

1. Ingredient (ii) with `w ⊥` **all** reaction vectors, `w ≥ 0`, `supp w = U`, and
   `φ_i(t_n) → 0 (i ∈ U)`, is *alone* a contradiction — no tiers needed. (Same proof as Lemma 4.8,
   with `T_1 ≡ C` deleted.) Call this **(\*)**. So if `U` is a siphon that is **not** critical, `z ∉ ω`
   immediately, and the whole tier apparatus is unnecessary.
2. Therefore the case that reaches the tier machinery is precisely `U` **critical**, i.e.
   `¬ ∃ v, (∀ s, 0 ≤ v s) ∧ (∀ s, 0 < v s ↔ s ∈ P) ∧ (∀ r, ∑ s, v s * N.reactionVector r s = 0)`
   — which is verbatim `CRNT/Dynamics/Siphon.lean:84-87`, the `IsCriticalSiphon` field the hole
   *supplies* through `hzeroMax` + the criticality derivable from `hwmax` via
   `isCriticalSiphon_of_siphonCarried` (`SiphonDimensionDescent.lean:68-80`).
3. For a critical `U`, Theorem 4.6 still produces a `w` — but with only **clause 2** of Definition 4.5,
   i.e. `w ⊥ (y_j − y_ℓ)` for `y_j, y_ℓ` **in the same tier**, not for all reaction vectors. So
   `(\*)` is unavailable, and `w · φ(t)` is constant only along the reactions *inside a tier*.
4. Under `SingleLinkageClass`, `T_1 ≡ C` (Anderson: "in the one linkage class case `T_1` can only
   consist of a union of linkage classes if `T_1 ≡ C`"), so (i) is forced — **and then clause 2 gives
   all reactions, and criticality contradicts it.** Hence no such partition exists and the argument
   closes.
5. **Without `SingleLinkageClass`, `T_1` can be a proper union of linkage classes, and then (i)
   fails, clause 2 does not give all reactions, and the Lemma 4.8 contradiction evaporates.** This is
   the case the hole is in. ∎

**Reading.** `IsCriticalSiphon P` and the mechanism "escape the face `SiphonFace P` and shrink it"
are **not complementary**: the descent estimate the file names is *excluded at precisely the faces
the hole quantifies over*. `hcodim : 2 ≤ finrank ℝ (stoichSubspace.map (projOn Pmax))` is the
packaged form of "this is not a facet", i.e. exactly the codimension range in which the `ℓ = 1`
collapse of Lemma 4.8 is unavailable. **Hole A is the case Anderson's method cannot see**, and this
is a proof of that, not a conjecture.

### 4.4 A second, smaller honesty point

`hmaxExact` and `hzcard` do **not** identify Anderson's `U = {i : z_i = 0 for some z ∈ ω}` with
`Pmax = zero set of wmax`. `U` is a *union* of ω-point zero sets; nothing in the hole's data says
`U` is itself an ω-point's zero set, so `hmaxExact` (which speaks only about ω-point zero sets
containing `Pmax`) is silent about `U ⊋ Pmax`. Identifying them needs a separate step (e.g. that `U`
is a siphon *and* `Pmax` is maximal among siphons, which `hzcard` does not give — `hzcard` bounds
zero **sets of ω-points** by cardinality, and `Network.siphonFace_forwardInvariant_of_relEntropy_le`
is what shows a siphon face is forward-invariant, not that its zero set is realised).

### 4.5 Cross-reference: the `projOn` / coordinate-deletion bridge (`hcodim`)

Upstream rulings **A-49** (bridge not needed) and **A-50** (bridge structurally
*impossible*, not merely absent) already answer this. **My A-52 does not depend on it.**
Upstream **A-47** concludes that the missing object is "a growth comparison across face
dimensions". **A-52 below is the sharpest possible complement to that: the growth comparison is
not merely unbuilt, it is *excluded* at exactly the faces Hole A quantifies over.**
The orchestrator had flagged, graded `[H]`, that `CRNT/Dynamics/FaceCodimension.lean` imports
`CRNT.Dynamics.FacetRepulsionAndersonShiu` and **no `Geometry` module at all**, so nothing bridges
the hole's `projOn P` projection to the coordinate-deletion projections in
`ProjectedFaceDimensionCode`. **The import half of that claim is now `[V]`** (file-content
evidence, my own read this session): `FaceCodimension.lean:1` is the single import
`import CRNT.Dynamics.FacetRepulsionAndersonShiu`, with no `Geometry` import.
`highCodimension_of_not_facet` is at `FaceCodimension.lean:174`, and its consumer in the hole's
closure is `GlobalAttractorTheorem.lean:1554`.

**Nothing in this document depends on that bridge, and nothing here is blocked by it.** The only
use I make of `hcodim` is as a *statement about the face* — `finrank ℝ (stoichSubspace.map
(projOn Pmax)) ≥ 2`, the literal content of `HighCodimensionSiphonFace.lean:131`, i.e. "the
`Pmax`-face is not a facet". That is the codimension range in which Lemma 4.8's `ℓ = 1` collapse is
unavailable (§4.3 step 5). Whether `projOn P` is *the same projection* as the coordinate-deletion
one is a separate question on a different route. If the answer turns out to be no, §4.3 is
unaffected: I never transport a geometric claim across the two projections — I only observe that
the hypothesis says "codimension ≥ 2".

### 4.6 Sharpening of A-52 — **every** zero set in the ω-family is critical, not just `Pmax`

`CRNT/Dynamics/GACOmegaPositive.lean:121-124` shows `isCriticalSiphon_zeroSet_of_mem_omegaLimit`
takes an **arbitrary** `w ∈ omegaLimit atTop ϕ {x₀}` and an **arbitrary** nonempty zero set
`(hzeroSet : ∀ s, s ∈ P ↔ w s = 0)` — it does not mention `Pmax`, `hzeroMax` or `hmaxExact`. So for
*every* `w ∈ ω` with a nonempty zero set, that zero set is a critical siphon.

Now apply §4.3 step 1 to an **arbitrary** member `Z = zeroSet(w)` of the family, not just `Pmax`.
Step 1 needs only `φ(t_n) → w` (which is what `w ∈ ω` gives, with `t_n → ∞`) together with
`φ_i(t_n) → 0` for `i ∈ Z` — which is exactly `w i = 0`. No maximality, no `hzcard`, no `hmaxExact`.
Therefore:

> **If hole A's hypotheses are jointly satisfiable, then every ω-limit point with a nonempty zero
> set has a critical-siphon zero set — so the ω-limit family consists *entirely* of critical siphon
> faces, with no non-critical member anywhere in it.**

This is where the two findings meet. Per `ArchSrEscape`'s correction (their singleton-ω refutation
does **not** generalise: at `|ω| = 2`, `zeroSet(w₁) = {s₁}`, `zeroSet(w₂) = {s₁,s₂}` makes the
strict-shrinking disjunct satisfiable), the descent is *enabled* by spread in
`{zeroSet(w) : w ∈ ω}`. §4.6 says that spread runs **exclusively among critical siphon faces** —
which is precisely the configuration A-52 proves Anderson's argument cannot address. So the two
results are not merely consistent: **the structure that would make the descent work is the same
structure that kills the named mechanism.** Any replacement argument must handle a *family* of
critical faces, not a single one, and cannot rely on the conservation relation that
`IsCriticalSiphon` forbids.

---

## 5. Is the estimate FALSE?

**No — `ComparableGrowthDescent` is not refuted, and `descend` is not a false statement.** It is
*equivalent to the hole's conclusion* (§1, `SiphonDimensionDescent.lean:368-377`). There is nothing
false to find in it. What is refuted is the **attribution and the stated mechanism**:

* **(N1)** Anderson arXiv:1101.0761 does not contain a siphon-dimension descent. **[V]** — all 23
  pages read this session; transcription §1.
* **(N2)** "the strict shrinking is forced by comparing the growth of the relative-entropy Lyapunov
  family across an escape from the face `SiphonFace P`" (`SiphonDimensionDescent.lean:120-122`) is
  **not a mechanism that works**, independent of formalisation: at a critical siphon face,
  Anderson's tier argument's necessary conservation relation is excluded by
  `IsCriticalSiphon`. §4.3. **[V]** by the two-step derivation above, whose only inputs are
  transcription §2.6/§2.9 and `CRNT/Dynamics/Siphon.lean:84-87`.
* **(N3)** The mechanism Anderson *does* use (E1, `LyapunovFamilyStrictlyDecreases`) is available
  in principle and closes **Anderson Thm 4.10**, not the descent — and needs
  `N.numLinkageClasses = 1`, which the hole does not supply and does not imply.
  **[V]** — the only non-tree input is `numLinkageClasses`'s definition (`LinkageClass.lean:93-94`);
  the hole's hypothesis list (`HighCodimensionSiphonFace.lean:111-133`, read this session) contains
  no linkage-class datum, and `hcodim` bounds a face dimension, not `ℓ`.

### 5.1 Search space actually covered

* **Complete read** of arXiv:1101.0761v6, 23 pages, §§1–5 + references. Every `Lemma`,
  `Theorem`, `Definition` numbered 3.3–4.12 transcribed (transcription §2.2–2.11).
* **Full-tree grep** (this session) for `relEntropy|RelEntropy|relative entr` → 60+ sites across
  `CRNT/Dynamics/`; for `reducedNetwork|reducedReactionNetwork|projectedDynam|ProjOn|
  boundedMassAction|BoundedMassAction` → exactly **one** hit
  (`FacetRepulsionAndersonShiu.lean:315-317`, the linear `projOn`); for
  `tier|Tier|reduced network|ReducedNetwork|stoichRank` → 131 files, the only substantive tier
  module being `TierPersistence.lean`.
* **Import-closure computation**: hole closure = 179 modules; `TierPersistence` **OUT**,
  `CriticalSiphonDissipationRepulsion` **OUT**, `FacetRepulsionAndersonShiu` **IN**,
  `SingleLinkageGAC` **IN**, `EscapeSiphonFace` **IN**.
* **Hole hypothesis list** read at `HighCodimensionSiphonFace.lean:111-133`.

### 5.2 Exactness

All statements above are exact (`ℤ`/`ℕ`/linear algebra over `ℝ`, no floating point, no
numerics, no `native_decide`). The tier ratios are `Real.exp ((n:ℝ) * (complexWValue w y -
complexWValue w y'))` — exact in `TierPersistence.lean:295-303`, read this session — and the
domination constants `q_{1,n}, q_{2,n}` are only ever used with `q_{1,n} → ∞`, so **no rate estimate
is lost by not formalising them numerically.**

### 5.3 What was left unsearched

* Anderson 2008 (arXiv index not fetched) — the entry-time / persistence route. Could in principle
  supply a *different* mechanism for excluding a critical-siphon face, but its stated subject is
  global asymptotic stability for a class of *globally persistent* systems, i.e. the conclusion,
  not a descent. Not pursued; would be the next thing to check.
* Anderson–Shiu 0903.0901 beyond the repository's own use at `FacetRepulsionAndersonShiu.lean`
  (codimension 1). `hcodim` puts hole A strictly above that case, so this is unlikely to help, but
  the paper was not re-read this session.
* Craciun v3 §8 Step 2 (ZSH exhaustiveness) — the alternative to the descent, already covered by
  `research/HOLEA-FRAMING.md` F-1/F-2 and DEAD-ENDS A-10/A-15.
* Whether a *multi-linkage* replacement for Lemma 4.8 exists in the literature. Anderson closes
  his own paper by naming exactly this as the open point (`a1101.pdf:389`); the weak dynamic
  non-emptiability line (Sontag, arXiv:1009.0720, ref [25]) is the natural place, not read here.

---

## 6. If someone wants to build it anyway — the minimum honest build order

Each step is a real, separable, sizeable piece. None of it is a "reduction".

1. **Projected dynamics for a species subset `U`.** A *new* `Network`-like structure on `U` with
   kinetics `κ_k(t) := Σ_{i : z_k|_U = z_i|_U} κ_i · (x(t)|_{U^c})_{(z_i')|_{U^c}}` (eq. 3.7), plus
   the derivation that `x|_U` solves it. Requires the time-dependent-rate layer, which does not
   exist (B2). **This is the true floor of the route.**
2. **`IsPartitionedAlong`** (Def 4.1) + **Lemma 4.2** as a compactness argument on the finite
   `N.complexes`. Careful with the sign convention (§2.2) and with `TierPersistence`'s opposite
   convention. `TierPersistence.lean` gives `tierMonomial` and the exponential special case, but not
   the general subsequence lemma, and its open flag is stronger.
3. **Stiemke (Lemma 4.3)** over `ℝ^m`, then **Theorem 4.6**. The log-growth argument at
   `a1101.pdf:249-255` is the analytic heart: `Σ c_k/m_k · v_k · ln(x_n|_U) → +∞` against a
   two-sided bound.
4. **E1 (C1)** from 2+3: the eq. (4.8)/(4.9) split and the weak-reversibility path with conditions
   1–5 (`a1101.pdf:308-312`). Purely combinatorial + the `η` bound.
5. **E2 (Lemma 4.8)** — and **stop here**: it is the only step that cannot be done without `ℓ = 1`.

So the floor is real and the ceiling is `SingleLinkageClass`. That is the honest shape of the route.

---

## 7. Ledger entries — **already landed** as `A-51`, `A-52`, `A-53`

`A-40` is used **twice** in `research/DEAD-ENDS.md` (lines 873 and 992) and `A-41`/`A-42` are also
taken (lines 1008, 1040), and A-47-A-50 were taken upstream while I worked, so the
numbering starts at **A-51**. The three entries below are appended
to `research/DEAD-ENDS.md` in this same commit; the text there is the authoritative copy.

**A-51. Anderson arXiv:1101.0761 contains no siphon-dimension descent. [V]**
*found-by:* `arch-sr-descent` · *round 2* · *revive-when:* a citation to an actual Anderson descent
paper is produced (see A-52).
All 23 pages read. No cardinality descent, no iteration over faces; the word *siphon* appears once,
in background. The residue's docstring at `SiphonDimensionDescent.lean:25-27` and `:120-122`
attaches Anderson's name to a mechanism that is not his.
**Evidence:** `research/papers/anderson-1101-0761-transcription.md` §§1–2, with page anchors.

**A-52. `IsCriticalSiphon` and the named descent mechanism are mutually exclusive at the same
face. [V]**
*found-by:* `arch-sr-descent` · *round 2* · *revive-when:* never as stated.
If the escape face `U` is a siphon that is not critical, a conservation relation `w ≥ 0` with
`supp w = U` orthogonal to all reaction vectors exists and contradicts `w·φ(t)` being constant while
`w·φ(t_n) → 0` — with no tiers at all. So the only case reaching the tier machinery is `U`
**critical**, and there Anderson's Lemma 4.8 needs `T_1 ≡ C` to upgrade Definition 4.5's
same-tier clause to all reactions; `T_1 ≡ C` is forced only by `numLinkageClasses = 1`.
**Hole A's `Pmax` is exactly such a critical face, and `hcodim` is exactly the codimension range
where the `ℓ = 1` collapse is unavailable.** Hole A is the case the method cannot see.
**Evidence:** transcription §2.6, §2.9; `CRNT/Dynamics/Siphon.lean:84-87`.

**A-53. `CRNT/Dynamics/TierPersistence.lean` is outside hole A's import closure and has the
opposite tier sign convention. [V]**
*found-by:* `arch-sr-descent` · *round 2* · *revive-when:* someone reuses it for Anderson Def 4.1.
Closure computed: 179 modules, `TierPersistence` OUT (it is in `CRNT.lean:512`). Its
`TierStrictBelow` (`:34-35`) is `ratio → 0`, i.e. Anderson's 4.1(ii) with tier names reversed —
the same direction hazard as A-2. Its own open flag is `EveryTransversalTierSequenceHasDirectionWitness`
(`:191-192`), **stronger** than Anderson's Lemma 4.2.

---

## 8. Certification of the negative result

* **Search space:** complete read of arXiv:1101.0761v6 (23 pp., §§1–5 + references); full-tree greps
  for `relEntropy`, tier/reduced-network/projection primitives, and `numLinkageClasses`; exact
  import-closure computation for hole A (179 modules).
* **Arithmetic:** none used. No numeric estimate is involved in any of N1–N3; the `q_{i,n}` constants
  are used only in the limit. No floating point anywhere in this document.
* **Left unsearched:** Anderson 2008 (SIAM J. Appl. Math. 68), Anderson–Shiu arXiv:0903.0901 beyond
  the repo's own codim-1 use, Craciun v3 §8 Step 2, and the weak-dynamic-non-emptiability line for a
  multi-linkage replacement of Lemma 4.8. Listed with reasons in §5.3.
* **No claim in §0, §4.3 or §5 rests on an unread source.** Anderson 2008 and Anderson–Shiu are
  marked `[NOT ACCESSIBLE]` in the transcription and are used nowhere in the argument.
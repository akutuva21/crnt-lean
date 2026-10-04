# Hole A: mining the 151 proved-but-unused modules

**Agent:** `FormBarrier-2` · **round 2** · **branch** `research/FormBarrier-2`

**Evidence grades** follow `research/README.md` §10. Everything marked `[M]` is a `file:line` I
opened myself in this session in the worktree `/Users/akutuva/Documents/Proofs/crnt-wt/FormBarrier-2`.
Anything marked `[H]` is relayed and must not be relied on. **No line number in this document came
from a peer or from a prior document** except where explicitly bracketed `[relayed]`.

**Method.** The source list is `docs/hole-reachability.md` (branch `research/infrascaffold`) lines
2292–2442, "Hole A: 151 modules in the import closure, never used". I re-derived the closure
independently by BFS over `^import CRNT...` lines from `CRNT.Dynamics.HighCodimensionSiphonFace`
and got **179 modules**, consistent with the generated doc's 178 ± one module of drift. Five
read-only scouts mined disjoint bands (Geometry, Dynamics, Equilibria/Theorems/Flux/Subnetwork/Stoich,
Deficiency/Graph/LinearAlgebra/Decision/Kinetics, Oscillation/Stochastic); I read the fan, the
inclusion, `SiphonDimensionDescent`, `GACOmegaPositive`, `SiphonFaceWeakReversibility`,
`PersistenceTheorem`, `PersistenceConfined`, `ConfinedInvariance`, `BoundaryDescent`,
`GenuineConfinement`, `ComplexBalanceLinearStability`, `ConservationLaw`, `SiphonConservation`,
`SiphonAutocatalysis`, `ToricBarrierTrapping`, `ToricFan`, `FanFaceLattice`, `StrictInflow` and
`FaceCodimension` myself.

---

## 1. THE FAN VERDICT — definitive, both assets, stated plainly

**The descent cannot use `ComplexBalanceStoichFan` (20 decls) or `ComplexBalanceStoichFanInclusion`
(38 decls). Three independent reasons, each fatal on its own.** Nobody should re-open the fan route
a fourth time. Details, all `[M]`:

### 1.1 Wrong conclusion shape, wrong index. There is no siphon and no cardinality anywhere in either module.

`grep -in "siphon\|omega\|ZeroSet" CRNT/Dynamics/ComplexBalanceStoichFanInclusion.lean
CRNT/Dynamics/ComplexBalanceStoichFan.lean` returns **zero matches**. I ran it. Neither file
mentions `Siphon`, `omegaLimit`, `ZeroSet`, or `card`. `descend`'s right disjunct is
`∃ Q : Finset S, Q.Nonempty ∧ N.IsCriticalSiphon Q ∧ Q.card < P.card ∧ N.SiphonCarried ϕ x₀ Q`
(`CRNT/Dynamics/SiphonDimensionDescent.lean:128-131`). Nothing in either module produces, bounds or
relates `Finset S` cardinalities, and nothing in either module quantifies over `omegaLimit`.
**These are velocity-field theorems. The descent is a statement about species sets.**

### 1.2 The one live consumer of the fan inside the closure ends in an already-machine-checked-dead criterion.

The chain exists and I traced it: `HighCodimensionSiphonFace.lean:3` imports
`CRNT.Dynamics.ToricBarrierTrapping`, which uses `N.relativeSourceOrderNegativeStoichFan` at
`ToricBarrierTrapping.lean:137, 184, 237, 288, 331, 448, 487`. So **the fan is NOT unused in the
tree** — confirming the A-30 caveat by my own reading, and correcting A-27's headline.

But every theorem in `ToricBarrierTrapping` that converts a fan statement into an ω-limit
statement is one of three packaged criteria, and all three take the coordinate-separation clause
`hsep : ∀ s : S, ∃ ε : ℝ, 0 < ε ∧ ∀ x : Concentration S, x.Positive → …` (`:334`, `:451`, `:490`).
Those are the `hsep` family, killed by **A-26** (compiled `CRNT/Dynamics/UpperRegionFloorRefutation.lean`)
and **A-31** (do not route the `hsep` refutation through the A-28 template). The A-28 template
(`universalPositive_omegaLimit_of_closedPositiveConfine`) does not reach them; the barrier-free
floor-along-orbit lemma does. **Cite both, per A-31.**

### 1.3 `δ` is not the blocker for the selector theorem — this corrects F-5 for *this* theorem — but the fan still buys nothing.

`research/HOLEA-FRAMING.md` F-5 says "the hole supplies **no δ** … 'just pick a δ' is exactly the
unproved strengthening A-12 forbids". **For `massActionVectorField_mem_toricField_…` this is
false.** The proof at `ComplexBalanceStoichFanInclusion.lean:345-349` is

```lean
have hdist : Metric.infDist (-X) (C : Set N.euclideanStoichSubspace) = 0 := Metric.infDist_zero_of_mem hX
have hnear : Metric.infDist (-X) (C : Set N.euclideanStoichSubspace) < δ := by rw [hdist]; exact hδ
```

`hnear` is discharged from `0 < δ`. **Any** `δ > 0` instantiates the selector. F-5 remains right
about the *downstream* consequence — `toricField_mono_delta` (`CRNT/Geometry/ToricFan.lean:86-88`)
shows a larger `δ` gives a *larger*, hence weaker, field, so a vacuous `δ` does not yield a
non-trivial differential inclusion. But the selector is not where `δ` bites, and F-5's phrasing
("the hole supplies no δ") invites a researcher to hunt for a δ that was never needed there.

### 1.4 CORRECTION TO MYSELF, recorded because it nearly became a wrong headline

Mid-analysis I concluded from a grep that **no theorem in `CRNT/` proves forward positivity of a
mass-action solution**, and that this was a third independent killer of the fan route (every
fan-consuming theorem needs `hΓpos : ∀ t, 0 ≤ t → (Γ t).Positive`, at `ToricBarrierTrapping.lean:126,
171, 221, 272, 314, 429, 480`). **That was a wrong grep.** The theorem exists:

```lean
theorem Network.genuineOrbit_pos (N : Network S) (κ : N.RateConstants)
    {Γ : ℝ → Concentration S} (hΓ0 : (Γ 0).Positive)
    (hΓd : ∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) :
    ∀ t, 0 ≤ t → (Γ t).Positive
```
`CRNT/Dynamics/GenuineConfinement.lean:53-56`.

At the hole this is `N.genuineOrbit_pos κ (by rw [hγ0]; exact hx₀) hsol` — which the hole file
**already writes out** at `HighCodimensionSiphonFace.lean:761, 972, 1568, 1618`. **A-35 is
therefore correct in full**: the `:373` instance needs only `hxs`, `hcb`, `genuineOrbit_pos`, and
`0 < δ`, and all four are available at the hole with no extra input. The accompanying
`genuineOrbit_relEntropy_le` (`GenuineConfinement.lean:141-146`) gives
`relEntropy x* (Γ t) ≤ relEntropy x* (Γ 0)` on top of it, also free at the hole.

`ComplexBalanceStoichFan` / `ComplexBalanceStoichFanInclusion` are **real, proved, correctly
instantiable infrastructure with a live consumer and a fully supplied hypothesis list. They are
still useless to the descent, for reasons 1.1 and 1.2, which are about conclusions, not inputs.**

---

## 2. SHORTLIST — genuinely relevant, with exact signatures

These are the only entries I would defend as "usable by the descent". Each was read by me.

### 2.1 The face-mass growth vehicle — the closest thing in the tree to a comparable-growth estimate

This is the most valuable find of the sweep. Two lemmas, and between them they are the *complete
analytic vehicle* for the descent estimate; only the comparison constant is missing.

```lean
-- CRNT/Dynamics/PersistenceConfined.lean:78-81
theorem Network.faceSum_field_le (N : Network S) (κ : N.RateConstants) {P : Finset S}
    (hP : N.IsSiphon P) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Concentration S, x.Nonnegative → (∀ s, x s ≤ B) →
      (∑ s ∈ P, N.massActionVectorField κ x s) ≤ C * faceSum P x
```

```lean
-- CRNT/Dynamics/PersistenceTheorem.lean:137-143
theorem Network.siphonFace_forwardInvariant (N : Network S) (κ : RateConstants N)
    {P : Finset S} {γ : ℝ → Concentration S} {L : ℝ}
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnn : ∀ t, 0 ≤ t → (γ t).Nonnegative)
    (hdiss : ∀ t, 0 ≤ t →
      deriv (fun u => faceSum P (γ u)) t ≤ L * faceSum P (γ t) ∨ faceSum P (γ t) ≤ 0)
    (h0 : γ 0 ∈ N.SiphonFace P) :
    ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P
```

```lean
-- CRNT/Equilibria/ComplexBalanceLinearStability.lean:821-824
theorem le_mul_exp_of_forward_deriv_le {V V' : ℝ → ℝ} {K b : ℝ}
    (hV : ∀ t ∈ Set.Icc (0 : ℝ) b, HasDerivAt V (V' t) t)
    (bound : ∀ t ∈ Set.Ico (0 : ℝ) b, V' t ≤ K * V t) :
    ∀ t ∈ Set.Icc (0 : ℝ) b, V t ≤ V 0 * Real.exp (K * t)
-- and :883-889 forward_lt_of_deriv_nonpos_of_lt, :932-936 forward_le_mul_exp_of_deriv_le_of_lt
```

**Chain.** Take `V = faceSum Pmax`, `L = C` from `faceSum_field_le`. The two hypotheses of
`siphonFace_forwardInvariant` are met (nonnegativity from the orthant-invariance layer,
`massAction_forwardInvariant_nonneg`, named in that module's own docstring at `:132-133`), and
`le_mul_exp_of_forward_deriv_le` closes the scalar comparison. All three Grönwall lemmas are
**hypothesis-free in `V, V'`** — they accept any Lyapunov family, including one indexed by face
dimension, at zero cost.

**The exact remaining gap, stated sharply.** `faceSum_field_le` is available for *every* siphon
`P`, with a constant `C_P` that is `∑ r κ.k r · (max 1 B)^(deg r) · |∑_{s∈P} ν_r s|` — visibly
**monotone increasing in `|P|`**. So the tree gives `C_Q ≤ C_P` for `Q ⊆ P`, i.e. the *wrong*
direction: a smaller face has a *smaller* growth constant, hence grows *slower*. **No theorem in
the tree forces `C_Q < C_P` or relates the two constants at all, and no theorem compares
`faceSum Pmax` with `faceSum Q` across faces.** That single missing comparison is the analytic
content `SiphonDimensionDescent.lean:116-123` describes as "comparing the growth of the
relative-entropy Lyapunov family across an escape from the face `SiphonFace P`". `faceSum_field_le`
is the closest formalisation of "the growth" that exists, and the reason it does not close the hole
is visible in its own constant: **it is an upper bound, and the descent needs a sign.**

The box hypothesis `(∀ s, x s ≤ B)` is not an extra input at the hole: it comes from `hK`/`hmaps`
by exactly the argument `genuineOrbit_pos` already runs (`GenuineConfinement.lean:63-76`,
`isCompact_Icc.exists_bound_of_continuousOn` then `exists_field_lower_bound`).

### 2.2 `CRNT.Dynamics.BoundaryDescent` — one import away, and it is the boundary-relaxed Lyapunov

**Not in Hole A's closure** — I re-derived the closure by BFS and `CRNT.Dynamics.BoundaryDescent`
is **absent** (only `CRNT.lean:388` imports it). It is nonetheless directly relevant and should be
imported by whoever attacks the descent.

```lean
-- CRNT/Dynamics/BoundaryDescent.lean:69-73
theorem Network.relEntropy_antitone_along_solution_of_pos_pos (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} (hpos : ∀ t, 0 < t → (γ t).Positive)
    (hsol : ∀ t s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t) :
    AntitoneOn (fun t => relEntropy xstar (γ t)) (Set.Ici 0)
```

It relaxes `relEntropy_antitone_along_solution` from *positive-everywhere* to *positive on the open
ray `(0,∞)`*. Its own Scope section (`:26-37`) records the wall precisely: **a genuinely
face-confined orbit — one that vanishes on `P` at positive `t` — is not covered**, because
`relEntropy` is never differentiable there, and closing that would need "a boundary dissipation
certificate or an interior-approximation/continuous-dependence argument … neither of which is
available here." **That sentence is the descent's analytic wall, written by the module that got
closest to it.**

### 2.3 `CRNT.Dynamics.ConfinedInvariance` — the box discharge, and the same wall

```lean
-- CRNT/Dynamics/ConfinedInvariance.lean:109-118
theorem Network.siphonFace_forwardInvariant_of_relEntropy_le (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) {xstar : Concentration S} (hxs : xstar.Positive)
    {γ : ℝ → Concentration S} {C : ℝ}
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnn : ∀ t, 0 ≤ t → (γ t).Nonnegative)
    (hrele : ∀ t, 0 ≤ t → relEntropy xstar (γ t) ≤ C)
    (h0 : γ 0 ∈ N.SiphonFace P) : ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P
```

Line `:129-130` states the irreducibility in the module's own voice: "The positivity hypothesis
`hpos` is irreducible here: the relative entropy is differentiable only in the open orthant, so
Lyapunov descent is unavailable on the boundary." Read this as a companion to 2.2.

### 2.4 `CRNT.Dynamics.SiphonAutocatalysis.exists_minimalCriticalSiphon_subset` — cardinality descent, **without carriedness**

```lean
-- CRNT/Dynamics/SiphonAutocatalysis.lean:599-601
theorem Network.exists_minimalCriticalSiphon_subset (N : Network S) {P : Finset S}
    (hP : N.IsCriticalSiphon P) :
    ∃ Q : Finset S, Q ⊆ P ∧ N.IsMinimalCriticalSiphon Q
```

This is the **only genuinely cardinality-decreasing critical-siphon statement in the tree** (its
proof contains the `R.card < Q.card` step at `:626`). It is in Hole A's closure (verified by BFS).

**It does not instantiate `descend`, and the gap is exactly one field:** `IsMinimalCriticalSiphon Q`
gives `IsCriticalSiphon Q` and minimality by inclusion, but **not `N.SiphonCarried ϕ x₀ Q`**, which
requires an ω-limit point vanishing exactly on `Q`. Producing that witness is the whole problem.
Recorded so nobody re-derives the finite combinatorics.

### 2.5 `CRNT.Dynamics.GACOmegaPositive.positiveOmega_or_lowerRankCriticalBoundaryFace` — the descent's *shape*, on the wrong index

```lean
-- CRNT/Dynamics/GACOmegaPositive.lean:196-217  (signature condensed)
theorem Network.positiveOmega_or_lowerRankCriticalBoundaryFace
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : …) (hK : IsCompact K) (hmaps : …)
    (hgenω : …) (hωnn : …) (hωaff : …) (hx₀ : x₀.Positive)
    (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c) :
    (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) ∨
      ∃ w ∈ omegaLimit atTop ϕ {x₀}, ∃ P : Finset S,
        P.Nonempty ∧ (∀ s, s ∈ P ↔ w s = 0) ∧ N.IsCriticalSiphon P ∧
        (N.restrictReactions (N.avoidingSiphonReactions P)).IsComplexBalanced … ∧
        (N.restrictReactions (N.avoidingSiphonReactions P)).stoichRank < N.stoichRank ∧
        N.massActionVectorField κ w = 0
```

**This is `descend`'s disjunction, verbatim in shape** — positive ω-point **or** a reduced object —
and it is the *closest structural analogue in the entire closure*. Its extra hypotheses are all
available at the hole: `hwr` from `weaklyReversible_of_positive_complexBalanced` (used that way at
`GlobalAttractorTheorem.lean:1147`), `hωc` from `exists_relEntropy_const_on_omegaLimit`
(`GlobalAttractorTheorem.lean:1073-1082`). The hole's own audit block says exactly this
(`HighCodimensionSiphonFace.lean:437-441`).

**Why it still does not close anything — two reasons, both structural:**

* **Wrong index.** It descends `stoichRank` of a *subnetwork* `N.restrictReactions
  (N.avoidingSiphonReactions P)`, not the *cardinality* of a carried siphon. `descend`'s right
  disjunct is `Q.card < P.card` on the *same* network `N`. There is no `SiphonCarried ϕ x₀ Q`
  relative to the subnetwork anywhere in the tree.
* **The module itself says the transfer is absent** — `:194-195`: the theorem "does not transfer
  that face equilibrium back into the parent orbit's omega-limit set."

The rank-drop itself is proved and unconditional-on-dynamics:
`restrictReactions_avoiding_siphon_stoichRank_lt`
(`CRNT/Dynamics/SiphonFaceWeakReversibility.lean:184-186`) takes **only** `hcrit : N.IsCriticalSiphon P`.

### 2.6 `CRNT.Dynamics.StrictInflow.massActionVectorField_pos_of_not_isSiphon` — the contrapositive engine, and why it cannot fire

```lean
-- CRNT/Dynamics/StrictInflow.lean:36-39
theorem Network.massActionVectorField_pos_of_not_isSiphon (N : Network S) (κ : N.RateConstants)
    {w : Concentration S} (hwnn : w.Nonnegative) {P : Finset S}
    (hP : ∀ s, s ∈ P ↔ w s = 0) (hns : ¬ N.IsSiphon P) :
    ∃ s ∈ P, 0 < N.massActionVectorField κ w s
```

Strict inward influx at a non-siphon zero set. **It never fires at `Pmax`**, because
`isCriticalSiphon_zeroSet_of_mem_omegaLimit` gives `IsSiphon Pmax` from the hole's own hypotheses.
Listed because it is the natural partner of 2.1 in a face-escape argument, and its non-firing at
`Pmax` is the reason a purely static escape argument cannot start.

### 2.7 `CRNT.Dynamics.ConservationLaw` — proved, and provably cannot help

```lean
-- CRNT/Dynamics/ConservationLaw.lean:78-85
theorem Network.not_critical_conserved_along_solution (N : Network S) (κ : RateConstants N)
    {P : Finset S} (hP : N.IsSiphon P) (hPne : P.Nonempty) (hnc : ¬ N.IsCriticalSiphon P) : …
theorem Network.conservationLaw_const_along_solution (N : Network S) (κ : RateConstants N)
    {w : S → ℝ} (hw : w ∈ orthSum N.stoichSubspace) {γ : ℝ → Concentration S} {t : ℝ} (ht : 0 ≤ t)
    (hsol : …) : ∑ s, w s * γ t s = ∑ s, w s * γ 0 s
```

Tempting ("a conserved quantity pins the siphon") and it is a **dead route with a proof**. The
premise is `¬ N.IsCriticalSiphon P`, and the hole's `Pmax` **is** critical. This is A-40 in
structural form, with the sign made explicit: at the hole the conservation laws live in
`orthSum N.stoichSubspace` and are constant across the compatibility class, so they carry **no
information distinguishing `Pmax` from any other ω-point's zero set**. Recorded so the route is not
re-walked on the strength of its attractive statement.

### 2.8 Everything the fan route needs, all available — and all dead downstream

`FanFaceLattice` (the module that actually consumes the embedding) is real and useful:

* `CRNT.Geometry.deltaCore` (`:127-129`), `deltaCore_mem` (`:149-156`) — the δ-core is a cone of the
  fan (Craciun Remark 4.5);
* `CRNT.Geometry.inner_nonneg_of_mem_toricField` (`:166-179`) and `..._of_mem_deltaCore` (`:182-185`)
  — "a vector in every nearby cone descends against the whole toric field", the descent bridge;
* `CRNT.Network.inner_euclideanMassActionField_nonneg` (`:293`), `..._of_mem_deltaCore` (`:306`).

These are the correct mechanism, and the hole's file already names the refutation that kills them:
`barrier_le_of_mem_omegaLimit` (`HighCodimensionSiphonFace.lean:272`) puts the boundary ω-point
`wmax` into the sublevel, and every piece of the barrier is affine so the sublevel is convex —
**A-16/A-26**. Recorded here only so that "the δ-core exists and is a fan cone" is not mistaken for
"the δ-core is available".

---

## 3. A-28 MARKING — the closed-positive-confinement family

These are genuinely unused and genuinely A-28-unreachable. **Marked, not presented as missed
opportunities**, per the caveat I was asked to carry.

| module | the A-28-shaped theorem |
|---|---|
| `CRNT.Dynamics.GlobalPersistence` | `PersistentOrbit.omegaLimit_positive` — `∀ w ∈ omegaLimit atTop ϕ {x₀}, w.Positive` |
| `CRNT.Dynamics.GACConfinement` | `gac_of_confinement` — confines to a compact positive set |
| `CRNT.Dynamics.GACNoCriticalSiphon` | `gac_of_hasNoCriticalSiphon` — ω = {x*} from `HasNoCriticalSiphon` |
| `CRNT.Dynamics.GACSeparatingCapstone` | `gac_of_separatingConfinement` |
| `CRNT.Dynamics.GACSeparatingRegion` | `gac_of_separatingRegion` |
| `CRNT.Dynamics.GACSeparatingWitness` | `separatingConfinement_of_persistentFrom`, `…_of_omegaLimit_singleton`, `persistentFrom_of_omegaLimit_singleton` |
| `CRNT.Dynamics.GlobalPermanence` | `PermanentOnPositiveClass` and the `StructurallyPermanent` family |
| `CRNT.Dynamics.NoCriticalSiphonPersistence` | derives `PersistentOrbit`, hence the universal form |
| `CRNT.Dynamics.EndotacticPermanence` (not in the 151; in the closure) | `Permanent` family |
| `Theorems.DeficiencyZero.AsymptoticStability` | `omegaLimit_eq_singleton_of_local` |

Per **A-38** and **A-43**: closed positive confines are built throughout the tree and the template
*discharges*. The contradiction needs the caller to **also** supply a boundary ω-point, which the
hole does (`hwmax`, `hzeroMax`, `hPmaxne`). None of the above is refuted; all are **uninstantiable
here**.

## 4. THE `hsep` FAMILY — a different shape, do not cite A-28 for it

Per **A-31**: `hsep` dies by the barrier-free floor-along-orbit argument, not by the
closed-positive-confinement template. Affected unused modules: `CRNT.Dynamics.ToricBarrierTrapping`
(`hsep` at `:334`, `:451`, `:490`) — **not in the 151**; it is used by the hole file. Also
`CRNT.Dynamics.FaceDirectionCone` — **not in the 151**; used. Anyone citing A-28 against an `hsep`
refutation will fail.

---

## 5. FULL TABLE — all 151, grouped

Condensed. "Off" = contributes nothing to a siphon-descent step, with the reason. Read by me or by
a scout whose file-content reading I spot-checked; the descent column is my judgement.

### 5.1 Dynamics (45 modules)

| module | what it actually proves | A-28 | descent |
|---|---|---|---|
| `BoundaryOmegaSiphon` | `isSiphon_zeroSet_of_mem_omegaLimit` — every ω-point's zero set is a siphon | not-A-28 | **yes** — supplies `IsSiphon Pmax` |
| `CriticalSiphonOmega` | `isCriticalSiphon_zeroSet_of_mem_omegaLimit` — `IsCriticalSiphon Pmax` | not-A-28 | **yes** — carriedness→criticality |
| `PersistenceTheorem` | `siphonFace_forwardInvariant` + `faceSum` apparatus | not-A-28 | **YES — §2.1** |
| `PersistenceConfined` | `faceSum_field_le`, `siphonFace_forwardInvariant_confined` | not-A-28 | **YES — §2.1** |
| `ConfinedInvariance` | `coord_le_uniformBox`, `siphonFace_forwardInvariant_of_relEntropy_le` | not-A-28 | **yes — §2.3** |
| `ConservationLaw` | conservation laws are constants of motion | not-A-28 | **yes but dead — §2.7** |
| `SiphonConservation` | `isCriticalSiphon_iff_mem_orthSum` — criticality as Farkas feasibility | not-A-28 | yes — reframes `IsCriticalSiphon` |
| `SiphonFaceWeakReversibility` | avoiding-siphon subnetwork is WR; `restrictReactions_avoiding_siphon_stoichRank_lt` | not-A-28 | **yes — §2.5** |
| `SiphonAutocatalysis` | minimal-critical-siphon / drainable / self-replicable dichotomy | not-A-28 | **yes — §2.4** |
| `GACOmegaPositive` | one positive ω-point ⇒ ω = {x*}; boundary ω-points are face equilibria | not-A-28 | **yes — §2.5** |
| `EscapeSiphonFace` | Butler–McGehee escape → forward-limit critical siphon | not-A-28 | yes — supplies a carried siphon from an escape |
| `StrictInflow` | `massActionVectorField_pos_of_not_isSiphon` | not-A-28 | **yes — §2.6** |
| `IsolatedInvariant` | `maximalInvariantSubset`, `isIsolatedInvariant_of_…` — the `M`/`Nbhd` data `siphonCarried_of_escape` needs | not-A-28 | yes — input to the escape |
| `ThmBGenuine` | neighborhood-descent Nagumo for the genuine flow; `GenuineZeroSeparating` | not-A-28 | yes — a barrier container, not a siphon step |
| `ZeroSeparating` | `ZeroSeparatingRegion` interface (1-D base case) | not-A-28 | off for the descent |
| `ExponentialDecay` | Lyapunov Grönwall wrappers (`le_mul_exp_of_deriv_le`, `hasDerivAt_lyapFun`) | not-A-28 | off — scalars only, no face |
| `ExponentialDichotomy` | stable/unstable subspace dichotomy | not-A-28 | off |
| `SpectralSplitting`, `SpectralSplittingReal` | real/complex spectrum splitting, `isInternal_stable_center_unstable` | not-A-28 | off |
| `RouthHurwitz` | Routh–Hurwitz stability criterion | not-A-28 | off |
| `FirstExit` | exit times, `mem_frontier_exitTime` | not-A-28 | off |
| `FlowConstruction` | builds the cutoff semiflow | not-A-28 | off (hole already has `hϕγ`) |
| `Viability`, `Nagumo`, `SublevelNagumo`, `SublevelInvariant`, `PolyRegionStrictInvariant`, `NegativeInvariance`, `ForwardInvariance`, `ClosedSetNagumo` | inward-pointing / Nagumo machinery for sublevel sets | not-A-28 | off as *siphon* steps; in-engine for a barrier argument |
| `ToricEmbedding`, `ToricEmbeddingOrder`, `ToricInclusion`, `ToricFieldPolar` | toric-inclusion field machinery; `cyclicProjectedVelocity_nonpos_of_rateSeparation` | not-A-28 | off — no ω-limit, no cardinality |
| `MassActionAlgebra`, `MassActionField` | `kineticMap_*`, `massActionVectorField_eq`, field continuity | not-A-28 | off — plumbing |
| `DifferentialInclusion` | `IsInclusionSolution` / `.of_ode` / `.mono` | not-A-28 | off — a repackaging of `hsol` |
| `Persistence`, `PersistenceConfined`, `PersistenceGAC` | `SiphonFace`, confinement, GAC packaging | not-A-28 | see above |
| `GlobalPersistence`, `GlobalPermanence`, `GACConfinement`, `GACNoCriticalSiphon`, `GACSeparatingCapstone`, `GACSeparatingRegion`, `GACSeparatingWitness`, `NoCriticalSiphonPersistence`, `GlobalStability` | permanence / persistence / separating-confinement | **A-28-unreachable** | see §3 |
| `BoundaryOmegaSiphon` dup, `SiphonConservation` dup | — | — | — |
| `ComplexBalanceStoichFan`, `ComplexBalanceStoichFanInclusion` | the source-order fan and the Thm-4.3 embedding | **not-A-28** (A-35 correct) | **NO — §1** |

### 5.2 Geometry (18 modules)

All formalize Craciun v3 §7–§8 in a self-contained convex/Euclidean setting with `Network` as an
input data type. **A grep for `omegaLimit` over the whole `CRNT/Geometry/` directory returns nothing**
— no geometry module quantifies over an ω-limit set, so none can produce a carried siphon.

| module | what it proves | A-28 | descent |
|---|---|---|---|
| `ConeFace` | `IsPolyhedralFan` (`faces_mem`/`inter_common`/`covers`), `IsExposedFaceOf` | not-A-28 | off — the fan predicate itself |
| `ToricFan` | `Fan E`, `toricField`, `coneDual_le_toricField`, `toricField_mono_delta` | not-A-28 | off — **but `:86-88` is what makes F-5's δ argument work** |
| `FanFaceLattice` | `deltaCore`, `inner_nonneg_of_mem_toricField`, `Network.inner_euclideanMassActionField_nonneg` | not-A-28 | **yes — §2.8** |
| `PolyhedralFan` | `coneDual`, bipolar identity, Newton polytope | not-A-28 | off |
| `FanRefinement` (156 decls) | `hyperplaneArrangementFamily`, `fanNormalSet` — a complete dual-FG fan refining any `F`; plus the `oneBit*` recursors | not-A-28 | off — **A-1 applies**: the recursors rank *projected* faces and prove a different theorem |
| `ZeroSeparatingInduction` (294 decls) | Craciun §7.3 chains, the ε̃ scale system (A-4: closed) | not-A-28 | off — **A-2**: `binaryWordValue` is anti-monotone |
| `ProjectedFaceDimensionCode` | `finrank_map_forgetLastCoordinate_bounds` (a coordinate *deletion* between different dimensions) | not-A-28 | off — see §6 |
| `LogProjectiveFaceCompatibility`, `LogProjectiveSmoothSection`, `LogProjectiveSection` | affine/smooth sections of log-projective rays | not-A-28 | off |
| `FaithfulCurve`, `FaithfulCurve2D`, `ZeroSeparatingCurve2D`, `ZeroSeparatingSurface`, `FiniteConeClosed`, `SimplicialConeClosed`, `Endotactic`, `ToricFieldPolar` | 2-D faithful/zero-separating curves; cone closure; endotactic weight certificates | not-A-28 | off — 2-D-specific or cone plumbing |

### 5.3 Equilibria / Theorems.DeficiencyZero / Flux / Subnetwork / Stoich (20 modules)

| module | what it proves | A-28 | descent |
|---|---|---|---|
| `ComplexBalanceLinearStability` | entropy-Hessian Lyapunov, sum-of-squares, **forward-Grönwall comparators** | not-A-28 | **YES — §2.1, the `V'` vehicle** |
| `AsymptoticStability` (in closure, not in the 151) | `relEntropy_coord_le`, `orbit_relEntropy_le`, `omegaLimit_eq_singleton_of_local` | `omegaLimit_eq_singleton_of_local` **A-28** | yes — coercivity |
| `ComplexBalanceGeometry` | toric parametrisation, tangent-space codimension `|S| − stoichRank` | not-A-28 | off — static, at `xstar` |
| `Wegscheider`, `DetailedBalanced`, `DetailedBalanceToric`, `DetailedBalanceEntropy`, `DetailedBalanceLinearStability` | detailed-balance ⇒ complex balance; Wegscheider potentials; entropy | not-A-28 | off — static |
| `TreeConstants` (56 decls) | directed Matrix–Tree theorem at the **complex** level | not-A-28 | off |
| `SteadyState`, `Flux.Cone`, `Flux.Elementary`, `Stoich.Vector` | steady states; flux cones; elementary flux modes | not-A-28 | off |
| `ReactionRestriction` | `massActionVectorField_partition`, `restrictReactions_stoichSubspace_le` — the face-restricted subnetwork | not-A-28 | yes — infrastructure for §2.5 |
| `Toric`, `Birch`, `BirchExistence`, `Existence`, `PositiveKernel`, `Statement`, `Confinement` | deficiency-zero ⇒ GAC; positive kernel vectors | not-A-28 | off — wrong branch (Hole A is the *critical-siphon* branch) |

### 5.4 Deficiency / Decision / Graph / LinearAlgebra / Kinetics / Basic (≈41 modules)

**Off-topic, confirmed.** Four bands: reaction-graph combinatorics (`Graph/*`, `Decision/*`,
`Combinatorics.DigraphExcess`, `Basic.Reaction`); deficiency-index bookkeeping (`Deficiency.Definition`
through `LinkageDeficiency`, `ExactSequence`, `CycleExactSequence`, `KernelDimension*`); chemistry-free
linear algebra (`LinearAlgebra/*`, `Multistationarity.PMatrix`); oscillation/stochastic kinetics
(`Kinetics.General`, `Generalized`, `MassActionJacobian`).

**The band (c) kinetic-Laplacian kernel modules are a trap and are now recorded as DEAD-ENDS TRAP
entries**: `ClosedSetKernel`, `Consistent`, `ConsistentWR`, `Drainage`, `KineticBlock`,
`PerClassKernel`, `SignedDrainage`, `SteadyStateKernel`, `TerminalKernelBound`,
`TerminalKernelDimension`, `TerminalReachable`, `TerminalSLC`, `TerminalSLCKernel` state their
"support contained in a set" conclusions about `b : N.ComplexIdx → ℝ` on the **COMPLEX** space, never
about `x : Concentration S`. Their statements *look* like they fit `hmaxExact` / `Pmax` and do not.
Two scouts working disjoint scopes reached this ruling independently.

### 5.5 Oscillation / Stochastic (22 modules)

**Off-topic, confirmed.** Periodic orbits, Hopf/Bifurcation predicates (`Oscillation.*`), and
Markov-chain ergodic theory (`Stochastic.*`: product-form stationary measures, kernels,
`RegionPrimitive`). Verified: **zero** of the 22 files contain the token `omegaLimit`, and **zero**
of the `Stochastic` files contain `massActionVectorField`, `HasDerivAt`, or `trajector`. The
Anderson–Craciun–Kurtz product-form tower is substantive and real and is nonetheless off-topic here:
it concerns stationary measures, not the ω-limit set of a bounded mass-action trajectory.

---

## 6. Correction to the orchestrator's broadcast item 3 — the `projOn` / `forgetLastCoordinate` bridge does not bind

Broadcast item 3 asked whether a bridge between the hole's `projOn Pmax` projection and
`ProjectedFaceDimensionCode`'s coordinate-deletion projections binds. **It does not**, and the reason
is stronger than absence:

* `projOn` is an **endomorphism** on a fixed species space, `projOn W p s = if s ∈ W then p s else 0`;
  `hcodim` is `2 ≤ finrank ℝ (N.stoichSubspace.map (projOn W))` (`HighCodimensionSiphonFace.lean:131`).
* `forgetLastCoordinate` maps `(Fin (n+1) → ℝ) →ₗ[ℝ] (Fin n → ℝ)` — **two different ambient
  dimensions**.

Matching them requires an isomorphism `S ≃ Fin (n+1)`, i.e. an ordering of the species, and
`Pmax : Finset S` is unordered. **The bridge is not a forgotten lemma; it does not typecheck as a
single map.** Its working theorem is a two-sided *inequality*
(`finrank_map_forgetLastCoordinate_bounds`), not an equality, so even with an ordering chosen it would
not transfer `hcodim` exactly.

And it is moot anyway: `hcodim`'s entire documented use is `hcodim → {hcard, hrank}`, discharged
inside the hole file by `two_le_card_of_two_le_finrank_map_projOn` and
`stoichRank_ne_one_of_two_le_finrank_map_projOn`, recorded in the file's own audit block at
`:1023-1028`. `[relayed: the two theorem names and the `:1023-1028` audit pointer came from a scout;
I did not open those lines myself]`

---

## 7. WHAT I SEARCHED FOR AND DID NOT FIND

Stated explicitly, because a negative result is only as good as its search space.

1. **Any theorem relating the growth constants of two different siphons.** `faceSum_field_le`
   produces `C_P` for a given `P`; nothing compares `C_P` and `C_Q`. Searched: all of `CRNT/Dynamics`,
   all of `CRNT/Equilibria`, `grep -rn "card <\|\.card_lt\|strictly smaller\|smaller siphon"` over
   `CRNT/` — the only `card <` in the dynamics layer is `SiphonAutocatalysis.lean:626` (§2.4).
2. **Any theorem producing a `SiphonCarried` witness for a smaller set.** `SiphonCarried` appears in
   exactly three places in `CRNT/`: its definition (`SiphonDimensionDescent.lean:61-63`), its two
   constructors (`siphonCarried_of_escape`, `isCriticalSiphon_of_siphonCarried`) and the hole file's
   own `exists_smaller_carried_siphon_of_zeroSet_inside`. All take the witness point as input.
3. **Any forward positivity theorem.** It exists — `genuineOrbit_pos` — and I initially missed it.
   Recorded as a lesson in §1.4 rather than hidden.
4. **Not searched:** the five unassigned stochastic fluctuation modules (`PoissonFluctuation`,
   `KurtzScaling`, `KurtzFluidLimit`, `TimeChangedFluctuation`, `UniformizedConvergence`), flagged
   by a scout as the Craciun large-deviation angle. I did not open them. If anyone wants the
   fluctuation angle for Hole A, that is the unmined ground.

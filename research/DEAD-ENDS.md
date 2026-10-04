# Negative-results ledger

**Branch of record:** `holes`. **Objective:** `python3 research/scripts/measure.py --no-gates` → `holes = 0`.
**Holes:** **A** = `CRNT/Dynamics/HighCodimensionSiphonFace.lean:135`,
`Network.exists_positive_omegaPoint_of_highCodimension_siphonFace` (Craciun v3 Theorem B / Global
Attractor Conjecture). **B** = `CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8607`,
`Network.stronglyConcordant_fullyOpen_of_trueSRCriterion` (Shinar–Feinberg true-SR criterion).

This file is the swarm's memory of what does **not** work. It exists because the most expensive
thing in an exploratory proof effort is re-walking a route that was already killed, and because the
prior art for that knowledge is scattered across `HANDOFF_gac_hole.md`,
`docs/gac-bridge-gap-analysis.md`, `docs/gac-v3-face-fill-plan.md`, module docstrings in
`CRNT/Dynamics/HighCodimensionSiphonFace.lean` and `CRNT/Multistationarity/`, and `+`-annotated
commits. **If you are about to spend a round on a route, grep this file first.**

The companion file [`routes/negative-checklist.md`](routes/negative-checklist.md) lists the
routes currently being walked, so a new researcher can tell "dead" from "in progress".

---

## 0. How to read the verification grade

Every entry carries exactly one grade. **The grade is about the failure, not about the
surrounding theorem.**

| grade | meaning | what you may conclude |
| --- | --- | --- |
| **[M] machine-checked** | The *failure itself* is the content of a Lean declaration in the tree — a `theorem`, a `¬`, a `False`, an unsatisfiability lemma. Re-deriving it will not help. | The route is dead. Do not re-walk it. Cite the declaration. |
| **[S] source-checked** | A documented fact about the *paper*, checked against the published source (Craciun v3 arXiv:1501.02860v3, Shinar–Feinberg). | The route is dead *as stated in that paper*. You may re-open it only by proving something the paper does not say. |
| **[N] narrative-only (hearsay)** | A claim recorded in a docstring or in this repo's markdown that was **never formalized**. Possibly paraphrased by a prior agent and possibly wrong. | **Do not treat as settled.** Verify it before building on it — or spend the round verifying it, which is itself worth +30 if you refute it. |

The [N] entries are deliberately marked and are ~40% of the file. That ratio is itself a finding:
this project's dominant failure mode is an LLM producing a beautiful, elaborating, meaningless
proof, and the unformalized negative claims are exactly where that shows up.

A specific trap: several modules carry a *proved* theorem whose docstring says "this does not
close the frontier branch". The **theorem is [M]**; the **"does not close it" is [N]**. Entries
below grade the claim actually being asserted, and say which is which.

### Deduplication note

Sources overlap heavily. `HANDOFF_gac_hole.md` §6, the `## The packaging audit against Craciun
v3` block of `HighCodimensionSiphonFace.lean`, and `docs/gac-v3-face-fill-plan.md` all restate the
same convex-barrier obstruction. That is **one** entry (#A3), not three. Where a later source
adds machine-checked content to an earlier narrative claim, the entry is graded on the strongest
form and both sources are cited.

---

## 1. Hole A — `exists_positive_omegaPoint_of_highCodimension_siphonFace`

### A1. The three packaged barrier criteria cannot be instantiated: any `hsep` instantiation derives `False`

* **Hole:** A. **Grade: [M]**
* **Tried:** every packaged criterion — `exists_positive_omegaPoint_of_convex_tiles`,
  `..._of_selfConsistent_normals`, `..._of_blueprintData` — from the residual's hypotheses, via
  the barrier engine `CRNT.Dynamics.ToricBarrierTrapping`.
* **Why it fails:** all three demand a separation clause `hsep`: a uniform coordinate floor
  `ε > 0` on **every** positive compatible point of the closed sublevel `{barrier ≤ R}`.
  `hstart` puts `x₀` in the sublevel and `barrier_le_of_toric_descent_in_band` puts the boundary
  ω-point `wmax` there too; every barrier piece is affine so the sublevel is convex, and the
  segment `x₀/n + (1−1/n)·wmax` stays inside while taking the value `x₀ s / n → 0` at any
  `s ∈ Pmax`.
* **Evidence:** `hsep_fails_of_boundaryPoint_mem_sublevel` (`HighCodimensionSiphonFace.lean:184`),
  `barrier_le_of_mem_omegaLimit` (`:272`); narrative `HighCodimensionSiphonFace.lean:137–174`;
  `docs/gac-bridge-gap-analysis.md`. Verified by `research/scripts/checkmod.sh
  CRNT/Dynamics/HighCodimensionSiphonFace.lean`.
* **What would make it work:** nothing — any instantiation proves *full* permanence, which
  `wmax` with `Pmax ≠ ∅` refutes. The conclusion sought is strictly weaker (a positive ω-point
  **in addition to** the boundary ones).
* **Found by:** GAC chain, 2026-09-28 (source file last touched 2026-09-28; `docs/gac-bridge-gap-analysis.md`).

### A2. The theorem's own conclusion is incompatible with `PersistentFrom` — the hole *is* v3's unproved "Step 4"

* **Hole:** A. **Grade: [M]** (the refutation); the surrounding provenance claim is **[S]**.
* **Tried:** closing the residual by exhibiting the compact forward-invariant `K_{x₀} ⊂ ℝⁿ_{>0}`
  that Craciun v3 §4 asserts verbatim ("there exists a compact forward invariant region
  `K_{x₀} ⊂ ℝⁿ_{>0}` such that `x₀ ∈ K_{x₀}`").
* **Why it fails:** such a `K₀` must contain `wmax` (ω-limit ⊆ closure of the trapped orbit ⊆
  `K₀`) while every point of `K₀` is strictly positive. Since `hzeroMax` gives `wmax s = 0` for
  `s ∈ Pmax` and `Pmax` is nonempty, the residual's hypotheses are *inconsistent* with
  `PersistentFrom`. Any proof of the hole is a proof of v3's §4 Step 4 — which the paper states
  but never carries out (§8 stops after Steps 1–2; there is no "§8 Step 4").
* **Evidence:** `not_persistentFrom_of_mem_omegaLimit_notPositive` (`:407`), with
  `omegaLimit_meets_positive_of_permanent` as the converse. Provenance: narrative `:1439–1490`,
  and the correction recorded from the v3 source (`[GacLit] 19:47`).
* **What would make it work:** supply a *non-convex* upper region with a uniform coordinate floor
  and prove the orbit never meets the zero-separating surface — the shape
  `exists_positive_omegaPoint_of_upperRegion` (`:1596`) already consumes via
  `orbit_stays_in_upperRegion` (`:1508`) and `persistentFrom_of_upperRegion` (`:1538`). That route
  avoids `hsep`, `hMclass` and convexity entirely and is **the live branch-(2) route**.
* **Found by:** GacDescend / GacRegion, 2026-09-28.

### A3. A globally homogeneous convex polyhedral barrier (max-of-affine) is impossible in dimension ≥ 3; unweighted zonotope vertices fail even in dimension 2

* **Hole:** A. **Grade: [M]**
* **Tried:** normals `n_C ∈ C` for each cone of the arrangement fan with `⟪n_C, X⟧ ≥
  ⟪n_C', X⟧` for all `X ∈ C` (Craciun Lemma 9.5 + the §4 reduction), i.e. the face points of a
  polytope whose normal fan refines the fan; matching across a wall forces the zonotope edge
  structure, so the weights solve a linear program.
* **Why it fails:** three unit vectors pairwise at inner product `c < 1` are a basis, so all
  eight sign vectors are realizable; the LP constraints collapse to strict diagonal dominance
  `w_k ≥ c(w_i + w_j)`; summing gives `W ≥ 2cW` with `W > 0`, hence `c ≤ 1/2`. At `c = 3/5`
  this is a contradiction.
* **Evidence:** `ConvexBarrierObstruction.not_exists_weights_gram` (`:79`),
  `not_exists_weights_vector` (`:122`), non-vacuity witness `witness_gram_posDef` (`:144`);
  `HANDOFF_gac_hole.md` §4 and §6; numerical cross-checks in
  `scripts/probe_zonotope_cone_selection.py`.
* **What would make it work:** a **bounded** window. Craciun's own construction lives in
  `[0,M]ⁿ` (log coordinates bounded below by `log ε₀`), where the constant offsets `b_i` *can*
  repair the violations — precisely the step that fails on an unbounded cone. So the obstruction
  kills the *global* convex barrier and the zonotope ansatz, **not** the paper's route.
* **Found by:** GAC chain, `ConvexBarrierObstruction.lean` 2026-09-24/28; handoff 2026-09-27.

### A4. Anderson–Shiu quadratic face mass is not monotone at codimension ≥ 2

* **Hole:** A. **Grade: [M]** for the monotonicity failure (formal argument in
  `HANDOFF_gac_hole.md` §6 and `HighCodimensionSiphonFace.lean:39–50`); **[N]** that "no
  strengthening of the estimate can cover it".
* **Tried:** pushing the existing `facet_repelling_near_facet_point` argument into the
  high-codimension branch by using `∑_{s ∈ Pmax} x s²` as the Lyapunov quantity.
* **Why it fails:** `facet_repelling_near_facet_point` needs every reaction vector restricted to
  `Pmax` to be a multiple of one direction `v`, i.e. exactly `finrank (stoichSubspace.map (projOn
  Pmax)) = 1`. Under `hcodim` the restricted vectors span at least a plane, and the leading term
  of the derivative is a quadratic form in the approach direction `u ≥ 0` whose sign varies with
  `u` — already for a reversible pair inside the face with equal rate constants it is
  `−c(u_A − u_B)²`.
* **Evidence:** narrative `HighCodimensionSiphonFace.lean:39–50`; `HANDOFF_gac_hole.md` §6.
  The span-one hypothesis is formalized (`FacetRepulsionAndersonShiu.exists_mem_speciesSupport_ne_zero_of_pSemiflow`,
  `:67`).
* **What would make it work:** a surface whose normal turns with the direction of approach —
  which is the whole point of a zero-separating hypersurface, i.e. route A2/A5.
* **Found by:** GAC chain, ≤2026-09-27.

### A5. `hMclass` (bounded positive compatibility class) is not derivable — false off conservative networks

* **Hole:** A. **Grade: [M]** (`CRNT.Examples.OpenSystem.exists_complexBalanced_unbounded_class`).
* **Tried:** satisfying the `hMclass` premise of `exists_positive_omegaPoint_of_blueprintData`
  from the residual's hypotheses.
* **Why it fails:** `hMclass` is a *repo* hypothesis, not the paper's. Craciun bounds the
  **trajectory**, not the class, and that bound comes from the cube `[0,M]ⁿ` plus `V ≤ L` inside
  the constructed region. A weakly reversible deficiency-zero network whose stoichiometric
  subspace is everything has no such `M`.
* **Evidence:** narrative `HighCodimensionSiphonFace.lean:337–350` (packaging audit item 3);
  refuting instance named there.
* **What would make it work:** restrict to conservative networks (the all-ones law bounds the
  class) — which is what `ToricBarrierExplicit`'s docstrings scope it to — **or** drop `hMclass`,
  which the branch-(2) route (A2) does. Non-conservative networks have no route through any
  `blueprintData`-shaped criterion.
* **Found by:** GacBio / packaging audit, 2026-09-28.

### A6. The vacuous tile definition: `activeFaceImage` over all positive `x` makes `hm` unsatisfiable

* **Hole:** A. **Grade: [M]**.
* **Tried:** the original definition of the tile `Network.activeFaceImage`, quantifying over every
  positive `x` satisfying the regime bound.
* **Why it fails:** a tile quantified over all `x` contains points with `x s ≈ xstar s` for
  `s ∈ P`, which makes `faceLogPart` arbitrarily small while leaving the off-face bound satisfied;
  `relevantCones_eq_fan_of_small` then makes *every* cone of the fan relevant (because `0` lies in
  every cone), and `mem_all_cones_of_hm` forces the piece's normal into every cone at once, which
  is incompatible with `0 < (m i) s` from `hpos`. `hm` is therefore **unsatisfiable** and
  `exists_positive_omegaPoint_of_blueprintData` was **vacuously true** — the reported "reduction"
  was worth nothing.
* **Evidence:** `Network.relevantCones_eq_fan_of_small`, `Network.mem_all_cones_of_hm`
  (`CRNT/Dynamics/ToricBarrierExplicit.lean`); guard lemmas `norm_ge_of_mem_activeFaceImage`,
  `not_small_of_mem_activeFaceImage`; `HANDOFF_gac_hole.md` §5c.
* **What would make it work:** the *repaired* tile, quantified over the trajectory and the band,
  is in the tree and is what all consumers now take. **Do not reintroduce the all-`x` version.**
  The repair does **not** by itself prove `hm` satisfiable — `not_small_of_mem_activeFaceImage`
  certifies only that the combination is not self-defeating.
* **Found by:** adversarial pass, `HANDOFF_gac_hole.md` §5c, 2026-09-27. **This is the single most
  important entry in this file**: it was invisible to the kernel.

### A7. The absolute-value floor condition is jointly unsatisfiable with `hstart` on conservative networks

* **Hole:** A. **Grade: [M]**.
* **Tried:** `hlevel` bounding other coordinates by `M·∑_{u ≠ s} |a u|`, combined with
  `hstart : ⟨m, x₀⟩ ≥ η` and `η > M∑_{u ≠ s}|m_u|`, on a network carrying the all-ones
  conservation law (i.e. every `m` in the stoichiometric subspace has `∑_u m_u = 0`).
* **Why it fails:** `⟨m,x⟩ = ∑_u m_u(x_u − M) ≤ M∑_{m_u<0}|m_u| = (M/2)∑_u|m_u|`, so the
  conjunction reduces to `m_s > ∑_{u≠s}|m_u| ≥ |∑_{u≠s} m_u| = m_s`. i.e. `m_s > m_s`. **The
  criterion was vacuous on precisely the networks it was built for** (the conservative case, where
  `hMclass` is automatic).
* **Evidence:** `Network.sum_posPart_le_erase_abs`, `Network.inner_le_erase_abs_of_sum_zero`,
  and the regression guard `Network.not_level_abs_and_start` (proves `False`) —
  `CRNT/Dynamics/ToricBarrierExplicit.lean`; `HANDOFF_gac_hole.md` §5e.
* **What would make it work:** the shipped fix — bound by **positive parts** `∑_{u≠s} max (a_u)
  0` instead of absolute values, which is valid because `x` is nonnegative. That reduces the
  conjunction to `m_s > 0`, exactly `hpos`. Still necessary and still not sufficient: see A8.
* **Found by:** adversarial pass, 2026-09-27.

### A8. Positive parts are necessary but not sufficient: the middle wall is rejected by `hlevel`; and per-species dominant halfspaces admit **no** admissible normal at `min x*`

* **Hole:** A. **Grade: [N]** (the numerical/script findings; the surrounding theorems are [M]).
* **Tried (i) — the convenient middle wall.** On `A + B ⇌ 2B, A + C ⇌ 2C` with unit rates, using
  the middle wall `(−2/3, 1/3, 1/3)`, which is positive at *both* face species so one piece covers
  both.
* **Why it fails:** inside a conservative class `∑_u c_u x_u = T` the coordinates cannot all sit
  at the ceiling at once, and the achievable `⟪a,x⟫` is only `≈ T·max_u(a_u/c_u)`. `hlevel` then
  needs `η > T/3` while the class allows `η ≤ T/3`. **A blueprint for this network must use the
  two outer walls, one per species.**
* **Tried (ii) — per-species dominant halfspaces** (`coordinate_floor_of_dominant_barrier` and its
  class-aware sharpening). On a conservative network, the species attaining `min x*` admits **no**
  admissible normal: the region must contain the whole forward orbit, whose closure contains `x*`,
  so `η ≤ ⟪m, x*⟫`; at best `β = 0` (`m u ≤ 0` for `u ≠ s`), and mass conservation puts `m` in
  `{∑ m = 0}`, so `⟪m,x*⟫ > 0` reads `x*_s` strictly exceeds a convex combination of the other
  `x*_u` — impossible exactly when `x*_s` is the minimum. Checked over four rate choices; the
  species attaining `min x*` always fails. With **all rates equal** a degenerate trap appears:
  `⟪m,x*⟫ = 0` for every `m` in the subspace, so *all* species fail.
* **Evidence:** `scripts/probe_hsep_dominant_obstruction.py`, `scripts/probe_residual_case_blueprint.py`;
  `HANDOFF_gac_hole.md` §5j, §5k. Related proved results: `le_of_halfspace_of_dominant`,
  `coordinate_floor_of_dominant_barrier`, `coordinate_floor_of_dominant_class_barrier`,
  `Network.le_of_halfspace_of_dominant` (all true, but the *route* is inadequate).
* **What would make it work:** the coordinate floors must come from the **global geometry** of the
  guarded region (the staircase), not from one dominant halfspace per species — which is what
  Craciun's surface does. Concretely: `exists_positive_omegaPoint_of_convex_tiles` and
  `..._of_selfConsistent_normals`, which take `hsep` abstractly, are the packaging to build
  against; `..._of_blueprintData`, which bakes in `piece : S → ι'`, `hpos` and `hlevel`, is the
  **wrong** packaging.
* **Found by:** adversarial pass, 2026-09-27. Note the epistemic hazard: the first pass at (ii)
  used unit rates and drew the *wrong* conclusion from it (the degenerate trap). Numeric
  conclusions in this area need generic rates.

### A9. `hregime` as originally stated is circular (required outside the region where the floors hold)

* **Hole:** A. **Grade: [M]** (the repair; the diagnosis is a careful reading).
* **Tried:** consuming `hregime` (which bounds `‖offFaceLogPart‖`) in
  `exists_positive_omegaPoint_of_convex_tiles` at points where `hlevel` holds, i.e. **at or
  outside** the guarded region.
* **Why it fails:** there the coordinate floors of `coordinate_floor_of_dominant_barrier`, which
  need `barrier ≤ R`, are unavailable. `hregime` needs off-face coordinates bounded **below** as
  well as above, so deriving it from the barrier's own floors is circular: the floors are what
  trapping gives, and trapping is what `hregime` is being used to prove. Compactness of `K` gives
  upper bounds only.
* **Evidence:** band-form repairs `PolyhedralBarrier.le_of_dini_slope_nonpos_at_level_le`,
  `..._in_band`, `barrier_le_of_local_descent_in_band`, `Network.barrier_le_of_toric_descent_in_band`
  (`CRNT/Geometry/PolyhedralBarrier.lean`, `CRNT/Dynamics/ToricBarrierTrapping.lean`);
  `HANDOFF_gac_hole.md` §5d.
* **What would make it work:** done, in the tree — all three packaged criteria now take `R < R'`
  and carry a band premise `barrier ≤ R'`. The circularity is gone from the criterion statements.
  The extra cost is that `hdeep` is now a **tuning condition on `R`**, not a consequence of the
  coefficient conditions, and must be established rather than derived.
* **Found by:** adversarial pass, 2026-09-27.

### A10. Separation from *every* other cone (`hm_of_single_chamber`) is unsatisfiable on wall tiles

* **Hole:** A. **Grade: [M]** for the shipped replacement; **[N]** for the unsatisfiability
  diagnosis.
* **Tried:** `hm_of_single_chamber` — each tile must be `δ + B`-separated from every cone other
  than its own `C i`.
* **Why it fails:** a tile sitting on a **wall** — a lower-dimensional cone, which is exactly
  where the normal is forced to live when the `δ`-slack reaches across a face — lies inside every
  chamber `D` adjacent to that wall, since `C ⊆ D`. So `dist(tile, D) = 0` and no separation from
  `D` is possible. None is needed: `m i ∈ C ⊆ D` already.
* **Evidence:** replacements `Network.hm_of_cone_family`,
  `Network.hm_of_cone_family_margins` (`CRNT/Dynamics/ToricBarrierExplicit.lean`); confirmed on
  the monomolecular 3-cycle (`scripts/probe_three_cycle_blueprint.py`, `HANDOFF_gac_hole.md` §5h)
  where `hm_of_single_chamber` would force a wall normal out of its own wall.
* **What would make it work:** build against `hm_of_cone_family`, which is the only form
  satisfiable on walls. `hm_of_single_chamber` remains true but is the wrong tool.
* **Found by:** adversarial pass, 2026-09-27.

### A11. One piece per species is not enough — pieces must be indexed by scale orderings/flags

* **Hole:** A. **Grade: [N]** (a structural analysis; the individual lemmas it rests on are [M]).
* **Tried:** index blueprint pieces by species (`piece : S → ι'`), one dominant piece per species.
* **Why it fails:** near the face, `⟨m,x⟩ ≈ ∑_s m_s·xstar_s·exp(−w_s)`, so the sum is dominated by
  the coordinate with the **smallest** `w_s`. A piece's active region pins only the shallowest
  coordinate; the remaining coordinates range over everything deeper, so the *direction* still
  sweeps many chambers. Pinning the direction needs the next coordinate pinned too, and so on.
* **Evidence:** `Network.margin_of_scale_ratio`, `Network.margin_of_depth`,
  `Network.exists_depth_for_margin`, `Network.hm_of_separating_margins`,
  `Network.dist_ge_of_separating_margin`, `inner_faceLogPart_eq_sum`
  (`CRNT/Dynamics/ToricBarrierExplicit.lean`); `HANDOFF_gac_hole.md` §5f. This is precisely why
  v3 §7 indexes by binary words `α ∈ {0,1}^n` with scales `ε(α)`.
* **What would make it work:** the open step is the *shape* claim — pieces indexed by flags of
  `P` with levels set by a scale chain, simultaneously with `hstart`, `hregime`, `hdeep`. That is
  the remaining content of v3 §7.4.3. **Live route**, not a dead one; listed so nobody re-derives
  the indexing argument.
* **Found by:** GAC chain, 2026-09-27.

### A12. The topological (two-closed-sets) method cannot fire on branch (I): a species split is always straddled

* **Hole:** A. **Grade: [M]**.
* **Tried:** applying the connectedness technology that killed branch (4) (see A14) to branch
  (I) — split the species set `I ∪ J = univ`, partition ω by which side its points' zeros live
  on, and contradict connectedness.
* **Why it fails:** whenever both sides are visited by zeros of ω-points (and no positive ω-point
  exists, so every ω-point has a zero), some **single** ω-point vanishes on both sides at once.
  The candidate sets `{q | ∃ s ∈ I, q s = 0}` and `{q | ∃ t ∈ J, q t = 0}` are then nonempty,
  closed and **not disjoint**, so `not_disjoint_closed_cover_omegaLimit` returns no contradiction.
  The mixed zero-set configuration of branch (I) is connected *through* a straddling point, not
  separable.
* **Evidence:** `exists_omegaPoint_vanishing_on_both_sides` (`:1692`),
  `exists_omegaPoint_vanishing_across_siphon` (`:1789`); narrative `:1662–1686`;
  commit `a96ec97`. Commit `76b3f03` separately pins the descent-iteration version.
* **What would make it work:** nothing by this method. Excluding branch (I) needs genuinely
  dynamical input, or an argument that does not route through `ComparableGrowthDescent`.
* **Found by:** GacDescend, 2026-09-28.

### A13. Descent-iteration route bottoms out at the goal itself

* **Hole:** A. **Grade: [M]**.
* **Tried:** iterate the induction of `omegaLimit_positive_of_descend` from `Pmax` down to the
  empty siphon, closing branch (I).
* **Why it fails:** cardinalities are naturals, so the chain reaches a cardinality-minimal carried
  critical siphon `Pm`, and at `Pm` the descent step is **literally** the residual's conclusion
  (its right disjunct would need a strictly smaller carried critical siphon, forbidden by
  minimality). Unconditional. Likewise `comparableGrowthDescent_iff_omegaPointPositive`: assembling
  the whole `ComparableGrowthDescent` structure *is* the statement.
* **Evidence:** `SiphonDimensionDescent.descendStep_iff_omegaPointPositive_of_cardMinimal`
  (`:347`), `comparableGrowthDescent_iff_omegaPointPositive`, `descendStep_of_carried_card_lt`
  (`:288`), `exists_cardMinimal_carried_siphon` (`:300`), `exists_cardMinimal_carried_siphon_lt`;
  narrative `SiphonDimensionDescent.lean:247–284`; commits `a96ec97`, `76b3f03`.
* **What would make it work:** exclude branch (I) by a dynamical argument under the genuine-orbit
  hypotheses (consuming `hsol` — see A16), or route around `ComparableGrowthDescent` entirely.
* **Found by:** GacDescend, 2026-09-28.

### A14. `hface` of `uniformLowerBound_offFace_of_zeroSet_eq` does **not** cover the tie branch (self-correction)

* **Hole:** A. **Grade: [M]**.
* **Tried:** applying `uniformLowerBound_offFace_of_zeroSet_eq` to *either* open disjunct of the
  trichotomy, because the module docstring said "both disjuncts share `hface`".
* **Why it fails:** `hface : ∀ z ∈ ω, ∀ s ∈ Pmax, z s = 0` is **universal**, and the trichotomy's
  third disjunct is a *per-point* split `∀ z, Z(z) = Pmax ∨ tie(z)`, where a tie witness is
  positive somewhere on `Pmax` and therefore violates `hface`. The earlier claim is correct only
  for the *existential* reading ("some ω-point vanishes on `Pmax`", namely `wmax`).
* **Evidence:** `hface_iff_zeroSet_eq` (`:1117`) pins the boundary exactly — given `hmaxExact`,
  `hface` ⟺ "every ω-point's zero set is exactly `Pmax`"; narrative `:1099–1115`;
  commit `35fb756`.
* **What would make it work:** for disjunct 4 one needs the *existential* form, or a
  point-localized version of the floor lemma. (This was superseded in practice: A15 kills
  disjunct 4 outright.)
* **Found by:** GacVac, 2026-09-28.

### A15. Branch (4) (exact ties) is dead — ties cannot coexist with face points

* **Hole:** A. **Grade: [M]**.
* **Tried:** obtain `hface` on disjunct 4 by exhibiting a mixed ω-limit set and separating it.
* **Why it fails:** the face points `A` and tie witnesses `T` are closed subsets of ω, disjoint by
  `hmaxExact`, and cover ω; `A` is nonempty because `wmax` lies in it. A precompact orbit's
  ω-limit set cannot be split by two disjoint nonempty closed sets (Cantor's intersection
  theorem applied to the closures of the forward tails), so `T` must be empty.
* **Evidence:** `hface_of_trichotomyThird` (`:1343`), from `omegaLimit_eq_iInter_closure_tail`
  (`:1143`) and `not_disjoint_closed_cover_omegaLimit` (`:1166`); commits `8542230`.
* **What would make it work:** nothing needed — this **closes** a disjunct. With A14 it means the
  off-face uniform floor lemma *is* available in the surviving residue.
* **Found by:** GacDeep, 2026-09-28.

### A16. Every static hypothesis is simultaneously satisfiable with the conclusion false — `hsol` is the only load-bearing premise

* **Hole:** A. **Grade: [M]**.
* **Tried:** any argument confined to the static hypotheses (`hωnn`, `hgenω`, `hωaff`, `hmaxExact`,
  `hzcard`, `hcodim`, `hcard`, `hrank`, `hK`, `hmaps`) — including "the model `ω = {wmax}`
  satisfies every static hypothesis", which had been asserted in prose and debated.
* **Why it fails:** on `CatalyticChain` (`A + C ⇌ 2C ⇌ B + C`, weakly reversible deficiency 0,
  `stoichRank = 2`) with `x* = x₀ = (1,1,1)`, boundary equilibrium `wmax = (3,0,0)`, face
  `Pmax = {B,C}` and the contraction flow `ϕ t x = wmax + e^{−t}(x − wmax)`: **all** static
  hypotheses hold and no ω-point is positive. The model falsifies `hsol` (its orbit is not a
  mass-action solution), so the conclusion is not derivable with `hsol` deleted.
* **Evidence:** `CRNT/Examples/CodimTwoFaceModel.lean`: `codimTwoModel_not_hsol` (`:313`),
  `codimTwoModel_all_but_hsol` (`:337`),
  `codimTwoModel_not_derivable_without_hsol` (`:377`); verified with `checkmod.sh`.
  Reinforced by the redundancy lemmas `hmaxExact_of_zeroSet_card_le` (`:1034`),
  `two_le_card_of_two_le_finrank_map_projOn` (`:1053`),
  `stoichRank_ne_one_of_two_le_finrank_map_projOn` (`:1090`) — `hmaxExact`, `hcard`/`hPmaxne` and
  `hrank` carry no independent content.
* **What would make it work:** **consume `hsol` essentially.** This is the single most important
  routing fact for hole A: any proposed proof that never touches the mass-action ODE premise is
  either wrong or already in the tree.
* **Found by:** GacVac, commit `6474732`, 2026-09-28.

### A17. Relative-entropy blow-up at the boundary is unavailable (Mathlib's `log 0 = 0`)

* **Hole:** A. **Grade: [M]**.
* **Tried:** "relative entropy blows up as a concentration goes to zero, contradicting its
  constancy on the ω-limit set".
* **Why it fails:** `relEntropy xstar x = ∑_i (x_i·log(x_i/xstar_i) − x_i + xstar_i)` with
  Mathlib's convention `Real.log 0 = 0`, so at an extinct coordinate the summand equals exactly
  `xstar s`. The entropy is **finite and continuous on the whole closed orthant**
  (`relEntropy_continuous`). The heuristic dies at the definition.
* **Evidence:** `relEntropy_ge_sum_zeroSet` (`:931`) — the finite substitute: the total reference
  weight of any extinct set is capped by the entropy value;
  `relEntropy_le_of_mem_omegaLimit` (`:957`);
  `sum_xstar_le_relEntropy_x₀_of_zero_omegaPoint` (`:996`).
* **What would make it work:** it does not yield a contradiction. The cap
  `∑_{s ∈ Pmax} xstar s ≤ relEntropy xstar x₀` pins a **strictly positive floor on the LaSalle
  constant** `c ≥ ∑_{s ∈ Pmax} xstar s > 0` of any trajectory whose ω-limit meets the boundary —
  a genuine constraint, but `relEntropy xstar x₀` is an arbitrary nonnegative number that can
  exceed any finite reference weight. The cap alone cannot exclude `Pmax`.
* **Found by:** GAC chain, 2026-09-28.

### A18. The conservation-law mechanism (Lead 1) is exact but cannot be instantiated

* **Hole:** A. **Grade: [M]** (the lemma); the non-instantiability is **[N]**.
* **Tried:** use stoichiometric compatibility to force an ω-point that vanishes outside `Pmax` to
  also vanish on `Pmax`, contradicting `hmaxExact`.
* **Why it fails:** `hout` requires either that `z` and `wmax` agree off `Pmax` (ω-points of one
  class vary freely off the face) or that `c` is supported inside `Pmax` (not available for an
  arbitrary ω-point). And the obvious repair — an invariant nonnegative everywhere and positive on
  **all** of `Pmax` — is a witness to `¬ N.IsCriticalSiphon Pmax`, which the derived
  `IsCriticalSiphon Pmax` forbids.
* **Evidence:** `eq_zero_on_pmax_of_conservation_eq` (`:569`); narrative `:526–534`.
* **What would make it work:** an invariant with the right support, i.e. real content about the
  specific network rather than the class. Alternatively exclude disjunct 4 dynamically — which
  A15 does.
* **Found by:** GAC chain, 2026-09-28.

### A19. `hmaxExact` can only exclude candidates, never produce one — static elimination is circular

* **Hole:** A. **Grade: [N]**.
* **Tried:** rule out every candidate carried siphon `Q` with `Q.card < Pmax.card` using
  `hmaxExact`, thereby forcing the left disjunct of `descend Pmax`.
* **Why it fails:** a carried `Q` with `Q.card < Pmax.card` cannot contain `Pmax`, so its witness
  `z` does not satisfy the premise `∀ s ∈ Pmax, z s = 0` that `hmaxExact z` needs. `hmaxExact`
  only ever *excludes*; eliminating all candidates makes `descend Pmax` equivalent to the goal.
* **Evidence:** narrative `HighCodimensionSiphonFace.lean:445–459`.
* **What would make it work:** a dynamical argument, i.e. A16 again.
* **Found by:** GAC chain, 2026-09-28.

### A20. `hzcard` cannot refute the third disjunct — the bound is one-sided

* **Hole:** A. **Grade: [N]** (a note; the bound itself is [M] as `hzcard`).
* **Tried:** push the zero-set cardinality bound to exclude the "strictly smaller carried siphon"
  disjunct of `omegaPoint_zeroSet_trichotomy`.
* **Why it fails:** `hzcard` says no ω-point's zero set is **larger** than `Pmax.card`. A strictly
  *smaller* zero set is perfectly consistent with it.
* **Evidence:** narrative `HighCodimensionSiphonFace.lean:732–734`.
* **What would make it work:** nothing static — see A13.
* **Found by:** GAC chain, 2026-09-28.

### A21. Codimension-zero and one-species variants are vacuous; the residual is exactly codimension ≥ 2

* **Hole:** A. **Grade: [M]**.
* **Tried:** the degenerate branches — a full-dimensional kernel of the `Pmax`-projection, or a
  one-species face.
* **Why it fails:** a full-dimensional kernel means every stoichiometric displacement vanishes on
  `W` (codimension zero), and for a one-species face the projection is exactly a line, so the
  facet hypothesis holds automatically and the facet branch closes.
* **Evidence:** `FaceCodimension.map_projOn_eq_bot_of_ker_finrank_eq` (`:49`),
  `eq_zero_of_mem_of_ker_finrank_eq` (`:60`), `one_le_finrank_map_projOn` (`:71`),
  `finrank_map_projOn_singleton_le_one` (`:87`), `facet_of_singleton_witness` (`:108`),
  `two_le_finrank_map_projOn_of_not_facet` (`:124`), `two_le_card_of_not_facet` (`:137`),
  `highCodimension_of_not_facet` (`:174`); `HANDOFF_gac_hole.md` §6.
  Corroborated by `two_le_card_of_two_le_finrank_map_projOn` (`HighCodimensionSiphonFace.lean:1053`),
  which says the same from the `hcodim` side.
* **What would make it work:** nothing — do not spend effort on the degenerate branches. Choosing
  `W = {s}` a singleton to make the facet count hold does not help: the Anderson–Shiu estimate
  needs `z` positive off `W`, which fails once the maximal zero set has ≥ 2 species.
* **Found by:** GacDeep / FaceCodimension, 2026-09-28.

### A22. Unrestricted ω-point predicates are false even for complex-balanced networks

* **Hole:** A. **Grade: [M]**.
* **Tried:** a version of the residual whose only orbit-side premise constrains ω-limit points
  (not the start orbit) — `PositiveOmegaPointForRates` in its original unrestricted form,
  `BoundaryOmegaExcluded`, and `ComparableGrowthDescentForRates`.
* **Why it fails:** on `2A ⇌ A + B` (weakly reversible deficiency 0, hence complex balanced at
  `κ ≡ 1`, `x* = (1,1)`), the contracting flow `ϕ t x = b + e^{−t}(x − b)` with `b = (0,1)` has
  ω-limit set exactly `{b}`, a boundary point in the class of `x₀ = (1/2,1/2)`. Every listed
  hypothesis holds and the conclusion fails. `b`'s own forward orbit is constant, so it *does*
  solve the ODE — only the start orbit's failure to do so is what the repaired predicate catches.
* **Evidence:** `CRNT/Examples/OmegaPointFakeFlow.lean`: `gacN_not_unrestrictedPositiveOmegaPoint`
  (`:214`), `gacN_not_boundaryOmegaExcluded` (`:227`),
  `gacN_not_comparableGrowthDescentForRates` (`:297`), `fake_orbit_not_massAction` (`:242`).
* **What would make it work:** add the initial-orbit ODE premise — which is exactly the premise
  A16 identifies as the only load-bearing one.
* **Found by:** GAC chain, 2026-09-24.

### A22b. **Do not misread** A22 as refuting the no-critical-siphon route

* **Hole:** A. **Grade: [M]**.
* `gacN` **does** have the critical siphon `{A}` (both reactions produce and consume `A`; any
  nonzero nonnegative invariant supported in `{A}` is orthogonal to `reactionVector r0 = (−1,1)`,
  forcing `v A = 0`). So the hypotheses of `omegaLimit_positive_of_hasNoCriticalSiphon` and
  `boundaryOmegaExcluded_of_hasNoCriticalSiphon` **fail** in that example and it is **silent**
  there. *(`CRNT/Examples/OmegaPointFakeFlow.lean`: `gacN_isCriticalSiphon_A` `:276`,
  `gacN_not_hasNoCriticalSiphon` `:291`, `omegaPoint_route_dead` `:320`.)* Do not cite it as a
  refutation of the conditional theorem.

### A23. Butler–McGehee escape route is vacuous in this setting

* **Hole:** A. **Grade: [M]** for the singleton statement; **[N]** for the "vacuous" verdict.
* **Tried:** producing a strictly smaller carried siphon from a forward limit
  (`siphonCarried_of_escape`, `exists_escape_forwardLimit_criticalSiphonFace`).
* **Why it fails:** for a complex-balanced orbit the ω-limit set consists of semiflow fixed
  points, each its own forward limit: `ω{q} = {q}`. Taking a forward limit exposes no new
  boundary structure.
* **Evidence:** `GlobalAttractorTheorem.omegaLimit_singleton_of_mem_omegaLimit` (`:1248`);
  `HANDOFF_gac_hole.md` §6 ("recorded in earlier sessions" — an explicitly hearsay record, kept
  here with that grade).
* **What would make it work:** nothing in the complex-balanced setting.
* **Found by:** GAC chain, ≤2026-09-27.

### A24. Lower-rank face equilibrium is never transferred back to the parent orbit's ω-limit set

* **Hole:** A. **Grade: [N]**.
* **Tried:** rank descent — from a boundary ω-point get a lower-rank face equilibrium and iterate.
* **Why it fails:** the alternative produced is "a boundary ω-point whose zero set is a nonempty
  critical siphon and whose avoiding-face network has strictly smaller stoichiometric rank and a
  positive complex-balanced face equilibrium". The face equilibrium lives **on the filled face**,
  not on the original orbit's ω-limit set, so the reduction cannot be iterated.
* **Evidence:** `GACOmegaPositive.positiveOmega_or_lowerRankCriticalBoundaryFace` (`:196`);
  narrative `:191–205`.
* **What would make it work:** the missing transfer step is exactly the residual's content.
* **Found by:** GacBio, 2026-09-28.

### A25. Weak reversibility obstructs globally inward active walls

* **Hole:** A. **Grade: [M]**.
* **Tried:** a separating surface whose normal is inward on **every** reaction — the premise the
  active-wall estimates in `ToricUniformWallMargin` need.
* **Why it fails:** a potential nondecreasing along every reaction is nondecreasing along every
  path, hence nonincreasing around each directed cycle; for a weakly reversible network the return
  path forces every inward pairing to vanish, so such a normal cannot be active (cannot
  distinguish two mutually reachable complexes).
* **Evidence:** `CRNT/Geometry/WeakReversibleWallObstruction.lean`:
  `complexPotential_le_of_reaches_of_nonneg` (`:23`),
  `WeaklyReversible.inner_reactionVector_eq_zero_of_nonneg` (`:37`),
  `not_activeWall_of_all_reactions_nonneg` (`:48`).
* **What would make it work:** control the **rate-weighted total velocity** in a region of
  concentration space instead — which is what the toric construction does. Those
  `ToricUniformWallMargin` estimates cannot construct the separating surfaces for general
  complex-balanced permanence.
* **Found by:** GAC chain, 2026-09-24.

### A26. Naive single-patch surface construction is over-determined once the active directions span — first in ℝ⁴

* **Hole:** A. **Grade: [M]**.
* **Tried:** one patch whose normal is simultaneously orthogonal to several attracting/ruling
  directions.
* **Why it fails:** a valid normal must be nonzero **and** orthogonal to every active direction.
  Below `finrank E` active directions a nonzero orthogonal normal always exists; once they span
  the ambient space, only the zero vector is orthogonal to all of them. The `n = 4` instance is
  formalized: three vectors in ℝ⁴ always leave one, four (the standard basis) need not.
* **Evidence:** `ZeroSeparatingInduction.exists_orthogonal_normal_of_card_lt_finrank` (`:8584`),
  `not_exists_orthogonal_normal_of_span_top` (`:8611`), `over_determined_in_dim_four` (`:8675`).
* **What would make it work:** the inductive simplicial/refinement route — and note that
  `ZeroSeparatingInduction.inductionStep_of_ruledBuild` (`:8715`) takes the swept-region
  decomposition `hbuild` **as an assumption**; the explicit decomposition is *not* constructed
  anywhere. Same for `ZeroSeparatingSurface.InductionStepHypothesis` (`:297`), whose `.elim` is
  the trivial unfolding and whose module docstring states the gluing, subdivision combinatorics
  and the Nagumo viability layer are all absent from Mathlib.
* **Found by:** face-fill work, 2026-09-27.

### A27. Blueprint premises that are individually plausible are insufficient

* **Hole:** A. **Grade: [M]**.
* Three cheap but real refutations, in `CRNT/Examples/GACBlueprintPremiseCounterexamples.lean`:
  1. **Shared start ≠ shared boundary compatibility.** `same_initial_value_does_not_force_trace_agreement`
     (`:20`): two candidate boundary traces agree at the distinguished initial vertex and disagree
     elsewhere.
  2. **Per-face local solvability ≠ compatible filling.**
     `each_affine_face_constraint_nonempty` (`:64`) with
     `incompatible_face_offsets_have_no_shared_vertex` (`:75`): four individually nonempty affine
     face constraints in ℝ³ (`p 0 = 0`, `p 1 = 0`, `p 2 = 0`, `p 0+p 1+p 2 = 1`) with no
     simultaneous solution.
  3. **Lexicographic enumeration ≠ acyclicity.** `toy_dependencies_form_cycle` (`:97`) with
     `toy_dependencies_not_lexicographically_decreasing` (`:103`): two lexicographically ordered
     faces can each require the other.
* **What would make it work:** note carefully that
  `wellFounded_of_decreasing_rank` (`:27`) and `fill_by_decreasing_rank` (`:45`) are **vacuous with
  respect to the blueprint**: they take `depends` and the strict-rank-decrease hypothesis as free
  parameters, so instantiating them with the real dependency relation **is** the unproved
  obligation. Citing them as progress is circular. Only the order-theoretic part of lexicographic
  filling is proved.
* **Found by:** face-fill work, 2026-09-25.

### A28. The smooth-surface route: the sphere satisfies Lemma 9.5 and fails Lemma 9.7

* **Hole:** A. **Grade: [N]** (a mathematical reading, formalized only for the convex analogue A3).
* **Tried:** a smooth zero-separating hypersurface whose outer normal lies in every cone within
  distance `δ` of each of its points.
* **Why it fails:** at `δ = 0` the sphere satisfies the condition exactly (its normal at `X` is
  `X`, which lies in the cone containing `X`) and fails Lemma 9.7. Near a wall — a
  low-dimensional cone — the surface must be **flat** on a slab of width ≥ `δ`.
* **Evidence:** `HighCodimensionSiphonFace.lean:51–60` and `HANDOFF_gac_hole.md` §4. Formalized
  for max-of-affine barriers in A3, not for general smooth surfaces.
* **What would make it work:** polyhedral surfaces with the §7.4.3 `ε(α)` scale hierarchy.
* **Found by:** GAC chain, 2026-09-27.

### A29. Craciun v3 does not prove its own Step-4 claim; several quoted formulas are `[INFERENCE]`

* **Hole:** A. **Grade: [S]** (checked against the v3 source).
* **Tried:** resting a route on "v3 §8 proves Theorem B".
* **Why it fails:** v3 asserts the `K_{x₀}` claim at §4 (lines 598/637, whose "Step 4" is the
  assembly), in 2D figure captions and in §5 LaSalle prose, but **§8 stops after Steps 1–2 and
  there is no "§8 Step 4"**. Lemmas 9.5/9.7 are stated only for ℝ³/(0,1)³ although §8 Step 2
  invokes 9.7 in `n` dimensions; Lemma 9.11's proof is a one-paragraph sketch. Two specific traps:
  * **Origin-avoidance ≠ boundary floor.** The v3 tex line 586 draft only says the closure of
    `Zupper` does not contain the origin. A point like `(1,0)` misses the origin yet has a zero
    coordinate, so this does **not** give `K ⊂ ℝⁿ_{>0}`. The full floor exists only in v2 §6
    verbatim and as bare assertions in v3.
  * **The formula `K = (upper region) ∩ [0,M]ⁿ ∩ {V ≤ L}` is written by no source.** Lines
    600/637/946 plus intro line 309 assert the factors separately; this is an
    `[INFERENCE]`-reconstruction. The published three-species `K` of CNP §7 is a different shape.
* **Evidence:** `HighCodimensionSiphonFace.lean:377–390` and `:1439–1490`; correction recorded
  from the source (`[GacLit] 19:47`).
* **What would make it work:** nothing — this is a scoping correction, not a route. Speak of the
  *claimed* proof. v3 is a preprint (v1 2015, v2 2016, v3 2026-09-23, no journal reference)
  treated as open in current literature: Wiuf, arXiv:2609.24553v1, lists the GAC as proved only
  in special cases and does not cite 1501.02860. No erratum or refutation was found.
* **Found by:** GacLit / GacDescend, 2026-09-28.

### A30. Things that are *not* dead — do not mistake these for dead ends

* **[M] `v3 §9.1`'s "non-crossing ⟹ forward invariance" bridge** was announced and never *stated*
  by the paper, but the repo now machine-checks the two-region form:
  `orbit_stays_in_upperRegion` (`:1508`). Combined with `persistentFrom_of_upperRegion` (`:1538`)
  and `exists_positive_omegaPoint_of_upperRegion` (`:1596`), Layer C ⟹ Layer B ⟹ Layer A is
  machine-checked. **This is the live branch-(2) route** and needs no `hMclass`, no convex barrier
  and no `hsep` — which is exactly why A1 and A5 do not touch it.
* **[M] `FanFaceLattice` supplies only the descent half.** Given one normal per tile lying in every
  cone near that tile, the region traps the flow. It does **not** construct those normals and
  tiles; that is the §7 blueprint and is open. Citing the module as progress is a scoping error.
* **[N] `CraciunV3BlueprintScales` formalizes only the scale-selection subargument**
  (`exists_strictScaleChain` `:23`, `exists_strictScaleChains` `:53`). The scale hierarchy is
  necessary, not sufficient; the tile incidence data and the hypersurface are not constructed.

---

## 2. Hole B — `stronglyConcordant_fullyOpen_of_trueSRCriterion`

### B1. Dropping `hsep` (`ReactantProductSeparated`) makes the true-SR criterion **false** — refuted at `S = Fin 2`

* **Hole:** B. **Grade: [M]**.
* **Tried:** the criterion with `ReactantProductSeparated` removed — either by restating the
  s-cycle condition in **net coefficients** (`SCycleNet`) instead of **labels** (`SCycle`), or by
  proving the cyclic-gain contradiction using the one-sided dominance `|reactionVector| ≤ coeff`.
* **Why it fails:** witness network `r₀ : B → A`, `r₁ : 2B → 2A + B` over `Fin 2` (species
  `0 = A`, `1 = B`). Species `B` occurs on **both** sides of `r₁` (source 2, target 1), so the
  true-SR edge label is `2` while `B`'s net coefficient is `|1 − 2| = 1`. The even cycle
  `A —ρ₀— B —ρ₁— A` satisfies the published label identity (`1·2 = 1·2`) and **fails** the net
  identity (`1·1 ≠ 1·2`). The fully open extension carries the strong-concordance witness
  `α = (3, −2)`, `σ = (−1, −1)` and is strongly discordant.
  The attempted repair fails too: `abs_reactionVector_le_trueSREdge_coeff` gives
  `|reactionVector| ≤ coeff` on **both** the left and the right edges of the cycle, so
  `∏ L_rv < ∏ R_rv` plus `∏ L_coeff = ∏ R_coeff` transfers no inequality across the identity.
  Only **equality** collapses the two quantities, and that is precisely `hsep`.
* **Evidence:** `CRNT/Examples/TrueSRNetCoeffCounterexample.lean`: `netN_not_reactantProductSeparated`
  (`:87`), `trueSRCriterion_netCoeff_counterexample` (`:642`), `unseparated_trueSRCriterion_false`
  (`:724`). The hinge: `Network.netCoeff_eq_coeff_of_separated` and
  `Network.TrueSRCycle.sCycleNet_iff_sCycle_of_separated`
  (`TrueChemistrySRCriterion.lean:2082`, `:2092`), machine-checked — so the criterion's hypothesis
  **cannot** be restated in net coefficients without loss.
* **Precedent:** this is the same standard as the repair of
  `stronglyConcordant_of_fullyOpen_of_weaklyNormal`, which was false as stated and was repaired
  by adding `hsep`, with the counterexample module committed alongside.
* **Found by:** codex/true-sr-repair chain, 2026-09-24.

### B2. The causal-orbit constructor provably cannot satisfy `hopp` — the endgame lemma is inapplicable as stated

* **Hole:** B. **Grade: [M]**. **This is the sharpest structural negative for hole B.**
* **Tried:** apply the proved degree-two endgame `no_degree_two_causal_cycle` to the cycle
  produced by `trueSRCycleOfPeriodicCausalOrbit`.
* **Why it fails:** `no_degree_two_causal_cycle` requires, at every position, that the cycle's
  **left** edge's flux term at that species be strictly *negative* (`hopp`). The constructor builds
  the left edge as the cause reaction chosen *for that very species*, so `constructed_left_causal`
  proves the same quantity strictly **positive**. The two are mirror images.
* **Evidence:** `CRNT/Multistationarity/TrueSRCausalCycleFacts.lean`: `constructed_left_causal`
  (`:95`), `constructed_hopp_false` (`:108`, deriving `False` from the conjunction); narrative
  `:72–79`.
* **What would make it work:** either re-orient one of the two statements (a *restatement* of an
  existing lemma, not of the hole — permitted, but document it in the commit message), or apply
  `no_degree_two_aggregate_causal_cycle` (`:4520`) whose `hopp` was fixed for the aggregate case.
  See `no_degree_two_aggregate_causal_cycle_of_offCycle_hrest` (`:7019`) for that chain and its own
  wall (B4).
* **Found by:** sr-route-gain chain, 2026-09-24/28.

### B3. A species-to-species chord is invisible to `TrueSRStrongCriterion` — both routes machine-checked closed

* **Hole:** B. **Grade: [M]**.
* **Tried (i) — parity (`hSR.2`).** Glue two species-to-species paths sharing the chord and read
  the resulting cycles' parity off the partners' c-pair counts.
* **Why it fails:** the two glues always have the **same** parity, so the two candidate cycles are
  either both even or both odd and `hSR.2` never bites.
* **Tried (ii) — the certificate.** Try to exhibit an `SToRIntersection` directly.
* **Why it fails:** when the common-edge subgraph is one simple path with species at both ends,
  criterion (ii) has no certificate: the final vertex of any certificate component is an endpoint
  of the component's last edge, hence one of the listed path's vertices; if it were interior, the
  component would reach that vertex twice (`vertex_simple`) or another component would share it
  (`components_separated`). So it is one of the two endpoints — a species — contradicting
  `ends_at_reaction`. The subtle case is covered: the common path may run
  `s_{k+1} — r_k — … — s`, both endpoints species, and still fails, because only the two
  *endpoints* matter.
* **Evidence:** `CRNT/Multistationarity/TrueSRSSGlueCPairs.lean`:
  `ssGlueCycle_even_iff_even` (`:193`), `no_sToRIntersection_of_speciesSpecies_common` (`:233`);
  commit `f626003`.
* **What would make it work:** the residue at 8607 is exactly a `leftEdge` step — i.e. a **cycle
  edge** — so the chord lemmas are inapplicable *by construction*, not by weakness. Any route
  must break the shape of the residue first (see B4, B5).
* **Found by:** sr-route-edge chain, 2026-09-28.

### B4. Naive off-cycle `hrest` scope is self-refuting; even the corrected scope lands in SF §5.7.2 Possibility 3

* **Hole:** B. **Grade: [N]** (the diagnosis; the corrected theorems are [M]).
* **Tried:** restrict the source inequality's residual term `hrest` to off-cycle source classes,
  expecting the cycle-reaction part to be free, so that
  `no_degree_two_aggregate_causal_cycle_of_offCycle_hrest` (`:7019`) closes the frontier.
* **Why it fails:** the class returned by `exists_positive_off_cycle_aggregate_class` has
  **strictly positive** class flux at the attachment species `C.species (finRotate n i)` (witness
  `hρpos`/`hattachment`) — exactly what `hrestOff` forbids. The route closes on an unsatisfiable
  hypothesis, not on a contradiction. Even with the corrected scoping
  (`sharpened_source_inequality_at_cycle_separator`, `:7100`, which absorbs the attachment into
  the positive external sum instead of excluding it), the telescoping slack survives precisely on
  the positive off-cycle term, so the continuation is leaf-removal over the **source block tree** —
  which the repository does not have (B5).
* **Evidence:** docstrings `:7001–7018` and the corrected scope at `:7086–7091`.
* **What would make it work:** the A.6 Case-2 source-block datum, or `hrest` degree-two isolation.
  **Blocked upstream at a missing datum, not at a hard combinatorial obstacle.**
* **Found by:** sr-route-gain chain, ≤2026-09-28.

### B5. Block / ear-decomposition existence theory is absent from both Mathlib and this repo

* **Hole:** B. **Grade: [N]** for the absence verdict; the vocabulary is [M].
* **Tried:** Shinar–Feinberg §5.9 leaf removal over the source block tree; A.1/A.3 directed-ear
  decomposition existence.
* **Why it fails:** only the first layer of vocabulary exists — `CRNT.SeparatesWithin`
  (`CRNT/Graph/SourceBlocks.lean:50`), `IsSeparatingVertexOn`, `ConnectedOn`, `IsNonseparableOn`,
  `IsEndBlockOn` (`:71`, deliberately **without** maximality). Missing: maximality of blocks,
  existence of the block decomposition and its block tree (including the leaf fact §5.9 needs),
  and directed-ear-decomposition existence (SF A.1, Prop A.3). There is also no `MaxFlow`/min-cut
  machinery anywhere under `CRNT/`.
  Without maximality or a block tree, `IsEndBlockOn` cannot be shown inhabited, so every route
  consuming an end block — including `sharpened_source_inequality_at_cycle_separator` (`:7100`) —
  is blocked.
* **What would make it work:** build the block theory. This is genuine unformalized content and is
  the natural `Scaffold/`/`CRNT/` expansion. Note also the recorded warning at the top of
  `SourceBlocks.lean`: quantifying `SeparatesWithin` over walks that leave `S` makes
  "nonseparability too cheap to obtain" — a definitional trap, and a possible duplicate of the
  `SeparatesWithin` scoping fix in commit `fe613e2`.
* **Found by:** sr-ineq chain, ≤2026-09-28.

### B6. The naive directed-ear route to SF Proposition 5.12 chains multipliers in the wrong direction

* **Hole:** B. **Grade: [N]** (the verdict; the inequality is [M]).
* **Tried:** extend feasible multipliers one directed ear at a time, using `multiplier_chain` to
  transport the already-fixed multipliers across the new ear.
* **Why it fails:** `multiplier_chain` yields `(∏ g)·m last ≤ m 0` — an **upper** bound on the
  *start* in terms of the *end*. Extending across a new ear requires a **lower** bound on the
  multiplier at the ear's tail. The only chaining tool in the tree produces inequalities in the
  direction that cannot feed an ear extension, so the extremal (shortest-path) solution is "not
  optional".
* **Evidence:** `Network.multiplier_chain` (`TrueChemistrySRCriterion.lean:3719`), narrative
  `:3708–3742`. The extremal construction that *does* work is
  `Network.exists_cycle_multipliers` (`:3763`, SF Prop 5.12 for a single cycle).
* **Found by:** sr-route-ear chain, ≤2026-09-28.

### B7. Degree-two reaction vertices make an S-to-R intersection impossible — voids `hSR.2` for two-species networks

* **Hole:** B. **Grade: [M]**.
* **Tried:** get `hSR.2`-type information for small networks by exhibiting an `SToRIntersection`.
* **Why it fails:** an S-to-R intersection requires a component of the common-edge subgraph to
  *end* at a reaction vertex. A degree-two reaction vertex of `C` carries both of that cycle's
  edges, so any cycle through it shares both and the component runs **through** rather than
  terminating. Hence the second conjunct of `TrueSRStrongCriterion` holds **vacuously** for
  networks all of whose reactions touch only two species, and vacuously relative to the
  distinguished causal cycle in the hole's open branch.
* **Evidence:** `TrueSRDegreeTwoNoSToR.no_sToRIntersection_of_degree_two` (`:59`), docstring
  `:11–19`.
* **Caveat:** the docstring cites two consequences. (i) `netV` in
  `CRNT/Examples/TrueSRFirstConjunctWitness.lean` — **that file is not in the tree** (checked), so
  that application is currently unverifiable. (ii) the hole-1 branch claim refers to
  `HANDOFF_hole1_reaction_start.md`, which is **also not in the tree**. Re-verify before citing.
* **Found by:** sr-route chain, 2026-09-25.

### B8. Naive odd-gap chord extraction is false — a gap of length one may itself be a cycle edge

* **Hole:** B. **Grade: [N]** (the diagnosis); the specialisations are [M].
* **Tried:** read every odd gap of a marked even cycle as a Banaji–Craciun chord, so that
  `no_spanning_path_of_trueSRCriterion` applies directly.
* **Why it fails:** a single-edge gap joining a cycle species to a cycle reaction "may itself be a
  cycle edge, in which case no chord arises — the same degeneracy the existing
  `no_nonneighbor_chord` isolates with its non-neighbour side conditions".
* **Evidence:** `TrueSRChordExtraction.no_spanning_path_of_trueSRCriterion` (`:124`), narrative
  `:14–26`. The degeneracy had to be discharged in two separate specialisations —
  `no_single_edge_chord_of_trueSRCriterion` (`TrueSRChordExtraction.lean:42`) and
  `no_reaction_interior_path_of_neighbourFree_of_trueSRCriterion`
  (`TrueSRReactionInteriorPath.lean:110`).
* **What would make it work:** the local formulation in B9.
* **Found by:** sr-walk-parity chain, 2026-09-25.

### B9. Global `hnd` had to be weakened to "the final edge is not a cycle edge"; the strong form is not usable

* **Hole:** B. **Grade: [M]** for the shipped replacement; **[N]** for the weakened-strong-form note.
* **Tried:** supplying `no_spanning_path_of_trueSRCriterion`'s `hnd` (the path never traverses a
  cycle edge, quantified over **every** position) from a minimal directed causal path.
* **Why it fails:** a minimal directed causal path running from an on-cycle *reaction* vertex into
  the off-cycle class leaves the interior free of on-cycle **reactions** but says nothing about
  interior **species**. Alternation puts every reaction vertex at an odd position, and an edge with
  both endpoints on the cycle has an on-cycle reaction endpoint, so that endpoint must be the
  terminal position — `hnd` collapses to a condition on the last edge alone.
* **Evidence:** `no_reaction_interior_path_of_trueSRCriterion` (`TrueSRReactionInteriorPath.lean:41`),
  `no_reaction_interior_path_of_neighbourFree_of_trueSRCriterion` (`:110`), narrative `:6–25`.
  The stronger `no_offCycle_interior_path_of_trueSRCriterion` (`TrueSRCycleSplit.lean:650`) remains
  unconsumed — a **dead end for the strong form only**.
* **Found by:** sr-walk-parity chain, 2026-09-25.

### B10. Banaji–Craciun Lemma 10 assumes edge-disjointness; the repo's `Gluable` demands vertex-disjointness

* **Hole:** B. **Grade: [N]** (the mismatch); the minimality lemmas are [M].
* **Tried:** apply the published Lemma 10 ("a chord edge-disjoint from the cycle exists") directly.
* **Why it fails:** the paper's chord is only edge-disjoint from the cycle, whereas
  `CRNT.Network.TrueSRPath.Gluable` requires interior **vertex** disjointness.
* **What would make it work:** minimality. A shortest chord with an interior vertex on the cycle
  can be cut there to give a **shorter** chord — initial cut if the vertex is a reaction, terminal
  cut if a species, since a chord runs species-to-reaction. Hence interior vertices of a *minimal*
  chord are forced off the cycle. `TrueSRMinimalChord.isChord_initialSegment` (`:40`) plus its
  terminal-cut counterpart machine-check the repair.
* **Found by:** sr-route chain, ≤2026-09-28.

### B11. `ConcordantWith (twoWayInfluenceSpecification) ↔ StronglyConcordant` was demoted: too strong for the shipped definitions

* **Hole:** B. **Grade: [N]** (the statement-drift record); the surviving implication is [M].
* **Tried:** bypassing the separation hypothesis by routing strong concordance through the
  two-way influence specification.
* **Why it fails:** the zero-rate clause of `StrongConcordanceWitness` constrains **source
  species only**, whereas `InfluenceConcordanceWitness` constrains **every** species with nonzero
  two-way influence. The biconditional was not derivable and was replaced by the one-way implication.
* **Evidence:** `InfluenceConcordance.concordantWith_twoWay_of_stronglyConcordant` (`:261`),
  docstring `:256–261`. Relevant because `StronglyConcordant.injective_of_twoWayWeaklyMonotonic`
  and `StronglyConcordant.twoWayReducedDerivative_injective`
  (`StrongConcordanceStability.lean:146`) all thread `hsep`.
* **Found by:** concordance chain, ≤2026-09-24.

### B12. Reduced P-matrix property is genuinely basis-dependent

* **Hole:** B. **Grade: [N]**.
* **Tried:** conclude the reduced (principal-submatrix) P-matrix property from the full Jacobian
  being a P-matrix, chart-independently, so that the injectivity criterion applies.
* **Why it fails:** a proper principal submatrix of `P·M·B` is `M|_{S(N)}` compressed onto a
  coordinate subspace **of the chart**, which depends on the chosen basis `B`. The
  chart-independence machinery only removes the coordinate-selection hypothesis at the level of
  the **top** reduced determinant.
* **Evidence:** `ReducedSRGraph.det_reducedJacobian_chart_independent`, docstrings
  `ReducedSRGraph.lean:24–31` and `ReducedSRGraphBridge.lean:20–23`. The chart-anchored
  `ReducedJacobianCompressionSRSign` is the satisfiable replacement. Related: the point-free
  full-Jacobian verdict of `SRCoverPointIndependence` does **not** transport to the pivot-reduced
  Jacobian, since the inverse-section columns of `B` are not standard basis vectors — and the
  basis chart `stoichChart`/`stoichProj` gives an oblique Schur-style compression, not a principal
  submatrix, so the coordinate-selection identity is unsatisfiable for it
  (`PivotReducedInjectivity.lean:10–13`).
* **What would make it work:** state the general-chart verdict as a condition on the reduced
  covers (the bridge module's route), or use the pivot-row chart.
* **Found by:** injectivity chain, ≤2026-09-28.

### B13. `finRotate` is not its own inverse — the two cyclic-gain orientations are not interchangeable

* **Hole:** B. **Grade: [N]**.
* **Tried:** re-derive the mirror orientation of the §5.7.2 gain telescope from
  `cyclic_gain_no_strict` by renaming indices, or apply the latter after a rotation.
* **Why it fails:** the paper's source convention produces the inequality in the orientation whose
  rotation sits on the **other** side; the index map does not give the mirror.
* **Evidence:** `cyclic_gain_no_strict` (`TrueChemistrySRCriterion.lean:3577`),
  `cyclic_gain_no_strict'` (`:3598`), narrative `:3591–3594`. Both kernels are machine-checked.
* **Found by:** sr-ineq chain, ≤2026-09-28.

### B14. `hreac` (reaction-class injectivity along the causal orbit) appears to require `hSR.2`

* **Hole:** B. **Grade: [N]**, and **flagged as unverified**: the cited script
  `hreac_needs_hSR.py` is **not present in the tree** (repo-wide check). Treat this as a lead for
  someone with budget, not as an established fact.
* **Tried:** prove `hreac` (the causal orbit never revisits a true-reaction *class*) from witness
  structure plus `hsep`.
* **Why it reportedly fails:** a search reportedly exhibits a separated, flow-free network with a
  valid strong-concordance witness and a valid causal choice whose unique periodic orbit has
  period 3 but only two active true-reaction classes, so class-injectivity fails by pigeonhole.
  Since `trueInternalCauseReaction` is `Classical.choose`, no such proof can exist.
* **Evidence:** module header `CRNT/Multistationarity/TrueSRSingleSharedEdge.lean:6–12`. The
  *near-free* part is machine-checked: at the level of channels, `hreac` is automatic
  (`trueInternalCause_injective_on_orbit`, `TrueSRCausalCycleFacts.lean:157`), so the only way it
  can fail is for the orbit to use two **distinct channels of one true reaction** — both directions
  of a reversible pair.
* **What would make it work:** verify the search (it is cheap and would be worth +30 if confirmed),
  or add a reversible-pair-exclusion hypothesis.
* **Found by:** sr-route chain, ≤2026-09-28.

### B15. First example counterexample is degenerate — do not use it as a template without the vacuity caveat

* **Hole:** B. **Grade: [M]** (the refutation); the vacuity diagnosis is **[N]**.
* **Tried:** refuting the criterion without excluding pre-existing flow channels.
* **Why it fails:** `flowN` has **every** channel a flow channel, so `flowN_no_edge` kills all
  true-SR edges and `flowN_trueSR` holds by exhaustion (`flowN_no_cycle` derives `False` from any
  cycle). The criterion holds **vacuously**.
* **Evidence:** `CRNT/Examples/TrueSRCounterexample.lean`: `trueSRCriterion_counterexample` (`:161`).
  `CRNT/Examples/TrueSRNetCoeffCounterexample.lean:648–656` contrasts itself explicitly: "Unlike
  `TrueSRCounterexample.lean`, where every channel was a flow channel so the true-SR graph had no
  edges at all and the criterion held vacuously, here the criterion has real content." **Use the
  second module as the non-vacuity template.**
* **Found by:** codex/true-sr-repair chain, 2026-09-23.

### B16. The second conjunct of `TrueSRStrongCriterion` cannot be dropped either — minimal witness `B→C, A→C, A+B→C`

* **Hole:** B. **Grade: [M]** (the one-edge certificate); **[N]** (the concrete minimality claim).
* **Tried:** weakening the criterion by discarding the common-edge/second conjunct.
* **Why it fails:** when two cycles share exactly one edge, there is one component with one edge
  whose vertices are that edge's species and reaction, so the classical condition holds *outright*.
  The minimal three-species network `B→C, A→C, A+B→C` witnesses non-droppability; the three-cycle
  through `A, B, C` is **odd** there (its c-pair sits at `A+B→C`), so the failure is located
  entirely in the pair of two-cycles.
* **Evidence:** `TrueSRCPairThirdEdge.sToRIntersection_of_single_shared_edge` (`:235`).
  The minimality claim is **not** `decide`-checked in the tree — verify it before citing.
* **Found by:** sr-route chain, ≤2026-09-28.

### B17. A superseded "not built here" claim, still quoted in a module header

* **Hole:** B. **Grade: [N]**, and **superseded**.
* `CRNT/Multistationarity/TrueSRGlueInterface.lean:16` declares `Gluable P Q → TrueSRCycle _` an
  interface with "the construction … is **not** built here". It **was** later built, as
  `Network.TrueSRPath.glueCycle` in `CRNT/Multistationarity/TrueSRGlueMaps.lean:245`.
  **Do not re-report this as an open gap.**

### B18. Files cited by docstrings that do not exist in the tree

* **Grade: [N]** — recorded so nobody spends a round looking for them.
  `CRNT/Examples/TrueSRFirstConjunctWitness.lean` (cited from
  `TrueSRDegreeTwoNoSToR.lean:15`), `HANDOFF_hole1_reaction_start.md` (cited from
  `TrueSRDegreeTwoNoSToR.lean:18`), and `scripts/hreac_needs_hSR.py` (cited from
  `TrueSRSingleSharedEdge.lean`; also `scripts/probe_*.py` referenced by `HANDOFF_gac_hole.md`
  should be checked individually). Also: `SeparatesWithin` lives in `CRNT/Graph/SourceBlocks.lean`,
  **not** under `CRNT/Multistationarity/`; no `SeparatesWithin*.lean` or `ReducedSRGraph*.lean`
  family beyond `ReducedSRGraph.lean` + `ReducedSRGraphBridge.lean` exists.

---

## 3. Cross-cutting process findings

### P1. Stated-and-elaborated ≠ correct

* **Grade: [M] where cited.**
* A6, A7, A8, A9, A10 and B1 all have the same shape: a clause of a packaged criterion was
  *stated*, and the tree typechecked, but the clause was **vacuous**, **circular**, or
  **unsatisfiable**. None of this was visible to the kernel. The standing rule this
  project learned: **check what would satisfy a clause before trusting a reduction that consumes
  it.** Concretely, for every hypothesis `h` of a criterion you intend to instantiate, write down
  a model and see whether `h` holds there.
* Source: `HANDOFF_gac_hole.md` §5e ("Three clauses tested, three defects found, all three
  repaired… None of these was visible to the kernel").

### P2. A scope disclaimer attached to a proved theorem is not a proved negative

* Modules that carry a genuinely proved theorem whose docstring says "this does not close the
  frontier branch" / "this is only a recursion principle": `sharpened_source_inequality_at_cycle_separator`
  (B4), `fill_by_decreasing_rank` (A27), `inductionStep_of_ruledBuild` (A26),
  `exists_strictScaleChain` (A30). In each case the **theorem is [M]** and the **scope claim is
  [N]**. When you cite these, cite them for what they prove, not for what they do not.

### P3. Numeric conclusions in this area need generic rates and exact counts

* **Grade: [N]**, method notes with hard-won content.
  * **Unit rates can hide the real obstruction.** The first pass at A8(ii) used unit rates and drew
    the wrong conclusion (with all rates equal, `x* ∝ c` and `⟪m,x*⟫ = 0` for *every* `m`, so all
    species fail for a degenerate reason). Generic rates are needed even to see the real
    obstruction.
  * **Angular sampling never lands on a line.** The first version of the monomolecular-3-cycle cone
    count reported 9 instead of 13 because it sampled directions; the rays must be computed
    exactly from each normal.
  * **Sanity-check your own model.** A first version of the `A + B ⇌ 2B, A + C ⇌ 2C` instance
    used unit rates and drew the wrong conclusion from it.
  * `dist_ge_of_separating_margins`-style statements are only usable after Cauchy–Schwarz: metric
    statements about cones are awkward, signed evaluations against the arrangement normals are not
    (`Network.dist_ge_of_separating_margin`).
  * Source: `HANDOFF_gac_hole.md` §5h, §5k; `scripts/probe_*.py`.

### P4. Infrastructure walls (not mathematical dead ends, but they block routes)

* **Grade: [M]** for the absence in the tree; **[N]** for the consequence.
  * **No Mathlib polytope / face-lattice / normal-fan API.** The single largest infrastructural
    blocker for hole A: the object Theorem B needs is "a family `n C ∈ C` indexed by the cones"
    — equivalently the face points of a polytope whose normal fan refines the fan — and there is
    nothing in Mathlib to build it on. (`HighCodimensionSiphonFace.lean:62–69`,
    `docs/gac-v3-face-fill-plan.md`.)
  * **`IsCompletePointedPolyhedralFan` is not defined.** `Fan` is only a `Finset` of proper cones,
    with the face-lattice and covering axioms explicitly omitted at `ToricFan.lean:47–51`
    (`docs/gac-v3-face-fill-plan.md:161–162`).
  * **The `oneBitFanFaceDependency` recursor has no caller producing geometric data.** Local atlas,
    seam certificates, common-face incidence and a well-founded recursor all exist in
    `CRNT/Geometry/FanRefinement.lean` and `ToricUniformWallMargin.lean` and audit clean — but
    nothing uses them to emit a global barrier. That caller is the single next task and has a
    completely specified signature in `docs/gac-v3-face-fill-plan.md:150–160`.
  * **A build-cache trap worth recording:** `lake build` could not replace a cached `.olean` in
    `.lake/build` ("operation not permitted"); the workaround was compiling the modified module to
    `/tmp` and overlaying it into a temporary Lean search tree. Prefer `research/scripts/checkmod.sh`,
    which is the sanctioned path and writes only into your own worktree.

### P5. Bridge-gap analysis: all three bridges are discharged; the residue is purely geometric

* **Grade: [M]**, `docs/gac-bridge-gap-analysis.lean` elaborates with **no `sorry` and no errors**.
* This is a **positive** result that closes off re-work: `ContinuousOn (γ x₀) (Ici 0)` (Dini
  lemmas weakened), `∀ t ≥ 0, (γ x₀ t).Positive` (`Network.orbit_pos_forward`, ceiling from
  `hK`/`hmaps`), and `StoichCompatible (γ x₀ 0) (γ x₀ t)`
  (`Network.stoichCompatible_of_forward_solution`). **Nothing about the orbit is missing.** The
  residue is exactly `hm`, `hstart`, `hregime` plus `hMclass`/`hpos`/`hlevel`.
* Two traps recorded there:
  * **Do not reparametrise the orbit as `fun t => γ x₀ (max t 0)`** to get global continuity: that
    curve fails `HasDerivAt` at `t = 0`, being constant to the left while the mass-action field
    there is generally nonzero.
  * **Search `CRNT/Theorems/DeficiencyZero/AsymptoticStoich.lean` / `AsymptoticStability.lean`
    before proving anything about mass-action solutions.** `sub_mem_stoichSubspace_of_solution`,
    `orbit_pos`, `exists_field_lower_bound` and `ge_mul_exp_of_forward_deriv_ge` already exist;
    bridge 3 is a three-line corollary and the first attempt reproved it from scratch.
* **Correction on record:** earlier notes claimed the blueprint criterion concludes "exactly the
  conclusion" of the residual with only `hm`, `hstart`, `hregime` left. The *conclusion* matches on
  the nose; the *hypotheses* did not — those three bridges are additional obligations. Since
  discharged, the old claim is stale.

---

## 3b. Round-1 route-doc findings (imported, IDs preserved)

These entries were written by peers on branch `holes` during round 1 and circulated by the
orchestrator. Their IDs (`A-n`, `B-n`) and their `[V]`/`[H]` grades are **preserved verbatim**,
because other agents and the orchestrator's directives already cite them by number — do not
renumber. They coexist with `§1`–`§3` above, which use the un-dashed `A1`/`B1`/`P1` scheme.
Where the two overlap, the mapping is given in the table at the end of this section; the
stronger (machine-checked) entry wins.

**Grade key for this section** (as used by the authors): `[V]` = verified by reading the cited
source in this repo or by a check that was actually run; `[H]` = hearsay.

### A-1. The `oneBit*` fan-face recursors prove the wrong statement **[V]**

* **Hole:** A. **found-by:** `arch-fanfill` · **round 1** · **revive-when:** a recursor ranking
  **ambient** faces exists with a genuinely rank-decreasing Case 1.1 → 1.2 edge.
* **What was tried:** drive Craciun v3 §7.4.3 Case 1.1 → Case 1.2 through the existing
  `oneBitFanFaceDependency` / `OneBitFanFaceSeamDependency` / `finiteOverlapDependency` recursors
  in `CRNT/Geometry/FanRefinement.lean`.
* **Why it fails:** all three rank their tasks by the `coneSpanRank` of the **projected** (`Fin n`)
  fan cell plus a strip/endpoint bit. Craciun's Case 1.1 → 1.2 edge joins two **ambient**
  (`n+1`)-dimensional faces with the *same* `π_n`-image. In that order the edge has rank change 0,
  exactly the zero-decrease case flagged in the comment at
  `hyperplaneArrangementCommonFace_rank_decrease` (`FanRefinement.lean:2221`).
* **Why this is dangerous:** a proof built on these recursors elaborates, looks right, and proves a
  different theorem. It will not fail loudly. **This is the sharpest instance of `#P1` in the
  whole ledger — read it before writing any face-fill proof.**
* **Evidence:** the ranking fields of the three recursors versus the projection-equality edge
  required by Craciun Remark 7.6 (`f-nbhd(σ₀) = ⋃{T_n : basepoint(T_n) ∈ σ}`).
* **Relationship to `#A27`:** `#A27` shows the *recursion principles* are vacuous; this shows the
  *concrete recursors* are additionally ranked on the wrong objects.

### A-2. `binaryWordValue` is the wrong termination measure **[V]**

* **Hole:** A. **found-by:** `arch-fanfill` · **round 1** · **revive-when:** a well-founded word
  order that *decreases* along the recursion edge is defined.
* **Why it fails:** it is **anti-monotone**. Later letters carry larger weights, so
  `value (α ++ [true]) = value (α ++ [false]) + 1` — the recursion runs *upward*. Craciun's
  footnote 81 says ε(α) "grows exactly in the opposite direction than the standard ordering of
  the binary numbers", confirming the Lean encoding uses the wrong order.
* **Evidence:** `CRNT/Geometry/ZeroSeparatingInduction.lean:2337`.
* **Consequence for the scale route (`#A11`, A-open-2):** any well-foundedness argument that runs
  through `binaryWordValue` is going the wrong way. Check this before building on it.

### A-3. §7.3 is **not** open — do not re-attack **[V]**

* **Hole:** A. **found-by:** `arch-fanfill` · **round 1** · **revive-when:** never.
* **Status:** closed **for a single chain**.
  `CoordinateProjectedFaceChain.preBlueprintNeighborhood`
  (`ZeroSeparatingInduction.lean:1831`) is a `def` well-founded by `termination_by k => k`, with
  `face_subset_preBlueprintNeighborhood` (`:1845`), `preBlueprintNeighborhood_projected`
  (`:1882` — the §7.3 projection-compatibility equation verbatim) and
  `isCompact_preBlueprintNeighborhood` (`:1905`) all proved.
* **What actually remains:** the *joint finite-face-lattice* version with Step 2 subdivision.
* **Note:** this is a **positive** boundary — it stops a swarm member from re-deriving §7.3.
  Recorded in the ledger because "already closed" is as expensive to re-walk as "dead".

### A-4. The ε̃ scale system (Craciun eq. 19) is **not** open — do not re-attack **[V]**

* **Hole:** A. **found-by:** `arch-fanfill` · **round 1** · **revive-when:** never.
* **Status:** proved five times over in `CRNT/Geometry/ZeroSeparatingInduction.lean`:
  `exists_binaryWordTileScale_separation_on_chain` (`:2741`),
  `exists_uniform_binaryWordTileScale_separation_on_chains` (`:2784`),
  `exists_binaryWordTileScale_separation_on_allOnes` (`:2831`),
  `exists_uniform_coherentBinaryWordTileScale_full_chain_separation` (`:2866`),
  `exists_uniform_coherentBinaryWordTileScale_separation` (`:3061`).
* **Consequence:** any route needing coherent scales *on one chain* already has them. This
  **narrows** A-open-2: the missing part is the joint finite-face-lattice coherence, not the
  per-chain scale selection (`#A30` records that `CraciunV3BlueprintScales` likewise covers only
  the scale-selection subargument).

### A-5. `Refines` is set-containment, not face-to-face equality **[V]**

* **Hole:** A. **found-by:** `arch-fanfill` · **round 1** · **revive-when:** a refinement predicate
  carrying the projection equality as a field exists.
* **Why it fails:** `Refines` (`FanRefinement.lean:94`) is set containment, and that module's own
  comment at `:3675` says the raw image family "need not satisfy the fan intersection axioms
  itself". So `π_n(B^ff_n) = B^ff_{n-1}` cannot be extracted from it.

### A-6. `IsCompletePointedPolyhedralFan` does not exist **[V]**

* **Hole:** A. **found-by:** `arch-fanfill` · **round 1** · **revive-when:** `infra-mathlib-fan`
  lands one.
* **Evidence:** `docs/gac-v3-face-fill-plan.md` records it missing; `ToricFan.lean:46–50` defines a
  fan type omitting the face-lattice and covering axioms entirely (the docstring there says so;
  `grep` for the name finds nothing under `CRNT/`).
* **Consequence:** every consumer needing completeness/pointedness has nothing to consume. Tier C
  prerequisite, not Tier B. **Duplicate of `#P4` — merged there.**

### A-7. The Anderson–Shiu route is correctly cited and must not be "corrected" **[V]**

* **Hole:** A. **found-by:** `papers-sf` · **round 1** · **revive-when:** never.
* Correct source: D. F. Anderson, *The dynamics of weakly reversible population processes near
  facets*, SIAM J. Appl. Math. **70** (2010) 1840–1858, **arXiv:0903.0901**. Theorem 3.2 is the
  near-facet estimate closing hole A's codimension-1 case.
* `CRNT/Dynamics/FacetRepulsionAndersonShiu.lean:22–24` already cites it correctly.
* **arXiv:2006.02483 is a dengue epidemiology paper and is not the source.** An early swarm brief
  asserted it was; that assertion was wrong and is recorded rather than deleted. **Keep this in the
  ledger: a wrong citation that "looks right" is exactly the failure `#P1` warns about, and
  `#A4` (of `HANDOFF`) is exactly where the Anderson–Shiu argument is used.**

### A-8. CNP does not contain the entry-loss function or the entry-time matrix **[V]**

* **Hole:** A. **found-by:** `papers-sf` · **round 1** · **revive-when:** never.
* **Consequence:** the `wmax`/`Pmax` package in `HighCodimensionSiphonFace.lean` is **not** CNP's
  construction and must not be justified by citing CNP. See `#A29` for the parallel correction on
  the Craciun v3 side.

### A-9. Craciun v3 is **arXiv:1501.02860**, not 2306.03055 **[V]**

* **Hole:** A. **found-by:** `papers-craciun` · **round 1** · **revive-when:** never.
* arXiv:2306.03055 is "Analyzing Syntactic Generalization Capacity of Pre-trained Language Models
  on Japanese Honorific Conversion" (Sekizawa & Yanaka, cs.CL). The correct paper is
  **arXiv:1501.02860**, G. Craciun, *Toric Differential Inclusions and a Proof of the Global
  Attractor Conjecture*, v3.
* The repository's own notes were right (`docs/persistence-gac.md:283`, `:300`); an earlier swarm
  brief was wrong.
* **Note:** this same wrong identifier is repeated in the round-1 task briefs. Anyone citing
  2306.03055 as Craciun is citing a language-modeling paper.

### A-10. The arXiv HTML of Craciun v3 is truncated — do not use it **[V]**

* **Hole:** A. **found-by:** `papers-craciun` · **round 1** · **revive-when:** never.
* `arxiv.org/html/1501.02860v3` ends mid-sentence in §6.1.1 and contains **no §7, §8 or §9**.
  Those are exactly the sections hole A needs. **A researcher who consults the HTML will silently
  conclude §7–§9 do not exist.** Use `arxiv.org/pdf/1501.02860v3` (91 pages, complete).
* Additionally: figures 1–15 are not machine-extractable and the constructions in §5, §6.1.1 and
  §6.2.1 are specified largely by figure reference, so their numeric blueprint data (specific ε
  values, red-dot placements, face enumerations) is **not recoverable from text**. Routes needing
  those numbers must reconstruct them or route through the textual §7.
* The LaTeX source tarball exists but the read tool cannot descend into the gzip; statements must
  be taken from the PDF.
* Craciun–Nazarov–Pantea (arXiv:1010.3050; **SIAM J. Appl. Math. 73 (2013), 305–329** — the year is
  **2013**, not 2010) contains no entry-loss function, no entry times, no entry-time matrix. Its
  mechanism is an invariant convex polygon orthogonal to normals of `conv(SC(N))`, in dimension
  ≤ 3. The entry-time machinery is D. F. Anderson, SIAM J. Appl. Math. **68** (2008), 1464–1476
  (full text not accessed; bibliographic fact only). `relEntropy` + tiers + Stiemke is Anderson
  arXiv:1101.0761.
* **Consequence:** the `wmax`/`Pmax` package in `HighCodimensionSiphonFace.lean` is **not** CNP's
  construction and must not be justified by citing CNP.
* **Scope caution (`#A29` interacts):** `#A29`'s "§8 stops after Steps 1–2" was established from
  the **PDF**, not the HTML. Anyone re-checking `#A29` must not use the HTML.

### B-1. The `hspan` witness for `no_spanning_path_of_trueSRCriterion` is **refuted** **[V]**

* **Hole:** B. **found-by:** `arch-sr-deg2` · **round 1** · **revive-when:** never, unless `hnd`
  is replaced by a satisfiable predicate.
* **What was tried:** supply the `hspan` witness (`∃ M, Q, hQ0, hQlast, hQnd`) that
  `no_spanning_path_of_trueSRCriterion` needs at `TrueChemistrySRCriterion.lean:8610` — the last
 step before the `sorry` at `:8607`.
* **Why it fails — a refutation, not a gap:** by `containsEdge_iff_cycleNeighbour`
  (`CRNT/Multistationarity/TrueSRCPairThirdEdge.lean:186`) together with
  `no_single_edge_chord_of_trueSRCriterion`
  (`CRNT/Multistationarity/TrueSRChordExtraction.lean:42`), **every** SR edge joining a cycle
  species to a cycle reaction is a cycle edge. Hence `hnd` at `:8610` fails at `p = M−1` for
  **every** candidate `Q`.
* **This is the headline finding for hole B in round 1:** the residue is not merely unproved — the
  hypothesis it needs is unsatisfiable given the lemmas already proved above it. **This subsumes
  and explains `#B3`, `#B8` and `#B9`: the `leftEdge-final` residue recorded in the source comment
  is not an oversight, it is forced.**

### B-2. Degree splitting at the residue is degenerate **[V]**

* **Hole:** B. **found-by:** `arch-sr-deg2` · **round 1** · **revive-when:** never.
* **deg 0 / deg 1:** impossible — `TrueSRDegreeTwoNoSToR.left_right_species_ne` /
  `left_not_sameIncidence_right`.
* **deg 2:** vacuous — `hQ0late` forces `Q0.vertex 1` to be an off-cycle reaction.
* **deg 3a** (extra edge to a cycle reaction): empty, by B-1.
* **deg 3b:** the only surviving case, and `hSR` is silent about it.
* **Consequence:** any degree-based case analysis at the residue must be aimed at deg 3b or not
  attempted. See also B-7 (the path is half-spanning, never spanning).

### B-3. `hrest` cannot be discharged at the residue **[V]**

* **Hole:** B. **found-by:** `arch-sr-deg2` · **round 1** · **revive-when:** the upstream case
  analysis is restructured so that `hrest` dominates line 8607.
* **Evidence:** `hrest` is **not in scope** at line 8607 — it occurs only at lines 1652, 1699, 4327,
  4466, 4536, 4665, 7035, 7117. Its natural instance at the attachment species is refuted by
  `hattachment` itself. Already documented in the docstring of
  `no_degree_two_aggregate_causal_cycle_of_offCycle_hrest` (lines 7006–7018).
* **Relationship to `#B4`:** `#B4` diagnoses *why* the `hrestOff` scope is self-refuting; this
  entry adds the sharper fact that **`hrest` is not even a hypothesis at the residue**. Anyone
  planning to "prove `hrest` at 8607" is planning to prove something not in scope.

### B-4. `no_sToRIntersection_of_degree_two` is unusable as a closer **[V]**

* **Hole:** B. **found-by:** `arch-sr-deg2` · **round 1** · **revive-when:** never.
* Its hypothesis makes the second conjunct of `TrueSRStrongCriterion` vacuous — it removes the
  very tool the residue relies on.
* **Relationship to `#B7`:** `#B7` records the theorem and its two applications; this records why
  the theorem cannot be used to *close* anything — using it deletes `hSR.2`. Read both together
  before proposing it as a route closer.

### B-5. `hopp` / `hcausal` / `¬hnc` are already sharp **[V]**

* **Hole:** B. **found-by:** `arch-sr-deg2` · **round 1** · **revive-when:** never.
* They determine the class flux at `C.species b` for **all** `n` cycle reactions exactly — two
  nonzeros of opposite sign at the two neighbours, zero elsewhere, by
  `nonAdjacent_cycleClassFlux_eq_zero`. No slack remains to strengthen.
* **Relationship to `#B2`:** consistent, and together they say the *flux* side of the residue is
  fully determined. The residue must be attacked on the **combinatorial path** side, not by
  sharpening flux information.

### B-6. The species-interior analogue does not apply **[V]**

* **Hole:** B. **found-by:** `arch-sr-deg2` · **round 1** · **revive-when:** never.
* Closing Case B via `no_reaction_species_ear_of_trueSRCriterion`
  (`TrueChemistrySRCriterion.lean:5735`) on `qC ⇝ … ⇝ q → s` fails because `s0` sits *strictly
  inside* every such path as an on-cycle species. That is precisely the S4/S5 obligation.
* **Relationship to `#B3`:** same shape — the in-tree ear lemmas are pointed the wrong way for the
  residue's path shape.

### B-7. `no_spanning_path_of_trueSRCriterion` cannot be applied to `Q0` **[V]**

* **Hole:** B. **found-by:** `arch-sr-case2` · **round 1** · **revive-when:** never.
* Blocked **provably**, not merely missing. Its hypothesis `hlast : C.HasVertex (Q.vertex ⟨M, _⟩)`
  is unsatisfiable: `hqm` puts `q` at position `m`, and `hQ0late` together with `hmpos : 0 < m`
  forces every index other than `0` off the cycle. `Q0` is **half-spanning**, never spanning.
* **Relationship to `#B9`:** `#B9` says the global `hnd` is unusable; this says even the endpoint
  hypothesis cannot be met by the residue's own path.

### B-8. `hopp` does **not** force `k = 1` here **[V]**

* **Hole:** B. **found-by:** `arch-sr-case2` · **round 1** · **revive-when:** never.
* `hopp`, `hcausal` and `¬hnc` together constrain only **cycle** classes at cycle species. The
  first hop of `Q0` lands on an **off-cycle** class, because `TrueInternalAggregateCausalEdge` has
  no `inl → inl` case.
* The source comment's "k = 1 is forced by `hopp`" is therefore **only true for a path that stays
  on the cycle**, and `Q0` is not such a path. **The comment's stated reason is wrong.**
* **Relationship to `#B2`:** `#B2` (mine) shows the *cycle* constructor cannot satisfy `hopp` at
  all; this shows `hopp` does not even *imply* the step bound the comment claims. Both point the
  same way: the residue's cycle facts are already exhausted.

### B-9. The residue's source comment is factually wrong about this tree **[V]**

* **Hole:** B. **found-by:** `arch-sr-case2` · **round 1** · **revive-when:** the port lands.
* The comment at `TrueChemistrySRCriterion.lean:8600–8607` says the residue "awaits the A.6
  Case-2 source-block datum or `hrest` degree-two isolation". **Neither exists in `holes`.**
* The A.6 Case-2 machinery — `CRNT/Multistationarity/TrueSREarCase2.lean` — was written on
  `sr-fig8` / `backup-fig8` (commit `637a970`). That branch was **`reset: moving to ef8048c`** and
  **never merged into `holes`**. The comment describes a proof architecture that is not in this
  tree.
* **Do not search `holes` for the datum. It is not there. Port it.**
* **This is the single most perishable entry in the ledger.** It corrects the source comment that
  the previous round left behind, and it invalidates the standing instruction "find the A.6 Case-2
  datum". Anyone who has been told to *find* it should stop and *port* it.

### B-10. There is no upstream case analysis to thread a datum from **[V]**

* **Hole:** B. **found-by:** `arch-sr-case2` · **round 1** · **revive-when:** never.
* `harr`, `hdecX`, `hdecY`, `CE`/`QE`/`PE`/`VE` appear **nowhere above** line 8607, and the whole
  proof constructs only **one** cycle plus **one** aggregate `RelPath`. A.6 Case-2 is not "one
  level up"; it is a different proof.
* **Consequence:** "thread the datum through the existing case analysis" is not a plan; there is no
  case analysis to thread through.

### ID mapping between the two schemes

| this section | `§1`–`§3` | note |
| --- | --- | --- |
| `A-6` | `P4` (bullet 2) | same finding, merged in `P4` |
| `A-8`, `A-10` (last bullet) | `A29` | parallel correction, different paper; keep both |
| `B-3` | `B4` | `B4` diagnoses the `hrestOff` scope; `B-3` says `hrest` is not in scope at all |
| `B-4` | `B7` | `B7` proves the theorem; `B-4` says it is unusable as a closer |
| `B-5` | — (new) | flux facts at the residue are exhausted |
| `B-1`, `B-2`, `B-6`–`B-10` | — (new) | residue-specific; no overlap with `§2` |
| `B-8` | `B2` | different fact, same direction; **B-8 is the sharper one** |

### The hole B route that survives round 1

Every other route is refuted, so this one is forced and narrow. In order:

1. **Port** from branch `backup-fig8` (commit `637a970`,
   `CRNT/Multistationarity/TrueSREarCase2.lean`) exactly four items:
   `lemmaA6_case2_twoComponents`, `lemmaA6_case2_oneComponent`,
   `TrueSRCycle.SignDirected`, `TrueSRCycle.sToRIntersectionOfTwoPaths`.
   Add a new file and import it from `CRNT.lean`. **Do not cherry-pick the branch wholesale** —
   its remaining content depends on further unmerged side branches (`sr-blocks` `84e49f2`,
   `sr-route-ear` `9285de1`).
2. **Build** `exists_second_evenCycle_of_offCycle_escape` — the ear-extraction producer, which is
   the actual blocker. Start from `relPathToTrueSRSSPath`
   (`TrueChemistrySRCriterion.lean:5475`) to lift the species-to-species `RelPath` to a
 `TrueSRSSPath`, and use the in-tree `ss_three_glued_even_of_two` (`:7976`) for parity.
3. **Only then** edit lines 8601–8607 to close the ear with the in-scope `hattachment` and feed
   the resulting two even cycles to `lemmaA6_case2_*`. The 170-line positive branch at
   8376–8546 must keep elaborating untouched: do not move the `by_cases hv0r` at `:8371`, the
   `exfalso` at `:8355`, or the `hvr` split at `:8301`.

Step 2 is worth more than steps 1 and 3 combined: it is the single theorem hole B waits on.
(Circulated by the orchestrator to the hole-B researchers, 2026-10-03; recorded here so the
ledger is the single index.)

## 3c. Framing revision — hole A re-read (round 1, `research/HOLEA-FRAMING.md`)

This section is the **highest-leverage content in the ledger**: it downgrades or kills several
routes catalogued above, and it is the reason a researcher reading `BRIEF-A.md` would aim at the
wrong target. Graded as the framing document grades itself.

**F-1. Hole A is not Craciun's Theorem B. Grade: [S]** (statement about the paper).
`BRIEF-A.md` says hole A "is exactly this paper's Theorem B". It is not. Theorem B is a statement
about an **exhaustive family of zero-separating hypersurfaces** (ZSH) for a toric differential
inclusion — and it has **no proof anywhere in the paper**: one sentence on p. 8, discharged by the
Step 0–4 programme in §4 and executed in §5 (2D), §6 (3D), §7 (nD blueprints), §8 (nD assembly).
By contrast `exists_positive_omegaPoint_of_highCodimension_siphonFace` carries a
critical-siphon-face apparatus — `hcodim`, `hmaxExact`, `hzcard`, `hrank` — that Craciun never
mentions: no siphons, no zero sets, no ω-points, no codimension. **Theorem B is a sufficient
means, not the statement.**
* **What would make it work:** n/a — this is a scoping correction.
* **Consequence for this ledger:** every entry above that describes the hole as "Craciun v3
  Theorem B" should be read with this caveat. `#A2` (the `K_{x₀}` Step-4 assembly) is the sharpest
  case: closing the hole *would* amount to proving v3 §4 Step 4, but Step 4 is not the hole's
  statement either.

**F-2. The hole's conclusion is strictly weaker than a ZSH — the blueprint induction is over-attempted. Grade: [N]** (an inference about the hole's minimal requirement; not machine-checked; `adv-refute`/`adv-audit` asked to confirm or refute).
The hole wants **one interior ω-point**. A ZSH (Definition 4.6) is much more: an exhaustive family
of surfaces with η-separation and ray-meeting properties. In particular clauses **4.6(i)**
(η-separation) and **4.6(ii)** (meeting every toric ray exactly once) can both be **dropped**.
* **Why this is a dead end, not just a demotion:** any researcher attempting the full
  faithful-blueprint induction is attempting **far more than the hole needs**. That is why this
  route has been failing for months — it is **over-attempted, not under-attempted**.
* **Compounds `A-1`:** the `oneBit*` recursors prove the wrong statement *and* the right statement
  is weaker than their target. Two independent reasons the same induction fails.
* **Status of the affected routes:** A-open-2 (flag-indexed tile shapes with a scale chain) and
  A-open-4 (the `oneBitFanFaceDependency` caller) are **demoted, not killed** — they remain
  sufficient, but they are no longer the cheapest sufficient route. See the checklist's
  re-prioritisation.

**F-3. The hole's hypotheses do not supply the fan — and never will. Grade: [N]** (as above).
Theorem B is about a toric differential inclusion `T_{F,δ}`, which requires a **polyhedral fan `F`
and a δ**. The hole's hypotheses contain **neither**. Bridging genuine trajectories to the
inclusion is **Theorem 4.3**, and Craciun *defers it entirely to [2]* (Anderson, arXiv:0903.0901).
* **So the gap is not "prove the blueprint induction". It is "the hole has no fan, and no plausible
  restatement gives it one."** Any route that needs a fan must first build it from the
  stoichiometric data — and that construction is precisely what nobody has done.
* **The unexploited asset:** `CRNT/Dynamics/ToricEmbeddingWR.lean` and
  `CRNT/Dynamics/ToricInclusion.lean` already carry the embedding at the **polar-cone level**, via
  `multiCycle_velocity_mem_polarCone` and
  `NetworkCycleDecomposition.velocity_mem_polarCone`. Nobody was looking at these in round 1.
* **Relationship to `#P4`:** `#P4` records that Mathlib has no polytope/face-lattice/normal-fan API
  and that `IsCompletePointedPolyhedralFan` is undefined. F-3 says this is not merely an
  inconvenience — it is **the blocker**, and it is a Tier C prerequisite that Tier B cannot route
  around.

**F-4. δ-uniformity machinery is unnecessary. Grade: [S]** (Remark 9.8, read from the PDF).
Per Craciun's **Remark 9.8**, **one blueprint at one δ suffices**. The "works for any fixed δ"
 flexibility means a researcher needs the *existence* of a blueprint at some δ, not uniformity over
 δ. This collapses a large part of the apparent obligation and **retires the premise that
 δ-propagation is the hard part.**
* **What was tried and is now dead:** treating "works for every δ" as a required deliverable. Note
  `docs/gac-bridge-gap-analysis.md` and `HANDOFF_gac_hole.md` §5f lean on δ-arbitrariness
  ("`δ` may be taken arbitrarily small … the separation only has to beat `B` plus an arbitrarily
  small margin") — that argument survives, but the *demand* for uniformity does not.
* **Interaction with `#A4`:** the ε̃ scale system is already proved five times over (A-4), and
 F-4 removes uniformity. Together these retire `arch-delta` and `form-scales`' round-1 premise.

**Reading the PDF, not the HTML.** F-1's author read the complete 91-page
`arxiv.org/pdf/1501.02860v3`. Per **`A-10`**, `arxiv.org/html/1501.02860v3` ends mid-§6.1.1 and
contains **no §7, §8 or §9** — a researcher consulting the HTML will silently conclude those
sections do not exist. Anyone re-checking F-1, F-2, F-4 or `#A29` **must** use the PDF. (For the
record: F-1's citation of "one sentence on p. 8" is consistent with `#A29`'s finding that v3 states
the `K_{x₀}` claim without proving it — the two are the same observation from different ends.)

**Found by:** `papers-craciun` / transcriber, round 1; circulated by the orchestrator 2026-10-03
as `research/HOLEA-FRAMING.md`. **Open:** `adv-refute` and `adv-audit` are to confirm or refute
F-2 and F-3 in round 2. Until then treat F-2/F-3 as **[N]**, and in particular **do not** delete a
blueprint route on the strength of them alone — re-prioritise it.

## 3d. Second wave of round-1 findings (orchestrator, 2026-10-03)

Same conventions as §3b: IDs and grades are the authors', preserved verbatim. Three of these are
**actionable TODOs rather than warnings**, and two of them are *repairable defects in the tree*
rather than statements about the paper.

### A-11. `CRNT.Geometry.CraciunZSH.hinterior` is FALSE as packaged — and the fix is the actionable task **[V]**

* **Hole:** A. **found-by:** orchestrator, round 1 · **revive-when:** never as stated.
* **What was tried:** instantiate the packaged criteria `..._of_convex_tiles` /
  `..._of_selfConsistent_normals` / `..._of_blueprintData` by deriving `hinterior` from the
  hypotheses at hand.
* **Why it fails:** `CraciunZSH.hinterior` uses `C ⊆ interior K_C`. Craciun's **actual** hypothesis
  is `C ⊆ relint_Ω K_C`, and the packaged version is **FALSE for every cone on a symmetry
  hyperplane `x_i = x_j`** — the normal case, per his own footnote 127. **Nobody is to attempt
  that derivation.**
* **Evidence:** the statement in `CRNT/Geometry/CraciunZSH.lean` versus Definition 4.6 / Lemma 9.7
  as printed in v3 (read from the PDF — see A-15).
* **What would make it work — THE ACTIONABLE TASK:** prove the **relint-chamber variant**. Add
  `chamber : Set E` with `C ⊆ chamber` and `chamber ⊆ K`, replace `C ⊆ interior K` by
  `∀ x ∈ C ∩ sphere 0 1, ∃ ρ > 0, ball x ρ x ⊆ K ∩ (affine span of chamber)`, and conclude
  `∃ M, ∀ x, infDist x C < δ → M < ‖x‖ → x ∈ K`. This is exactly Lemma 9.7's hypothesis and it
  **unblocks every application of the packaged criteria**.
* **Assigned:** `form-domination`, `form-tiles`, `form-barrier` — **stop trying to instantiate
  `hinterior`; do this instead.**
* **Relationship to `#A1`/`#F-2`:** a third independent instance of `#P1` — a packaged predicate
  that typechecks, is consumed by real criteria, and is false.

### A-12. There is no slack `ε(δ)` on the normal — any such Lean statement is an unproved strengthening **[V]**

* **Hole:** A. **found-by:** orchestrator (correcting its own `BRIEF-A.md` §A.5) · **round 1** ·
  **revive-when:** never without an independent proof of the strict variant.
* **Tried premise that was wrong:** "how far a normal may stray" — i.e. a quantitative bound on
  `n ∈ C` depending on `δ`.
* **Why it fails:** Lemma 9.7's normal conclusion is **NON-STRICT** (`n ∈ C`, a *closed* cone);
  the only quantification is an existential threshold realised as `‖log P‖ ≥ max_C M_C`.
* **Consequence:** **any Lean statement putting a slack `ε(δ)` on the normal is an unproved
  strengthening — do not attempt it.** This collapses part of `arch-delta`'s and `form-scales`'
  round-1 slice; both are to report it as a dead end and pivot to P1 (supply a fan, `#F-3`) or to
  the relint-chamber lemma (A-11).

### A-13. Lemma 9.5/9.7 are stated only for ℝ³/(0,1)³ — the n-dimensional upgrade is unwritten **[V]**

* **Hole:** A. **found-by:** `papers-craciun`, round 1 · **revive-when:** never — record it.
* **What was tried / what is missing:** §8 Step 2 invokes Lemma 9.7 in `n` dimensions, but 9.5/9.7
  are printed only for ℝ³ and `(0,1)³`. **The n-dimensional upgrade is not written down anywhere
  in v3 and is not derivable from the printed statements.**
* **Why it matters:** it is an *independent, unwritten generalization*. Do not assume it.
  **Proving it from scratch is a legitimate and valuable deliverable** — and, given `#F-2`
  (the hole needs much less than a ZSH), a proof of the n-dimensional 9.7 may be closer to
  sufficient than the full blueprint is.

### A-14. The width-≥δ flatness argument fails at vertices and 1-dimensional pieces **[V]**

* **Hole:** A. **found-by:** orchestrator, round 1 · **revive-when:** with an explicit interior
  hypothesis.
* **Tried:** quote the flatness claim (a zero-separating surface must be flat on a slab of width
  ≥ `δ` around every cone) as written in `HANDOFF_gac_hole.md` §4 and in the
  `HighCodimensionSiphonFace.lean` module header.
* **Why it fails:** the argument fails **at vertices and 1-dimensional pieces**, where the cone has
  empty interior. The **polyhedrality conclusion survives** via the weaker, dimension-free,
  δ-free statement.
* **Consequence:** **do not quote the flatness claim unqualified in any new module.** `#A28` in
  §1 carries the same argument and inherits this defect — read them together.

### A-15. Craciun v3 §7/§9 is unreachable via the arXiv HTML; it truncates silently **[V]**

* **Hole:** A. **found-by:** `papers-craciun`, round 1 · **revive-when:** never.
* `arxiv.org/html/1501.02860v3` ends mid-§6.1.2 with **no error**, and `#S9` anchors return the
  same prefix. **Use `https://www.alphaxiv.org/abs/1501.02860v3` or the PDF.** A researcher who
  fetches the HTML will conclude §7–§9 do not exist.
* **Relationship to `A-10`:** `A-10` records the same truncation at §6.1.1 from the PDF-side
  investigation; this gives the precise failure mode (**silent**, plus misleading anchors).
  Together they are the reason **every** §7/§8/§9 claim in this ledger is graded from the PDF.
  `papers-*`: transcribe from the PDF/alphaxiv only.

### B-11. The `TrueSREarCase2.lean` port cannot be a file copy **[V]**

* **Hole:** B. **found-by:** orchestrator, round 1 · **revive-when:** never as a copy.
* **What was tried:** copy `CRNT/Multistationarity/TrueSREarCase2.lean` from `backup-fig8`
  (`637a970`) into `holes` — the route in `B-9` / ledger §3b step 1.
* **Why it fails:** line 1 imports `CRNT.Multistationarity.TrueSREarCase1`, which **does not
  exist on `holes`**. And `TrueSRCycle.even_of_signChange` exists only as a ***private*** theorem at
  `TrueChemistrySRCriterion.lean:6885`; a public version must be proved. **Re-author from the import
  line up.**
* **Hard constraint — read this before writing the port:** the ported file **must NOT** import
  `TrueChemistrySRCriterion`. That drags `sorryAx` into its axiom footprint and couples it to the
  very file we are closing. **The branch file's comment at line 190 does this deliberately —
  preserve it.** A port that imports it produces a module whose `#print axioms` contains
  `sorryAx`, i.e. a laundering of the hole rather than progress.

### B-12. The ear can never close via `hnd`; it must terminate in `hSR.2` **[V]**

* **Hole:** B. **found-by:** orchestrator, round 1, from **B-1** · **revive-when:** never.
* By B-1 every SR edge joining a cycle species to a cycle reaction is a cycle edge, so `hnd` fails
  at `p = M−1` for **every** candidate `Q`. The ear produced by
  `exists_second_evenCycle_of_offCycle_escape` therefore **cannot** be closed through the spanning
  path machinery at all.
* **What would make it work:** the ear must terminate in the **second** conjunct `hSR.2`, via
  `lemmaA6_case2_twoComponents` / `lemmaA6_case2_oneComponent` /
  `TrueSRCycle.sToRIntersectionOfTwoPaths` — which is the whole reason the port in B-11 is
  mandatory rather than optional.
* **This is the second sentence that stands above everything else this round:**
  **hole B's residue needs an ear that closes in `hSR.2`, not `hnd`.**

**Note on the grades in §3b, §3c and §3d.** Entries in those three sections are **relayed, not
independently verified by me**. I did not re-derive the ranking fields of `FanRefinement`, the
anti-monotonicity of `binaryWordValue`, the `containsEdge_iff_cycleNeighbour` refutation, the
falsity of `CraciunZSH.hinterior`, or the absence of `TrueSREarCase1` from `holes`. They are
recorded because the orchestrator circulated them as established and because dropping them would be
worse than keeping them — but the honest grade *from my vantage point* is **"relayed, unverified
by this file's author"**, which is a notch below the `[V]` their authors earned. If you build on one,
verify it first; if you find one wrong, correct it here and say so in your commit message. Per §4.3,
a grade may only be upgraded by the agent who earns the upgrade.

## 3e. F-3 RETRACTED, and the landing site (round 1, final)

**This section retracts part of §3c.** It is kept in full rather than deleted: an entry that was
wrong, the evidence that killed it, and the two dead routes it sent researchers down are worth
more than a quiet edit. Per §4.5 of the protocol — *never delete an entry*.

### R-1. **F-3 is RETRACTED — it was false. The fan exists unconditionally.** **[V]**

* **Hole:** A. **found-by:** `arch-delta` + an `adv-audit` subagent, independently; verified by the
  orchestrator; re-verified by me against the sources. **round 1** · **revive-when:** never.
* **What F-3 claimed (§3c):** "the hole's hypotheses do not supply the fan — and never will",
  and `ToricEmbeddingWR.lean` is the highest-value asset in the tree. **Both wrong.**
* **Why F-3 is false:** the fan is already built and already proved complete.
  `Network.relativeSourceOrderStoichFan` (`CRNT/Dynamics/ComplexBalanceStoichFan.lean:98`) is
  constructed from `N.stoichSubspace` and `N.R` **alone** — no `δ`, no `hxs`, no `hcb`, no
  reference to any of the hole's hypotheses — with
  `relativeSourceOrderStoichFan_isPolyhedralFan` (`:330`) proving `CRNT.IsPolyhedralFan`,
  `exists_relativeSourceOrderConeInStoich_mem` (`:305`) proving covering,
  `relativeSourceOrderStoichFan_inter_mem` (`:140`) and `_faces_mem` (`:250`) giving
  intersection and face closure, and `relativeSourceOrderNegativeStoichFan` (`:357`) likewise
  complete.
* **And Theorem 4.3 — the embedding Craciun defers to [2] — is already proved.**
  `isInclusionSolution_massAction_relativeSourceOrder`
  (`ComplexBalanceStoichFanInclusion.lean:539`) and `isInclusionSolutionOn_…` (`:560`) take
  **exactly the hole's hypotheses** (`hxs : xstar.Positive`, `hcb : N.IsComplexBalanced κ xstar`,
  `hδ : 0 < δ`, orbit positivity, and the genuine-derivative clause `hderiv`/`hsol`) and conclude
  the trajectory solves `relativeSourceOrderToricInclusionField xstar δ`.
  Supporting layer: `massActionVectorField_mem_toricField_relativeSourceOrderNegativeStoichFan`
  (`:373`), `exists_coordinate_refinement_of_relativeSourceOrderNegativeStoichFan` (`:51`),
  `relativeSourceOrderNegativeStoichFan_hasDualFGCells` (`:33`),
  `relativeSourceOrderNegativeConeFamily_hasExposedCommonFaces` (`:802`).
* **The actual gap is wiring, and it is small:** `CRNT/Dynamics/GlobalAttractorTheorem.lean`
  imports `CRNT.Dynamics.ComplexBalanceStoichFan` at line 2 and then never mentions it — grep for
  `relativeSourceOrderStoichFan|stoichFan|_isPolyhedralFan` over all 1789 lines returns **zero
  matches** (re-derived by me). The complete fan and the inclusion bridge are compiled into the
  hole's dependency cone, fully proved, and **unused**.
* **What this kills:** §3c's F-3 and the entire P1 priority derived from it ("supply a fan from
  the stoichiometric data", "build the fan, or prove that no such fan is constructible"). **Do not
  build a fan. It is already there.**
* **What this changes for `#A29` / F-1:** nothing. F-1 (hole A is *not* Theorem B) is unaffected
  and stands — that correction was about what the hole *asks for*, not about what exists in the
  tree.

### R-2. `CRNT/Dynamics/ToricEmbeddingWR.lean` is the weaker path and is partially dead — **stop reading it** **[V]**

* **Hole:** A. **found-by:** orchestrator, round 1 · **revive-when:** never.
* **What was tried:** route hole A through `multiCycle_velocity_mem_polarCone`
  (`ToricEmbeddingWR.lean:136`) and `NetworkCycleDecomposition.velocity_mem_polarCone` (`:232`),
  which F-3 nominated as "the highest-value asset in the tree".
* **Why it fails:** both take a `CycleDecomposition` structure (`:93`) /
  `NetworkCycleDecomposition` (`:160`) that **nothing in the tree builds**, and the `mono` field is
  **refuted** by `CRNT/Examples/CycleRateNonMonotone.lean:89`
  (`tri_no_monotone_rotation`) — confirmed present at that line.
* **What would make it work:** construct the decomposition, which nobody has and which R-1 makes
  unnecessary. **Use the StoichFan path (R-1) instead.**
* **This is the cost of a false premise.** F-3 sent a dozen researchers toward a weaker,
  partly-refuted route; the cost was a round. The orchestrator recorded this as its own error
  rather than dropping it, and so does this file.

### R-3. `CraciunZSH`'s `hinterior` is load-bearing at **five** sites, not one **[V]**

* **Hole:** A. **found-by:** orchestrator, round 1 · **revive-when:** the relint-chamber fix lands.
* **Correction to `A-11`:** the `C ⊆ interior K` requirement is load-bearing at
  `exists_eventual_tube_subset_of_cone_interior` (`CRNT/Geometry/CraciunZSH.lean:32`),
  `exists_uniform_eventual_tube_subset_of_finite_properCone_pairs` (`:222`, hypothesis literally
  named `hinterior`), propagating transitively to `:186`, `:311`, `:346` and `:378`.
  (I confirmed the `hinterior` hypothesis binding at `:225`, `:314` and its uses at `:237`, `:326`.)
* **Consequence:** you are blocked at **all five**, not merely at the packaged criteria.
* **The open question, now the thing to determine:** whether
  `CRNT/Dynamics/FaceDirectionCone.lean` **routes around** these five sites or **through** them.
  **If it routes around them, that is very likely the shortest path to closing hole A.**
* **Sharper form of the fix** (orchestrator/transcriber, superseding `A-11`'s sketch): do **not**
  use `⊆ affine span` in the replacement — it is sufficient but not necessary and may be
  unprovable. Craciun's hypothesis is "C is contained in the relative interior of `K_C` **with
  respect to the set** `{X₃ ≤ X₂ ≤ X₁ ≤ 0}`". State the conclusion as
  `infDist x C < δ ∧ M < ‖x‖ → x ∈ K^sym` (union with mirror images) and **apply symmetry
  afterwards**, which is what Craciun does.
* **On `A-13` (the n-dimensional upgrade), a useful split:** the *proof* is dimension-agnostic —
  the only genuinely 3-dimensional inputs are **Lemma 9.9's diffeomorphism** and **Lemma 9.10's
  four angle clauses**. The escape step `B(C,δ) \ B(0,M) ⊂ K^sym` is a short lemma; the
  Jacobian/angle work is the expensive half. **That split is the deliverable** — proving the short
  half is a concrete, self-contained win even if the expensive half is not reached.

### R-4. The landing site: `FaceDirectionCone.lean` is already parameterised by the hole's `Pmax` **[V]**

* **Hole:** A. **found-by:** an `adv-audit` subagent, round 1 · **revive-when:** never — this is the
  place to build.
* **What this is:** `CRNT/Dynamics/FaceDirectionCone.lean` contains the exact, already-parameterised
  bridge between the fan and the hole's conclusion:
 * `faceDirectionCone P` (`:92`) — parameterised by a `Finset S` face `P`. **The hole's `Pmax` is
   exactly such a `P`.**
  * `faceLogPart` (`:204`) / `offFaceLogPart` (`:210`)
  * `faceRelevantCones P δ B` (`:317`) — the fan's near-cones within `δ + B` of `faceDirectionCone P`
  * `faceRelevantCore` (`:333`), `faceRelevantCore_mem` (`:337`), `mem_of_mem_faceRelevantCore` (`:342`)
  * terminal criteria `exists_positive_omegaPoint_of_tiled_faceCores` (`:367`) and
    **`exists_positive_omegaPoint_of_faceRelevantCore` (`:417`)**
* **Why it matters:** it is already parameterised by `δ` and `B`, and already terminates in the
  hole's exact conclusion. **Read this module before building anything.**
* **The endgame, inside the hole's own file:** `exists_positive_omegaPoint_of_upperRegion`
  (`HighCodimensionSiphonFace.lean:1596`) is the hole's own Step-4 criterion, and its **only two
  unbuilt inputs are `hfloor`** (the uniform coordinate floor) **and the non-crossing `hsplit`**.
  With the fan, the inclusion bridge and the face cores in hand, this is the natural final target.
* **What would make it work:** state the exact residual — which hypotheses of
  `exists_positive_omegaPoint_of_faceRelevantCore` / `_of_upperRegion` are derivable from what the
  hole supplies (`hzeroMax`, `hmaxExact`, `hzcard`, `hcodim`, `hcard`, `hrank`, plus the orbit
  hypotheses) and which are not. **That statement IS the hole's remaining proof.** Produce it as
  Lean signatures.
* **The supply side:** `faceRelevantCones` and `faceRelevantCore` are the hypotheses to be supplied.
  Determine what it takes to construct `faceRelevantCore` for the source-order fan — **including
  whether the tile data is available for `B` small.** Do not re-derive the fan (R-1).

### R-5. Hole B's next theorem cannot even be typed — the RR reaction-arc builder does not exist **[V]**

* **Hole:** B. **found-by:** orchestrator, round 1 · **revive-when:** the builder lands.
* **What was tried:** state `exists_second_evenCycle_of_offCycle_escape` (the surviving route,
  ledger §3b) and start proving it.
* **Why it fails:** `holes` has `C.speciesArc` / `C.speciesArcBwd`
  (`CRNT/Multistationarity/TrueSRSpeciesPath.lean:645`, `:755`) giving `TrueSRSSPath`s of a
  cycle's arcs with `SSGluable` essentially free — but `arcFwd` / `arcBwd` exist **only in the
  species flavour** (`TrueSRCycleSplit.lean:85`, `:88`). **The reaction-arc (RR) builder is the
  missing prerequisite**, and without it the target theorem cannot even be written down.
* **What would make it work:** build the RR arc builder first; **then** the ear; **then** close it
  in `hSR.2`, **never** in `hnd` (**B-12**, from **B-1**).
* **Ordering note:** this is a *typing* prerequisite, not a mathematical one. Anyone who reports
  "I could not find a way to state it" has hit this, not an obstruction.

### R-6. The `hinterior` chain is **bypassed entirely** — A-11 drops from blocker to not-needed **[V]**

* **Hole:** A. **found-by:** `arch-delta`, round 1 · **revive-when:** only for faithfulness, not
  correctness.
* **What was tried:** determine whether `CRNT/Dynamics/FaceDirectionCone.lean` routes around the
  five `hinterior` sites of `CraciunZSH.lean` (**R-3**) or through them.
* **Why it routes around:** `FaceDirectionCone.lean` imports exactly one thing —
  `import CRNT.Dynamics.ToricBarrierTrapping` (line 1) — and **never imports
  `CRNT.Geometry.CraciunZSH`**; none of `:32, :186, :222, :311, :346, :378` is reachable from it
  (grep for `CraciunZSH` / `exists_eventual_tube_subset` / `exists_uniform`: zero matches).
  The mechanism: `mem_relevantCones_of_infDist_lt` (`:300`) takes
  `hC : infDist (relativeLogFanState xstar x) C < δ` and derives membership in
  `relevantCones (faceDirectionCone P) δ B` purely from the triangle inequality plus
  `dist_relativeLogFanState_faceLogPart = ‖offFaceLogPart‖ ≤ B`. **No tube lemma.** The
  relevant-cone set is *defined* as "cones within `δ + B` of `faceDirectionCone P`", so cone
  containment is definitional; `relevantCore` is a `Finset.inf'` — an intersection, not a
  geometric enlargement.
* **The single line that is the blueprint's `hnear` clause:**
  `exact N.mem_of_mem_relevantCore (hσne k) (hm k) C (N.mem_relevantCones_of_infDist_lt P hface hbound hCF hCnear)`
  in `mem_of_mem_faceRelevantCore` (`:342`) — it hands out `m ∈ C` for every relevant `C`.
  Both terminal criteria do exactly this and are otherwise **fully proved**.
* **Consequence:** Craciun's `relint_Ω K_C` and the whole `K_C`-chamber apparatus of Lemma 9.7
  are **not on the critical path**. The role of `K_C` is played by `faceDirectionCone P`, built
  directly from the hole's own `Pmax`, and the containment `m ∈ C` is a *hypothesis* (`hm`),
  **never a geometric consequence needing a δ-tube**. The δ is **inert** — it enters only through
  `δ + B` in the definition.
* **Released:** `form-domination`, `form-tiles` are released from the `hinterior` fight. Do the
  relint-chamber fix for faithfulness eventually; **it blocks nothing.**
* **Relationship to `A-11`/`R-3`:** `R-3` is still *true* (the hypothesis is load-bearing at five
  sites) but those sites are **off the critical path**. Read them together: the chain is
  load-bearing *within `CraciunZSH`*, and `CraciunZSH` is simply not what hole A uses.

### R-7. The residual for `exists_positive_omegaPoint_of_faceRelevantCore` is four hypotheses **[V]**

* **Hole:** A. **found-by:** orchestrator / `arch-delta`, round 1.
* For the criterion at `FaceDirectionCone.lean:417`, the hole must supply exactly:
  1. **`hcore`** — `faceRelevantCones P δ B` nonempty. **Trivial**: the fan covers and
     `faceDirectionCone P` is nonempty. A three-line lemma.
  2. **`hm`** — one `m ∈ faceRelevantCore P δ B`, i.e. `m` in **every** cone within `δ + B` of
     `faceDirectionCone P`. **This is genuine content.** Candidate: the ray along the `Pmax`
     coordinate directions — but it must survive the `δ + B` thickening, which is where the
     geometry bites. **This is the substantive lemma of the branch.**
  3. **`hstart`** (`⟪-m, state (γ x₀ 0)⟫ ≤ c`) and **`hface`** — note `hface` only needs
     `c ≤ ⟪-m, ·⟫` *together with* "below `xstar` on `P` and off-part `≤ B`": a **one-sided**
     condition, **not a level set**. This matters — see `#A1`.
  4. **`hsep`** — the guarded region bounded away from every coordinate hyperplane. **See the fork
     below: this is the disputed one.**
* **The decisive question is not on this list; it is whether item 4 is chargeable at all.**

### R-8. THE FORK, first answer — `hsep` IS refutable here **[M]** — **but see §3f: the conclusion is CONTESTED**

* **Hole:** A. **found-by:** the fork was posed by the orchestrator, round 1; **the answer was
  already machine-checked and is entry `#A1` of this file.** **revive-when:** only if
  `wmax`-in-the-sublevel reasoning is broken.
* **The question:** under the hole's hypotheses, is `hsep` refutable? If yes,
  `exists_positive_omegaPoint_of_faceRelevantCore` is the **wrong** target — its `hsep` hypothesis
  cannot be discharged — and `exists_positive_omegaPoint_of_upperRegion` (`:1596`) is the right
  endgame.
* **The answer: yes, and it is `#A1`, machine-checked.** `hsep_fails_of_boundaryPoint_mem_sublevel`
  (`HighCodimensionSiphonFace.lean:184`) proves, from `hstart`, boundary membership of `wmax` in the
  sublevel, `x₀.Positive`, `wmax` nonnegative and `StoichCompatible`, that there is **no**
  `ε > 0` with `ε ≤ x s` for every positive compatible point of the closed sublevel.
  `barrier_le_of_mem_omegaLimit` (`:272`) supplies the second hypothesis: trapping along the orbit
  puts **every** ω-limit point into any sublevel that traps it, and the residual's `hmaps`/`hK`
  give exactly that. `hzeroMax` gives `wmax s = 0` for `s ∈ Pmax`, non-empty by `hcard`.
  **So the fork resolves to the `_of_upperRegion` branch**, whose only two unbuilt inputs are
  **`hfloor`** (the uniform coordinate floor) **and the non-crossing `hsplit`**. Items 1–3 above
  become moot.
  **Grading and scope — read this carefully, it is the one place where over-claiming would do real
  damage.** `#A1` is graded **[M]** because the *refutation lemma* is a Lean theorem: I located
  `hsep_fails_of_boundaryPoint_mem_sublevel` at `:184` and `barrier_le_of_mem_omegaLimit` at `:272`,
  and the module header at `:310–324` states the same conclusion. What `#A1` does **not** do — and
  what the orchestrator asked to be *established either way* — is provide a single Lean theorem
  whose hypotheses are exactly the hole's and whose conclusion is `¬ hsep` for the specific `m`, `b`,
  `R` a `_of_faceRelevantCore` instantiation would supply. **`#A1` is about a sublevel; the fork is
  about a criterion.** The refutation carries over because the sublevel is a *hypothesis* of the
  packaged criteria, but the chain from "this sublevel is refutable" to "that criterion's `hsep` is
  undischargeable" is currently prose.
  **The single most valuable lemma anyone can write right now:** make that chain explicit — state
  the `_of_faceRelevantCore` instantiation's `hsep` as a Lean term and prove it refutable from the
  hole's hypotheses. That converts the fork from a judgement call into a theorem and tells twelve
  researchers which of two targets to work on. **It is worth more than any individual lemma in the
  residual list (R-7), because R-7's item 4 is only worth discharging if the answer goes the
  other way.**
  **Who has it:** the orchestrator assigned this fork to `arch-alt`, `adv-refute`, `adv-audit`,
  `form-barrier`, `arch-fanface`. **This entry is my contribution to that assignment, not a
  substitute for it** — I have pointed at the existing machine-checked refutation and named the
  precise gap in it. Whoever closes it should update this entry and grade it `[M]` on the evidence
  of their own theorem, per §4.3.

## 3f. THE FORK IS CONTESTED — adjudicate before grinding either branch

**Read this before acting on §3e R-8.** That entry answered the fork (`hsep` refutable ⇒ go to
`_of_upperRegion`). **`form-barrier`'s compiled result agrees. `papers-craciun`'s reading
contradicts the conclusion.** Both are recorded here; **the ledger does not adjudicate**, because
the question is checkable in a few lines of Lean and should not be settled by prose.

### C-1. `form-barrier`: every packaged rung is dead; the endgame is `_of_upperRegion` **[M]**

* **found-by:** `form-barrier`, round 1 · module `CRNT/Dynamics/BlueprintRouteRefutation.lean`,
  four theorems, **compiled** (in flight).
* `floor_on_omegaLimit_of_floor_along_orbit` — a uniform coordinate floor along the forward orbit
  forces the **same** floor on every ω-limit point. Barrier-free: no `N`, no `κ`, no fan.
* `no_uniform_floor_along_orbit_of_boundaryOmegaPoint` — if `w ∈ ω` and `w s = 0`, there is **no**
  `ε > 0` with `ε ≤ γ x₀ t s` for all `t ≥ 0`. **Stronger and simpler than `#A1`**, which needs
  convexity of the sublevel; this one does not.
* `not_separationClause_of_boundaryOmegaPoint` — `hstart` + trapping + one boundary ω-point +
  compatibility **refutes `hsep`** in the exact `hsep` shape of `…_of_convex_tiles` /
  `…_of_selfConsistent_normals`. *This is precisely the Lean theorem `#A1`/`R-8` said was missing.*
* **`blueprintData_inconsistent_with_highCodimension` — the headline:** takes **exactly** the
  hypotheses of `exists_positive_omegaPoint_of_blueprintData` plus hole A's ω-limit hypotheses and
  concludes **`False`**.
* **Verdict:** every rung of the ladder — `blueprintData`, `selfConsistent_normals`,
  `convex_tiles`, `tiled_faceCores`, `faceRelevantCore`, `toric_blueprint`, `toric_halfspace` —
  routes through `exists_positive_omegaPoint_of_coordinate_floors` with `T = S`, so **all are
  dead**. The right endgame is `exists_positive_omegaPoint_of_upperRegion` (`:1596`), whose `hfloor`
  is a floor on a **region** the orbit is confined to, not along the whole orbit — so **not
  touched** by those refutations.
* **This supersedes `#A1` as the stronger form of the same refutation.** `#A1` stays (it is the
  convex-sublevel argument); this is its barrier-free sibling.

### C-2. `papers-craciun`: `_of_upperRegion` is dead too — `hfloor` is inconsistent, not unbuilt **[N]**

* **found-by:** `papers-craciun`, round 1 · **read-only inference, no build, explicitly labelled
  inference by its author.** Grade **[N]** accordingly.
* **Claim:** **both** branches are dead, including `_of_upperRegion`.
* **Argument:** the criterion's own proof at `:1560–1564` builds
  `K := closure Zupper ∩ {relEntropy ≤ L}`, proves `hKpos` from `hfloor`, and hands `ω ⊆ K` to the
  chain. Since `hwmax : wmax ∈ ω`, that `K` **must contain `wmax`**, and `hKpos` forces
  `wmax.Positive` — contradicting `hzeroMax` (`wmax s = 0` for all `s ∈ Pmax`) and `hPmaxne`.
* **Hence:** **`hfloor` is not an unbuilt input; it is an inconsistent one.** Establishing it makes
  the criterion's own conclusion false.
* **Self-correction, also important:** it corrects C-1 on `faceRelevantCore` — the `x.Positive`
  shield **does** shield `hsep` from the segment refutation, but the shield cuts both ways:
  **`hsep` is not implied by anything in the hole**; it is a strictly stronger hypothesis that
  *encodes the conclusion*. This is a sharper statement than `#A1`, and it cuts against my own
  `R-8` reasoning.
* **Its verdict:** the fan is real but is **infrastructure, not the critical path**. The live path
  is `Network.ComparableGrowthDescent` with its proved `omegaLimit_positive_of_descend`
  (`SiphonDimensionDescent.lean:137`), named in the hole's own docstring at `:139–175`.

### C-3. The dispute, stated so it can be settled **[the one question]**

**Does `hfloor` on `Zupper` conflict with `wmax ∈ ω`?**
* C-1 says **no** — it is a floor on a *region*, not a floor along the whole orbit.
* C-2 says **yes** — because `ω ⊆ closure Zupper ∩ {relEntropy ≤ L}` inside the theorem's own
  proof forces `wmax` into a set that `hKpos` makes positive.
* **The checkable core:** *inside `exists_positive_omegaPoint_of_upperRegion`'s own proof, is
  `ω ⊆ K` forced, and does `hKpos` + `hzeroMax` + `hPmaxne` then yield `False`?* Every ingredient is
  in the tree. **A `False`-level theorem either way settles it.**
* **Do not average the two verdicts.** One of them is wrong.

### C-4. Freeze instruction (2026-10-03)

**Nobody is to grind `hm`, `hstart`, `hface` or `hcore`** until C-3 is settled. C-1's point stands
regardless of which way the fork goes: if `hsep` is refutable, supplying those four inputs buys
nothing, because the criterion then yields `False` rather than the conclusion. Twelve researchers
grinding a refuted criterion is the exact waste this swarm's adversarial tier exists to prevent.
* **Adjudicators:** `adv-refute`, `adv-audit` (compile a verdict; prose is not accepted).
* **Contested party:** `form-barrier` — test head-on whether `hfloor` can be satisfied by a `Zupper`
  that does **not** contain `wmax`, i.e. whether `hsplit` can route the orbit into an upper region
  avoiding `wmax`. *This is a few lines of Lean and settles it.*
* **Fallback if `_of_upperRegion` dies:** the surviving route is `ComparableGrowthDescent`
  (`papers-craciun`, **C-2**). Note this collides with `#A13`: the descent iteration bottoms out in
  the goal itself, so the route must **exclude** branch (I) dynamically, not iterate.
* **Read `#A13` before taking the fallback.** `descendStep_iff_omegaPointPositive_of_cardMinimal`
  makes iteration useless; only a dynamical exclusion of branch (I) — consuming `hsol` essentially
  per `#A16` — can work.

### C-5. Two accepted facts, independent of how the fork lands **[M]**

* **The bridge gap analysis holds.** `docs/gac-bridge-gap-analysis.lean` elaborates with **zero
  output, zero errors, zero warnings, zero `sorry`**. But its `hMclass` hypothesis is **not**
  derivable for non-conservative networks (`#A5`), so it is a reduction to blueprint data **plus a
  bounded-class assumption**, **not** a reduction to hole A. *This qualifies `#P5` — read them
  together.*
* **The GAC chain is one `sorry` wide.** `#print axioms` on `complexBalanced_genuinePermanent`,
  `complexBalanced_permanent` and `complexBalanced_globalAttractor` each report exactly
  `[propext, sorryAx, Classical.choice, Quot.sound]`, and the transitive-import closure from
  `GlobalAttractorTheorem` (326 modules) contains **exactly one** executable `sorry`, at
  `HighCodimensionSiphonFace.lean:135`. **Closing hole A closes the GAC chain.** Hole B's file is
  **not** in that closure — so the two holes are genuinely independent, and work on one does not
 de-risk the other.

## 4. Maintenance protocol — how to keep this file alive

> **This section is load-bearing.** Twenty stale progress documents is itself a failure mode of
> this project; do not add a 21st. This file is not a progress document: it is a *negative*
> index, and it is only worth anything if it is current. Follow the protocol.

### 4.1 When to add an entry

Add an entry **the moment** you know a route failed. Specifically:

1. **You hit a wall and can say what the wall is.** Add it before you pivot, not after you land
   your replacement route.
2. **Your route doc has a dead-end section** (`research/README.md` §2, Tier A requirement:
   "an explicit statement of what is *false* or dead"). Transcribe those into here.
3. **You found a machine-checked refutation.** Grade it **[M]** and name the declaration.
4. **You noticed you were about to re-walk something in §1 or §2.** Add a cross-reference line
   under the entry you nearly duplicated *and* say so in your route doc — this is how the
   duplication rate stays low.

### 4.2 The three-line format

Append to the **relevant hole section** (`## 1.` for hole A, `## 2.` for hole B, `## 3.` for
process findings). Numbering is `A<n>` / `B<n>` / `P<n>`, continuing from the current maximum —
**never renumber existing entries**: other documents cite them by number, and renumbering silently
breaks every citation. Use the next free number.

```
### <ID>. <One-line title: what was tried and what killed it>

* **Hole:** <A|B|both>. **Grade: [M] | [N] | [S]**
* **Tried:** <what was tried — one or two sentences, concrete enough that someone can tell whether
  they are trying the same thing>
* **Why it fails:** <the obstruction>
* **Evidence:** `<file>:<line>` + `<exact declaration name>`; or `file:line` + "narrative"; or
  "checked against <source>". If no declaration, say so explicitly.
* **What would make it work:** <the missing ingredient, or "nothing — do not re-walk">
* **Found by:** <agent name> <YYYY-MM-DD>
```

Seven bullets, not three — the assignment's "three-line format" refers to the *minimum* viable
entry (`Tried` / `Why it fails` / `Evidence`); the remaining four exist because every entry in this
file has needed them at least once. A short entry with fewer than three of the seven is a sign you
have not finished diagnosing the failure. **Do not add an entry you cannot fill in.**

### 4.3 How to mark verification status — and how to upgrade it

* **[M]** — you must name a Lean declaration that proves the *failure*. If the theorem you are
  citing proves something *adjacent* and the failure is in its docstring, grade the failure **[N]**
  and say "the theorem is [M], the scope claim is [N]". See P2.
* **[N]** — mark the evidence as unverified where you can. If a finding cites a script or a file
  that is not in the tree, say so inline (B14, B18). An [N] entry with a missing source is a
  **lead**, not a fact, and must say so.
* **[S]** — reserved for statements about the *paper* verified against the published source. Cite
  the version and, where possible, the line.
* **Upgrading is a first-class contribution.** If you are the person who finally formalises an [N]
  entry (or refutes it), change the grade, add the declaration, and note
  `upgraded from [N] by <agent> <date>` in the entry. Turning a piece of hearsay into a theorem is
  worth as much as the original lemma.
* **Never upgrade an [N] to [M] on the strength of a docstring.** Run
  `research/scripts/checkmod.sh <module>` and confirm the module elaborates.

### 4.4 Also maintain `research/routes/negative-checklist.md`

That file lists the routes *currently being walked*, so a later researcher can distinguish "dead"
from "in progress". **Keep it accurate by reading the other `research/routes/*.md` files each
round** and by watching `research/LEDGER.md`'s roster. Procedure:

1. `git ls-tree -r --name-only research/swarm research/routes` and the same for each
   `research/<agent>` branch, to see what route docs exist.
2. For each new/changed route doc: note the agent, the hole, the target signature, and whether it
   duplicates an entry in `DEAD-ENDS.md`. **If it does, flag it in the route doc itself** — say
   plainly "this duplicates DEAD-ENDS #A1" — so the finding travels with the route.
3. Mark rows `active` / `stalled` / `landed` / `killed (see DEAD-ENDS #X)`.

### 4.5 What does *not* belong here

* **Not progress.** "Lemma X now compiles" is not a dead end. If a route doc's only content is
  progress, it belongs in `research/routes/`, not here.
* **Not tasks or TODOs.** If the answer is "this needs more work", that is an open route, not a
  dead end — put it in the checklist, not in §1/§2.
* **Not duplicate sources.** If three documents record the same obstruction, that is **one**
  entry with three citations. The prior art in this repo restates the convex-barrier obstruction in
  at least four places; collapsing that into one numbered entry is the whole value of this file.
* **Not speculation.** If you cannot say what would make it work, you have not diagnosed the
  failure — see 4.2.

### 4.6 Provenance of this consolidation

Round 1, `adv-negative`, 2026-10-03. Sources deduplicated:
`HANDOFF_gac_hole.md` (esp. §4, §5b–§5k, §6), `docs/gac-bridge-gap-analysis.md`,
`docs/gac-v3-face-fill-plan.md`, the narrative blocks of
`CRNT/Dynamics/HighCodimensionSiphonFace.lean` and `CRNT/Dynamics/SiphonDimensionDescent.lean`,
`CRNT/Examples/*Counterexample*.lean`, `CRNT/Examples/OmegaPointFakeFlow.lean`,
`CRNT/Examples/CodimTwoFaceModel.lean`, `CRNT/Geometry/{ConvexBarrierObstruction,
WeakReversibleWallObstruction,ZeroSeparatingInduction,CraciunV3BlueprintScales,FanFaceLattice}.lean`,
`CRNT/Dynamics/{OmegaPointPositive,FaceCodimension,FacetRepulsionAndersonShiu,GlobalAttractorTheorem}.lean`,
`CRNT/Multistationarity/{TrueChemistrySRCriterion,TrueSRCausalCycleFacts,TrueSRSingleSharedEdge,
TrueSRChordExtraction,TrueSRReactionInteriorPath,TrueSRDegreeTwoNoSToR,TrueSRSSGlueCPairs,
TrueSRMinimalChord,TrueSRCPairThirdEdge,InfluenceConcordance,ReducedSRGraph,PivotReducedInjectivity}.lean`,
`CRNT/Graph/SourceBlocks.lean`, and the `+`-annotated commits `e76e8c3 f245e05 a96ec97 76b3f03
8542230 dbe5657 f323a04 f626003 6a5b4ca be62655 35fb756 6474732 35fb756 96432b5 de87c5c`.
**On verification — read this before trusting any [M] grade below.** Line numbers and declaration
names in this file were re-derived directly from the `holes` checkout by `grep`/`read`, not copied
from a prior agent's report. The **grades themselves are inherited from the source that recorded
the finding**: an [M] entry asserts that a Lean declaration exists in the tree proving the failure,
and every such declaration was located and named here. What I did **not** do is re-elaborate the
carrying modules. A `research/scripts/checkmod.sh` pass on eight of them returned:
`CRNT/Examples/GACBlueprintPremiseCounterexamples.lean` and
`CRNT/Geometry/ConvexBarrierObstruction.lean` **elaborate**; the other six
(`CodimTwoFaceModel`, `OmegaPointFakeFlow`, `WeakReversibleWallObstruction`,
`TrueSRCausalCycleFacts`, `TrueSRSSGlueCPairs`, `TrueSRDegreeTwoNoSToR`) **failed for an
environmental reason only** — their dependency `.olean`s are absent from this worktree's search
path (`error: object file '…/HighCodimensionSiphonFace.olean' … does not exist`), not because of
any diagnostic in the module itself. Those six carry no fresh dependency builds, so their failure
is not evidence about them either way.

**So: the [M] grades rest on located declarations in a tree that is known to compile, not on a
check I ran.** That is the honest statement, and it is exactly the distinction `#P1` is about. If
you intend to build on an [M] entry, run `checkmod.sh` on its module first — from a worktree whose
dependency oleans are present. **Do not upgrade a grade on the strength of this paragraph.**

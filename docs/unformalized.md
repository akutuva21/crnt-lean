<!-- GENERATED FILE (partly). The ranking prose is curated; every count is computed by
     `python3 scripts/gen_docs.py --stats` and `scripts/gen_glossary.py`.
     Regenerate the counts with:  python3 scripts/gen_docs.py --stats
-->
# What is not formalized here

Published CRNT mathematics that this tree does **not** contain, ranked by how much it
would change the picture if it were proved.

## How to read the ranking

Three axes, in priority order:

1. **Would it close a hole?** The frozen objective is `holes = 0`. A theorem that closes
   one of the two remaining `sorry`s outranks everything else by a wide margin.
2. **Would it retire a route?** A `False`-level or `sorryAx`-level negative result is worth
   as much as a positive one here: it stops the swarm spending a round on a dead end, and
   three priority reversals this round came from exactly that.
3. **Would it enable anything?** Everything else. An unformalized theorem that is proved
   becomes an instrument; one that is merely "known" stays a rumour.

**Provenance warning, which applies to this whole document.** Almost nothing in this list is
attested by an in-tree source saying "this is not formalized". It is inferred from the
absence of a declaration, the presence of a docstring that names the gap, and the citation
harvest in [`glossary.md`](glossary.md). Items are marked **[V]** when an in-tree docstring
or ledger entry states the gap explicitly, and **[I]** when it is my inference from the
shape of the tree. Nothing here is a claim that the mathematics is open in the literature
— in several cases it is proved and merely absent here.

## Coverage as measured

| reference | modules citing it |
|---|---|
| Shiu / Nagumo differential inequalities | 13 |
| Feinberg–Horn–Jackson | 13 |
| Craciun v3 (toric inclusions, arXiv:1501.02860) | 12 |
| Shinar–Feinberg | 5 |
| Anderson–Shiu | 3 |
| Craciun, GAC v1 | 3 |

**831 of 872 modules cite no paper at all** — computed by `scripts/surface_index.py`. That is
the single most important number in this document. The tree is self-consistent, thoroughly
proved, and overwhelmingly *unattributed*: a reader cannot tell from the sources which
published result any given lemma is tracking. It also means the absence of a citation
below is weak evidence of absence of the mathematics, which is why every entry here is
justified by the positive shape of what *is* present, not by silence elsewhere.

---

## Tier 0 — would close a hole

### 0.1 Craciun v3 §8 Step 0–4: the zero-separating hypersurface construction **[V]**

*Paper:* Craciun, *Toric differential inclusions and a proof of the global attractor conjecture*,
arXiv:1501.02860 (v3). The existence claim is one sentence in §4 and is discharged by the
§§5–8 programme; §§7–8 carry out Steps 1–2 only.

*What the tree has:* the toric layer in full and unused —
`CRNT/Geometry/PolyhedralBarrier.lean` (invariance engine),
`CRNT/Dynamics/ComplexBalanceStoichFan.lean` (a complete pointed polyhedral fan over
`N.stoichSubspace`, `IsPolyhedralFan` proved), `ComplexBalanceStoichFanInclusion.lean`
(the Craciun Theorem-4.3 embedding, which Craciun himself defers to Anderson), and
`CRNT/Dynamics/FaceDirectionCone.lean` (near-cones of the fan around a face, terminating in
`exists_positive_omegaPoint_of_faceRelevantCore`).

*What is missing:* the surface itself. No module constructs a family of zero-separating
hypersurfaces, and Mathlib has no polytope, face-lattice or normal-fan API to build one on —
`docs/architecture.md` records this as the standing obstacle.

**Status changed this round, and it matters more than the entry.** Two independent
machine-checked results now bear on it. `network.universalPositive_omegaLimit_of_closedPositiveConfine`
(`CRNT/Dynamics/UpperRegionFloorRefutation.lean`) shows that *every* criterion in the tree
discharging orbit-confinement through a closed, everywhere-positive set yields the
**universal** form `∀ w ∈ ω, w.Positive`, whereas the hole asks for `∃ p ∈ ω, p.Positive`
**while permitting** a boundary ω-point. And `PersistentOrbit.omegaLimit_positive`
(`GlobalPersistence.lean:161`) already reaches the universal form from hypotheses the hole
*has*. So the whole packaged barrier family — the natural consumer of the toric layer — is
retired for one structural reason. **[I]**: the honest reading is that the toric layer is
real infrastructure with no live consumer, not a missed opportunity. A route that consumes
it must conclude *directly* rather than by confinement.

### 0.2 Anderson's comparable-growth Lyapunov estimate **[V]**

*Paper:* Anderson, the comparable-growth estimate behind the Global Attractor Conjecture;
in-tree as `Network.ComparableGrowthDescent` (`CRNT/Dynamics/SiphonDimensionDescent.lean:116-131`),
whose own docstring says the estimate is "the content not formalised here".

*State:* `descend : ∀ P, P.Nonempty → IsCriticalSiphon P → SiphonCarried ϕ x₀ P →
  (∃ p ∈ ω, p.Positive) ∨ (∃ Q, … Q.card < P.card …)` — every carried critical siphon either
coexists with a positive ω-point or forces a strictly smaller one.

*Why it is Tier 0:* `SiphonDimensionDescent.lean:158`
(`omegaLimit_positive_of_boundary_point`) takes **exactly the hole's hypotheses minus all the
`Pmax` data**, plus this one predicate. The hole is therefore a thin wrapper over it.
And `comparableGrowthDescent_iff_omegaPointPositive` (`:369`) shows the predicate is
*equivalent* to the goal at a cardinality-minimal carried siphon — so it is not a shortcut,
it is the same difficulty stated in dynamical form. **[I]**

*Line-number correction.* The orchestrator cites the blocked estimate at
`SiphonDimensionDescent.lean:531-534` with `eq_zero_on_pmax_of_conservation_eq` at `:569`.
Both are **beyond EOF** — that file is 381 lines. The intended references are
`HighCodimensionSiphonFace.lean:530` (the prose naming the blocked step) and `:573`
(the theorem `eq_zero_on_pmax_of_conservation_eq` itself). Worth correcting wherever the
citation is repeated.

### 0.3 Shinar–Feinberg: `exists_second_evenCycle_of_offCycle_escape` **[I]**

*Paper:* Shinar–Feinberg, *Structural at-systems of the complex plane* — the strong
concordance criterion behind `stronglyConcordant_fullyOpen_of_trueSRCriterion`
(`CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8607`).

*State:* when an off-cycle class is reachable from a cycle species, a second even cycle must
exist. **[I]** — I did not prove this is the right formulation; it is what the route
documents name.

*State of the machinery:* `RRGluable` (`TrueSRParityRR.lean:260-271`) is a plain public
`structure`; the public `glueArc` (`:388`) already wraps the private `prepend`, so no
privacy change is needed. `rrGluedCycle` (`:518`) rewrites into `glueCycle`, so the parity
lemmas apply. The missing pieces are the `RRGluable`/`Gluable` instances — of which
`reaction_disjoint` is the only one with content, since the species flavour has no reaction
vertex clause — and four A.6 Case-2 items that are **absent from the tree entirely**
(`lemmaA6_case2_twoComponents`, `lemmaA6_case2_oneComponent`, `TrueSRCycle.SignDirected`,
`TrueSRCycle.sToRIntersectionOfTwoPaths`; repo-wide grep, no matches). **[I]**

---

## Tier 1 — would retire routes

### 1.1 Connectedness of the ω-limit set **[V]**

Every route retired this round concludes `∀ w ∈ ω, w.Positive` where the hole needs `∃`.
The one structural fact that would separate them is that a **connected** ω-limit set cannot
be split into a positive part and a boundary part — which is what
`not_disjoint_closed_cover_omegaLimit` (`HighCodimensionSiphonFace.lean`) gestures at and
what the `exists_omegaPoint_vanishing_on_both_sides` analysis shows *cannot* fire in the
species-partition form. `IsConnected (omegaLimit atTop ϕ {x₀})` is not stated anywhere in
`CRNT/`. **[I]** This is the strongest surviving structural candidate and nobody has built
it.

### 1.2 The n-dimensional upgrade of Lemma 9.7 **[V]**

*Paper:* Craciun v3 Lemma 9.7 is stated only for `ℝ³`/`(0,1)³`, yet §8 Step 2 invokes it in
`n` dimensions. The upgrade is not written down in the paper and is not derivable from the
printed statements. **[I]** on the *split*: the Jacobian/angle work is the expensive half and
is dimension-agnostic; the escape step `B(C,δ) \ B(0,M) ⊂ K^sym` is a short lemma. Proving the
escape step alone would be a legitimate, bounded deliverable.

### 1.3 Craciun's actual relative-interior hypothesis **[V]**

`CRNT/Geometry/CraciunZSH.hinterior` requires `C ⊆ interior K_C`. Craciun's hypothesis is
`C ⊆ relint_Ω K_C`, which is **weaker and true** on symmetry hyperplanes; the packaged
version is false in the normal case (his own footnote 127). It is load-bearing at five sites
(`CraciunZSH.lean` :32, :186, :222, :311, :346, :378). **[I]** on the resolution: the fix is
a chamber variant, and per `CRNT/Dynamics/FaceDirectionCone.lean` the whole `K_C` apparatus
may now be bypassed, so this is a cleanup rather than a blocker.

---

## Tier 2 — would enable

### 2.1 Deficiency-zero and the global attractor theorem **[I]**

`CRNT/Deficiency/` is the largest area by module count after `Dynamics/` and `Multistationarity/`,
and `docs/deficiency.md` documents it at length. The **injective-for-injective-kinetics**
statement for weakly reversible deficiency-zero networks — the classical multistationarity
result — is the headline CRNT theorem whose absence from a tree this size is most surprising.
Whether it is present under another name is exactly the question the theorem index answers.

### 2.2 Signed graph transformations in the several variables **[I]**

`CRNT/Graph/` has weak and strong reversibility, linkage classes, cycle covers and source
blocks. Multiple signed graph transformations (the MSGT theorem, the modern route to
deficiency-zero multistationarity) are the standard next layer and do not appear.

### 2.3 Stochastic multistationarity **[I]**

`CRNT/Stochastic/` has 38 modules and `docs/stochastic.md` documents them. The
Anderson–Craciun–Kurtz stationary distribution is present as a product-form object; what is
absent is any *combinatorial* criterion for multistationarity in the stochastic setting,
which is the open end of that programme.

### 2.4 Oscillation beyond Hopf **[I]**

105 modules under `CRNT/Oscillation/`, with Hopf bifurcations, Floquet theory, planar
return maps and global index theorems. The Swift–Hershberg catalogue results are the
standard companions and are not obviously present.

### 2.5 The true-SR (Shinar–Feinberg) development beyond the criterion **[I]**

The `TrueSR*` family (≈20 modules) is an internally consistent, fully proved combinatorial
development whose vocabulary (`TrueSRCycle`, `TrueSREdge`, `TrueSRSSPath`, `Gluable`,
`RRGluable`) has **no one-to-one translation** into the paper's. That is itself a finding:
the tree has formalized a large amount of combinatorics that cannot currently be checked
against the source. A glossary entry mapping each construction to its paper counterpart
would make the whole family auditable — and would be a bounded, purely documentational task.

---

## The honest summary

The tree is not short of machinery. It has 846 `CRNT` modules, 9,871 declarations, 6,945
theorems, a complete toric fan, a proved embedding, a full combinatorial development of the
Shinar–Feinberg criterion, and — as of this round — a machine-checked proof that the whole
family of packaged permanence criteria is inapplicable to the remaining hole.

It is short of two things: a statement that the machinery can prove, and attribution. The
first is what the two holes are. The second is what `docs/theorem-index.md` and
`docs/glossary.md` are for, and 831 uncited modules say it is a real gap rather than a
presentational one.
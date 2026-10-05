# Hole A against the published GAC case list

Read the primary source this session: **G. Craciun, *Toric Differential Inclusions and a Proof of the
Global Attractor Conjecture*, arXiv:1501.02860v3** (fetched via `read` on `/pdf/1501.02860`; 91pp,
complete — the alphaxiv detour in DEAD-ENDS A-15 is unnecessary).

Everything marked `[SOURCED]` is quoted from that PDF.

## 1. The published case list, verbatim

§1, `[SOURCED]`:

> "The conjecture … has resisted efforts for a proof for over five decades, but proofs of many
> special cases have been obtained during this time … In particular, **Craciun, Nazarov and Pantea
> [3] have proved the three-dimensional case, and Pantea has generalized this result for the case
> where the dimension of the linear invariant subspaces is at most three** [18]. Using a different
> approach, **Anderson has proved the conjecture under the additional hypothesis that the graph G
> has a single connected component** [5], and this result has been **generalized by
> Gopalkrishnan, Miller, and Shiu for the case where G is strongly endotactic** [15]."

And it explicitly lists what the paper itself does **not** cover `[SOURCED]`:

> "The results described above do not provide a proof of the global attractor conjecture in full
> generality, and also do not provide a proof for any of the following three important special
> cases: *(i)* the case where *G* is **reversible**, *(ii)* … reversible and **detailed balanced**,
> and *(iii)* … reversible and *k*<sub>y→y′</sub> = *k*<sub>y′→y</sub>."

**Terminology correction relevant to the repo.** "single connected component" of `G` is the
single-**linkage**-class condition, i.e. `N.numLinkageClasses = 1`. DEAD-ENDS A-57/A-63 are
therefore **confirmed correct** by the primary source: under ℓ=1 Anderson's result gives "every ω-point
is positive", which contradicts the hole's own `hwmax`. So the hole's hypotheses are *inconsistent*
under ℓ=1, and that route stays closed. `[SOURCED]`

## 2. "strongly endotactic" is a published GAC case, and the repo already models it

The Gopalkrishnan–Miller–Shiu generalization is cited by Craciun as a case where **the full GAC
holds** (not merely persistence). The repo has a substantial endotactic development:

- `CRNT/Geometry/EndotacticGlobal.lean`
- `N.Endotactic`, `N.StronglyEndotacticStd`
  (`CRNT/Dynamics/TierDirectionProjection.lean:342`, `:347`;
  `CRNT/Dynamics/TierPersistence.lean:168`, `:197`, `:215`, `:457`)
- `StrongEndotacticCertificate` (`CRNT/Dynamics/GlobalPersistenceCertificates.lean:198`)

**This is the hypothesis the repo has never matched against `HighCodimensionSiphonFace.lean`'s
twenty hypotheses.** `hcodim` is `2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn Pmax))` and
`hrank : N.stoichRank ≠ 1` — neither is an endotacticity hypothesis, and nothing in
`:111-133` mentions endotacticity. So the GMS case does not cover the hole either. But it is now a
**named, citable alternative** rather than an unnamed "maybe some literature case applies", and it
belongs in the ledger as a route that was never evaluated rather than one assumed unavailable.

## 3. The in-tree interfaces already match the literature

`CRNT/Dynamics/KnownGlobalPersistenceClasses.lean` (94 lines) records the published cases as Lean
interfaces, and its docstring states `[SOURCED]`-equivalent policy:

> "No proposition in this file is an axiom: downstream code must receive a proof before using it."

| interface | line | published counterpart |
|---|---|---|
| `TwoDimensionalWRBoundedPersistenceClaim` | 52 | Pantea, dim of linear invariant subspace ≤ 3, rank 2 |
| `TwoSpeciesEndotacticPermanenceClaim` | 58 | CNP two-*species* endotactic |
| `TwoSpeciesWRPermanenceClaim` | 63 | derived from the above (`twoSpeciesWRPermanence_of_endotacticPermanence`, `:67`) |
| `IsFirstOrder` / `FirstOrderEndotacticPersistenceClaim` | 84, 90 | 2026 first-order endotactic global-stability |

**Crucially, `Pantea` is the closest published result to the hole, and it is keyed on
`N.stoichRank = 2`.** The hole carries `hrank : N.stoichRank ≠ 1`, i.e. rank ≥ 2 — so **the rank-2
sub-case of the hole is covered by a published theorem that is already sitting in the tree as an
unproved interface.**

## 4. The concrete new route this unlocks — the only one the literature suggests

Split the hole on `hcodim`/rank and try to consume `TwoDimensionalWRBoundedPersistenceClaim`:

- **rank = 2 case:** supply `N.WeaklyReversible` and `N.StructurallyBoundedPositiveTrajectories`.
  The latter is *almost* free here: the hole already has `hK`/`hmaps` for one trajectory, and
  `N.StructurallyBoundedPositiveTrajectories` quantifies over **all** `κ` and **all** `x₀`
  (`:46-48`), which is strictly more than the hole has. So this needs the boundedness upgrade, not
  the endotacticity hypothesis.
  **Caveat that may kill it:** the theorem concludes `N.StructurallyPersistentStd`, i.e. *every* ω-point
  positive — which under the hole's `hwmax`/`hzeroMax`/`hPmaxne` is `False`, not the hole's goal
  (DEAD-ENDS A-19's "universal vs existential" point). It would close the hole **by refutation of
  its hypotheses**, i.e. by proving `¬` the conjunction. That is a legitimate `False`-production
  only if the upgraded hypotheses are genuinely available; if they are not, this route is dead in
  the same way `PersistentFrom` was (A-18/A-19).
- **weak reversibility:** the hole does **not** assume it. `N.WeaklyReversible` is not among
  `:111-133`. Complex-balanced does **not** imply it (a positive complex-balanced equilibrium need
  not come from a weakly reversible network). So this case is likely closed too, and needs an
  explicit check rather than an assumption.

**Honest status: this narrows the search but does not open a route.** What it establishes is that
the hole sits in the case Craciun explicitly leaves to §8 ("Proof of the global attractor conjecture
in the *n*-dimensional case", p. 77), and that the two nearest published theorems are (a) keyed on
rank 2 + weak reversibility, neither available, and (b) keyed on strong endotacticity, which the hole
neither assumes nor is implied by.

## 5. What is *not* answered

Craciun's own §5 (2D), §6 (3D), §7 (subdivisions/blueprints), §8 (n-dimensional) are the general
construction. The hole's codim-≥2 face case is not separately treated anywhere in the paper — it is
absorbed into the general blueprint argument. **So no published shortcut exists for the hole's exact
configuration**, and DEAD-ENDS A-1/A-2/A-12/A-65 (the blueprint recursors rank the wrong quantity;
`binaryWordValue` is anti-monotone; Lemma 9.7 has no quantitative slack; the fan cannot serve the
descent) stand unrefuted by anything in the primary source.

## 6. Cited sources
- G. Craciun, *Toric Differential Inclusions and a Proof of the Global Attractor Conjecture*,
  arXiv:1501.02860v3, §1 (case list), §4 (Steps 0–4 plan), §7, §8. `[SOURCED]`
- D. F. Anderson, *A proof of the global attractor conjecture in the single linkage class case*,
  SIAM J. Appl. Math. **71**(4): 1487–1508, 2011 — confirms ℓ=1 route (DEAD-ENDS A-57/A-63).
- M. Pantea, generalization to dimension ≤ 3 of the linear invariant subspace — recorded in-tree as
  `TwoDimensionalWRBoundedPersistenceClaim`.
- M. Gopalkrishnan, E. Miller, Z. Shiu, strongly endotactic case — **not represented in-tree as a GAC
  interface**; the repo has `StrongEndotacticStd` but not the GAC conclusion. Candidate for the
  frontier ledger.

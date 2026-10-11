# HANDOFF — GAC hole (Hole A): vertex case closed, session of 2026-10-10

This is a **reduction**, not a closure.  `#print axioms
CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace` still reports `sorryAx`.

## What changed

`exists_positive_omegaPoint_of_highCodimension_siphonFace` (statement unchanged) is now proved by a
case split on `Network.IsVertexZeroSet Pmax` — "no nonzero stoichiometric vector vanishes on
`Pmax`", i.e. the `Pmax`-face of the compatibility class is the single point `wmax`:

* **vertex** — closed by `Network.false_of_vertex_omegaPoint`
  (`CRNT/Dynamics/VertexOmegaExclusion.lean`, audits clean);
* **non-vertex** — the new
  `exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex`, same hypotheses plus
  `hnv : ¬ N.IsVertexZeroSet Pmax`, carries the only `sorry` in the tree.

`three_le_stoichRank_of_nonVertex` proves that `hcodim` and `hnv` together force
`3 ≤ N.stoichRank` (via `isVertexZeroSet_of_finrank_map_eq`, rank–nullity on
`projOn Pmax` restricted to the stoichiometric subspace).  So the residual is now closed for every
network of stoichiometric rank two, and what remains is faces of dimension ≥ 1 and codimension ≥ 2.

## The vertex argument (CDSS 2009, Proposition 20; Anderson 2008, Theorem 3.7)

`relEntropy_lt_near_vertex`: the relative entropy `E` has a strict local maximum at a vertex `w`
along the class.  For `y = w + u` positive with `u` stoichiometric:

1. `relEntropyTerm_sub_le` (tangent-line form of Gibbs, from `relEntropyTerm_nonneg`):
   `E y − E w ≤ ∑ s, log (y s / x* s) · u s`.
2. On `P` (the zero set) `u s = y s < ρ`, so the factor is at most `log ρ + ∑ |log x*|`.
3. Off `P`, `|u s| ≤ w s / 2` keeps `|log (y s / x* s)|` below a constant `B`.
4. `exists_norm_le_sum_zeroSet`: on a vertex, `m · ‖u‖ ≤ ∑_{s∈P} |u s|` (compactness of the unit
   sphere of the stoichiometric subspace).
5. Choosing `log ρ = −(A + n B / m) − 1` gives `E y − E w ≤ −∑_{s∈P} u s < 0`.

`false_of_vertex_omegaPoint`: an orbit point `γ x₀ t₀` inside the ball has `E < E w`, while Lyapunov
descent from `t₀` (`genuineOrbit_relEntropy_le` on the shifted curve) and closedness of the
sublevel put the ω-point `w` below `E (γ x₀ t₀)`.

## Why this does not extend to non-vertex faces

On a face of positive dimension the entropy can increase along directions tangent to the face, so
`w` is no longer a local maximum along the class; this is exactly where Pantea (2012) needs a
separate argument for codimension-two faces in rank three and where the general case is the open
part of the conjecture.  The obstruction notes in `HighCodimensionSiphonFace.lean` (uniform floors
refutable, `PersistentFrom` equivalent to the claimed Theorem B/C) apply unchanged to the
non-vertex residual.

## Verification

* `CRNT` (752 modules incl. `VertexOmegaExclusion`, now imported by `CRNT.lean`) and
  `CRNTFrontier` (529 modules) build with zero failures.
* `test/AxiomAudit.lean` and `test/FrontierAuditCurrent.lean` pass with new pins:
  `false_of_vertex_omegaPoint` and `three_le_stoichRank_of_nonVertex` clean,
  `…_nonVertex` with `sorryAx`.
* Static gates pass; `lakefile.toml` regenerated (adds `test.BanajiCraciunAudit`).

## Environment note

330 Mathlib source files (`.lean` only, e.g. `Mathlib/Dynamics/OmegaLimit.lean`) had been left
empty by the out-of-space extraction; they were re-extracted.  Oleans were never affected.  Check
with `find Mathlib -name '*.lean' -size 0` before grepping Mathlib.

# HANDOFF — the Global Attractor Conjecture is closed (2026-10-11)

## State

* `scripts/dump_sorries.py`: **0** `sorry` in the tree.
* `complexBalanced_globalAttractor`, `complexBalanced_permanent`,
  `complexBalanced_genuinePermanent`, `exists_positive_omegaPoint_of_highCodimension_siphonFace`
  and `exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex` all depend on
  `[propext, Classical.choice, Quot.sound]` only.
* Builds: `CRNT` (814 modules) and `CRNTFrontier` (547 modules) build with 0 failures.
* Tests: `test/AxiomAudit.lean`, `test/FrontierAuditCurrent.lean`, `test/PersistenceAudit.lean`
  all pass.
* Static gates: `research/Audit/ledger_coverage.py` (verified core sorryAx-free, orphans 93),
  `scripts/check_stubs.py` (0 hollow), `scripts/check_imports.py`, `scripts/check_exclusions.py`
  all pass.

## How the residual was closed

`exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex` now follows from

    Network.complexBalanced_forward_floor :
      complex balanced at a positive x*, (γ 0) positive, γ a forward mass-action solution,
      γ bounded above for t ≥ 0  ⟹  ∃ η > 0, ∀ t ≥ 0, ∀ s, η ≤ γ t s

(`CRNT/Persistence/ComplexBalancedFloor.lean`).  With a floor, every ω-point is positive, which
contradicts `wmax s = 0` for `s ∈ Pmax`.  No ω-limit structure hypothesis of the residual is used.

## The new modules (`CRNT/Persistence/`, dependency order)

| Module | Content |
|---|---|
| `CirculationPairing` | `circulation_pairing_nonneg`: for a nonnegative circulation and a potential nonincreasing in a height, `∑ w a b · g a · (φ b − φ a) ≥ 0`. |
| `FieldDecomposition` | `dot_massActionField_nonneg`: a valid inward normal sees a nonnegative complex-balanced field. |
| `NestedEnvelope` | Blueprint trees `BTree`; `realized_of_isMin` localizes the minimizing path of the nested envelope. |
| `Arrangement` | Affine arrangements, projection, `LfsGe`, `gap_ge`, `lfsGe_update`. |
| `ColumnSegments` | One blueprint column: section/band/top segments and their chain properties. |
| `Blueprint` | `build` and `build_spec` (well-formed, proper, positive gaps, leaf feature-size bound). |
| `PathWalk` | Path enumeration, accumulated basepoint/radius, `val_eq`, `walk`. |
| `LogConversion` | `conv_up`, `conv_down`: tail-sum bounds → log-ratio bounds. |
| `LevelValidity` | `level_validity`: the sign condition for one level at a minimizing path inside the box. |
| `SortReduction` | `sort_reduce`: bubble-sort reduction to sorted points. |
| `RegionIndex` | `LevelPack`, tail-block index identities. |
| `ZeroSeparatingRegion` | `sorted_valid`, `exists_zsh` (the polyhedral region, start point, floor, band validity). |
| `ComplexBalancedFloor` | `complexBalanced_forward_floor`, via `PolyhedralBarrier.barrier_le_of_local_descent_in_band`. |

Mathematical route: Craciun v3 (toric differential inclusions), with these explicit replacements
for v3 §7–§8: (i) the region is an intersection of half-spaces `⟨a, x⟩ ≥ c` organized by level
`m` (acting on the `m+1` smallest coordinates at scale `ε^{e_m}`) and closed under permutations;
(ii) each level's offsets realize a nested lower envelope whose active facet is localized by
`realized_of_isMin`, so no vertex-by-vertex surface construction is needed; (iii) the blueprint
is built from the local feature size of the projected arrangements, and only the top
arrangement (complex differences + walls) enters the validity condition; (iv) the field
condition only needs the "downhill" half of the toric differential inclusion, which the
complex-balanced decomposition provides directly.

## Repository changes this session

* `CRNT.lean` now imports `CRNT.Persistence.ComplexBalancedFloor`,
  `CRNT.Dynamics.HighCodimensionSiphonFace`, `CRNT.Dynamics.GlobalAttractorTheorem`,
  `CRNT.Dynamics.GACLowRank`, `CRNT.Dynamics.GACVertexFacet`, `CRNT.Examples.CatalyticChainGAC`
  (graduated into the verified core).
* `research/Audit/known_holes.txt`: no entries.  `research/Audit/orphan_baseline.txt`: 93.
  `scripts/stub_baseline.txt`: 0 entries.
* `test/AxiomAudit.lean`, `test/FrontierAuditCurrent.lean`: the five former hole pins now expect
  the clean axiom set.  New `test/PersistenceAudit.lean`.
* `CRNT/Dynamics/HighCodimensionSiphonFace.lean`: proof of the residual; module docstring
  rewritten to describe the closure.

## Statement-fidelity notes

* `HasGlobalAttractorProperty` quantifies over global flows `ϕ : Flow ℝ≥0 (Concentration S)`
  (pre-existing formulation).  For networks without such a global flow it says nothing; the
  flow-free statements `complexBalanced_genuinePermanent` and `complexBalanced_forward_floor`
  carry the content independently.
* `complexBalanced_forward_floor` assumes an upper bound on the trajectory, which holds for
  complex-balanced systems (bounded sublevel sets of the relative entropy); the GAC chain supplies
  it from the compact set `K` of the residual.

## Next steps

* Continue coverage of basic CRNT (see `LEDGER.md` and `docs/`).
* Optional: generalize `complexBalanced_forward_floor` to weakly reversible systems via a toric
  differential inclusion embedding (the bounded-trajectory persistence conjecture); the region
  `exists_zsh` already handles both signs only for the downhill half, so the two-sided version of
  validity would be needed.

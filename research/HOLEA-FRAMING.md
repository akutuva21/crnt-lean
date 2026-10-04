# Hole A, reframed (round 1)

**This document supersedes the framing in `BRIEF-A.md` §A.3 and §A.5.** Everything the round-1
Tier A and papers researchers were chasing turns out to be the wrong target.

## F-1. Hole A is **not** Craciun's Theorem B

`BRIEF-A.md` says hole A is "exactly this paper's Theorem B". It is not.

Craciun's Theorem B is a statement about an **exhaustive family of zero-separating hypersurfaces**
(ZSH) for a toric differential inclusion — and it has **no proof anywhere in the paper**. It is
one sentence on p. 8, discharged by the Step 0–4 programme in §4 and executed in §5 (2D), §6 (3D),
§7 (nD blueprints) and §8 (nD assembly).

By contrast `exists_positive_omegaPoint_of_highCodimension_siphonFace` carries a
critical-siphon-face apparatus — `hcodim`, `hmaxExact`, `hzcard`, `hrank` — that Craciun never
mentions. He has no siphons, no zero sets, no ω-points, no codimension. Theorem B is **a sufficient
means** for the hole's conclusion, not its statement.

## F-2. The hole's conclusion is strictly **weaker** than a ZSH — attack far less

The hole wants **one interior ω-point**. A ZSH (Definition 4.6) is much more: an exhaustive family
of surfaces with η-separation and ray-meeting properties. In particular clauses **4.6(i)**
(η-separation) and **4.6(ii)** (meeting every toric ray exactly once) can both be **dropped**.

**Consequence:** any researcher attempting the full faithful-blueprint induction is attempting far
more than the hole needs. That is why this route has been failing for months — it is over-attempted,
not under-attempted. Note this compounds entry **A-1**: the `oneBit*` recursors prove the wrong
statement *and* the right statement is weaker than what they target.

## F-3. **The hole's hypotheses do not supply the fan — and never will**

This is the real blocker.

Theorem B is about a toric differential inclusion `T_{F,δ}`, which requires a **polyhedral fan
`F` and a δ**. The hole's hypotheses contain **neither**. Bridging genuine trajectories to the
inclusion is **Theorem 4.3**, and Craciun *defers it entirely to [2]* (Anderson, arXiv:0903.0901).

So the gap is **not** "prove the blueprint induction". It is **"the hole has no fan, and no
plausible restatement gives it one"**. Any route that needs a fan must first build the fan from the
stoichiometric data — and that construction is precisely what nobody has done.

**Where the embedding machinery already lives:** `CRNT/Dynamics/ToricEmbeddingWR.lean` and
`CRNT/Dynamics/ToricInclusion.lean` already carry the embedding at the polar-cone level, via
`multiCycle_velocity_mem_polarCone` and `NetworkCycleDecomposition.velocity_mem_polarCone`. This is
the highest-value existing asset for F-3 and nobody was looking at it in round 1.

## F-4. δ-uniformity machinery is unnecessary

Per Craciun's **Remark 9.8**, **one blueprint at one δ suffices**. The "works for any fixed δ"
flexibility means a researcher needs the *existence* of a blueprint at some δ, not uniformity over
δ. That collapses a large part of the apparent obligation — and it retires the entire `arch-delta`
and `form-scales` premise that δ-propagation is the hard part.

## What to attempt instead, in priority order

1. **Supply a fan from the stoichiometric data.** Construct, from the hypotheses actually present
   (stoichiometric subspace, complex-balanced equilibrium `hcb`, the critical siphon, `Pmax`), a
   complete pointed polyhedral fan `F` in the relevant coordinates. Read `ToricEmbeddingWR.lean` and
   `ToricInclusion.lean` first — the polar-cone-level embedding may already give `F` implicitly.
   **This is the top priority.**
2. **Weaken the target to what the hole actually needs** (F-2) and find the cheapest surface-like
   or point-like certificate that satisfies the *weakened* conclusion. A ZSH is not required.
3. Only then, and only if 1 and 2 fail, attack the blueprint induction — and then only with an
   **ambient-rank-decreasing** recursor (entry A-1 says the existing projected-rank recursors prove
   a different theorem).

**Do not** spend another round on §7.4.3 faithful blueprints at full strength, on δ-uniformity, or
on the `oneBit*` recursors.

## Evidence grades

All of the above is `[V]` as to the paper's contents — the transcriber read the complete 91-page
PDF. F-2 and F-3 are **inferences** about the hole's minimal requirement drawn from those contents
plus the hole's statement; they have not been machine-checked, and `adv-refute` / `adv-audit` are
asked to confirm or refute them in round 2.
import CRNT.Dynamics.TierScaleTruncation

/-!
# Structural partner in the strict-upward case of Lemma 4.5

The difficult case of Lemma 4.5 starts with a reaction whose source is strictly below its target.
Truncate a multiscale decomposition at that reaction's first separating scale.  The truncated
sequence is transversal, hence tier descending in a tier-descending network.  A descending reaction
from its top source tier then has source strictly above the bad reaction's source.
-/

open Filter
open scoped BigOperators Topology


/-!
## Open obligation: `hfirst` in `strictUpwardScalePartner`

The `by_contra hns` block below attempts to prove

    TierStrictBelow (D.truncatedSequence ibad) (N.reaction r).source (N.reaction rstar).source

but that goal is **false under its own hypotheses**, so no tactic repair will close it. The
enclosing branch assumes `ibad < isrc`, where `isrc` is the *first* level at which the
`(r.source, rstar.source)` gap is nonzero. Every gap at level `≤ ibad` therefore vanishes, which is
exactly what `hsameTr` records: the two complexes are `TierSame` in the sequence truncated at
`ibad`. And `TierStrictBelow.not_same_reverse` (in `CRNT/Dynamics/TierOrderAlgebra.lean`) shows
`TierSame` and `TierStrictBelow` are mutually exclusive.

So the contradiction for `hfirst` has to come from somewhere else. The available material is
`hbadTr` (`r.source` strictly below `r.target` in the truncated sequence) and `htop`/`htrDesc` (the
truncated sequence still satisfies tier-descent, with its own top-source-tier witness `rstar'`).
Relating `rstar.source` to `r.target` through that descent is the missing step, and it is the
mathematical content of Lemma 4.5's strict-upward case rather than a proof-engineering detail.
Reconstructing it would mean inventing the argument, so it is left explicit.

This module has no reverse dependencies anywhere in the tree, so it is carried on the frontier
ledger rather than blocking `import CRNT`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A strict comparison visible after a scale truncation was already strict in the original tier
sequence. -/
theorem TierScaleDecomposition.strictBelow_original_of_truncated
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (htier : N.IsTierSequence xs)
    (k : Fin D.levels) {y y' : Complex S} (hy : y ∈ N.complexes) (hy' : y' ∈ N.complexes)
    (htr : TierStrictBelow (D.truncatedSequence k) y y') :
    TierStrictBelow xs y y' := by
  have hposTr := D.truncatedSequence_positive k
  have hcmp := htier.2.2 y hy y' hy'
  rcases hcmp with hle | hrev
  · rcases hle with hstrict | hsame
    · exact hstrict
    · have hsameTr := D.same_truncated_of_gaps_zero k (fun j _ =>
        D.same_gap_zero hy hy' hsame j)
      exact False.elim (htr.not_same_reverse hposTr (hsameTr.symm hposTr))
  · have hrevTrLE : TierLE (D.truncatedSequence k) y' y :=
      D.tierLE_truncated htier k hy' hy (Or.inl hrev)
    exact False.elim (htr.not_tierLE_reverse hposTr hrevTrLE)

/-- Structural data selected in the strict-upward case before proving the domination estimate. -/
structure StrictUpwardStructuralPartner (N : Network S)
    (xs : ℕ → Concentration S) (r : N.R) where
  partner : N.R
  source_strict : TierStrictBelow xs (N.reaction r).source (N.reaction partner).source
  partner_descends : TierStrictBelow xs (N.reaction partner).target
    (N.reaction partner).source

/-- **Structural half of the strict-upward case of Lemma 4.5.** -/
noncomputable def TierDescending.strictUpwardStructuralPartner
    {N : Network S} (htd : N.TierDescending)
    {xs : ℕ → Concentration S} (htrans : N.IsTransversalTierSequence xs)
    (D : N.TierScaleDecomposition xs) (r : N.R)
    (hup : TierStrictBelow xs (N.reaction r).source (N.reaction r).target) :
    N.StrictUpwardStructuralPartner xs r := by
  classical
  let i : Fin D.levels := Classical.choose
    (D.strict_first (N.source_mem_complexes r) (N.target_mem_complexes r) hup)
  have hi := Classical.choose_spec
    (D.strict_first (N.source_mem_complexes r) (N.target_mem_complexes r) hup)
  have htrTrans : N.IsTransversalTierSequence (D.truncatedSequence i) := by
    simpa [i] using D.truncated_isTransversalTierSequence_at_reaction htrans.1 r hup
  have htrDesc : N.IsTierDescendingSequence (D.truncatedSequence i) := htd _ htrTrans
  let rstar : N.R := Classical.choose htrDesc.2
  have htop := (Classical.choose_spec htrDesc.2).1
  have hstar := (Classical.choose_spec htrDesc.2).2
  have htrUp : TierStrictBelow (D.truncatedSequence i)
      (N.reaction r).source (N.reaction r).target :=
    D.strictBelow_truncated_of_first i i le_rfl hi.1 hi.2
  have htrSrc : TierStrictBelow (D.truncatedSequence i)
      (N.reaction r).source (N.reaction rstar).source := by
    have hle := htop r
    rcases hle with hstrict | hsame
    · exact hstrict
    · have htopr : N.IsTopSourceTier (D.truncatedSequence i) r := by
        intro q
        exact (htop q).trans (D.truncatedSequence_positive i)
          (Or.inr (hsame.symm (D.truncatedSequence_positive i)))
      have hdown := htrDesc.1 r htopr
      exact False.elim (htrUp.not_tierLE_reverse (D.truncatedSequence_positive i) hdown)
  have hsrcOrig : TierStrictBelow xs
      (N.reaction r).source (N.reaction rstar).source :=
    D.strictBelow_original_of_truncated htrans.1 i
      (N.source_mem_complexes r) (N.source_mem_complexes rstar) htrSrc
  have hstarOrig : TierStrictBelow xs
      (N.reaction rstar).target (N.reaction rstar).source :=
    D.strictBelow_original_of_truncated htrans.1 i
      (N.target_mem_complexes rstar) (N.source_mem_complexes rstar) hstar
  exact ⟨rstar, hsrcOrig, hstarOrig⟩

/-- Scale-aware structural partner. -/
structure StrictUpwardScalePartner (N : Network S)
    {xs : ℕ → Concentration S} (D : N.TierScaleDecomposition xs) (r : N.R) where
  partner : N.R
  source_bad : TierStrictBelow xs (N.reaction r).source (N.reaction r).target
  source_strict : TierStrictBelow xs (N.reaction r).source (N.reaction partner).source
  partner_descends : TierStrictBelow xs (N.reaction partner).target
    (N.reaction partner).source
  source_first_le_bad_first :
    let ibad : Fin D.levels := Classical.choose
      (D.strict_first (N.source_mem_complexes r) (N.target_mem_complexes r) source_bad)
    let isrc : Fin D.levels := Classical.choose
      (D.strict_first (N.source_mem_complexes r) (N.source_mem_complexes partner) source_strict)
    isrc ≤ ibad

/-- The partner source separates from the bad source no later than the bad reaction separates from
its target. -/
noncomputable def TierDescending.strictUpwardScalePartner
    {N : Network S} (htd : N.TierDescending)
    {xs : ℕ → Concentration S} (htrans : N.IsTransversalTierSequence xs)
    (D : N.TierScaleDecomposition xs) (r : N.R)
    (hup : TierStrictBelow xs (N.reaction r).source (N.reaction r).target) :
    N.StrictUpwardScalePartner D r := by
  classical
  -- The partner has to be the one produced by tier-descent *on the truncated sequence at
  -- `ibad`*, not an arbitrary structural partner.  `strictUpwardStructuralPartner` forgets
  -- the truncated-level strictness, and without it the index bound `isrc ≤ ibad` simply does
  -- not hold for the partner it returns.  So the construction is inlined here, keeping
  -- `htrSrc`, which is exactly what pins the first separation inside the first `ibad` levels.
  let ibad : Fin D.levels := Classical.choose
    (D.strict_first (N.source_mem_complexes r) (N.target_mem_complexes r) hup)
  have hibad := Classical.choose_spec
    (D.strict_first (N.source_mem_complexes r) (N.target_mem_complexes r) hup)
  have htrTrans : N.IsTransversalTierSequence (D.truncatedSequence ibad) := by
    simpa [ibad] using D.truncated_isTransversalTierSequence_at_reaction htrans.1 r hup
  have htrDesc : N.IsTierDescendingSequence (D.truncatedSequence ibad) := htd _ htrTrans
  let rstar : N.R := Classical.choose htrDesc.2
  have htop := (Classical.choose_spec htrDesc.2).1
  have hstarTr := (Classical.choose_spec htrDesc.2).2
  have htrUp : TierStrictBelow (D.truncatedSequence ibad)
      (N.reaction r).source (N.reaction r).target :=
    D.strictBelow_truncated_of_first ibad ibad le_rfl hibad.1 hibad.2
  have htrSrc : TierStrictBelow (D.truncatedSequence ibad)
      (N.reaction r).source (N.reaction rstar).source := by
    rcases htop r with hstrict | hsame
    · exact hstrict
    · have htopr : N.IsTopSourceTier (D.truncatedSequence ibad) r := by
        intro q
        exact (htop q).trans (D.truncatedSequence_positive ibad)
          (Or.inr (hsame.symm (D.truncatedSequence_positive ibad)))
      have hdown := htrDesc.1 r htopr
      exact False.elim (htrUp.not_tierLE_reverse (D.truncatedSequence_positive ibad) hdown)
  have hsrc : TierStrictBelow xs
      (N.reaction r).source (N.reaction rstar).source :=
    D.strictBelow_original_of_truncated htrans.1 ibad
      (N.source_mem_complexes r) (N.source_mem_complexes rstar) htrSrc
  have hstar : TierStrictBelow xs
      (N.reaction rstar).target (N.reaction rstar).source :=
    D.strictBelow_original_of_truncated htrans.1 ibad
      (N.target_mem_complexes rstar) (N.source_mem_complexes rstar) hstarTr
  refine ⟨rstar, hup, hsrc, hstar, ?_⟩
  -- If the first separation of the two sources came strictly after `ibad`, every gap up to
  -- `ibad` would vanish, making the two sources tier-same in `truncatedSequence ibad` and
  -- contradicting `htrSrc`.
  dsimp only
  by_contra hnot
  have hibad_lt : ibad < Classical.choose
      (D.strict_first (N.source_mem_complexes r) (N.source_mem_complexes rstar) hsrc) :=
    lt_of_not_ge hnot
  have hisrc := Classical.choose_spec
    (D.strict_first (N.source_mem_complexes r) (N.source_mem_complexes rstar) hsrc)
  have hzero : ∀ j : Fin D.levels, j ≤ ibad →
      tierDirectionGap (D.direction j) (N.reaction r).source (N.reaction rstar).source = 0 := by
    intro j hj
    exact hisrc.1 j (lt_of_le_of_lt hj hibad_lt)
  have hsameTr := D.same_truncated_of_gaps_zero ibad hzero
  exact htrSrc.not_same_reverse (D.truncatedSequence_positive ibad)
    (TierSame.symm (D.truncatedSequence_positive ibad) hsameTr)

end Network
end CRNT

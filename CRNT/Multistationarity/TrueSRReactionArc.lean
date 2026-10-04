import CRNT.Multistationarity.TrueSRParityRR
import CRNT.Multistationarity.TrueSRGlueInterface
import CRNT.Multistationarity.TrueSRRotate

/-!
# Reaction-to-reaction arcs of a cycle

`CRNT/Multistationarity/TrueSRArc.lean` reads an arc off a `TrueSRCycle` as a
**species-to-reaction** `TrueSRPath`: from `C.species 0` to `C.reaction k` along
`leftEdge 0, rightEdge 0, leftEdge 1, …`. `TrueSRSpeciesPath.lean` has the species-to-species
flavour (`speciesArc`/`speciesArcBwd`). **The reaction-to-reaction flavour did not exist**, and
it is what Lemma A.6 Case 2 needs: every one of the five `lemmaA6_case2_arrangement*` entry
points takes an ear `C q : N.TrueSRPathRR a` — the cycle arc cut at the four attachment vertices
`R_O … R_I` — and `RRGluable` (`TrueSRParityRR.lean:260`) then feeds `glueArc`.

Before this module:

```
$ grep -rn "TrueSRPathRR" CRNT/ --include=*.lean -l
CRNT/Multistationarity/TrueSREarCase2.lean        (backup-fig8 only, never merged)
CRNT/Multistationarity/TrueSRParityRR.lean        (definition site)
CRNT/Multistationarity/TrueChemistrySRCriterion.lean   (a comment, line 5688)

$ grep -rn "first_ne_tail_edge\|first_species\|first_ne_tail_vertex" CRNT/ --include=*.lean \
    | grep -v TrueSRParityRR.lean
(nothing)
```

Nothing in the tree ever built a `TrueSRPathRR`, so the five arrangement theorems were
*unreachable* — there was no term of the shape they consume. This module supplies the first
such term.

## The construction

For `k + 1 < n` the reaction-to-reaction arc of `C` is

```
R_{r-1} --rightEdge (r-1)--> S_r --leftEdge r--> R_r --rightEdge r--> S_{r+1} -- … --> R_{r+k}
```

`TrueSRPathRR k` is exactly a leading edge plus a `TrueSRPath (2 * k + 1)` tail, so

* `first := (C.rotate r).rightEdge ⟨n - 1⟩` — the cycle edge that *enters* the arc at `S_r`.
  The `rotate r` absorbs the starting position and `n - 1 ≡ r - 1 (mod n)`, so all index
  arithmetic stays on the rotated cycle where the relevant positions are `⟨0⟩` and `⟨n - 1⟩`;
* `tail := (C.rotate r).initialArcPath k hk` — the existing species-to-reaction arc.

Total `2 * k + 2` edges, as a `TrueSRPathRR k` requires.

## Why `k + 1 < n` and not `k < n`

`k < n` is *not* enough, and the failure is a real one rather than a technicality: at `k = n - 1`
the construction walks the entire cycle, so the last vertex of the tail,
`(C.rotate r).initialArcPath (n-1) _ .vertex ⟨2n-1⟩`, is `Sum.inr ⟨reaction ⟨n-1⟩⟩` — precisely
the start reaction of `first` — and `TrueSRPathRR.first_ne_tail_vertex` forbids exactly that.
`k + 1 < n` gives `k ≤ n - 2`, so every reaction position of the tail is at most `n - 2` and
therefore differs from `n - 1` by `reaction_injective`. This is also the correct arithmetical
restriction: a *proper* arc must not be the whole cycle.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

namespace TrueSRCycle

variable {n : ℕ}

/-- The last position of a nontrivial cycle. -/
def lastIdx (C : N.TrueSRCycle n) : Fin n :=
  ⟨n - 1, by have := C.nontrivial; omega⟩

/-- **The reaction-to-reaction arc of a cycle.**

`C.reactionArcFrom r k hk` runs from the cycle reaction at rotated position `n - 1` to the cycle
reaction at rotated position `k`, along `rightEdge (n - 1)` followed by the initial arc.
Requires `k + 1 < n`; see the module header for why `k < n` is not enough. -/
noncomputable def reactionArcFrom (C : N.TrueSRCycle n) (r k : ℕ) (hk : k + 1 < n) :
    N.TrueSRPathRR k where
  first := (C.rotate r).rightEdge (lastIdx C)
  tail := (C.rotate r).initialArcPath k (by have := C.nontrivial; omega)
  first_species := by
    have hsp : ((C.rotate r).rightEdge (lastIdx C)).species
        = (C.rotate r).species ⟨0, by have := C.nontrivial; omega⟩ := by
      rw [(C.rotate r).right_species (lastIdx C)]
      apply congrArg (C.rotate r).species
      apply Fin.ext
      simp only [lastIdx]
      have hnn : n - 1 + 1 = n := by omega
      rw [hnn, Nat.mod_self]
    have hvp : ((C.rotate r).initialArcPath k (by have := C.nontrivial; omega)).vertex
          (⟨0, by omega⟩ : Fin (2 * k + 2)) =
        Sum.inl ((C.rotate r).species ⟨0, by have := C.nontrivial; omega⟩) := by
      rw [(C.rotate r).initialArcPath_vertex_even (k := k)
        (hk := by have := C.nontrivial; omega) (⟨0, by omega⟩ : Fin (2 * k + 2)) (by simp)]
      simp
    rw [hsp, hvp]
  first_ne_tail_edge := by
    intro i hi
    have hi1 := i.isLt
    rcases Nat.even_or_odd i.1 with hev | hod
    · have htail := hi.2.1
      rw [(C.rotate r).initialArcPath_edge_even (k := k)
        (hk := by have := C.nontrivial; omega) i (Nat.even_iff.mp hev)] at htail
      rw [(C.rotate r).right_reaction, (C.rotate r).left_reaction] at htail
      have hidx : (lastIdx C : Fin n) = ⟨i.1 / 2, by omega⟩ :=
        (C.rotate r).reaction_injective htail
      have hval := congrArg Fin.val hidx
      simp only [lastIdx] at hval
      omega
    · have htail := hi.2.1
      have hmod : i.1 % 2 = 1 := by have := Nat.odd_iff.mp hod; omega
      rw [(C.rotate r).initialArcPath_edge_odd (k := k)
        (hk := by have := C.nontrivial; omega) i (by omega)] at htail
      rw [(C.rotate r).right_reaction, (C.rotate r).right_reaction] at htail
      have hidx : (lastIdx C : Fin n) = ⟨i.1 / 2, by omega⟩ :=
        (C.rotate r).reaction_injective htail
      have hval := congrArg Fin.val hidx
      simp only [lastIdx] at hval
      omega
  first_ne_tail_vertex := by
    intro i hi
    have hi1 := i.isLt
    rcases Nat.even_or_odd i.1 with hev | hod
    · rw [(C.rotate r).initialArcPath_vertex_even (k := k)
        (hk := by have := C.nontrivial; omega) i (Nat.even_iff.mp hev)] at hi
      exact absurd hi Sum.inr_ne_inl
    · have hmod : i.1 % 2 = 1 := by have := Nat.odd_iff.mp hod; omega
      rw [(C.rotate r).initialArcPath_vertex_odd (k := k)
        (hk := by have := C.nontrivial; omega) i (by omega)] at hi
      have hred : ((C.rotate r).rightEdge (lastIdx C)).reaction
          = (C.rotate r).reaction ⟨i.1 / 2, by omega⟩ := congrArg Subtype.val (Sum.inr.inj hi)
      rw [(C.rotate r).right_reaction] at hred
      have hidx : (lastIdx C : Fin n) = ⟨i.1 / 2, by omega⟩ :=
        (C.rotate r).reaction_injective hred
      have hval := congrArg Fin.val hidx
      simp only [lastIdx] at hval
      omega

/-- **The arc's start reaction** is the cycle reaction at rotated position `n - 1`, i.e. at
`(r - 1) mod n` in the unrotated indexing.  This is the datum `RRGluable.same_start` needs. -/
theorem reactionArcFrom_startReaction (C : N.TrueSRCycle n) (r k : ℕ) (hk : k + 1 < n) :
    (C.reactionArcFrom r k hk).startReaction.1 = (C.rotate r).reaction (lastIdx C) := by
  rw [TrueSRPathRR.startReaction]
  exact (C.rotate r).right_reaction _

/-- **The arc's end reaction** is the cycle reaction at rotated position `k`, i.e. at
`(r + k) mod n` in the unrotated indexing.  This is the datum `RRGluable.same_end` needs. -/
theorem reactionArcFrom_endReaction (C : N.TrueSRCycle n) (r k : ℕ) (hk : k + 1 < n) :
    (C.reactionArcFrom r k hk).endReaction.1 =
      (C.rotate r).reaction ⟨k, by have := C.nontrivial; omega⟩ := by
  rw [TrueSRPathRR.endReaction]
  exact congrArg Subtype.val ((C.rotate r).initialArcPath_endReaction k _)

end TrueSRCycle

end CRNT.Network
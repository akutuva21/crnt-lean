import Mathlib.Logic.Equiv.Fin.Rotate
import CRNT.Multistationarity.TrueChemistrySRGraph
import CRNT.Multistationarity.StrongConcordance
import CRNT.Graph.RelPath
import CRNT.Multistationarity.TrueSRChordExtraction
import CRNT.Multistationarity.TrueSRCPairThirdEdge
import CRNT.Multistationarity.TrueSRMinimalChord

/-!
# Inverted-import copy of `TrueSRCycleSpeciesDegree`

This draft demonstrates that the Hole B import cycle is breakable **without moving any
mathematics out of `TrueChemistrySRCriterion.lean`'s dependency cone**.  It is a standalone
module that

1. reproduces verbatim the nine `TrueChemistrySRCriterion.lean` declarations that
   `CRNT/Multistationarity/TrueSRCycleSpeciesDegree.lean` consumes, in the order they occur
   upstream, and
2. reproduces the whole body of `TrueSRCycleSpeciesDegree.lean` with its `import
   CRNT.Multistationarity.TrueChemistrySRCriterion` line removed.

The only edits relative to upstream are: three `private` keywords dropped (see the module's
docstring in `TrueChemistrySRCriterion.lean` — the claimed privacy of `trueInternalClassFlux`,
`TrueInternalAggregateCausalEdge` and `ActiveAggregateTrueReaction` is *false*, see
`research/routes/HoleB-Residue-Reduction.md` §obstacle 1 and the audit recorded in
`research/routes/`), and the removal of the cycle-importing `import` line.

Nothing here is new mathematics: every proof script below is byte-identical to the upstream one.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

open scoped BigOperators

/-! ### From `TrueChemistrySRCriterion.lean:1586-1592` -/

/-- The internal original channels alone have strictly positive signed flux at every active
species. Flow-channel terms can be dropped because strong concordance makes each of them
nonpositive. This aggregate form is useful when parallel and reverse channels are grouped by
their true-reaction class. -/
noncomputable def nonflowOriginalChannels (N : Network S) : Finset N.R := by
  classical
  exact Finset.univ.filter (fun r => ¬ N.IsFlowChannel r)

/-! ### From `TrueChemistrySRCriterion.lean:1806-1888`

Upstream this is `private`; it is de-privatised here because `TrueChemistrySRCriterion.lean`
itself uses it (at `:7367`, `:8488`, `:8526`) after the split.  Its own proof depends on
nothing private. -/

/-- Under separation, a true-reaction class has only one endpoint label at a given species,
even when its edges come from different parallel or reversed channels. -/
theorem trueSREdge_endpoint_eq_of_same_class_and_species (N : Network S)
    (hsep : N.ReactantProductSeparated) (e f : N.TrueSREdge)
    (hreaction : e.reaction = f.reaction) (hspecies : e.species = f.species) :
    e.endpoint = f.endpoint := by
  have hclass : N.trueReaction e.representative = N.trueReaction f.representative :=
    e.representative_class.trans (hreaction.trans f.representative_class.symm)
  have hsame : N.SameTrueReaction e.representative f.representative := Quotient.exact hclass
  rcases hsame with hsame | hrev
  · rcases e.endpoint_is_source_or_target with heSrc | heTgt <;>
      rcases f.endpoint_is_source_or_target with hfSrc | hfTgt
    · rw [heSrc, hfSrc, hsame.1]
    · exfalso
      have hsrc : (N.reaction e.representative).source e.species ≠ 0 := by
        rw [← heSrc]
        exact e.occurs
      have htgtE : (N.reaction e.representative).target e.species = 0 :=
        hsep e.representative e.species hsrc
      have htgtF : (N.reaction f.representative).target f.species ≠ 0 := by
        rw [← hfTgt]
        exact f.occurs
      apply htgtF
      calc
        (N.reaction f.representative).target f.species =
            (N.reaction e.representative).target e.species := by
          rw [← hspecies]
          exact (congrFun hsame.2 e.species).symm
        _ = 0 := htgtE
    · exfalso
      have hsrcF : (N.reaction f.representative).source f.species ≠ 0 := by
        rw [← hfSrc]
        exact f.occurs
      have htgtF : (N.reaction f.representative).target f.species = 0 :=
        hsep f.representative f.species hsrcF
      have htgtE : (N.reaction e.representative).target e.species ≠ 0 := by
        rw [← heTgt]
        exact e.occurs
      apply htgtE
      calc
        (N.reaction e.representative).target e.species =
            (N.reaction f.representative).target f.species := by
          rw [← hspecies]
          exact congrFun hsame.2 e.species
        _ = 0 := by simpa [hspecies] using htgtF
    · rw [heTgt, hfTgt, hsame.2]
  · rcases e.endpoint_is_source_or_target with heSrc | heTgt <;>
      rcases f.endpoint_is_source_or_target with hfSrc | hfTgt
    · exfalso
      have hsrcE : (N.reaction e.representative).source e.species ≠ 0 := by
        rw [← heSrc]
        exact e.occurs
      have htgtE : (N.reaction e.representative).target e.species = 0 :=
        hsep e.representative e.species hsrcE
      have hsrcF : (N.reaction f.representative).source f.species ≠ 0 := by
        rw [← hfSrc]
        exact f.occurs
      apply hsrcF
      calc
        (N.reaction f.representative).source f.species =
            (N.reaction e.representative).target e.species := by
          rw [← hspecies]
          exact (congrFun hrev.2 e.species).symm
        _ = 0 := htgtE
    · rw [heSrc, hfTgt, hrev.1]
    · rw [heTgt, hfSrc, hrev.2]
    · exfalso
      have htgtF : (N.reaction f.representative).target f.species ≠ 0 := by
        rw [← hfTgt]
        exact f.occurs
      have hsrcF : (N.reaction f.representative).source f.species = 0 := by
        by_contra hne
        exact htgtF (hsep f.representative f.species hne)
      have htgtE : (N.reaction e.representative).target e.species ≠ 0 := by
        rw [← heTgt]
        exact e.occurs
      apply htgtE
      calc
        (N.reaction e.representative).target e.species =
            (N.reaction f.representative).source f.species := by
          rw [← hspecies]
          exact congrFun hrev.2 e.species
        _ = 0 := hsrcF

/-! ### From `TrueChemistrySRCriterion.lean:1974-2027` -/

/-- The labeled true-SR edge realizing a nonzero reaction-vector entry.  The source endpoint is
used for positive reactant-minus-product direction and the target endpoint for negative
direction.  This choice makes c-pair parity track sign changes in the causal orbit. -/
noncomputable def trueSREdgeOfReactionVectorNe (N : Network S)
    (r : N.R) (hrint : ¬ N.IsFlowChannel r) (s : S)
    (hrs : N.reactionVector r s ≠ 0) : N.TrueSREdge := by
  have hdir : N.reactionDirectionSign r s ≠ 0 := by
    have heq : N.reactionDirectionSign r s = - N.reactionVector r s := by
      simp [reactionDirectionSign, reactionVector_apply]
    rw [heq]
    exact neg_ne_zero.mpr hrs
  by_cases hp : 0 < N.reactionDirectionSign r s
  · refine {
      species := s
      reaction := N.trueReaction r
      internal := ?_
      endpoint := (N.reaction r).source
      representative := r
      representative_class := rfl
      endpoint_is_source_or_target := Or.inl rfl
      occurs := ?_ }
    · exact hrint
    · intro hz
      have hle : N.reactionDirectionSign r s ≤ 0 := by
        simp [reactionDirectionSign, hz]
      linarith
  · have hn : N.reactionDirectionSign r s < 0 := lt_of_le_of_ne (not_lt.mp hp) (hdir)
    refine {
      species := s
      reaction := N.trueReaction r
      internal := ?_
      endpoint := (N.reaction r).target
      representative := r
      representative_class := rfl
      endpoint_is_source_or_target := Or.inr rfl
      occurs := ?_ }
    · exact hrint
    · intro hz
      have hge : 0 ≤ N.reactionDirectionSign r s := by
        simp [reactionDirectionSign, hz]
      linarith

@[simp] theorem trueSREdgeOfReactionVectorNe_species (N : Network S)
    (r : N.R) (hrint : ¬ N.IsFlowChannel r) (s : S)
    (hrs : N.reactionVector r s ≠ 0) :
    (N.trueSREdgeOfReactionVectorNe r hrint s hrs).species = s := by
  unfold trueSREdgeOfReactionVectorNe
  split <;> rfl

@[simp] theorem trueSREdgeOfReactionVectorNe_reaction (N : Network S)
    (r : N.R) (hrint : ¬ N.IsFlowChannel r) (s : S)
    (hrs : N.reactionVector r s ≠ 0) :
    (N.trueSREdgeOfReactionVectorNe r hrint s hrs).reaction = N.trueReaction r := by
  unfold trueSREdgeOfReactionVectorNe
  split <;> rfl

noncomputable local instance instTrueReactionFintype (N : Network S) :
    Fintype N.TrueReaction := Fintype.ofFinite _

/-- The net witness flux at a species, after summing all non-flow channels in one true-reaction
class. -/
noncomputable def trueInternalClassFlux (N : Network S)
    (α : N.fullyOpen.R → ℝ) (ρ : N.TrueReaction) (s : S) : ℝ := by
  classical
  exact ∑ r ∈ N.nonflowOriginalChannels.filter (fun r => N.trueReaction r = ρ),
    α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r s

/-! ### From `TrueChemistrySRCriterion.lean:4679-4702` -/

/-- True-reaction classes whose aggregate internal flux is nonzero. -/
abbrev ActiveAggregateTrueReaction (N : Network S)
    (α : N.fullyOpen.R → ℝ) (σ : S → ℝ) :=
  {ρ : N.TrueReaction // ∃ s : S, σ s ≠ 0 ∧ N.trueInternalClassFlux α ρ s ≠ 0}

/-- Vertices of the class-aggregated sign-causality graph. -/
abbrev AggregateActiveSpecies (σ : S → ℝ) := {s : S // σ s ≠ 0}

abbrev TrueInternalAggregateVertex (N : Network S)
    (α : N.fullyOpen.R → ℝ) (σ : S → ℝ) :=
  AggregateActiveSpecies σ ⊕ N.ActiveAggregateTrueReaction α σ

/-- Directed causal edges formed from aggregate class fluxes, so one quotient edge cannot mix
oppositely oriented channel representatives. -/
def TrueInternalAggregateCausalEdge (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (u v : N.TrueInternalAggregateVertex α σ) : Prop :=
  match u, v with
  | Sum.inl s, Sum.inr ρ =>
      (N.trueInternalClassFlux α ρ.1 s.1) * σ s.1 < 0
  | Sum.inr ρ, Sum.inl s =>
      0 < (N.trueInternalClassFlux α ρ.1 s.1) * σ s.1
  | Sum.inl _, Sum.inl _ => False
  | Sum.inr _, Sum.inr _ => False

/-! ### From `TrueChemistrySRCriterion.lean:4761-4797`

`exists_trueSREdge_of_nonzero_trueInternalClassFlux` is `private` upstream and is
de-privatised here because `nonAdjacent_cycleClassFlux_eq_zero` needs it after the move; it is
also used further upstream at `:5057`, `:5082`, `:8816`.  Its own dependency
`exists_nonzero_channel_of_trueInternalClassFlux` has no consumer outside this pair anywhere in
the tree, so it stays `private`.  Neither depends on any private name. -/

private theorem exists_nonzero_channel_of_trueInternalClassFlux (N : Network S)
    {α : N.fullyOpen.R → ℝ} (ρ : N.TrueReaction) (s : S)
    (hflux : N.trueInternalClassFlux α ρ s ≠ 0) :
    ∃ r, r ∈ N.nonflowOriginalChannels ∧ N.trueReaction r = ρ ∧
      α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r s ≠ 0 := by
  classical
  let A := N.nonflowOriginalChannels.filter (fun r => N.trueReaction r = ρ)
  by_contra hnone
  have hz : ∀ r ∈ A,
      α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r s = 0 := by
    intro r hr
    by_contra hne
    exact hnone ⟨r, (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2, hne⟩
  have hsum : (∑ r ∈ A,
      α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r s) = 0 :=
    Finset.sum_eq_zero hz
  apply hflux
  simpa [trueInternalClassFlux, A] using hsum

/-- A nonzero aggregate flux coordinate is witnessed by a real channel incidence, which can be
turned into a labeled true-SR edge. -/
theorem exists_trueSREdge_of_nonzero_trueInternalClassFlux (N : Network S)
    {α : N.fullyOpen.R → ℝ} (ρ : N.TrueReaction) (s : S)
    (hflux : N.trueInternalClassFlux α ρ s ≠ 0) :
    ∃ e : N.TrueSREdge, e.species = s ∧ e.reaction = ρ := by
  obtain ⟨r, hrNF, hrρ, hterm⟩ := N.exists_nonzero_channel_of_trueInternalClassFlux ρ s hflux
  have hnotflow : ¬ N.IsFlowChannel r := by
    simpa [nonflowOriginalChannels] using hrNF
  have hν : N.reactionVector r s ≠ 0 := by
    intro hz
    apply hterm
    rw [hz, mul_zero]
  refine ⟨N.trueSREdgeOfReactionVectorNe r hnotflow s hν, ?_, ?_⟩
  · simp
  · rw [N.trueSREdgeOfReactionVectorNe_reaction]
    exact hrρ

/-! ### From `TrueChemistrySRCriterion.lean:6962-7001` -/

/-- **A non-neighbor cycle reaction has zero class flux at a cycle species.**
A nonzero class flux at that species yields a labeled SR edge joining the species
`C.species j` to the reaction `C.reaction t` (`exists_trueSREdge_of_nonzero_trueInternalClassFlux`);
when `t` is neither `j` nor `(j - 1) % n` the edge is not a cycle edge
(`containsEdge_iff_cycleNeighbour`), so it is a single-edge chord of the even cycle `C`, which
`no_single_edge_chord_of_trueSRCriterion` forbids. The flux therefore vanishes — in *either*
causal direction, since the SR edge carries no orientation. -/
theorem nonAdjacent_cycleClassFlux_eq_zero (N : Network S)
    (hsep : N.ReactantProductSeparated) (hSR : N.TrueSRStrongCriterion)
    {n : ℕ} {α : N.fullyOpen.R → ℝ}
    (C : N.TrueSRCycle n) (hC : C.Even)
    (j t : Fin n) (hne : t.1 ≠ j.1) (hne' : (t.1 + 1) % n ≠ j.1) :
    N.trueInternalClassFlux α (C.reaction t) (C.species j) = 0 := by
  classical
  by_contra hz
  obtain ⟨e, hes, her⟩ :=
    N.exists_trueSREdge_of_nonzero_trueInternalClassFlux (C.reaction t) (C.species j) hz
  have huniq : ∀ f g : N.TrueSREdge, f.reaction = g.reaction → f.species = g.species →
      f.endpoint = g.endpoint :=
    fun f g hr hs => N.trueSREdge_endpoint_eq_of_same_class_and_species hsep f g hr hs
  have hnc : ¬ C.ContainsEdge e := by
    rw [N.containsEdge_iff_cycleNeighbour huniq C e j t hes her]
    intro h
    rcases h with h | h
    · exact hne (congrArg Fin.val h).symm
    · exact hne' h.symm
  exact no_single_edge_chord_of_trueSRCriterion hSR C hC huniq e j t hes her
    (fun u hu => hnc (Or.inl ⟨u, hu⟩)) (fun u hu => hnc (Or.inr ⟨u, hu⟩))

end Network
end CRNT

/-! ### `CRNT/Multistationarity/TrueSRCycleSpeciesDegree.lean`, import line removed -/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}
  {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}

namespace TrueSRCycle

variable (C : N.TrueSRCycle n)

/-- The successor index used by `C.right_species`: `finRotate n i` is `⟨(i.1 + 1) % n, _⟩`. -/
theorem finRotate_val (C : N.TrueSRCycle n) (i : Fin n) :
    (finRotate n i).1 = (i.1 + 1) % n := by
  have hn := C.nontrivial
  have hn1 : 1 < n := by omega
  have h := congrArg Fin.val (finRotate_apply i)
  simpa [Fin.add_def, hn1] using h

/-- **The cycle's own left-edge reaction is negative at that species.**  Restating `hopp` at the
index itself rather than at its successor. -/
theorem hoppAt (C : N.TrueSRCycle n)
    (hopp : ∀ i : Fin n,
      N.trueInternalClassFlux α (C.reaction (finRotate n i)) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)) < 0) (j : Fin n) :
    N.trueInternalClassFlux α (C.reaction j) (C.species j) * σ (C.species j) < 0 := by
  have hh := hopp ((finRotate n).symm j)
  rwa [Equiv.apply_symm_apply] at hh

/-- **The cycle's own right-edge reaction is positive at that species.**  Restating `hcausal` at
the index itself: `(finRotate n).symm j` is the reaction whose *right* edge meets `C.species j`. -/
theorem hcausalAt (C : N.TrueSRCycle n)
    (hcausal : ∀ i : Fin n,
      0 < N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i))) (j : Fin n) :
    0 < N.trueInternalClassFlux α (C.reaction ((finRotate n).symm j)) (C.species j) *
      σ (C.species j) := by
  have hh := hcausal ((finRotate n).symm j)
  rwa [Equiv.apply_symm_apply] at hh

/-- **Non-neighbouring cycle classes have zero flux at a cycle species.**  `nonAdjacent_cycle-
ClassFlux_eq_zero` in the `(a, b)` order used by the trichotomy below. -/
theorem classFlux_eq_zero_of_nonNeighbour (C : N.TrueSRCycle n)
    (hsep : N.ReactantProductSeparated) (hSR : N.TrueSRStrongCriterion) (hCeven : C.Even)
    (a b : Fin n) (hab : a ≠ b) (hba : b.1 ≠ (a.1 + 1) % n) :
    N.trueInternalClassFlux α (C.reaction a) (C.species b) = 0 :=
  N.nonAdjacent_cycleClassFlux_eq_zero hsep hSR C hCeven b a
    (fun h => hab (Fin.ext h)) (fun hh => hba hh.symm)

/-- **The degree-two content of a cycle species, first half: a strictly negative aggregate flux
at `C.species b` comes from the cycle reaction `C.reaction b` and from nothing else.**

So a cycle species has out-degree exactly `1` over the cycle classes, and the unique out-neighbour
is the reaction carrying its *left* edge. -/
theorem negFlux_eq_leftEdge (C : N.TrueSRCycle n) (hsep : N.ReactantProductSeparated)
    (hSR : N.TrueSRStrongCriterion) (hCeven : C.Even)
    (hcausal : ∀ i : Fin n,
      0 < N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)))
    (a b : Fin n)
    (h : N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) < 0) :
    a = b := by
  have hne0 : N.trueInternalClassFlux α (C.reaction a) (C.species b) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h
    exact (lt_irrefl 0) h
  have hsucc : Fin n := ⟨(a.1 + 1) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩
  by_cases h1 : a = b
  · exact h1
  by_cases h2 : b.1 = (a.1 + 1) % n
  · exfalso
    have hfin : b = finRotate n a := Fin.ext (h2.trans (C.finRotate_val a).symm)
    rw [hfin] at h
    have hh := hcausal a
    linarith
  · exact absurd hne0 (fun hz => hz (classFlux_eq_zero_of_nonNeighbour C hsep hSR hCeven a b h1 h2))

/-- **The degree-two content of a cycle species, second half: a strictly positive aggregate flux
at `C.species b` comes from the reaction carrying its *right* edge and from nothing else.** -/
theorem posFlux_eq_rightEdge (C : N.TrueSRCycle n) (hsep : N.ReactantProductSeparated)
    (hSR : N.TrueSRStrongCriterion) (hCeven : C.Even)
    (hcausal : ∀ i : Fin n,
      0 < N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)))
    (hopp : ∀ i : Fin n,
      N.trueInternalClassFlux α (C.reaction (finRotate n i)) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)) < 0)
    (a b : Fin n)
    (h : 0 < N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b)) :
    b.1 = (a.1 + 1) % n := by
  have hne0 : N.trueInternalClassFlux α (C.reaction a) (C.species b) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h
    exact (lt_irrefl 0) h
  by_cases h1 : a = b
  · exfalso
    have hh := hoppAt C hopp a
    rw [h1] at h
    rw [h1] at hh
    linarith
  by_cases h2 : b.1 = (a.1 + 1) % n
  · exact h2
  · exact absurd hne0 (fun hz => hz (classFlux_eq_zero_of_nonNeighbour C hsep hSR hCeven a b h1 h2))

/-- **The trichotomy — the degree-two content in one statement.**  The aggregate class flux of a
cycle reaction at a cycle species is nonzero only at that reaction's two cycle neighbours; there
it has the sign dictated by the orientation.  Equivalently: the aggregate causal degree of a cycle
species over the cycle classes is exactly one out and one in. -/
theorem classFlux_trichotomy (C : N.TrueSRCycle n) (hsep : N.ReactantProductSeparated)
    (hSR : N.TrueSRStrongCriterion) (hCeven : C.Even)
    (hcausal : ∀ i : Fin n,
      0 < N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)))
    (hopp : ∀ i : Fin n,
      N.trueInternalClassFlux α (C.reaction (finRotate n i)) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)) < 0)
    (a b : Fin n) :
    (0 < N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) ∧
        b.1 = (a.1 + 1) % n) ∨
      (N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) = 0 ∧
        a ≠ b ∧ b.1 ≠ (a.1 + 1) % n) ∨
      (N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) < 0 ∧ a = b) := by
  have hsign : 0 < N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) ∨
      (0 = N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b)) ∨
      N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) < 0 :=
    lt_trichotomy (0 : ℝ)
      (N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b))
  rcases hsign with hlt | heq | hgt
  · exact Or.inl ⟨hlt, posFlux_eq_rightEdge C hsep hSR hCeven hcausal hopp a b hlt⟩
  · by_cases h1 : a = b
    · exfalso
      have hh := hoppAt C hopp a
      rw [h1] at heq
      rw [h1] at hh
      linarith
    by_cases h2 : b.1 = (a.1 + 1) % n
    · exfalso
      have hfin : b = finRotate n a := Fin.ext (h2.trans (C.finRotate_val a).symm)
      rw [hfin] at heq
      have hh := hcausal a
      linarith
    · exact Or.inr (Or.inl ⟨heq.symm, h1, h2⟩)
  · exact Or.inr (Or.inr ⟨hgt, negFlux_eq_leftEdge C hsep hSR hCeven hcausal a b hgt⟩)

/-- **No off-cycle true-reaction class drains any cycle species.**

This is the single named proposition on which the Hole B residue at
`TrueChemistrySRCriterion.lean:8607` depends: it is what forbids the first hop of the minimal
aggregate causal path `Q0` out of the on-cycle species `s0` from landing on an off-cycle class.
DEAD-ENDS B-3 records that `hrest` cannot discharge it (its natural instance is refuted by
`hattachment`); this `no_offCycle_negFlux` is the correctly-scoped replacement. -/
def no_offCycle_negFlux (α : N.fullyOpen.R → ℝ) (σ : S → ℝ) (C : N.TrueSRCycle n) : Prop :=
  ∀ (b : Fin n) (ρ : N.TrueReaction), ¬ C.HasReaction ρ →
    0 ≤ N.trueInternalClassFlux α ρ (C.species b) * σ (C.species b)

/-- **One-step case split out of a cycle species.**  A strictly negative aggregate flux at
`C.species b` comes either from `C.reaction b` itself, or from a class off the cycle.  Under
`no_offCycle_negFlux` the first alternative is forced: *the step lands on `C.reaction b`*. -/
theorem negCausalStep_from_cycleSpecies (C : N.TrueSRCycle n)
    (hsep : N.ReactantProductSeparated) (hSR : N.TrueSRStrongCriterion) (hCeven : C.Even)
    (hcausal : ∀ i : Fin n,
      0 < N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)))
    (hoff : no_offCycle_negFlux α σ C) (b : Fin n) (ρ : N.TrueReaction)
    (h : N.trueInternalClassFlux α ρ (C.species b) * σ (C.species b) < 0) :
    ρ = C.reaction b := by
  by_cases hC : C.HasReaction ρ
  · obtain ⟨t, ht⟩ := hC
    rw [← ht] at h
    rw [← ht]
    exact congrArg C.reaction (negFlux_eq_leftEdge C hsep hSR hCeven hcausal t b h)
  · exact absurd h (not_lt_of_ge (hoff b ρ hC))

/-- Lifting `TrueSRCycle.HasVertex` to the aggregate causal graph's vertex type.  This is the
predicate `hg0` and `hQ0late` are stated with inside `TrueChemistrySRCriterion.lean`, where it is
reached through the `private` map `aggregateVertexToTrueSRVertex` — unreachable from another
module, which is why it is restated here. -/
def aggregateVertexOnCycle (α : N.fullyOpen.R → ℝ) (σ : S → ℝ) (C : N.TrueSRCycle n) :
    N.TrueInternalAggregateVertex α σ → Prop
  | Sum.inl s => C.HasSpecies s.1
  | Sum.inr ρ => C.HasReaction ρ.1

/-- **Conditional discharge of the Hole B residue, Case B.**

A minimal aggregate causal path that starts at a cycle species and whose every other vertex is
off the cycle cannot exist, provided no off-cycle class drains a cycle species.  At the residue
(`TrueChemistrySRCriterion.lean:8579`–`8607`, `cases hv0 … | inl s0`) the situation is exactly this
with `m > 0`, so the residue follows from `no_offCycle_negFlux` alone. -/
theorem no_escape_from_cycleSpecies (C : N.TrueSRCycle n)
    (hsep : N.ReactantProductSeparated) (hSR : N.TrueSRStrongCriterion) (hCeven : C.Even)
    (hcausal : ∀ i : Fin n,
      0 < N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)))
    (hoff : no_offCycle_negFlux α σ C)
    {T : Finset (N.TrueInternalAggregateVertex α σ)} {m : ℕ}
    (Q : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T m) (hm : 0 < m)
    {s0 : AggregateActiveSpecies σ}
    (hv0 : Q.vertex ⟨0, by omega⟩ = Sum.inl s0) (hs0C : C.HasSpecies s0.1)
    (hlate : ∀ i : Fin (m + 1), i.1 ≠ 0 →
      ¬ aggregateVertexOnCycle α σ C (Q.vertex i)) : False := by
  classical
  obtain ⟨b, hb⟩ := hs0C
  have hstep : N.TrueInternalAggregateCausalEdge
      (Q.vertex ⟨0, by omega⟩ : N.TrueInternalAggregateVertex α σ)
      (Q.vertex (⟨1, by omega⟩ : Fin (m + 1))) := by
    exact Q.step ⟨0, hm⟩
  rw [hv0] at hstep
  cases hv1 : Q.vertex (⟨1, by omega⟩ : Fin (m + 1)) with
  | inl x =>
      have hbad : N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)
          (Sum.inl s0) (Sum.inl x) := by
        rw [hv1] at hstep
        exact hstep
      exact hbad.elim
  | inr ρ1 =>
      have hgood : N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)
          (Sum.inl s0) (Sum.inr ρ1) := by
        rw [hv1] at hstep
        exact hstep
      change N.trueInternalClassFlux α ρ1.1 s0.1 * σ s0.1 < 0 at hgood
      have hρ : ρ1.1 = C.reaction b := by
        rw [← hb] at hgood
        exact negCausalStep_from_cycleSpecies C hsep hSR hCeven hcausal hoff b ρ1.1 hgood
      have hlate1 : ¬ aggregateVertexOnCycle α σ C
          (Q.vertex (⟨1, by omega⟩ : Fin (m + 1))) :=
        hlate (⟨1, by omega⟩ : Fin (m + 1)) (by show (1 : ℕ) ≠ 0; omega)
      refine hlate1 (hv1 ▸ ?_)
      show C.HasReaction ρ1.1
      rw [hρ]
      exact ⟨b, rfl⟩

/-- **The ear's off-cycle end, extracted.**  If `no_offCycle_negFlux` fails, there is an off-cycle
true-reaction class with a strictly negative class flux at some cycle species.  Together with
`hattachment` (which gives an off-cycle class *positive* at another cycle species) this is the
pair of off-cycle endpoints the A.6 Case-2 ear needs; the hypothesis is refutable by nothing in
scope, which is exactly why DEAD-ENDS B-3 lists it as the frontier. -/
theorem exists_offCycle_negFlux_class {n : ℕ} {C : N.TrueSRCycle n}
    (hoff_neg : ¬ no_offCycle_negFlux α σ C) :
    ∃ (b : Fin n) (ρ : N.TrueReaction), ¬ C.HasReaction ρ ∧
      N.trueInternalClassFlux α ρ (C.species b) * σ (C.species b) < 0 := by
  by_contra hnone
  apply hoff_neg
  intro b ρ hρ
  by_contra h
  exact hnone ⟨b, ρ, hρ, not_le.mp h⟩

end TrueSRCycle

end CRNT.Network
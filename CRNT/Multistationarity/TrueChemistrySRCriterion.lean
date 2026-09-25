import Mathlib.Logic.Equiv.Fin.Rotate
import CRNT.Multistationarity.TrueChemistrySRGraph
import CRNT.Multistationarity.StrongConcordance
import CRNT.Multistationarity.WeakNormality
import CRNT.Multistationarity.GainPotential
import CRNT.Graph.FiniteSource
import CRNT.Graph.RelPath
import CRNT.Multistationarity.TrueSRSingleSharedEdge
import CRNT.Multistationarity.TrueSRCycleChord
import CRNT.Multistationarity.TrueSRMinimalChord
import CRNT.Multistationarity.TrueSRChordParity
import CRNT.Multistationarity.TrueSREdgePath
import CRNT.Multistationarity.TrueSRGlueCPairs
import CRNT.Multistationarity.TrueSRCycleReverse
import CRNT.Multistationarity.TrueSRNoArcChord
import CRNT.Multistationarity.TrueSRChordExtraction
import CRNT.Multistationarity.TrueSRSpeciesPath

/-!
# True-chemistry SR criteria for concordance and strong concordance

This module states the classical orientation-free SR theorem using the chemically
faithful SR graph of `TrueChemistrySRGraph.lean`.

For a reactant/product-separated network, if every e-cycle is an s-cycle and no two e-cycles
have an S-to-R intersection, then its fully open extension is strongly concordant. More
generally the same graphical condition gives strong concordance for a nondegenerate/weakly-normal
network by passing through its fully open extension. Separation is essential: without it, the
SR-graph labels need not equal the net coefficients constrained by the stoichiometric kernel.

The graph-to-sign-causality proof is long and intentionally isolated in one theorem.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Side condition repairing the true-chemistry SR criterion when the original network
already contains reactions incident to the zero complex.  Such a channel must literally be one of
the singleton inflow/outflow channels added by `fullyOpen`; otherwise omitting it from the true SR
graph can hide a genuine sign-causality edge. -/
def ZeroComplexReactionsAreFlows (N : Network S) : Prop :=
  ∀ r, N.IsFlowChannel r →
    (∃ s : S, N.reaction r = inflowReaction s) ∨
    (∃ s : S, N.reaction r = outflowReaction s)

private def liftTrueReaction (N : Network S) : N.TrueReaction → N.fullyOpen.TrueReaction :=
  Quotient.map Sum.inl (by
    intro r q h
    exact h)

private theorem liftTrueReaction_mk (N : Network S) (r : N.R) :
    liftTrueReaction N (N.trueReaction r) = N.fullyOpen.trueReaction (Sum.inl r) := rfl

private theorem internal_liftTrueReaction (N : Network S) {ρ : N.TrueReaction}
    (hρ : TrueReaction.Internal N ρ) :
    TrueReaction.Internal N.fullyOpen (liftTrueReaction N ρ) := by
  induction ρ using Quotient.inductionOn with
  | _ r =>
    exact hρ

private theorem liftTrueReaction_injective (N : Network S) :
    Function.Injective (liftTrueReaction N) := by
  intro ρ σ h
  induction ρ using Quotient.inductionOn with
  | _ r =>
    induction σ using Quotient.inductionOn with
    | _ q =>
      apply Quotient.sound
      have hf : N.fullyOpen.SameTrueReaction (Sum.inl r) (Sum.inl q) := Quotient.exact h
      exact hf

private theorem internalFullyOpen_exists_original (N : Network S)
    (ρ : N.fullyOpen.InternalTrueReaction) :
    ∃ r : N.R, N.fullyOpen.trueReaction (Sum.inl r) = ρ.1 := by
  rcases Quotient.exists_rep ρ.1 with ⟨q, hq⟩
  have hi : TrueReaction.Internal N.fullyOpen (N.fullyOpen.trueReaction q) := by
    change TrueReaction.Internal N.fullyOpen (Quotient.mk N.fullyOpen.trueReactionSetoid q)
    rw [hq]
    exact ρ.2
  rcases q with r | q
  · exact ⟨r, hq⟩
  · rcases q with s | s
    · exfalso
      apply hi
      exact Or.inl rfl
    · exfalso
      apply hi
      exact Or.inr rfl

private theorem internal_original_of_internal_lift (N : Network S) (r : N.R)
    (h : TrueReaction.Internal N.fullyOpen (N.fullyOpen.trueReaction (Sum.inl r))) :
    TrueReaction.Internal N (N.trueReaction r) := by
  exact h

private noncomputable def internalTrueReactionEquiv (N : Network S) :
    N.InternalTrueReaction ≃ N.fullyOpen.InternalTrueReaction := by
  let f : N.InternalTrueReaction → N.fullyOpen.InternalTrueReaction := fun ρ =>
    ⟨liftTrueReaction N ρ.1, internal_liftTrueReaction N ρ.2⟩
  let g : N.fullyOpen.InternalTrueReaction → N.InternalTrueReaction := fun ρ =>
    let r := Classical.choose (internalFullyOpen_exists_original N ρ)
    ⟨N.trueReaction r, internal_original_of_internal_lift N r (by
      rw [Classical.choose_spec (internalFullyOpen_exists_original N ρ)]
      exact ρ.2)⟩
  refine { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro ρ
    apply Subtype.ext
    apply liftTrueReaction_injective N
    change liftTrueReaction N (g (f ρ)).1 = liftTrueReaction N ρ.1
    change N.fullyOpen.trueReaction (Sum.inl (Classical.choose (internalFullyOpen_exists_original N (f ρ)))) = liftTrueReaction N ρ.1
    exact Classical.choose_spec (internalFullyOpen_exists_original N (f ρ))
  · intro ρ
    apply Subtype.ext
    change liftTrueReaction N (g ρ).1 = ρ.1
    change N.fullyOpen.trueReaction (Sum.inl (Classical.choose (internalFullyOpen_exists_original N ρ))) = ρ.1
    exact Classical.choose_spec (internalFullyOpen_exists_original N ρ)



private def liftTrueSREdge (N : Network S) (e : N.TrueSREdge) :
    N.fullyOpen.TrueSREdge where
  species := e.species
  reaction := liftTrueReaction N e.reaction
  internal := internal_liftTrueReaction N e.internal
  endpoint := e.endpoint
  representative := Sum.inl e.representative
  representative_class := by
    change N.fullyOpen.trueReaction (Sum.inl e.representative) = liftTrueReaction N e.reaction
    rw [← e.representative_class]
    rfl
  endpoint_is_source_or_target := by
    simpa using e.endpoint_is_source_or_target
  occurs := e.occurs

@[simp] private theorem liftTrueSREdge_species (N : Network S) (e : N.TrueSREdge) :
    (liftTrueSREdge N e).species = e.species := rfl

@[simp] private theorem liftTrueSREdge_endpoint (N : Network S) (e : N.TrueSREdge) :
    (liftTrueSREdge N e).endpoint = e.endpoint := rfl

@[simp] private theorem liftTrueSREdge_reaction (N : Network S) (e : N.TrueSREdge) :
    (liftTrueSREdge N e).reaction = liftTrueReaction N e.reaction := rfl

@[simp] private theorem liftTrueSREdge_coeff (N : Network S) (e : N.TrueSREdge) :
    (liftTrueSREdge N e).coeff = e.coeff := rfl

private theorem liftTrueSREdge_sameIncidence_iff (N : Network S) (e f : N.TrueSREdge) :
    (liftTrueSREdge N e).SameIncidence (liftTrueSREdge N f) ↔ e.SameIncidence f := by
  simp only [TrueSREdge.SameIncidence, liftTrueSREdge_species, liftTrueSREdge_reaction,
    liftTrueSREdge_endpoint]
  constructor
  · rintro ⟨hs, hr, he⟩
    exact ⟨hs, liftTrueReaction_injective N hr, he⟩
  · rintro ⟨hs, hr, he⟩
    exact ⟨hs, congrArg (liftTrueReaction N) hr, he⟩

private theorem liftTrueSREdge_shareVertex_iff (N : Network S) (e f : N.TrueSREdge) :
    (liftTrueSREdge N e).ShareVertex (liftTrueSREdge N f) ↔ e.ShareVertex f := by
  simp only [TrueSREdge.ShareVertex, liftTrueSREdge_species, liftTrueSREdge_reaction]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (liftTrueReaction_injective N h)
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (congrArg (liftTrueReaction N) h)

private noncomputable def liftTrueSRVertex (N : Network S) :
    N.TrueSRVertex → N.fullyOpen.TrueSRVertex
  | Sum.inl s => Sum.inl s
  | Sum.inr ρ => Sum.inr (internalTrueReactionEquiv N ρ)

private theorem liftTrueSRVertex_injective (N : Network S) :
    Function.Injective (liftTrueSRVertex N) := by
  intro u v h
  rcases u with s | ρ <;> rcases v with t | σ
  · cases h
    rfl
  · simp [liftTrueSRVertex] at h
  · simp [liftTrueSRVertex] at h
  · simp only [liftTrueSRVertex, Sum.inr.injEq] at h
    exact congrArg Sum.inr ((internalTrueReactionEquiv N).injective h)

private theorem liftTrueSREdge_connects (N : Network S) (e : N.TrueSREdge)
    (u v : N.TrueSRVertex) (h : e.Connects u v) :
    (liftTrueSREdge N e).Connects (liftTrueSRVertex N u) (liftTrueSRVertex N v) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

private def liftTrueSRCycle (N : Network S) {n : ℕ} (C : N.TrueSRCycle n) :
    N.fullyOpen.TrueSRCycle n where
  nontrivial := C.nontrivial
  species := C.species
  reaction := fun i => liftTrueReaction N (C.reaction i)
  leftEdge := fun i => liftTrueSREdge N (C.leftEdge i)
  rightEdge := fun i => liftTrueSREdge N (C.rightEdge i)
  left_species := C.left_species
  left_reaction := by intro i; exact congrArg (liftTrueReaction N) (C.left_reaction i)
  right_species := C.right_species
  right_reaction := by intro i; exact congrArg (liftTrueReaction N) (C.right_reaction i)
  species_injective := C.species_injective
  reaction_injective := by
    intro i j h
    exact C.reaction_injective (liftTrueReaction_injective N h)

private theorem liftTrueSRCycle_isCPair (N : Network S) {n : ℕ}
    (C : N.TrueSRCycle n) (i : Fin n) :
    (liftTrueSRCycle N C).isCPair i ↔ C.isCPair i := by
  rfl

private theorem liftTrueSRCycle_numCPairs (N : Network S) {n : ℕ}
    (C : N.TrueSRCycle n) :
    (liftTrueSRCycle N C).numCPairs = C.numCPairs := by
  rfl

private theorem liftTrueSRCycle_even_iff (N : Network S) {n : ℕ}
    (C : N.TrueSRCycle n) :
    (liftTrueSRCycle N C).Even ↔ C.Even := by
  rw [TrueSRCycle.Even, TrueSRCycle.Even, liftTrueSRCycle_numCPairs]

private theorem liftTrueSRCycle_sCycle_iff (N : Network S) {n : ℕ}
    (C : N.TrueSRCycle n) :
    (liftTrueSRCycle N C).SCycle ↔ C.SCycle := by
  simp [TrueSRCycle.SCycle, liftTrueSRCycle, liftTrueSREdge, TrueSREdge.coeff]

/-- The net-coefficient s-cycle condition transfers across the fully open lift, exactly as the
label version does.  Needed if the criterion is ever read with `SCycleNet`; proved now because
it is independent of that decision. -/
private theorem liftTrueSRCycle_sCycleNet_iff (N : Network S) {n : ℕ}
    (C : N.TrueSRCycle n) :
    (liftTrueSRCycle N C).SCycleNet ↔ C.SCycleNet := by
  simp [TrueSRCycle.SCycleNet, liftTrueSRCycle, liftTrueSREdge, TrueSREdge.netCoeff]

private theorem containsEdge_lift (N : Network S) {n : ℕ}
    (C : N.TrueSRCycle n) (e : N.TrueSREdge) (h : C.ContainsEdge e) :
    (liftTrueSRCycle N C).ContainsEdge (liftTrueSREdge N e) := by
  rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact Or.inl ⟨i, (liftTrueSREdge_sameIncidence_iff N e (C.leftEdge i)).2 hi⟩
  · exact Or.inr ⟨i, (liftTrueSREdge_sameIncidence_iff N e (C.rightEdge i)).2 hi⟩



private theorem fullyOpenEdge_rep_not_flow (N : Network S)
    (e : N.fullyOpen.TrueSREdge) :
    ¬ N.fullyOpen.IsFlowChannel e.representative := by
  change TrueReaction.Internal N.fullyOpen (N.fullyOpen.trueReaction e.representative)
  rw [e.representative_class]
  exact e.internal

private theorem fullyOpenEdge_rep_exists_original (N : Network S)
    (e : N.fullyOpen.TrueSREdge) :
    ∃ r : N.R, e.representative = Sum.inl r := by
  have hnf := fullyOpenEdge_rep_not_flow N e
  cases hrep : e.representative with
  | inl r => exact ⟨r, rfl⟩
  | inr q =>
      cases q with
      | inl s =>
          exfalso
          apply hnf
          simp [hrep, Network.IsFlowChannel, inflowReaction]
      | inr s =>
          exfalso
          apply hnf
          simp [hrep, Network.IsFlowChannel, outflowReaction]

private noncomputable def lowerTrueSREdge (N : Network S)
    (e : N.fullyOpen.TrueSREdge) : N.TrueSREdge := by
  let ρ : N.InternalTrueReaction :=
    (internalTrueReactionEquiv N).symm ⟨e.reaction, e.internal⟩
  let r : N.R := Classical.choose (fullyOpenEdge_rep_exists_original N e)
  have hr : e.representative = Sum.inl r :=
    Classical.choose_spec (fullyOpenEdge_rep_exists_original N e)
  refine {
    species := e.species
    reaction := ρ.1
    internal := ρ.2
    endpoint := e.endpoint
    representative := r
    representative_class := ?_
    endpoint_is_source_or_target := ?_
    occurs := e.occurs }
  · apply liftTrueReaction_injective N
    have hρ : liftTrueReaction N ρ.1 = e.reaction := by
      have heq := (internalTrueReactionEquiv N).apply_symm_apply ⟨e.reaction, e.internal⟩
      exact congrArg Subtype.val heq
    rw [hρ]
    change N.fullyOpen.trueReaction (Sum.inl r) = e.reaction
    rw [← hr]
    exact e.representative_class
  · have h := e.endpoint_is_source_or_target
    rw [hr] at h
    simpa using h

@[simp] private theorem lowerTrueSREdge_species (N : Network S)
    (e : N.fullyOpen.TrueSREdge) :
    (lowerTrueSREdge N e).species = e.species := rfl

@[simp] private theorem lowerTrueSREdge_endpoint (N : Network S)
    (e : N.fullyOpen.TrueSREdge) :
    (lowerTrueSREdge N e).endpoint = e.endpoint := rfl

@[simp] private theorem lowerTrueSREdge_coeff (N : Network S)
    (e : N.fullyOpen.TrueSREdge) :
    (lowerTrueSREdge N e).coeff = e.coeff := rfl

private theorem lift_lowerTrueSREdge_reaction (N : Network S)
    (e : N.fullyOpen.TrueSREdge) :
    liftTrueReaction N (lowerTrueSREdge N e).reaction = e.reaction := by
  let ρ : N.InternalTrueReaction :=
    (internalTrueReactionEquiv N).symm ⟨e.reaction, e.internal⟩
  change liftTrueReaction N ρ.1 = e.reaction
  have heq := (internalTrueReactionEquiv N).apply_symm_apply ⟨e.reaction, e.internal⟩
  exact congrArg Subtype.val heq

private theorem lowerTrueSREdge_sameIncidence_iff (N : Network S)
    (e f : N.fullyOpen.TrueSREdge) :
    (lowerTrueSREdge N e).SameIncidence (lowerTrueSREdge N f) ↔
      e.SameIncidence f := by
  simp only [TrueSREdge.SameIncidence, lowerTrueSREdge_species, lowerTrueSREdge_endpoint]
  constructor
  · rintro ⟨hs, hr, he⟩
    refine ⟨hs, ?_, he⟩
    have := congrArg (liftTrueReaction N) hr
    simpa [lift_lowerTrueSREdge_reaction] using this
  · rintro ⟨hs, hr, he⟩
    refine ⟨hs, ?_, he⟩
    apply liftTrueReaction_injective N
    rw [lift_lowerTrueSREdge_reaction, lift_lowerTrueSREdge_reaction]
    exact hr

private theorem lowerTrueSREdge_shareVertex_iff (N : Network S)
    (e f : N.fullyOpen.TrueSREdge) :
    (lowerTrueSREdge N e).ShareVertex (lowerTrueSREdge N f) ↔
      e.ShareVertex f := by
  simp only [TrueSREdge.ShareVertex, lowerTrueSREdge_species]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · right
      have := congrArg (liftTrueReaction N) h
      simpa [lift_lowerTrueSREdge_reaction] using this
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · right
      apply liftTrueReaction_injective N
      rw [lift_lowerTrueSREdge_reaction, lift_lowerTrueSREdge_reaction]
      exact h

private theorem edge_sameIncidence_lift_lower (N : Network S)
    (e : N.fullyOpen.TrueSREdge) :
    e.SameIncidence (liftTrueSREdge N (lowerTrueSREdge N e)) := by
  refine ⟨rfl, ?_, rfl⟩
  symm
  exact lift_lowerTrueSREdge_reaction N e

private noncomputable def lowerTrueSRVertex (N : Network S) :
    N.fullyOpen.TrueSRVertex → N.TrueSRVertex
  | Sum.inl s => Sum.inl s
  | Sum.inr ρ => Sum.inr ((internalTrueReactionEquiv N).symm ρ)

private theorem lowerTrueSRVertex_injective (N : Network S) :
    Function.Injective (lowerTrueSRVertex N) := by
  intro u v h
  rcases u with s | ρ <;> rcases v with t | σ
  · cases h
    rfl
  · simp [lowerTrueSRVertex] at h
  · simp [lowerTrueSRVertex] at h
  · simp only [lowerTrueSRVertex, Sum.inr.injEq] at h
    exact congrArg Sum.inr ((internalTrueReactionEquiv N).symm.injective h)

private theorem lower_liftTrueSRVertex (N : Network S) (u : N.TrueSRVertex) :
    lowerTrueSRVertex N (liftTrueSRVertex N u) = u := by
  rcases u with s | ρ
  · rfl
  · simp [liftTrueSRVertex, lowerTrueSRVertex]

private theorem lift_lowerTrueSRVertex (N : Network S) (u : N.fullyOpen.TrueSRVertex) :
    liftTrueSRVertex N (lowerTrueSRVertex N u) = u := by
  rcases u with s | ρ
  · rfl
  · simp [liftTrueSRVertex, lowerTrueSRVertex]

private theorem lowerTrueSREdge_connects (N : Network S) (e : N.fullyOpen.TrueSREdge)
    (u v : N.fullyOpen.TrueSRVertex) (h : e.Connects u v) :
    (lowerTrueSREdge N e).Connects (lowerTrueSRVertex N u) (lowerTrueSRVertex N v) := by
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · subst u
    subst v
    exact Or.inl ⟨rfl, rfl⟩
  · subst u
    subst v
    exact Or.inr ⟨rfl, rfl⟩




private theorem cycleReaction_internal {N : Network S} {n : ℕ}
    (C : N.TrueSRCycle n) (i : Fin n) :
    TrueReaction.Internal N (C.reaction i) := by
  rw [← C.left_reaction i]
  exact (C.leftEdge i).internal

private noncomputable def lowerCycleReaction (N : Network S) {n : ℕ}
    (C : N.fullyOpen.TrueSRCycle n) (i : Fin n) : N.TrueReaction :=
  ((internalTrueReactionEquiv N).symm
    ⟨C.reaction i, cycleReaction_internal C i⟩).1

private theorem lift_lowerCycleReaction (N : Network S) {n : ℕ}
    (C : N.fullyOpen.TrueSRCycle n) (i : Fin n) :
    liftTrueReaction N (lowerCycleReaction N C i) = C.reaction i := by
  have h := (internalTrueReactionEquiv N).apply_symm_apply
    ⟨C.reaction i, cycleReaction_internal C i⟩
  exact congrArg Subtype.val h

private noncomputable def lowerTrueSRCycle (N : Network S) {n : ℕ}
    (C : N.fullyOpen.TrueSRCycle n) : N.TrueSRCycle n where
  nontrivial := C.nontrivial
  species := C.species
  reaction := lowerCycleReaction N C
  leftEdge := fun i => lowerTrueSREdge N (C.leftEdge i)
  rightEdge := fun i => lowerTrueSREdge N (C.rightEdge i)
  left_species := C.left_species
  left_reaction := by
    intro i
    apply liftTrueReaction_injective N
    rw [lift_lowerTrueSREdge_reaction, lift_lowerCycleReaction]
    exact C.left_reaction i
  right_species := C.right_species
  right_reaction := by
    intro i
    apply liftTrueReaction_injective N
    rw [lift_lowerTrueSREdge_reaction, lift_lowerCycleReaction]
    exact C.right_reaction i
  species_injective := C.species_injective
  reaction_injective := by
    intro i j h
    apply C.reaction_injective
    rw [← lift_lowerCycleReaction N C i, ← lift_lowerCycleReaction N C j]
    exact congrArg (liftTrueReaction N) h

private theorem lowerTrueSRCycle_isCPair (N : Network S) {n : ℕ}
    (C : N.fullyOpen.TrueSRCycle n) (i : Fin n) :
    (lowerTrueSRCycle N C).isCPair i ↔ C.isCPair i := by
  rfl

private theorem lowerTrueSRCycle_numCPairs (N : Network S) {n : ℕ}
    (C : N.fullyOpen.TrueSRCycle n) :
    (lowerTrueSRCycle N C).numCPairs = C.numCPairs := by
  rfl

private theorem lowerTrueSRCycle_even_iff (N : Network S) {n : ℕ}
    (C : N.fullyOpen.TrueSRCycle n) :
    (lowerTrueSRCycle N C).Even ↔ C.Even := by
  rw [TrueSRCycle.Even, TrueSRCycle.Even, lowerTrueSRCycle_numCPairs]

private theorem lowerTrueSRCycle_sCycle_iff (N : Network S) {n : ℕ}
    (C : N.fullyOpen.TrueSRCycle n) :
    (lowerTrueSRCycle N C).SCycle ↔ C.SCycle := by
  simp [TrueSRCycle.SCycle, lowerTrueSRCycle, lowerTrueSREdge, TrueSREdge.coeff]

/-- Lowering an edge preserves its net coefficient: the chosen original representative has the
same reaction as the fully open one it came from. -/
private theorem lowerTrueSREdge_netCoeff (N : Network S) (e : N.fullyOpen.TrueSREdge) :
    (lowerTrueSREdge N e).netCoeff = e.netCoeff := by
  have hsp : (lowerTrueSREdge N e).species = e.species := rfl
  have hrep : (lowerTrueSREdge N e).representative =
      Classical.choose (fullyOpenEdge_rep_exists_original N e) := rfl
  have hr : e.representative =
      Sum.inl (Classical.choose (fullyOpenEdge_rep_exists_original N e)) :=
    Classical.choose_spec (fullyOpenEdge_rep_exists_original N e)
  have h1 : N.fullyOpen.reaction e.representative =
      N.fullyOpen.reaction
        (Sum.inl (Classical.choose (fullyOpenEdge_rep_exists_original N e))) :=
    congrArg _ hr
  rw [fullyOpen_reaction_inl] at h1
  have hre : N.reaction (lowerTrueSREdge N e).representative =
      N.fullyOpen.reaction e.representative := by
    rw [hrep, h1]
  simp only [TrueSREdge.netCoeff, hsp, hre]

/-- The net-coefficient s-cycle condition transfers back down the fully open lift. -/
private theorem lowerTrueSRCycle_sCycleNet_iff (N : Network S) {n : ℕ}
    (C : N.fullyOpen.TrueSRCycle n) :
    (lowerTrueSRCycle N C).SCycleNet ↔ C.SCycleNet := by
  unfold TrueSRCycle.SCycleNet
  rw [Finset.prod_congr rfl (fun i _ =>
      show ((lowerTrueSRCycle N C).leftEdge i).netCoeff = (C.leftEdge i).netCoeff from by
        simpa [lowerTrueSRCycle] using N.lowerTrueSREdge_netCoeff (C.leftEdge i)),
    Finset.prod_congr rfl (fun i _ =>
      show ((lowerTrueSRCycle N C).rightEdge i).netCoeff = (C.rightEdge i).netCoeff from by
        simpa [lowerTrueSRCycle] using N.lowerTrueSREdge_netCoeff (C.rightEdge i))]

private theorem containsEdge_lower (N : Network S) {n : ℕ}
    (C : N.fullyOpen.TrueSRCycle n) (e : N.fullyOpen.TrueSREdge)
    (h : C.ContainsEdge e) :
    (lowerTrueSRCycle N C).ContainsEdge (lowerTrueSREdge N e) := by
  rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact Or.inl ⟨i, (lowerTrueSREdge_sameIncidence_iff N e (C.leftEdge i)).2 hi⟩
  · exact Or.inr ⟨i, (lowerTrueSREdge_sameIncidence_iff N e (C.rightEdge i)).2 hi⟩

private theorem containsEdge_lift_iff_lower (N : Network S) {n : ℕ}
    (C : N.fullyOpen.TrueSRCycle n) (e : N.fullyOpen.TrueSREdge) :
    C.ContainsEdge e ↔
      (lowerTrueSRCycle N C).ContainsEdge (lowerTrueSREdge N e) := by
  constructor
  · exact containsEdge_lower N C e
  · intro h
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
    · left
      refine ⟨i, ?_⟩
      exact (lowerTrueSREdge_sameIncidence_iff N e (C.leftEdge i)).1 hi
    · right
      refine ⟨i, ?_⟩
      exact (lowerTrueSREdge_sameIncidence_iff N e (C.rightEdge i)).1 hi



private theorem full_sameIncidence_lift_iff_lower (N : Network S)
    (e : N.fullyOpen.TrueSREdge) (f : N.TrueSREdge) :
    e.SameIncidence (liftTrueSREdge N f) ↔
      (lowerTrueSREdge N e).SameIncidence f := by
  simp only [TrueSREdge.SameIncidence, liftTrueSREdge_species,
    liftTrueSREdge_reaction, liftTrueSREdge_endpoint,
    lowerTrueSREdge_species, lowerTrueSREdge_endpoint]
  constructor
  · rintro ⟨hs, hr, he⟩
    refine ⟨hs, ?_, he⟩
    apply liftTrueReaction_injective N
    rw [lift_lowerTrueSREdge_reaction]
    exact hr
  · rintro ⟨hs, hr, he⟩
    refine ⟨hs, ?_, he⟩
    have h := congrArg (liftTrueReaction N) hr
    rw [lift_lowerTrueSREdge_reaction] at h
    exact h

private theorem lift_sameIncidence_full_iff_lower (N : Network S)
    (f : N.TrueSREdge) (e : N.fullyOpen.TrueSREdge) :
    (liftTrueSREdge N f).SameIncidence e ↔
      f.SameIncidence (lowerTrueSREdge N e) := by
  simp only [TrueSREdge.SameIncidence, liftTrueSREdge_species,
    liftTrueSREdge_reaction, liftTrueSREdge_endpoint,
    lowerTrueSREdge_species, lowerTrueSREdge_endpoint]
  constructor
  · rintro ⟨hs, hr, he⟩
    refine ⟨hs, ?_, he⟩
    apply liftTrueReaction_injective N
    rw [lift_lowerTrueSREdge_reaction]
    exact hr
  · rintro ⟨hs, hr, he⟩
    refine ⟨hs, ?_, he⟩
    have h := congrArg (liftTrueReaction N) hr
    rw [lift_lowerTrueSREdge_reaction] at h
    exact h

private theorem containsEdge_liftCycle_iff_lowerEdge (N : Network S) {n : ℕ}
    (C : N.TrueSRCycle n) (e : N.fullyOpen.TrueSREdge) :
    (liftTrueSRCycle N C).ContainsEdge e ↔
      C.ContainsEdge (lowerTrueSREdge N e) := by
  constructor
  · intro h
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl ⟨i, (full_sameIncidence_lift_iff_lower N e (C.leftEdge i)).1 hi⟩
    · exact Or.inr ⟨i, (full_sameIncidence_lift_iff_lower N e (C.rightEdge i)).1 hi⟩
  · intro h
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl ⟨i, (full_sameIncidence_lift_iff_lower N e (C.leftEdge i)).2 hi⟩
    · exact Or.inr ⟨i, (full_sameIncidence_lift_iff_lower N e (C.rightEdge i)).2 hi⟩

private theorem containsEdge_lowerCycle_iff_liftEdge (N : Network S) {n : ℕ}
    (C : N.fullyOpen.TrueSRCycle n) (e : N.TrueSREdge) :
    (lowerTrueSRCycle N C).ContainsEdge e ↔
      C.ContainsEdge (liftTrueSREdge N e) := by
  constructor
  · intro h
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl ⟨i, (lift_sameIncidence_full_iff_lower N e (C.leftEdge i)).2 hi⟩
    · exact Or.inr ⟨i, (lift_sameIncidence_full_iff_lower N e (C.rightEdge i)).2 hi⟩
  · intro h
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl ⟨i, (lift_sameIncidence_full_iff_lower N e (C.leftEdge i)).1 hi⟩
    · exact Or.inr ⟨i, (lift_sameIncidence_full_iff_lower N e (C.rightEdge i)).1 hi⟩



private noncomputable def liftSToRIntersection (N : Network S) {m n : ℕ}
    {C : N.TrueSRCycle m} {D : N.TrueSRCycle n}
    (I : C.SToRIntersection D) :
    (liftTrueSRCycle N C).SToRIntersection (liftTrueSRCycle N D) where
  componentCount := I.componentCount
  componentCount_pos := I.componentCount_pos
  componentLength := I.componentLength
  componentLength_pos := I.componentLength_pos
  edge := fun c i => liftTrueSREdge N (I.edge c i)
  vertex := fun c i => liftTrueSRVertex N (I.vertex c i)
  edge_on_C := by
    intro c i
    exact containsEdge_lift N C (I.edge c i) (I.edge_on_C c i)
  edge_on_D := by
    intro c i
    exact containsEdge_lift N D (I.edge c i) (I.edge_on_D c i)
  connects := by
    intro c i
    exact liftTrueSREdge_connects N (I.edge c i)
      (I.vertex c (Fin.castSucc i)) (I.vertex c i.succ) (I.connects c i)
  edge_simple := by
    intro c i j h
    exact I.edge_simple c ((liftTrueSREdge_sameIncidence_iff N _ _).1 h)
  vertex_simple := by
    intro c i j h
    apply I.vertex_simple c
    exact liftTrueSRVertex_injective N h
  starts_at_species := by
    intro c
    rcases I.starts_at_species c with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change liftTrueSRVertex N (I.vertex c 0) = Sum.inl s
    rw [hs]
    rfl
  ends_at_reaction := by
    intro c
    rcases I.ends_at_reaction c with ⟨ρ, hρ⟩
    refine ⟨internalTrueReactionEquiv N ρ, ?_⟩
    change liftTrueSRVertex N (I.vertex c (Fin.last (I.componentLength c))) =
      Sum.inr (internalTrueReactionEquiv N ρ)
    rw [hρ]
    rfl
  covers_common := by
    intro e heC heD
    have hC : C.ContainsEdge (lowerTrueSREdge N e) :=
      (containsEdge_liftCycle_iff_lowerEdge N C e).1 heC
    have hD : D.ContainsEdge (lowerTrueSREdge N e) :=
      (containsEdge_liftCycle_iff_lowerEdge N D e).1 heD
    rcases I.covers_common (lowerTrueSREdge N e) hC hD with ⟨c, i, hi⟩
    exact ⟨c, i, (full_sameIncidence_lift_iff_lower N e (I.edge c i)).2 hi⟩
  components_separated := by
    intro c d hcd i j hshare
    apply I.components_separated hcd i j
    exact (liftTrueSREdge_shareVertex_iff N _ _).1 hshare

private noncomputable def lowerSToRIntersection (N : Network S) {m n : ℕ}
    {C : N.fullyOpen.TrueSRCycle m} {D : N.fullyOpen.TrueSRCycle n}
    (I : C.SToRIntersection D) :
    (lowerTrueSRCycle N C).SToRIntersection (lowerTrueSRCycle N D) where
  componentCount := I.componentCount
  componentCount_pos := I.componentCount_pos
  componentLength := I.componentLength
  componentLength_pos := I.componentLength_pos
  edge := fun c i => lowerTrueSREdge N (I.edge c i)
  vertex := fun c i => lowerTrueSRVertex N (I.vertex c i)
  edge_on_C := by
    intro c i
    exact containsEdge_lower N C (I.edge c i) (I.edge_on_C c i)
  edge_on_D := by
    intro c i
    exact containsEdge_lower N D (I.edge c i) (I.edge_on_D c i)
  connects := by
    intro c i
    exact lowerTrueSREdge_connects N (I.edge c i)
      (I.vertex c (Fin.castSucc i)) (I.vertex c i.succ) (I.connects c i)
  edge_simple := by
    intro c i j h
    exact I.edge_simple c ((lowerTrueSREdge_sameIncidence_iff N _ _).1 h)
  vertex_simple := by
    intro c i j h
    apply I.vertex_simple c
    exact lowerTrueSRVertex_injective N h
  starts_at_species := by
    intro c
    rcases I.starts_at_species c with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change lowerTrueSRVertex N (I.vertex c 0) = Sum.inl s
    rw [hs]
    rfl
  ends_at_reaction := by
    intro c
    rcases I.ends_at_reaction c with ⟨ρ, hρ⟩
    refine ⟨(internalTrueReactionEquiv N).symm ρ, ?_⟩
    change lowerTrueSRVertex N (I.vertex c (Fin.last (I.componentLength c))) =
      Sum.inr ((internalTrueReactionEquiv N).symm ρ)
    rw [hρ]
    rfl
  covers_common := by
    intro e heC heD
    have hC : C.ContainsEdge (liftTrueSREdge N e) :=
      (containsEdge_lowerCycle_iff_liftEdge N C e).1 heC
    have hD : D.ContainsEdge (liftTrueSREdge N e) :=
      (containsEdge_lowerCycle_iff_liftEdge N D e).1 heD
    rcases I.covers_common (liftTrueSREdge N e) hC hD with ⟨c, i, hi⟩
    exact ⟨c, i, (lift_sameIncidence_full_iff_lower N e (I.edge c i)).1 hi⟩
  components_separated := by
    intro c d hcd i j hshare
    apply I.components_separated hcd i j
    exact (lowerTrueSREdge_shareVertex_iff N _ _).1 hshare

/-- The true chemistry of a fully-open extension has the same internal SR data as the
original network.  Flow reactions contribute no true-chemistry vertices. -/
theorem fullyOpen_trueSRCriterion_iff (N : Network S) :
    N.fullyOpen.TrueSRStrongCriterion ↔ N.TrueSRStrongCriterion := by
  constructor
  · rintro ⟨hcycle, hinter⟩
    constructor
    · intro n C hEven
      have hLiftEven : (liftTrueSRCycle N C).Even :=
        (liftTrueSRCycle_even_iff N C).2 hEven
      have hLiftS := hcycle (liftTrueSRCycle N C) hLiftEven
      exact (liftTrueSRCycle_sCycle_iff N C).1 hLiftS
    · intro m n C D hCEven hDEven hI
      apply hinter (liftTrueSRCycle N C) (liftTrueSRCycle N D)
        ((liftTrueSRCycle_even_iff N C).2 hCEven)
        ((liftTrueSRCycle_even_iff N D).2 hDEven)
      rcases hI with ⟨I⟩
      exact ⟨liftSToRIntersection N I⟩
  · rintro ⟨hcycle, hinter⟩
    constructor
    · intro n C hEven
      have hLowEven : (lowerTrueSRCycle N C).Even :=
        (lowerTrueSRCycle_even_iff N C).2 hEven
      have hLowS := hcycle (lowerTrueSRCycle N C) hLowEven
      exact (lowerTrueSRCycle_sCycle_iff N C).1 hLowS
    · intro m n C D hCEven hDEven hI
      apply hinter (lowerTrueSRCycle N C) (lowerTrueSRCycle N D)
        ((lowerTrueSRCycle_even_iff N C).2 hCEven)
        ((lowerTrueSRCycle_even_iff N D).2 hDEven)
      rcases hI with ⟨I⟩
      exact ⟨lowerSToRIntersection N I⟩


/-! ## Sign-causality kernel for a fully-open discordance witness

The fully-open inflow/outflow coordinates force the original-reaction balance at each
nonzero species to have the same sign as the witness displacement.  Consequently every
active species has an internal reaction contributing with that sign, while the strong
concordance witness condition supplies another active species on the same reaction with
the opposite contribution sign.  These are the local causal units used by the classical
source-block/ear-decomposition proof. -/

open scoped BigOperators

private theorem outflow_pos_of_sigma_pos (N : Network S) {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : 0 < σ s) :
    0 < α (Sum.inr (Sum.inr s)) := by
  rcases lt_trichotomy (α (Sum.inr (Sum.inr s))) 0 with hneg | hzero | hpos
  · obtain ⟨t, ht⟩ := W.negative_reaction (Sum.inr (Sum.inr s)) hneg
    rcases ht with ⟨htsign, htne⟩
    have hts : t = s := by
      simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
        singletonComplex_apply] at htne
      exact htne
    subst t
    simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
      singletonComplex_apply, hs] at htsign
  · rcases W.zero_reaction (Sum.inr (Sum.inr s)) hzero with hall | hopp
    · have hz := hall s (by simp [fullyOpen_reaction_outflow, outflowReaction,
          singletonComplex_apply])
      linarith
    · rcases hopp with ⟨u, v, hu, hv⟩
      rcases hu with ⟨husign, hune⟩
      rcases hv with ⟨hvsign, hvne⟩
      have hus : u = s := by
        simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
          singletonComplex_apply] at hune
        exact hune
      have hvs : v = s := by
        simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
          singletonComplex_apply] at hvne
        exact hvne
      subst u; subst v
      simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
        singletonComplex_apply, hs] at husign hvsign
  · exact hpos
private theorem inflow_nonpos_of_sigma_pos (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : 0 < σ s) :
    α (Sum.inr (Sum.inl s)) ≤ 0 := by
  by_contra h
  have hpos : 0 < α (Sum.inr (Sum.inl s)) := lt_of_not_ge h
  obtain ⟨t, ht⟩ := W.positive_reaction (Sum.inr (Sum.inl s)) hpos
  rcases ht with ⟨htsign, htne⟩
  have hts : t = s := by
    simp [reactionDirectionSign, fullyOpen_reaction_inflow, inflowReaction,
      singletonComplex_apply] at htne
    exact htne
  subst t
  simp [reactionDirectionSign, fullyOpen_reaction_inflow, inflowReaction,
    singletonComplex_apply, hs] at htsign

private theorem outflow_neg_of_sigma_neg (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s < 0) :
    α (Sum.inr (Sum.inr s)) < 0 := by
  rcases lt_trichotomy (α (Sum.inr (Sum.inr s))) 0 with hneg | hzero | hpos
  · exact hneg
  · rcases W.zero_reaction (Sum.inr (Sum.inr s)) hzero with hall | hopp
    · have hz := hall s (by simp [fullyOpen_reaction_outflow, outflowReaction,
          singletonComplex_apply])
      linarith
    · rcases hopp with ⟨u, v, hu, hv⟩
      rcases hu with ⟨husign, hune⟩
      rcases hv with ⟨hvsign, hvne⟩
      have hus : u = s := by
        simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
          singletonComplex_apply] at hune
        exact hune
      have hvs : v = s := by
        simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
          singletonComplex_apply] at hvne
        exact hvne
      subst u; subst v
      simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
        singletonComplex_apply, hs] at husign hvsign
  · obtain ⟨t, ht⟩ := W.positive_reaction (Sum.inr (Sum.inr s)) hpos
    rcases ht with ⟨htsign, htne⟩
    have hts : t = s := by
      simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
        singletonComplex_apply] at htne
      exact htne
    subst t
    simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
      singletonComplex_apply, hs] at htsign

private theorem inflow_nonneg_of_sigma_neg (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s < 0) :
    0 ≤ α (Sum.inr (Sum.inl s)) := by
  by_contra h
  have hneg : α (Sum.inr (Sum.inl s)) < 0 := lt_of_not_ge h
  obtain ⟨t, ht⟩ := W.negative_reaction (Sum.inr (Sum.inl s)) hneg
  rcases ht with ⟨htsign, htne⟩
  have hts : t = s := by
    simp [reactionDirectionSign, fullyOpen_reaction_inflow, inflowReaction,
      singletonComplex_apply] at htne
    exact htne
  subst t
  simp [reactionDirectionSign, fullyOpen_reaction_inflow, inflowReaction,
    singletonComplex_apply, hs] at htsign

private theorem flow_zero_of_sigma_zero (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s = 0) :
    α (Sum.inr (Sum.inl s)) = 0 ∧ α (Sum.inr (Sum.inr s)) = 0 := by
  constructor
  · rcases lt_trichotomy (α (Sum.inr (Sum.inl s))) 0 with hneg | hzero | hpos
    · obtain ⟨t, ht⟩ := W.negative_reaction (Sum.inr (Sum.inl s)) hneg
      rcases ht with ⟨htsign, htne⟩
      have hts : t = s := by
        simp [reactionDirectionSign, fullyOpen_reaction_inflow, inflowReaction,
          singletonComplex_apply] at htne
        exact htne
      subst t
      simp [reactionDirectionSign, fullyOpen_reaction_inflow, inflowReaction,
        singletonComplex_apply, hs] at htsign
    · exact hzero
    · obtain ⟨t, ht⟩ := W.positive_reaction (Sum.inr (Sum.inl s)) hpos
      rcases ht with ⟨htsign, htne⟩
      have hts : t = s := by
        simp [reactionDirectionSign, fullyOpen_reaction_inflow, inflowReaction,
          singletonComplex_apply] at htne
        exact htne
      subst t
      simp [reactionDirectionSign, fullyOpen_reaction_inflow, inflowReaction,
        singletonComplex_apply, hs] at htsign
  · rcases lt_trichotomy (α (Sum.inr (Sum.inr s))) 0 with hneg | hzero | hpos
    · obtain ⟨t, ht⟩ := W.negative_reaction (Sum.inr (Sum.inr s)) hneg
      rcases ht with ⟨htsign, htne⟩
      have hts : t = s := by
        simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
          singletonComplex_apply] at htne
        exact htne
      subst t
      simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
        singletonComplex_apply, hs] at htsign
    · exact hzero
    · obtain ⟨t, ht⟩ := W.positive_reaction (Sum.inr (Sum.inr s)) hpos
      rcases ht with ⟨htsign, htne⟩
      have hts : t = s := by
        simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
          singletonComplex_apply] at htne
        exact htne
      subst t
      simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
        singletonComplex_apply, hs] at htsign

private theorem internal_balance_eq_flow_difference (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : S) :
    (∑ r : N.R, α (Sum.inl r) * N.reactionVector r s) =
      α (Sum.inr (Sum.inr s)) - α (Sum.inr (Sum.inl s)) := by
  have hk := N.fullyOpen.inKerL_apply W.mem_kerL s
  change (∑ q : N.R ⊕ (S ⊕ S), α q * N.fullyOpen.reactionVector q s) = 0 at hk
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hk
  have hin : (∑ t : S, α (Sum.inr (Sum.inl t)) *
      N.fullyOpen.reactionVector (Sum.inr (Sum.inl t)) s) =
      α (Sum.inr (Sum.inl s)) := by
    rw [Finset.sum_eq_single s]
    · rw [N.reactionVector_inflow s]
      simp
    · intro t _ hts
      rw [N.reactionVector_inflow t]
      simp [Pi.single_eq_of_ne (Ne.symm hts)]
    · simp
  have hout : (∑ t : S, α (Sum.inr (Sum.inr t)) *
      N.fullyOpen.reactionVector (Sum.inr (Sum.inr t)) s) =
      - α (Sum.inr (Sum.inr s)) := by
    rw [Finset.sum_eq_single s]
    · rw [N.reactionVector_outflow s]
      simp
    · intro t _ hts
      rw [N.reactionVector_outflow t]
      simp [Pi.single_eq_of_ne (Ne.symm hts)]
    · simp
  rw [hin, hout] at hk
  have hk' : (∑ r : N.R, α (Sum.inl r) * N.reactionVector r s) +
      (α (Sum.inr (Sum.inl s)) - α (Sum.inr (Sum.inr s))) = 0 := by
    simpa [reactionVector_apply, sub_eq_add_neg] using hk
  linarith

private theorem internal_balance_same_sign (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : S) :
    SignType.sign (∑ r : N.R, α (Sum.inl r) * N.reactionVector r s) =
      SignType.sign (σ s) := by
  rcases lt_trichotomy (σ s) 0 with hsneg | hszero | hspos
  · have ho := outflow_neg_of_sigma_neg N W hsneg
    have hi := inflow_nonneg_of_sigma_neg N W hsneg
    have hb := internal_balance_eq_flow_difference N W s
    have hbalneg : (∑ r : N.R, α (Sum.inl r) * N.reactionVector r s) < 0 := by linarith
    rw [sign_neg hbalneg, sign_neg hsneg]
  · have hf := flow_zero_of_sigma_zero N W hszero
    have hb := internal_balance_eq_flow_difference N W s
    rw [hf.1, hf.2] at hb
    have hbalzero : (∑ r : N.R, α (Sum.inl r) * N.reactionVector r s) = 0 := by linarith
    rw [hbalzero, hszero, sign_zero]
  · have ho := outflow_pos_of_sigma_pos N W hspos
    have hi := inflow_nonpos_of_sigma_pos N W hspos
    have hb := internal_balance_eq_flow_difference N W s
    have hbalpos : 0 < (∑ r : N.R, α (Sum.inl r) * N.reactionVector r s) := by linarith
    rw [sign_pos hbalpos, sign_pos hspos]
private theorem exists_internal_term_same_sign (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s ≠ 0) :
    ∃ r : N.R,
      0 < (α (Sum.inl r) * N.reactionVector r s) * σ s := by
  have hsign := internal_balance_same_sign N W s
  rcases lt_or_gt_of_ne hs with hsneg | hspos
  · have hsumneg : (∑ r : N.R, α (Sum.inl r) * N.reactionVector r s) < 0 := by
      apply sign_eq_neg_one_iff.mp
      rw [hsign, sign_neg hsneg]
    have hex : ∃ r : N.R, α (Sum.inl r) * N.reactionVector r s < 0 := by
      by_contra hn
      push Not at hn
      have hnn : 0 ≤ ∑ r : N.R, α (Sum.inl r) * N.reactionVector r s :=
        Finset.sum_nonneg fun r _ => hn r
      linarith
    rcases hex with ⟨r, hr⟩
    exact ⟨r, mul_pos_of_neg_of_neg hr hsneg⟩
  · have hsumpos : 0 < (∑ r : N.R, α (Sum.inl r) * N.reactionVector r s) := by
      apply sign_eq_one_iff.mp
      rw [hsign, sign_pos hspos]
    have hex : ∃ r : N.R, 0 < α (Sum.inl r) * N.reactionVector r s := by
      by_contra hn
      push Not at hn
      have hnp : (∑ r : N.R, α (Sum.inl r) * N.reactionVector r s) ≤ 0 :=
        Finset.sum_nonpos fun r _ => hn r
      linarith
    rcases hex with ⟨r, hr⟩
    exact ⟨r, mul_pos hr hspos⟩

private theorem original_inflow_term_nonpos (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    {r : N.R} {t s : S} (hr : N.reaction r = inflowReaction t) :
    (α (Sum.inl r) * N.reactionVector r s) * σ s ≤ 0 := by
  by_cases hst : s = t
  · subst s
    have hrv : N.reactionVector r t = 1 := by
      rw [reactionVector_apply, hr]
      simp [inflowReaction, singletonComplex_apply]
    rw [hrv]
    simp only [mul_one]
    rcases lt_trichotomy (α (Sum.inl r)) 0 with ha | ha | ha
    · obtain ⟨u, hu⟩ := W.negative_reaction (Sum.inl r) ha
      rcases hu with ⟨hsign, hdirne⟩
      have hut : u = t := by
        by_contra hne
        apply hdirne
        simp [reactionDirectionSign, fullyOpen_reaction_inl, hr,
          inflowReaction, singletonComplex_apply, hne]
      subst u
      have hspos : 0 < σ t := by
        apply sign_eq_one_iff.mp
        simpa [reactionDirectionSign, fullyOpen_reaction_inl, hr,
          inflowReaction, singletonComplex_apply] using hsign
      exact (mul_nonpos_of_nonpos_of_nonneg ha.le hspos.le)
    · simp [ha]
    · obtain ⟨u, hu⟩ := W.positive_reaction (Sum.inl r) ha
      rcases hu with ⟨hsign, hdirne⟩
      have hut : u = t := by
        by_contra hne
        apply hdirne
        simp [reactionDirectionSign, fullyOpen_reaction_inl, hr,
          inflowReaction, singletonComplex_apply, hne]
      subst u
      have hsneg : σ t < 0 := by
        apply sign_eq_neg_one_iff.mp
        simpa [reactionDirectionSign, fullyOpen_reaction_inl, hr,
          inflowReaction, singletonComplex_apply] using hsign
      exact (mul_nonpos_of_nonneg_of_nonpos ha.le hsneg.le)
  · have hrv : N.reactionVector r s = 0 := by
      rw [reactionVector_apply, hr]
      simp [inflowReaction, singletonComplex_apply, hst]
    rw [hrv]
    simp

private theorem original_outflow_term_nonpos (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    {r : N.R} {t s : S} (hr : N.reaction r = outflowReaction t) :
    (α (Sum.inl r) * N.reactionVector r s) * σ s ≤ 0 := by
  by_cases hst : s = t
  · subst s
    have hrv : N.reactionVector r t = -1 := by
      rw [reactionVector_apply, hr]
      simp [outflowReaction, singletonComplex_apply]
    rw [hrv]
    rcases lt_trichotomy (α (Sum.inl r)) 0 with ha | ha | ha
    · obtain ⟨u, hu⟩ := W.negative_reaction (Sum.inl r) ha
      rcases hu with ⟨hsign, hdirne⟩
      have hut : u = t := by
        by_contra hne
        apply hdirne
        simp [reactionDirectionSign, fullyOpen_reaction_inl, hr,
          outflowReaction, singletonComplex_apply, hne]
      subst u
      have hsneg : σ t < 0 := by
        apply sign_eq_neg_one_iff.mp
        simpa [reactionDirectionSign, fullyOpen_reaction_inl, hr,
          outflowReaction, singletonComplex_apply] using hsign
      nlinarith
    · simp [ha]
    · obtain ⟨u, hu⟩ := W.positive_reaction (Sum.inl r) ha
      rcases hu with ⟨hsign, hdirne⟩
      have hut : u = t := by
        by_contra hne
        apply hdirne
        simp [reactionDirectionSign, fullyOpen_reaction_inl, hr,
          outflowReaction, singletonComplex_apply, hne]
      subst u
      have hspos : 0 < σ t := by
        apply sign_eq_one_iff.mp
        simpa [reactionDirectionSign, fullyOpen_reaction_inl, hr,
          outflowReaction, singletonComplex_apply] using hsign
      nlinarith
  · have hrv : N.reactionVector r s = 0 := by
      rw [reactionVector_apply, hr]
      simp [outflowReaction, singletonComplex_apply, hst]
    rw [hrv]
    simp

private theorem original_flow_term_nonpos (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    {r : N.R} (hr : N.IsFlowChannel r) (s : S) :
    (α (Sum.inl r) * N.reactionVector r s) * σ s ≤ 0 := by
  rcases hflow r hr with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact original_inflow_term_nonpos N W ht
  · exact original_outflow_term_nonpos N W ht


/-- Under the zero-complex side condition, the same-sign contribution selected from a fully-open
strong-concordance witness can be chosen from a genuine internal reaction of the original network.
This is exactly where `ZeroComplexReactionsAreFlows` enters the repaired true-SR argument. -/
theorem exists_true_internal_term_same_sign (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s ≠ 0) :
    ∃ r : N.R, ¬ N.IsFlowChannel r ∧
      0 < (α (Sum.inl r) * N.reactionVector r s) * σ s := by
  obtain ⟨r, hrpos⟩ := exists_internal_term_same_sign N W hs
  refine ⟨r, ?_, hrpos⟩
  intro hrflow
  have hnonpos := original_flow_term_nonpos N hflow W hrflow s
  linarith

/-- **Sign of the degradation coefficient.**  In the fully open extension the coefficient that
the witness assigns to the degradation reaction `s → 0` carries exactly the sign of `σ s`.

This is the numerical foothold of the Shinar--Feinberg source argument.  The witness is stated
purely in terms of signs, so it looks as though no magnitudes are available; but it pins the
sign of one specific coordinate of `α`, and the kernel relation `InKerL α` then converts that
into a *strict* inequality among the internal terms.  The magnitudes that eventually appear in
the cyclic gain inequality are the `|α R|` themselves, not magnitudes of `σ`. -/
theorem outflow_coeff_mul_sigma_pos (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s ≠ 0) :
    0 < α (Sum.inr (Sum.inr s)) * σ s := by
  have hdir : ∀ t : S,
      N.fullyOpen.reactionDirectionSign (Sum.inr (Sum.inr s)) t =
        if t = s then (1 : ℝ) else 0 := by
    intro t
    by_cases ht : t = s
    · subst t
      simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
        singletonComplex_apply]
    · simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
        singletonComplex_apply, ht]
  -- Any species witnessing `Promotes` or `Opposes` for a degradation reaction must be `s`
  -- itself, since the direction sign is supported at `s` alone.
  have hforce : ∀ t : S,
      N.fullyOpen.reactionDirectionSign (Sum.inr (Sum.inr s)) t ≠ 0 → t = s := by
    intro t ht
    by_contra hne
    exact ht (by simpa [hdir t, hne] using rfl)
  rcases lt_trichotomy (α (Sum.inr (Sum.inr s))) 0 with ha | ha | ha
  · obtain ⟨u, hsign, hdirne⟩ := W.negative_reaction (Sum.inr (Sum.inr s)) ha
    rw [hforce u hdirne] at hsign
    have hneg : σ s < 0 := by
      apply sign_eq_neg_one_iff.mp
      simpa [hdir s] using hsign
    nlinarith
  · exfalso
    rcases W.zero_reaction (Sum.inr (Sum.inr s)) ha with hzero | ⟨u, v, hu, hv⟩
    · exact hs (hzero s (by
        simp [fullyOpen_reaction_outflow, outflowReaction, singletonComplex_apply]))
    · rw [hforce u hu.2] at hu
      rw [hforce v hv.2] at hv
      have h1 : SignType.sign (σ s) = 1 := by simpa [hdir s] using hu.1
      have h2 : SignType.sign (σ s) = -1 := by simpa [hdir s] using hv.1
      rw [h1] at h2
      exact absurd h2 (by decide)
  · obtain ⟨u, hsign, hdirne⟩ := W.positive_reaction (Sum.inr (Sum.inr s)) ha
    rw [hforce u hdirne] at hsign
    have hpos : 0 < σ s := by
      apply sign_eq_one_iff.mp
      simpa [hdir s] using hsign
    nlinarith

/-- **The degradation coefficient is the net internal-plus-synthesis flux at a species.**
Splitting `InKerL α` for the fully open extension over the three kinds of reaction isolates
the coefficient of `s → 0`.  This is the kernel bookkeeping behind Shinar--Feinberg (14). -/
theorem outflow_coeff_eq_internal_add_inflow (N : Network S)
    {α : N.fullyOpen.R → ℝ} (hα : N.fullyOpen.InKerL α) (s : S) :
    α (Sum.inr (Sum.inr s)) =
      (∑ r : N.R, α (Sum.inl r) * N.reactionVector r s) + α (Sum.inr (Sum.inl s)) := by
  have h : ∑ q : N.R ⊕ (S ⊕ S), α q * N.fullyOpen.reactionVector q s = 0 :=
    N.fullyOpen.inKerL_apply hα s
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h
  have hin : ∀ t : S,
      α (Sum.inr (Sum.inl t)) * N.fullyOpen.reactionVector (Sum.inr (Sum.inl t)) s =
        if t = s then α (Sum.inr (Sum.inl t)) else 0 := by
    intro t
    rw [N.reactionVector_inflow t]
    by_cases ht : t = s <;> simp [Pi.single_apply, ht]
  have hout : ∀ t : S,
      α (Sum.inr (Sum.inr t)) * N.fullyOpen.reactionVector (Sum.inr (Sum.inr t)) s =
        if t = s then -α (Sum.inr (Sum.inr t)) else 0 := by
    intro t
    rw [N.reactionVector_outflow t]
    by_cases ht : t = s <;> simp [Pi.single_apply, ht]
  have hinl : ∀ r : N.R,
      α (Sum.inl r) * N.fullyOpen.reactionVector (Sum.inl r) s =
        α (Sum.inl r) * N.reactionVector r s := by
    intro r
    congr 1
  simp only [hinl, hin, hout, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  linarith

/-- **The Shinar--Feinberg source foothold, aggregate form.**  At every signed species the net
internal-plus-synthesis flux agrees in sign with `σ s`, strictly.  This is the inequality that
the block decomposition of the causal source later localizes to a single cyclic gain.  The
synthesis term is in fact always nonpositive and is removed in `internal_flux_mul_sigma_pos`
below; `ZeroComplexReactionsAreFlows` is needed for a different reason, namely reactions of the
*true* chemistry whose reactant complex is the zero complex (see
`CRNT/Examples/TrueSRCounterexample` for the network that fails without it). -/
theorem internal_add_inflow_mul_sigma_pos (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s ≠ 0) :
    0 < ((∑ r : N.R, α (Sum.inl r) * N.reactionVector r s)
      + α (Sum.inr (Sum.inl s))) * σ s := by
  have hkey := N.outflow_coeff_mul_sigma_pos W hs
  rwa [N.outflow_coeff_eq_internal_add_inflow W.mem_kerL s] at hkey

/-- The synthesis coefficient always opposes `σ s`, so its term is nonpositive.  The direction
sign of `0 → s` is `-1` at `s` and zero elsewhere, so any species witnessing `Promotes` or
`Opposes` must be `s` itself, and either alternative makes the product negative. -/
theorem inflow_coeff_mul_sigma_nonpos (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : S) :
    α (Sum.inr (Sum.inl s)) * σ s ≤ 0 := by
  have hdir : ∀ t : S,
      N.fullyOpen.reactionDirectionSign (Sum.inr (Sum.inl s)) t =
        if t = s then (-1 : ℝ) else 0 := by
    intro t
    by_cases ht : t = s
    · subst t
      simp [reactionDirectionSign, fullyOpen_reaction_inflow, inflowReaction,
        singletonComplex_apply]
    · simp [reactionDirectionSign, fullyOpen_reaction_inflow, inflowReaction,
        singletonComplex_apply, ht]
  have hforce : ∀ t : S,
      N.fullyOpen.reactionDirectionSign (Sum.inr (Sum.inl s)) t ≠ 0 → t = s := by
    intro t ht
    by_contra hne
    exact ht (by simpa [hdir t, hne] using rfl)
  rcases lt_trichotomy (α (Sum.inr (Sum.inl s))) 0 with ha | ha | ha
  · obtain ⟨u, hsign, hdirne⟩ := W.negative_reaction (Sum.inr (Sum.inl s)) ha
    rw [hforce u hdirne] at hsign
    have hpos : 0 < σ s := by
      apply sign_eq_one_iff.mp
      simpa [hdir s] using hsign
    nlinarith
  · simp [ha]
  · obtain ⟨u, hsign, hdirne⟩ := W.positive_reaction (Sum.inr (Sum.inl s)) ha
    rw [hforce u hdirne] at hsign
    have hneg : σ s < 0 := by
      apply sign_eq_neg_one_iff.mp
      simpa [hdir s] using hsign
    nlinarith

/-- **Shinar--Feinberg (15) for strong concordance.**  At every signed species the net internal
flux strictly agrees in sign with `σ s`.  The synthesis term present in
`internal_add_inflow_mul_sigma_pos` drops out because it is always nonpositive, so this is the
clean form: the true chemistry alone must account for the sign of every signed species.

This is the inequality that the block decomposition of the causal source later localizes to a
single cyclic gain, with the gain magnitudes being the `|α R|`. -/
theorem internal_flux_mul_sigma_pos (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s ≠ 0) :
    0 < (∑ r : N.R, α (Sum.inl r) * N.reactionVector r s) * σ s := by
  have hsum := N.internal_add_inflow_mul_sigma_pos W hs
  have hin := N.inflow_coeff_mul_sigma_nonpos W s
  nlinarith [hsum, hin]

/-- **Restrict the strict source inequality to a reaction subset.**

If every reaction outside `A` contributes nonpositively after multiplication by the species
sign, the global kernel inequality remains strict when summed only over `A`.  This packages the
finite-source restriction step for the later graph argument. -/
theorem internal_flux_mul_sigma_pos_on_finset (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s ≠ 0)
    (A : Finset N.R)
    (hout : ∀ r ∈ Finset.univ \ A,
      (α (Sum.inl r) * N.reactionVector r s) * σ s ≤ 0) :
    0 < ∑ r ∈ A, (α (Sum.inl r) * N.reactionVector r s) * σ s := by
  apply CRNT.sum_subset_pos_of_nonpos_outside _ A hout
  have hglobal := N.internal_flux_mul_sigma_pos W hs
  rw [← Finset.sum_mul]
  exact hglobal

/-- The internal original channels alone have strictly positive signed flux at every active
species. Flow-channel terms can be dropped because strong concordance makes each of them
nonpositive. This aggregate form is useful when parallel and reverse channels are grouped by
their true-reaction class. -/
noncomputable def nonflowOriginalChannels (N : Network S) : Finset N.R := by
  classical
  exact Finset.univ.filter (fun r => ¬ N.IsFlowChannel r)

theorem internal_flux_mul_sigma_pos_on_nonflow_channels (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s ≠ 0) :
    0 < ∑ r ∈ N.nonflowOriginalChannels,
      (α (Sum.inl r) * N.reactionVector r s) * σ s := by
  classical
  let I : Finset N.R := Finset.univ.filter (fun r => ¬ N.IsFlowChannel r)
  apply N.internal_flux_mul_sigma_pos_on_finset W hs I
  intro r hr
  have hrnot : r ∉ I := (Finset.mem_sdiff.mp hr).2
  have hnotnot : ¬¬ N.IsFlowChannel r := by simpa [I] using hrnot
  exact N.original_flow_term_nonpos hflow W (Classical.not_not.mp hnotnot) s

/-- **The SR edge label and the kernel term agree only under reactant/product separation.**

The Shinar--Feinberg source inequalities are stated with the *edge* labels of the SR graph,
namely the stoichiometric coefficient of the species in the labelling complex, whereas the
kernel relation `InKerL α` supplies the *net* coefficient `target s - source s`.  Those two
numbers coincide, up to sign, exactly when the species does not occur on both sides of the
reaction.  The published proof makes that a standing assumption ("a species can appear on only
one side of a reaction"); `ReactantProductSeparated` is its formal counterpart.

This lemma records the identification, and so pins down precisely where the separation
condition enters the argument: without it the numbers that the SR graph labels the edges with
are not the numbers the kernel relation constrains, and the cyclic gain inequality derived from
`internal_flux_mul_sigma_pos` is about the net coefficients rather than the edge labels. -/
theorem abs_reactionVector_eq_edge_label (N : Network S)
    (hsep : N.ReactantProductSeparated) (r : N.R) (s : S) :
    |N.reactionVector r s| =
      if (N.reaction r).source s ≠ 0 then ((N.reaction r).source s : ℝ)
      else ((N.reaction r).target s : ℝ) := by
  rw [reactionVector_apply]
  by_cases hsrc : (N.reaction r).source s ≠ 0
  · have htgt : (N.reaction r).target s = 0 := hsep r s hsrc
    rw [if_pos hsrc, htgt]
    have : (0 : ℝ) < ((N.reaction r).source s : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hsrc
    rw [Nat.cast_zero, zero_sub, abs_neg, abs_of_pos this]
  · rw [if_neg hsrc]
    have hz : (N.reaction r).source s = 0 := by
      by_contra h
      exact hsrc h
    rw [hz, Nat.cast_zero, sub_zero, abs_of_nonneg (by positivity)]

/-- **Degree-two localization of the source inequality.**

If at a signed species `s` only two reactions of the true chemistry carry a nonzero flux term,
one of them causal for the sign of `s` and the other opposing it, then the opposing term is
strictly dominated.  In Shinar--Feinberg terms this is the collapse of the source inequality
(25) at a species of an end species-block, where exactly two of the block's reactions meet `s`;
iterating it around a directed causal cycle is what produces the cyclic gain.

The inequality is stated with the net coefficients `|reactionVector r s|`.  Under
`ReactantProductSeparated` those are the SR-graph edge labels, by
`abs_reactionVector_eq_edge_label`. -/
theorem gain_of_two_term_flux (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s ≠ 0)
    {r₁ r₂ : N.R} (hne : r₁ ≠ r₂)
    (hrest : ∀ r : N.R, r ≠ r₁ → r ≠ r₂ → α (Sum.inl r) * N.reactionVector r s = 0)
    (hcausal : 0 < (α (Sum.inl r₁) * N.reactionVector r₁ s) * σ s)
    (hopp : (α (Sum.inl r₂) * N.reactionVector r₂ s) * σ s < 0) :
    |α (Sum.inl r₂)| * |N.reactionVector r₂ s| <
      |α (Sum.inl r₁)| * |N.reactionVector r₁ s| := by
  classical
  set x := α (Sum.inl r₁) * N.reactionVector r₁ s with hx
  set y := α (Sum.inl r₂) * N.reactionVector r₂ s with hy
  -- The full internal flux at `s` reduces to the two surviving terms.
  have hsum : (∑ r : N.R, α (Sum.inl r) * N.reactionVector r s) = x + y := by
    rw [← Finset.sum_subset (Finset.subset_univ ({r₁, r₂} : Finset N.R))]
    · rw [Finset.sum_pair hne]
    · intro r _ hr
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
      exact hrest r hr.1 hr.2
  have htot : 0 < (x + y) * σ s := by
    have := N.internal_flux_mul_sigma_pos W hs
    rwa [hsum] at this
  -- Compare absolute values through `σ s`.
  have habs : |σ s| > 0 := abs_pos.mpr hs
  have hxabs : |x| * |σ s| = x * σ s := by
    rw [← abs_mul]
    exact abs_of_pos hcausal
  have hyabs : |y| * |σ s| = -(y * σ s) := by
    rw [← abs_mul]
    exact abs_of_neg hopp
  have hlt : |y| * |σ s| < |x| * |σ s| := by
    rw [hxabs, hyabs]
    nlinarith [htot]
  have : |y| < |x| := lt_of_mul_lt_mul_right (by linarith [hlt]) (le_of_lt habs)
  rw [hx, hy, abs_mul, abs_mul] at this
  exact this

/-- **Degree-two gain with sign-controlled off-block terms.**

The source-block inequalities do not require every reaction outside the selected block to vanish.
They only require that each such flux contribution oppose the sign of the species. Summing those
nonpositive contributions leaves the same strict comparison between the causal and opposing
cycle terms as in `gain_of_two_term_flux`.

This is the form used by the Shinar--Feinberg end-block argument: reactions outside an end block
can meet its separating species, but their contributions strengthen the source inequality after
the block terms are removed. -/
theorem gain_of_two_term_flux_of_nonpos_rest (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s ≠ 0)
    {r₁ r₂ : N.R} (hne : r₁ ≠ r₂)
    (hrest : ∀ r : N.R, r ≠ r₁ → r ≠ r₂ →
      (α (Sum.inl r) * N.reactionVector r s) * σ s ≤ 0)
    (hcausal : 0 < (α (Sum.inl r₁) * N.reactionVector r₁ s) * σ s)
    (hopp : (α (Sum.inl r₂) * N.reactionVector r₂ s) * σ s < 0) :
    |α (Sum.inl r₂)| * |N.reactionVector r₂ s| <
      |α (Sum.inl r₁)| * |N.reactionVector r₁ s| := by
  classical
  set x := α (Sum.inl r₁) * N.reactionVector r₁ s with hx
  set y := α (Sum.inl r₂) * N.reactionVector r₂ s with hy
  let pair : Finset N.R := {r₁, r₂}
  have hout : ∀ r ∈ Finset.univ \ pair,
      (α (Sum.inl r) * N.reactionVector r s) * σ s ≤ 0 := by
    intro r hr
    have hrPair : r ∉ pair := (Finset.mem_sdiff.mp hr).2
    have hr1 : r ≠ r₁ := by
      intro heq
      apply hrPair
      simp [heq, pair]
    have hr2 : r ≠ r₂ := by
      intro heq
      apply hrPair
      simp [heq, pair]
    exact hrest r hr1 hr2
  have hpairPos := N.internal_flux_mul_sigma_pos_on_finset W hs pair hout
  have hpairEq :
      (∑ r ∈ pair, (α (Sum.inl r) * N.reactionVector r s) * σ s) =
        (x + y) * σ s := by
    simp only [pair, Finset.sum_pair hne]
    rw [hx, hy]
    ring
  have hxy : 0 < (x + y) * σ s := by
    rw [← hpairEq]
    exact hpairPos
  have hxpos : 0 < x * σ s := by simpa [hx] using hcausal
  have hyneg : y * σ s < 0 := by simpa [hy] using hopp
  have habs : |σ s| > 0 := abs_pos.mpr hs
  have hxabs : |x| * |σ s| = x * σ s := by
    rw [← abs_mul]
    exact abs_of_pos hxpos
  have hyabs : |y| * |σ s| = -(y * σ s) := by
    rw [← abs_mul]
    exact abs_of_neg hyneg
  have hlt : |y| * |σ s| < |x| * |σ s| := by
    rw [hxabs, hyabs]
    nlinarith [hxy]
  have : |y| < |x| := lt_of_mul_lt_mul_right (by linarith [hlt]) (le_of_lt habs)
  rw [hx, hy, abs_mul, abs_mul] at this
  exact this

/-- **The SR edge label is the net coefficient, under separation.**  For every true-SR edge the
stoichiometric label it carries equals the absolute net coefficient of its species in the
representative reaction.  This is the form in which `abs_reactionVector_eq_edge_label` is
actually used: it converts the kernel-side inequalities of
`gain_of_two_term_flux` into statements about `TrueSREdge.coeff`, which is what
`TrueSRCycle.SCycle` and `TrueSRCycle.no_strict_gain` speak about.

Separation is used in the product-endpoint branch: the label is nonzero there, so the species
cannot also occur in the reactant complex. -/
theorem edge_coeff_eq_abs_reactionVector (N : Network S)
    (hsep : N.ReactantProductSeparated) (e : N.TrueSREdge) :
    (e.coeff : ℝ) = |N.reactionVector e.representative e.species| := by
  have hocc : e.endpoint e.species ≠ 0 := e.occurs
  rcases e.endpoint_is_source_or_target with hsrc | htgt
  · -- The edge is labelled by the reactant complex.
    have hs : (N.reaction e.representative).source e.species ≠ 0 := by
      rw [← hsrc]; exact hocc
    rw [N.abs_reactionVector_eq_edge_label hsep, if_pos hs, TrueSREdge.coeff, hsrc]
  · -- The edge is labelled by the product complex; separation forces the reactant slot empty.
    have ht : (N.reaction e.representative).target e.species ≠ 0 := by
      rw [← htgt]; exact hocc
    have hs : (N.reaction e.representative).source e.species = 0 := by
      by_contra h
      exact ht (hsep e.representative e.species h)
    rw [N.abs_reactionVector_eq_edge_label hsep, if_neg (by simp [hs]),
      TrueSREdge.coeff, htgt]

/-- Reactant/product separation makes an incidence edge's endpoint unique once its concrete
reaction representative and species are fixed. -/
theorem trueSREdge_endpoint_eq_of_same_representative_and_species (N : Network S)
    (hsep : N.ReactantProductSeparated) (e f : N.TrueSREdge)
    (hrep : e.representative = f.representative) (hsp : e.species = f.species) :
    e.endpoint = f.endpoint := by
  rcases e.endpoint_is_source_or_target with heSrc | heTgt <;>
    rcases f.endpoint_is_source_or_target with hfSrc | hfTgt
  · rw [heSrc, hfSrc, hrep]
  · have hsrc : (N.reaction e.representative).source e.species ≠ 0 := by
      rw [← heSrc]
      exact e.occurs
    have htgt : (N.reaction e.representative).target e.species ≠ 0 := by
      have h := f.occurs
      rw [hfTgt, ← hrep, ← hsp] at h
      exact h
    exfalso
    exact htgt (hsep e.representative e.species hsrc)
  · have hsrc : (N.reaction e.representative).source e.species ≠ 0 := by
      have h := f.occurs
      rw [hfSrc, ← hrep, ← hsp] at h
      exact h
    have htgt : (N.reaction e.representative).target e.species ≠ 0 := by
      rw [← heTgt]
      exact e.occurs
    exfalso
    exact htgt (hsep e.representative e.species hsrc)
  · rw [heTgt, hfTgt, hrep]

/-- Under separation, a true-reaction class has only one endpoint label at a given species,
even when its edges come from different parallel or reversed channels. -/
private theorem trueSREdge_endpoint_eq_of_same_class_and_species (N : Network S)
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

theorem exists_internal_opposite_species (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {r : N.R}
    (hr : α (Sum.inl r) ≠ 0) :
    ∃ t : S, (α (Sum.inl r) * N.reactionVector r t) * σ t < 0 := by
  rcases lt_or_gt_of_ne hr with haNeg | haPos
  · obtain ⟨t, ht⟩ := W.negative_reaction (Sum.inl r) haNeg
    change N.Opposes r σ t at ht
    rcases ht with ⟨hsign, hdirne⟩
    have hdir : N.reactionDirectionSign r t = - N.reactionVector r t := by
      simp [reactionDirectionSign, reactionVector_apply]
    have hvne : N.reactionVector r t ≠ 0 := by
      intro hv
      apply hdirne
      rw [hdir, hv, neg_zero]
    rcases lt_or_gt_of_ne hvne with hvneg | hvpos
    · have hdirpos : 0 < N.reactionDirectionSign r t := by rw [hdir]; linarith
      have hsneg : σ t < 0 := by
        apply sign_eq_neg_one_iff.mp
        simpa [sign_pos hdirpos] using hsign
      have hatv : 0 < α (Sum.inl r) * N.reactionVector r t :=
        mul_pos_of_neg_of_neg haNeg hvneg
      exact ⟨t, mul_neg_of_pos_of_neg hatv hsneg⟩
    · have hdirneg : N.reactionDirectionSign r t < 0 := by rw [hdir]; linarith
      have hspos : 0 < σ t := by
        apply sign_eq_one_iff.mp
        simpa [sign_neg hdirneg] using hsign
      have hatv : α (Sum.inl r) * N.reactionVector r t < 0 :=
        mul_neg_of_neg_of_pos haNeg hvpos
      exact ⟨t, mul_neg_of_neg_of_pos hatv hspos⟩
  · obtain ⟨t, ht⟩ := W.positive_reaction (Sum.inl r) haPos
    change N.Promotes r σ t at ht
    rcases ht with ⟨hsign, hdirne⟩
    have hdir : N.reactionDirectionSign r t = - N.reactionVector r t := by
      simp [reactionDirectionSign, reactionVector_apply]
    have hvne : N.reactionVector r t ≠ 0 := by
      intro hv
      apply hdirne
      rw [hdir, hv, neg_zero]
    rcases lt_or_gt_of_ne hvne with hvneg | hvpos
    · have hdirpos : 0 < N.reactionDirectionSign r t := by rw [hdir]; linarith
      have hspos : 0 < σ t := by
        apply sign_eq_one_iff.mp
        simpa [sign_pos hdirpos] using hsign
      have hatv : α (Sum.inl r) * N.reactionVector r t < 0 :=
        mul_neg_of_pos_of_neg haPos hvneg
      exact ⟨t, mul_neg_of_neg_of_pos hatv hspos⟩
    · have hdirneg : N.reactionDirectionSign r t < 0 := by rw [hdir]; linarith
      have hsneg : σ t < 0 := by
        apply sign_eq_neg_one_iff.mp
        simpa [sign_neg hdirneg] using hsign
      have hatv : 0 < α (Sum.inl r) * N.reactionVector r t := mul_pos haPos hvpos
      exact ⟨t, mul_neg_of_pos_of_neg hatv hsneg⟩

private theorem exists_causal_unit_predecessor (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s ≠ 0) :
    ∃ (r : N.R) (t : S),
      0 < (α (Sum.inl r) * N.reactionVector r s) * σ s ∧
      (α (Sum.inl r) * N.reactionVector r t) * σ t < 0 := by
  obtain ⟨r, hrs⟩ := exists_internal_term_same_sign N W hs
  have har : α (Sum.inl r) ≠ 0 := by
    intro h
    simp [h] at hrs
  obtain ⟨t, hrt⟩ := exists_internal_opposite_species N W har
  exact ⟨r, t, hrs, hrt⟩
private theorem exists_causal_unit_predecessor_ne (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s ≠ 0) :
    ∃ (r : N.R) (t : S), t ≠ s ∧ σ t ≠ 0 ∧
      0 < (α (Sum.inl r) * N.reactionVector r s) * σ s ∧
      (α (Sum.inl r) * N.reactionVector r t) * σ t < 0 := by
  obtain ⟨r, t, hrs, hrt⟩ := exists_causal_unit_predecessor N W hs
  have htσ : σ t ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hrt
    exact (lt_irrefl 0) hrt
  have hts : t ≠ s := by
    intro h
    subst t
    linarith
  exact ⟨r, t, hts, htσ, hrs, hrt⟩

/-- Canonical labeled true-SR edge selected by the sign of a nonzero reaction-vector coordinate.
The source endpoint is used for positive reactant-minus-product direction and the target endpoint for
negative direction.  This choice makes c-pair parity track sign changes in the causal orbit. -/
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

@[simp] private theorem trueSREdgeOfReactionVectorNe_representative (N : Network S)
    (r : N.R) (hrint : ¬ N.IsFlowChannel r) (s : S)
    (hrs : N.reactionVector r s ≠ 0) :
    (N.trueSREdgeOfReactionVectorNe r hrint s hrs).representative = r := by
  unfold trueSREdgeOfReactionVectorNe
  split <;> rfl

/-- **The SR edge label dominates the net coefficient, and the gap is exactly non-separation.**

For the edges the causal construction produces the label is the reactant coefficient when the
species is net-consumed and the product coefficient when it is net-produced, so in both cases it
is at least the absolute net coefficient, with equality precisely when the species does not
occur on the other side of the reaction.

This settles the direction of the mismatch discussed in
`CRNT/Examples/TrueSRCounterexample.lean`, and it is the reason the true-SR argument cannot be
carried out in net coefficients alone: the strict cyclic gain derived from `InKerL α` lives in
`|reactionVector|`, the `SCycle` identity lives in `coeff`, and since `coeff ≥ |reactionVector|`
on *both* the left and the right edges of a cycle, neither inequality transfers to the other
side.  Multiplying the gain around the cycle gives `∏ L_rv < ∏ R_rv`, which together with
`∏ L_coeff = ∏ R_coeff` and `coeff ≥ rv` throughout yields no contradiction.  Equality — that
is, `ReactantProductSeparated` — is what collapses the two into one quantity. -/
theorem abs_reactionVector_le_trueSREdge_coeff (N : Network S)
    (r : N.R) (hrint : ¬ N.IsFlowChannel r) (s : S)
    (hrs : N.reactionVector r s ≠ 0) :
    |N.reactionVector r s| ≤
      ((N.trueSREdgeOfReactionVectorNe r hrint s hrs).coeff : ℝ) := by
  have heq : N.reactionDirectionSign r s = - N.reactionVector r s := by
    simp [reactionDirectionSign, reactionVector_apply]
  unfold trueSREdgeOfReactionVectorNe TrueSREdge.coeff
  split
  · -- net-consumed: the label is the reactant coefficient
    rename_i hp
    have hneg : N.reactionVector r s < 0 := by
      rw [heq] at hp; linarith
    rw [abs_of_neg hneg, reactionVector_apply]
    have : (0 : ℝ) ≤ ((N.reaction r).target s : ℝ) := by positivity
    push_cast
    linarith
  · -- net-produced: the label is the product coefficient
    rename_i hp
    have hpos : 0 < N.reactionVector r s := by
      rw [heq] at hp
      rcases lt_trichotomy (N.reactionVector r s) 0 with h | h | h
      · exact absurd (by linarith : (0:ℝ) < -N.reactionVector r s) hp
      · exact absurd h hrs
      · exact h
    rw [abs_of_pos hpos, reactionVector_apply]
    have : (0 : ℝ) ≤ ((N.reaction r).source s : ℝ) := by positivity
    push_cast
    linarith

/-- Under separation the net coefficient of an edge is its label, so the two s-cycle conditions
coincide.  This shows the `SCycleNet` variant is a conservative reading of the published
s-cycle condition: it agrees with `SCycle` on exactly the networks Shinar--Feinberg consider. -/
theorem netCoeff_eq_coeff_of_separated (N : Network S)
    (hsep : N.ReactantProductSeparated) (e : N.TrueSREdge) :
    e.netCoeff = (e.coeff : ℝ) := by
  have h := N.edge_coeff_eq_abs_reactionVector hsep e
  have hrv : N.reactionVector e.representative e.species =
      ((N.reaction e.representative).target e.species : ℝ)
        - ((N.reaction e.representative).source e.species : ℝ) := reactionVector_apply ..
  rw [TrueSREdge.netCoeff, ← hrv, ← h]

/-- The two s-cycle conditions agree under reactant/product separation. -/
theorem TrueSRCycle.sCycleNet_iff_sCycle_of_separated (N : Network S)
    (hsep : N.ReactantProductSeparated) {n : ℕ} (C : N.TrueSRCycle n) :
    C.SCycleNet ↔ C.SCycle := by
  unfold TrueSRCycle.SCycleNet TrueSRCycle.SCycle
  rw [Finset.prod_congr rfl (fun i _ => N.netCoeff_eq_coeff_of_separated hsep (C.leftEdge i)),
    Finset.prod_congr rfl (fun i _ => N.netCoeff_eq_coeff_of_separated hsep (C.rightEdge i))]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

theorem trueSREdge_sameEndpoint_iff_direction_mul_pos (N : Network S) (r : N.R) (hr : ¬ N.IsFlowChannel r) (s t : S)
    (hs : N.reactionVector r s ≠ 0) (ht : N.reactionVector r t ≠ 0) :
    (N.trueSREdgeOfReactionVectorNe r hr s hs).endpoint =
      (N.trueSREdgeOfReactionVectorNe r hr t ht).endpoint ↔
      0 < N.reactionDirectionSign r s * N.reactionDirectionSign r t := by
  have hds : N.reactionDirectionSign r s ≠ 0 := by
    rw [show N.reactionDirectionSign r s = - N.reactionVector r s by
      simp [reactionDirectionSign, reactionVector_apply]]
    exact neg_ne_zero.mpr hs
  have hdt : N.reactionDirectionSign r t ≠ 0 := by
    rw [show N.reactionDirectionSign r t = - N.reactionVector r t by
      simp [reactionDirectionSign, reactionVector_apply]]
    exact neg_ne_zero.mpr ht
  have hst : (N.reaction r).source ≠ (N.reaction r).target := by
    intro h
    apply hs
    simp [reactionVector_apply, h]
  by_cases hsp : 0 < N.reactionDirectionSign r s
  · by_cases htp : 0 < N.reactionDirectionSign r t
    · simp [trueSREdgeOfReactionVectorNe, hsp, htp, mul_pos hsp htp]
    · have htn : N.reactionDirectionSign r t < 0 := lt_of_le_of_ne (not_lt.mp htp) hdt
      simp [trueSREdgeOfReactionVectorNe, hsp, htp, hst,
        not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hsp.le htn.le)]
  · have hsn : N.reactionDirectionSign r s < 0 := lt_of_le_of_ne (not_lt.mp hsp) hds
    by_cases htp : 0 < N.reactionDirectionSign r t
    · simp [trueSREdgeOfReactionVectorNe, hsp, htp, Ne.symm hst,
        not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hsn.le htp.le)]
    · have htn : N.reactionDirectionSign r t < 0 := lt_of_le_of_ne (not_lt.mp htp) hdt
      simp [trueSREdgeOfReactionVectorNe, hsp, htp, mul_pos_of_neg_of_neg hsn htn]

@[simp] theorem trueSREdge_endpoint_source_iff (N : Network S)
    (r : N.R) (hrint : ¬ N.IsFlowChannel r) (s : S)
    (hrs : N.reactionVector r s ≠ 0) :
    (N.trueSREdgeOfReactionVectorNe r hrint s hrs).endpoint = (N.reaction r).source ↔
      0 < N.reactionDirectionSign r s := by
  unfold trueSREdgeOfReactionVectorNe
  split_ifs with h
  · simp [h]
  · simp only
    constructor
    · intro heq
      have hst : (N.reaction r).source s = (N.reaction r).target s := (congrFun heq s).symm
      exfalso
      apply hrs
      simp [reactionVector_apply, hst]
    · exact fun hp => (h hp).elim


/-! ### Finite causal orbit

Choosing one same-sign internal contribution at each active species and one opposite-sign
species at each active reaction gives an alternating self-map.  Finiteness forces a periodic
active species; its minimal period is even and at least four.  This is the simple-cycle seed
needed before translating the causal orbit to labeled true-SR edges. -/

private abbrev ActiveSpecies (σ : S → ℝ) := {s : S // σ s ≠ 0}

/-- Active original reactions that are genuine internal true-chemistry channels. -/
abbrev ActiveTrueInternalReaction (N : Network S) (α : N.fullyOpen.R → ℝ) :=
  {r : N.R // α (Sum.inl r) ≠ 0 ∧ ¬ N.IsFlowChannel r}

/-- Choose a genuine internal reaction contributing with the same sign as an active species. -/
noncomputable def trueInternalCauseReaction (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) :
    N.ActiveTrueInternalReaction α := by
  let hex := N.exists_true_internal_term_same_sign hflow W s.2
  exact ⟨Classical.choose hex,
    ⟨by
      intro hz
      have hp := (Classical.choose_spec hex).2
      rw [hz, zero_mul, zero_mul] at hp
      linarith,
    (Classical.choose_spec hex).1⟩⟩

/-- The selected true-internal causal reaction has a strictly same-sign contribution. -/
theorem trueInternalCauseReaction_pos (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) :
    0 < (α (Sum.inl (N.trueInternalCauseReaction hflow W s).1) *
      N.reactionVector (N.trueInternalCauseReaction hflow W s).1 s.1) * σ s.1 := by
  unfold trueInternalCauseReaction
  simp only
  exact (Classical.choose_spec (N.exists_true_internal_term_same_sign hflow W s.2)).2

/-- Every reaction chosen as a causal cause carries a nonzero witness coefficient, so its
absolute value is a legitimate positive weight.  This is the `a` of the cyclic gain: the weights
in the Shinar--Feinberg source inequalities are the `|α R|`, and the causal selection guarantees
they are strictly positive along a causal cycle. -/
theorem abs_alpha_trueInternalCauseReaction_pos (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) :
    0 < |α (Sum.inl (N.trueInternalCauseReaction hflow W s).1)| := by
  have hp := N.trueInternalCauseReaction_pos hflow W s
  have hne : α (Sum.inl (N.trueInternalCauseReaction hflow W s).1) ≠ 0 := by
    intro hz
    rw [hz, zero_mul, zero_mul] at hp
    exact lt_irrefl 0 hp
  exact abs_pos.mpr hne

private abbrev ActiveReaction (N : Network S) (α : N.fullyOpen.R → ℝ) :=
  {r : N.R // α (Sum.inl r) ≠ 0}

private noncomputable def causeReaction (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) :
    ActiveReaction N α :=
  let hex := exists_internal_term_same_sign N W s.2
  ⟨Classical.choose hex, fun h => by
    have hp := Classical.choose_spec hex
    rw [h, zero_mul, zero_mul] at hp
    linarith⟩

private theorem causeReaction_pos (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) :
    0 < (α (Sum.inl (causeReaction N W s).1) *
      N.reactionVector (causeReaction N W s).1 s.1) * σ s.1 := by
  unfold causeReaction
  simp only
  exact Classical.choose_spec (exists_internal_term_same_sign N W s.2)

private noncomputable def oppositeSpecies (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (r : ActiveReaction N α) :
    ActiveSpecies σ :=
  let hex := exists_internal_opposite_species N W r.2
  ⟨Classical.choose hex, fun h => by
    have hn := Classical.choose_spec hex
    rw [h, mul_zero] at hn
    linarith⟩

private theorem oppositeSpecies_neg (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (r : ActiveReaction N α) :
    (α (Sum.inl r.1) * N.reactionVector r.1 (oppositeSpecies N W r).1) *
      σ (oppositeSpecies N W r).1 < 0 := by
  unfold oppositeSpecies
  simp only
  exact Classical.choose_spec (exists_internal_opposite_species N W r.2)


/-- Opposite-sign species selected from a genuine internal causal reaction. -/
noncomputable def trueInternalOppositeSpecies (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (r : N.ActiveTrueInternalReaction α) : ActiveSpecies σ :=
  N.oppositeSpecies W ⟨r.1, r.2.1⟩

/-- The selected opposite species has a strictly opposite-sign contribution. -/
theorem trueInternalOppositeSpecies_neg (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (r : N.ActiveTrueInternalReaction α) :
    (α (Sum.inl r.1) * N.reactionVector r.1 (N.trueInternalOppositeSpecies W r).1) *
      σ (N.trueInternalOppositeSpecies W r).1 < 0 := by
  exact N.oppositeSpecies_neg W ⟨r.1, r.2.1⟩

/-- Species-to-species causal step using only genuine internal true-chemistry reactions. -/
noncomputable def trueInternalCausalSpeciesStep (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) : ActiveSpecies σ → ActiveSpecies σ :=
  fun s => N.trueInternalOppositeSpecies W (N.trueInternalCauseReaction hflow W s)

/-- A true-internal causal species step never fixes an active species. -/
theorem trueInternalCausalSpeciesStep_ne (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) :
    N.trueInternalCausalSpeciesStep hflow W s ≠ s := by
  intro h
  have hp := N.trueInternalCauseReaction_pos hflow W s
  have hn := N.trueInternalOppositeSpecies_neg W (N.trueInternalCauseReaction hflow W s)
  have hv := congrArg Subtype.val h
  have hv' : (N.trueInternalOppositeSpecies W (N.trueInternalCauseReaction hflow W s) : S) = s := by
    simpa [trueInternalCausalSpeciesStep] using hv
  rw [hv'] at hn
  linarith

/-- An edge of the full internal sign-causality graph: an internal reaction contributes with
the sign of `s` and with the opposite sign at `t`. Keeping all such edges is essential when
choosing a source component; a source of one arbitrary choice function need not be a source in
the full graph. -/
def TrueInternalCausalEdge (N : Network S) (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (s t : ActiveSpecies σ) : Prop :=
  ∃ r : N.ActiveTrueInternalReaction α,
    0 < (α (Sum.inl r.1) * N.reactionVector r.1 s.1) * σ s.1 ∧
    (α (Sum.inl r.1) * N.reactionVector r.1 t.1) * σ t.1 < 0

/-- Vertices of the bipartite sign-causality graph for a witness: active species and active
internal reactions. -/
abbrev TrueInternalSignCausalVertex (N : Network S)
    (α : N.fullyOpen.R → ℝ) (σ : S → ℝ) :=
  ActiveSpecies σ ⊕ N.ActiveTrueInternalReaction α

/-- The directed bipartite sign-causality graph. An edge from a species to a reaction records
a negative signed flux term; an edge from a reaction to a species records a positive one. -/
def TrueInternalSignCausalEdge (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (u v : N.TrueInternalSignCausalVertex α σ) : Prop :=
  match u, v with
  | Sum.inl s, Sum.inr r =>
      (α (Sum.inl r.1) * N.reactionVector r.1 s.1) * σ s.1 < 0
  | Sum.inr r, Sum.inl s =>
      0 < (α (Sum.inl r.1) * N.reactionVector r.1 s.1) * σ s.1
  | Sum.inl _, Sum.inl _ => False
  | Sum.inr _, Sum.inr _ => False

/-- The true-reaction class of an active internal channel, retaining the proof that the class is
internal. -/
noncomputable def trueInternalReactionClass (N : Network S)
    {α : N.fullyOpen.R → ℝ}
    (r : N.ActiveTrueInternalReaction α) : N.InternalTrueReaction :=
  ⟨N.trueReaction r.1, r.2.2⟩

/-- Internal true-reaction classes represented by at least one active original channel. -/
abbrev ActiveTrueInternalReactionClass (N : Network S)
    (α : N.fullyOpen.R → ℝ) :=
  {ρ : N.InternalTrueReaction //
    ∃ r : N.ActiveTrueInternalReaction α, N.trueInternalReactionClass r = ρ}

/-- Vertices of the quotient sign-causality graph: active species and active true-reaction
classes. -/
abbrev TrueInternalQuotientVertex (N : Network S)
    (α : N.fullyOpen.R → ℝ) (σ : S → ℝ) :=
  ActiveSpecies σ ⊕ N.ActiveTrueInternalReactionClass α

/-- Collapsing parallel and reverse channels into one reaction vertex retains an edge whenever
some active representative supplies the corresponding signed-flux term. -/
def TrueInternalQuotientCausalEdge (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (u v : N.TrueInternalQuotientVertex α σ) : Prop :=
  match u, v with
  | Sum.inl s, Sum.inr ρ =>
      ∃ r : N.ActiveTrueInternalReaction α,
        N.trueInternalReactionClass r = ρ.1 ∧
        (α (Sum.inl r.1) * N.reactionVector r.1 s.1) * σ s.1 < 0
  | Sum.inr ρ, Sum.inl s =>
      ∃ r : N.ActiveTrueInternalReaction α,
        N.trueInternalReactionClass r = ρ.1 ∧
        0 < (α (Sum.inl r.1) * N.reactionVector r.1 s.1) * σ s.1
  | Sum.inl _, Sum.inl _ => False
  | Sum.inr _, Sum.inr _ => False

/-- Map one active channel reaction vertex into its quotient true-reaction class. -/
noncomputable def activeTrueInternalReactionClassVertex (N : Network S)
    {α : N.fullyOpen.R → ℝ}
    (r : N.ActiveTrueInternalReaction α) : N.ActiveTrueInternalReactionClass α :=
  ⟨N.trueInternalReactionClass r, ⟨r, rfl⟩⟩

/-- Lift a quotient source back to the original-channel sign-causality graph. -/
noncomputable def liftTrueInternalQuotientSource (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalQuotientVertex α σ)) :
    Finset (N.TrueInternalSignCausalVertex α σ) := by
  classical
  exact Finset.univ.filter (fun v =>
    match v with
    | Sum.inl s => Sum.inl s ∈ T
    | Sum.inr r => Sum.inr (N.activeTrueInternalReactionClassVertex r) ∈ T)

@[simp] theorem mem_liftTrueInternalQuotientSource_species (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalQuotientVertex α σ)) (s : ActiveSpecies σ) :
    Sum.inl s ∈ N.liftTrueInternalQuotientSource T ↔ Sum.inl s ∈ T := by
  simp [liftTrueInternalQuotientSource]

@[simp] theorem mem_liftTrueInternalQuotientSource_reaction (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalQuotientVertex α σ))
    (r : N.ActiveTrueInternalReaction α) :
    Sum.inr r ∈ N.liftTrueInternalQuotientSource T ↔
      Sum.inr (N.activeTrueInternalReactionClassVertex r) ∈ T := by
  simp [liftTrueInternalQuotientSource]

/-- The chosen causal species step is one edge in the full sign-causality graph. -/
theorem trueInternalCausalEdge_step (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) :
    N.TrueInternalCausalEdge hflow W s (N.trueInternalCausalSpeciesStep hflow W s) := by
  exact ⟨N.trueInternalCauseReaction hflow W s,
    N.trueInternalCauseReaction_pos hflow W s,
    N.trueInternalOppositeSpecies_neg W (N.trueInternalCauseReaction hflow W s)⟩

private theorem signProduct_causal_iff {a b c x y : ℝ}
    (hp : 0 < (a*b)*x) (hn : (a*c)*y < 0) :
    (0 < b*c ↔ x*y < 0) := by
  have hp' : 0 < a * (b*x) := by simpa [mul_assoc] using hp
  have hn' : a * (c*y) < 0 := by simpa [mul_assoc] using hn
  have hh : (a * (b*x)) * (a * (c*y)) < 0 := mul_neg_of_pos_of_neg hp' hn'
  have ha2 : 0 ≤ a^2 := sq_nonneg a
  have hq : (b*c) * (x*y) < 0 := by nlinarith [hh]
  rcases mul_neg_iff.mp hq with h | h
  · exact ⟨fun _ => h.2, fun _ => h.1⟩
  · constructor <;> intro hz <;> linarith [h.1, h.2]

/-- Left labeled true-SR edge of one genuine internal causal step. -/
noncomputable def trueInternalCausalLeftEdge (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) : N.TrueSREdge := by
  let r := N.trueInternalCauseReaction hflow W s
  apply N.trueSREdgeOfReactionVectorNe r.1 r.2.2 s.1
  intro hz
  have hp := N.trueInternalCauseReaction_pos hflow W s
  rw [hz, mul_zero, zero_mul] at hp
  exact lt_irrefl 0 hp

/-- Right labeled true-SR edge of one genuine internal causal step. -/
noncomputable def trueInternalCausalRightEdge (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) : N.TrueSREdge := by
  let r := N.trueInternalCauseReaction hflow W s
  let t := N.trueInternalOppositeSpecies W r
  apply N.trueSREdgeOfReactionVectorNe r.1 r.2.2 t.1
  intro hz
  have hn := N.trueInternalOppositeSpecies_neg W r
  rw [hz, mul_zero, zero_mul] at hn
  exact lt_irrefl 0 hn

@[simp] theorem trueInternalCausalLeftEdge_species (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) :
    (N.trueInternalCausalLeftEdge hflow W s).species = s.1 := by
  unfold trueInternalCausalLeftEdge
  simp

@[simp] theorem trueInternalCausalRightEdge_species (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) :
    (N.trueInternalCausalRightEdge hflow W s).species =
      (N.trueInternalCausalSpeciesStep hflow W s).1 := by
  unfold trueInternalCausalRightEdge trueInternalCausalSpeciesStep
  simp

@[simp] theorem trueInternalCausalEdges_reaction (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) :
    (N.trueInternalCausalLeftEdge hflow W s).reaction =
      (N.trueInternalCausalRightEdge hflow W s).reaction := by
  unfold trueInternalCausalLeftEdge trueInternalCausalRightEdge
  simp

theorem trueInternalCausalEdges_cPair_iff_signChange (N : Network S) (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : {s : S // σ s ≠ 0}) :
    (N.trueInternalCausalLeftEdge hflow W s).CPair
      (N.trueInternalCausalRightEdge hflow W s) ↔
      σ s.1 * σ (N.trueInternalCausalSpeciesStep hflow W s).1 < 0 := by
  let r := N.trueInternalCauseReaction hflow W s
  let t := N.trueInternalOppositeSpecies W r
  have hrs : N.reactionVector r.1 s.1 ≠ 0 := by
    intro hz
    have hp := N.trueInternalCauseReaction_pos hflow W s
    rw [hz, mul_zero, zero_mul] at hp
    exact lt_irrefl 0 hp
  have hrt : N.reactionVector r.1 t.1 ≠ 0 := by
    intro hz
    have hn := N.trueInternalOppositeSpecies_neg W r
    rw [hz, mul_zero, zero_mul] at hn
    exact lt_irrefl 0 hn
  have hp := N.trueInternalCauseReaction_pos hflow W s
  have hn := N.trueInternalOppositeSpecies_neg W r
  have hsign := signProduct_causal_iff hp hn
  have hdir : N.reactionDirectionSign r.1 s.1 * N.reactionDirectionSign r.1 t.1 =
      N.reactionVector r.1 s.1 * N.reactionVector r.1 t.1 := by
    simp [reactionDirectionSign, reactionVector_apply]
    ring
  unfold TrueSREdge.CPair
  rw [and_iff_right (N.trueInternalCausalEdges_reaction hflow W s)]
  unfold trueInternalCausalLeftEdge trueInternalCausalRightEdge
  rw [N.trueSREdge_sameEndpoint_iff_direction_mul_pos r.1 r.2.2 s.1 t.1 hrs hrt]
  rw [hdir]
  simpa [r, t, trueInternalCausalSpeciesStep] using hsign

private theorem opposite_cause_ne (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) :
    oppositeSpecies N W (causeReaction N W s) ≠ s := by
  intro h
  have hp := causeReaction_pos N W s
  have hn := oppositeSpecies_neg N W (causeReaction N W s)
  have hv := congrArg Subtype.val h
  rw [hv] at hn
  linarith

private noncomputable def causalStep (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) :
    ActiveSpecies σ ⊕ ActiveReaction N α → ActiveSpecies σ ⊕ ActiveReaction N α
  | Sum.inl s => Sum.inr (causeReaction N W s)
  | Sum.inr r => Sum.inl (oppositeSpecies N W r)

@[simp] private theorem causalStep_species (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) :
    causalStep N W (Sum.inl s) = Sum.inr (causeReaction N W s) := rfl

@[simp] private theorem causalStep_reaction (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (r : ActiveReaction N α) :
    causalStep N W (Sum.inr r) = Sum.inl (oppositeSpecies N W r) := rfl

private theorem causalStep_sq_species_ne (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) :
    (causalStep N W)^[2] (Sum.inl s) ≠ Sum.inl s := by
  simp [Function.iterate_succ_apply, opposite_cause_ne N W s]

private theorem exists_periodic_point_finite {A : Type*} [Fintype A] [Nonempty A]
    (f : A → A) : ∃ x : A, x ∈ Function.periodicPts f := by
  classical
  let x0 : A := Classical.choice inferInstance
  obtain ⟨m, n, hmn, hne⟩ : ∃ m n : ℕ, f^[m] x0 = f^[n] x0 ∧ m ≠ n := by
    simpa [Function.Injective] using not_injective_infinite_finite (fun k : ℕ => f^[k] x0)
  rcases lt_or_gt_of_ne hne with hmnlt | hmnlt
  · let y := f^[m] x0
    have hper : Function.IsPeriodicPt f (n - m) y := by
      unfold Function.IsPeriodicPt Function.IsFixedPt y
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hmnlt.le]
      exact hmn.symm
    exact ⟨y, Function.mk_mem_periodicPts (Nat.sub_pos_of_lt hmnlt) hper⟩
  · let y := f^[n] x0
    have hper : Function.IsPeriodicPt f (m - n) y := by
      unfold Function.IsPeriodicPt Function.IsFixedPt y
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hmnlt.le]
      exact hmn
    exact ⟨y, Function.mk_mem_periodicPts (Nat.sub_pos_of_lt hmnlt) hper⟩


/-- The repaired causal graph has a periodic active-species orbit of length at least two.  The
remaining true-SR step is to quotient any repeated true-reaction vertex and extract a simple cycle. -/
theorem exists_periodic_trueInternalCausalSpecies (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) :
    ∃ s : ActiveSpecies σ,
      s ∈ Function.periodicPts (N.trueInternalCausalSpeciesStep hflow W) ∧
      2 ≤ Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s := by
  classical
  letI : Nonempty (ActiveSpecies σ) := by
    by_contra h
    have hall : ∀ s : S, σ s = 0 := by
      intro s
      by_contra hs
      exact h ⟨⟨s, hs⟩⟩
    apply W.sigma_ne
    funext s
    exact hall s
  obtain ⟨s, hsper⟩ := exists_periodic_point_finite (N.trueInternalCausalSpeciesStep hflow W)
  refine ⟨s, hsper, ?_⟩
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts hsper
  have hne1 : Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s ≠ 1 := by
    intro h1
    have hfix := Function.iterate_minimalPeriod
      (f := N.trueInternalCausalSpeciesStep hflow W) (x := s)
    rw [h1, Function.iterate_one] at hfix
    exact N.trueInternalCausalSpeciesStep_ne hflow W s hfix
  omega

private theorem activeSpecies_nonempty (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) : Nonempty (ActiveSpecies σ) := by
  by_contra h
  have hall : ∀ s : S, σ s = 0 := by
    intro s
    by_contra hs
    exact h ⟨⟨s, hs⟩⟩
  apply W.sigma_ne
  funext s
  exact hall s

/-- A finite nonempty source strongly connected component exists in the full bipartite
sign-causality graph. This preserves reaction vertices, which is necessary for the source-block
decomposition. -/
theorem exists_trueInternalSignCausalSource (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) :
    ∃ T : Finset (N.TrueInternalSignCausalVertex α σ), T.Nonempty ∧
      (∀ a ∈ T, ∀ b ∈ T,
        Relation.ReflTransGen (N.TrueInternalSignCausalEdge W) a b) ∧
      (∀ a b, N.TrueInternalSignCausalEdge W a b → b ∈ T → a ∈ T) := by
  classical
  letI : Nonempty (ActiveSpecies σ) := N.activeSpecies_nonempty W
  letI : Nonempty (N.TrueInternalSignCausalVertex α σ) :=
    ⟨Sum.inl (Classical.choice inferInstance)⟩
  exact CRNT.exists_finite_source (N.TrueInternalSignCausalEdge W)

/-- Original reaction channels whose active true-internal reaction vertex lies in a chosen
bipartite source. -/
noncomputable def trueInternalSignSourceReactions (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalSignCausalVertex α σ)) : Finset N.R := by
  classical
  exact Finset.univ.filter (fun r =>
    ∃ r' : N.ActiveTrueInternalReaction α, r'.1 = r ∧ Sum.inr r' ∈ T)

/-- At a species vertex of a sign-causality source, the strict flux inequality remains strict
when restricted to reaction vertices in that source. Positive terms outside the source would
be incoming graph edges, while flow-channel terms are nonpositive by strong concordance. -/
theorem internal_flux_mul_sigma_pos_on_trueInternalSignSourceReactions
    (N : Network S) (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalSignCausalVertex α σ))
    (hsource : ∀ a b, N.TrueInternalSignCausalEdge W a b → b ∈ T → a ∈ T)
    {s : ActiveSpecies σ} (hs : Sum.inl s ∈ T) :
    0 < ∑ r ∈ N.trueInternalSignSourceReactions (α := α) (σ := σ) T,
      (α (Sum.inl r) * N.reactionVector r s.1) * σ s.1 := by
  apply N.internal_flux_mul_sigma_pos_on_finset W s.2 _ ?_
  intro r hr
  have hrA : r ∉ N.trueInternalSignSourceReactions (α := α) (σ := σ) T :=
    (Finset.mem_sdiff.mp hr).2
  simp only [trueInternalSignSourceReactions, Finset.mem_filter,
    Finset.mem_univ, true_and] at hrA
  by_cases hrflow : N.IsFlowChannel r
  · exact original_flow_term_nonpos N hflow W hrflow s.1
  · by_cases hα : α (Sum.inl r) = 0
    · simp [hα]
    · let r' : N.ActiveTrueInternalReaction α := ⟨r, ⟨hα, hrflow⟩⟩
      by_contra hnot
      have hpos : 0 < (α (Sum.inl r) * N.reactionVector r s.1) * σ s.1 :=
        lt_of_not_ge hnot
      have hedge : N.TrueInternalSignCausalEdge W (Sum.inr r') (Sum.inl s) := by
        exact hpos
      have hin : Sum.inr r' ∈ T := hsource _ _ hedge hs
      exact hrA ⟨r', rfl, hin⟩

/-- Every nonempty sign-causality source contains both a species vertex and a reaction vertex.
The witness supplies a causal unit at either endpoint, and source closure keeps its neighboring
vertex inside the component. -/
theorem trueInternalSignSource_has_both_vertex_kinds (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalSignCausalVertex α σ))
    (hne : T.Nonempty)
    (hsource : ∀ a b, N.TrueInternalSignCausalEdge W a b → b ∈ T → a ∈ T) :
    (∃ s : ActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ r : N.ActiveTrueInternalReaction α, Sum.inr r ∈ T) := by
  classical
  obtain ⟨v, hv⟩ := hne
  rcases v with s | r
  · constructor
    · exact ⟨s, hv⟩
    · let r := N.trueInternalCauseReaction hflow W s
      have hp := N.trueInternalCauseReaction_pos hflow W s
      have hedge : N.TrueInternalSignCausalEdge W (Sum.inr r) (Sum.inl s) := hp
      exact ⟨r, hsource _ _ hedge hv⟩
  · constructor
    · let s := N.trueInternalOppositeSpecies W r
      have hn := N.trueInternalOppositeSpecies_neg W r
      have hedge : N.TrueInternalSignCausalEdge W (Sum.inl s) (Sum.inr r) := hn
      exact ⟨s, hsource _ _ hedge hv⟩
    · exact ⟨r, hv⟩

/-- Package the finite sign-causality source together with its nonempty species and reaction
parts and the strict localized source inequalities. -/
theorem exists_trueInternalSignCausalSource_data (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) :
    ∃ T : Finset (N.TrueInternalSignCausalVertex α σ),
      T.Nonempty ∧
      (∃ s : ActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ r : N.ActiveTrueInternalReaction α, Sum.inr r ∈ T) ∧
      (∀ a ∈ T, ∀ b ∈ T,
        Relation.ReflTransGen (N.TrueInternalSignCausalEdge W) a b) ∧
      (∀ a b, N.TrueInternalSignCausalEdge W a b → b ∈ T → a ∈ T) ∧
      (∀ s : ActiveSpecies σ, Sum.inl s ∈ T →
        0 < ∑ r ∈ N.trueInternalSignSourceReactions (α := α) (σ := σ) T,
          (α (Sum.inl r) * N.reactionVector r s.1) * σ s.1) := by
  obtain ⟨T, hne, hscc, hsource⟩ := N.exists_trueInternalSignCausalSource W
  have hparts := N.trueInternalSignSource_has_both_vertex_kinds
    hflow W T hne hsource
  refine ⟨T, hne, hparts.1, hparts.2, hscc, hsource, ?_⟩
  intro s hs
  exact N.internal_flux_mul_sigma_pos_on_trueInternalSignSourceReactions
    hflow W T hsource hs

/-- A finite source can be formed after quotienting parallel and reverse channels into their
true-reaction classes. Lifting that source to every active representative preserves predecessor
closure, so the already-established strict source inequalities remain available. -/
theorem exists_trueInternalQuotientSignCausalSource_data (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) :
    ∃ T : Finset (N.TrueInternalQuotientVertex α σ),
      T.Nonempty ∧
      (∀ a ∈ T, ∀ b ∈ T,
        Relation.ReflTransGen (N.TrueInternalQuotientCausalEdge W) a b) ∧
      (∀ a b, N.TrueInternalQuotientCausalEdge W a b → b ∈ T → a ∈ T) ∧
      (∃ s : ActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ r : N.ActiveTrueInternalReactionClass α, Sum.inr r ∈ T) ∧
      (∀ s : ActiveSpecies σ, Sum.inl s ∈ T →
        0 < ∑ r ∈ N.trueInternalSignSourceReactions
            (α := α) (σ := σ) (N.liftTrueInternalQuotientSource T),
          (α (Sum.inl r) * N.reactionVector r s.1) * σ s.1) := by
  classical
  letI : Nonempty (ActiveSpecies σ) := N.activeSpecies_nonempty W
  letI : Nonempty (N.TrueInternalQuotientVertex α σ) :=
    ⟨Sum.inl (Classical.choice inferInstance)⟩
  obtain ⟨T, hne, hscc, hsource⟩ :=
    CRNT.exists_finite_source (N.TrueInternalQuotientCausalEdge W)
  let U := N.liftTrueInternalQuotientSource T
  have hUne : U.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    cases v with
    | inl s => exact ⟨Sum.inl s, (N.mem_liftTrueInternalQuotientSource_species T s).2 hv⟩
    | inr q =>
        obtain ⟨r, hr⟩ := q.2
        have hq : N.activeTrueInternalReactionClassVertex r = q := Subtype.ext hr
        exact ⟨Sum.inr r, (N.mem_liftTrueInternalQuotientSource_reaction T r).2
          (by simpa [hq] using hv)⟩
  have hUsource : ∀ a b, N.TrueInternalSignCausalEdge W a b → b ∈ U → a ∈ U := by
    intro a b hab hb
    cases a with
    | inl s =>
        cases b with
        | inl t => simp [TrueInternalSignCausalEdge] at hab
        | inr r =>
            have htarget : Sum.inr (N.activeTrueInternalReactionClassVertex r) ∈ T :=
              (N.mem_liftTrueInternalQuotientSource_reaction T r).1 hb
            have hqedge : N.TrueInternalQuotientCausalEdge W (Sum.inl s)
                (Sum.inr (N.activeTrueInternalReactionClassVertex r)) := by
              exact ⟨r, rfl, hab⟩
            have hsT := hsource _ _ hqedge htarget
            exact (N.mem_liftTrueInternalQuotientSource_species T s).2 hsT
    | inr r =>
        cases b with
        | inl s =>
            have htarget : Sum.inl s ∈ T :=
              (N.mem_liftTrueInternalQuotientSource_species T s).1 hb
            have hqedge : N.TrueInternalQuotientCausalEdge W
                (Sum.inr (N.activeTrueInternalReactionClassVertex r)) (Sum.inl s) := by
              exact ⟨r, rfl, hab⟩
            have hrT := hsource _ _ hqedge htarget
            exact (N.mem_liftTrueInternalQuotientSource_reaction T r).2 hrT
        | inr q => simp [TrueInternalSignCausalEdge] at hab
  have hparts := N.trueInternalSignSource_has_both_vertex_kinds hflow W U hUne hUsource
  have hspecies : ∃ s : ActiveSpecies σ, Sum.inl s ∈ T := by
    obtain ⟨s, hs⟩ := hparts.1
    exact ⟨s, (N.mem_liftTrueInternalQuotientSource_species T s).1 hs⟩
  have hreaction : ∃ r : N.ActiveTrueInternalReactionClass α, Sum.inr r ∈ T := by
    obtain ⟨r, hr⟩ := hparts.2
    exact ⟨N.activeTrueInternalReactionClassVertex r,
      (N.mem_liftTrueInternalQuotientSource_reaction T r).1 hr⟩
  refine ⟨T, hne, hscc, hsource, hspecies, hreaction, ?_⟩
  intro s hs
  exact N.internal_flux_mul_sigma_pos_on_trueInternalSignSourceReactions
    hflow W U hUsource ((N.mem_liftTrueInternalQuotientSource_species T s).2 hs)

private theorem exists_first_step_of_reflTransGen {V : Type*} {E : V → V → Prop}
    {a b : V} (h : Relation.ReflTransGen E a b) (hne : a ≠ b) :
    ∃ c, E a c ∧ Relation.ReflTransGen E c b := by
  rcases Relation.ReflTransGen.cases_head h with hab | ⟨c, hac, hcb⟩
  · exact (hne hab).elim
  · exact ⟨c, hac, hcb⟩

private theorem trueInternalQuotientCausalEdge_irrefl (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (v : N.TrueInternalQuotientVertex α σ) :
    ¬ N.TrueInternalQuotientCausalEdge W v v := by
  cases v <;> exact id

private def trueInternalQuotientVertexIsSpecies (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} :
    N.TrueInternalQuotientVertex α σ → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

private theorem trueInternalQuotientCausalEdge_flips_kind (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    {a b : N.TrueInternalQuotientVertex α σ}
    (h : N.TrueInternalQuotientCausalEdge W a b) :
    N.trueInternalQuotientVertexIsSpecies b = !N.trueInternalQuotientVertexIsSpecies a := by
  cases a <;> cases b <;> simp_all [TrueInternalQuotientCausalEdge,
    trueInternalQuotientVertexIsSpecies]

private theorem exists_trueInternalQuotientSource_successor (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalQuotientVertex α σ))
    (hscc : ∀ a ∈ T, ∀ b ∈ T,
      Relation.ReflTransGen (N.TrueInternalQuotientCausalEdge W) a b)
    (hsource : ∀ a b, N.TrueInternalQuotientCausalEdge W a b → b ∈ T → a ∈ T)
    (hparts : (∃ s : ActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ r : N.ActiveTrueInternalReactionClass α, Sum.inr r ∈ T))
    (v : N.TrueInternalQuotientVertex α σ) (hv : v ∈ T) :
    ∃ w, w ∈ T ∧ N.TrueInternalQuotientCausalEdge W v w := by
  let target : N.TrueInternalQuotientVertex α σ :=
    match v with
    | Sum.inl _ => Sum.inr hparts.2.choose
    | Sum.inr _ => Sum.inl hparts.1.choose
  have htarget : target ∈ T := by
    cases v with
    | inl s => exact hparts.2.choose_spec
    | inr r => exact hparts.1.choose_spec
  have hvne : v ≠ target := by cases v <;> simp [target]
  obtain ⟨w, hvw, hwt⟩ := exists_first_step_of_reflTransGen
    (hscc v hv target htarget) hvne
  exact ⟨w, CRNT.source_closed_under_predecessors hsource hwt htarget, hvw⟩

private noncomputable def trueInternalQuotientSourceStep (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalQuotientVertex α σ))
    (hscc : ∀ a ∈ T, ∀ b ∈ T,
      Relation.ReflTransGen (N.TrueInternalQuotientCausalEdge W) a b)
    (hsource : ∀ a b, N.TrueInternalQuotientCausalEdge W a b → b ∈ T → a ∈ T)
    (hparts : (∃ s : ActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ r : N.ActiveTrueInternalReactionClass α, Sum.inr r ∈ T)) :
    {v : N.TrueInternalQuotientVertex α σ // v ∈ T} →
      {v : N.TrueInternalQuotientVertex α σ // v ∈ T} := by
  classical
  intro v
  let hout := N.exists_trueInternalQuotientSource_successor
    W T hscc hsource hparts v.1 v.2
  exact ⟨Classical.choose hout, (Classical.choose_spec hout).1⟩

private theorem trueInternalQuotientSourceStep_edge (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalQuotientVertex α σ))
    (hscc : ∀ a ∈ T, ∀ b ∈ T,
      Relation.ReflTransGen (N.TrueInternalQuotientCausalEdge W) a b)
    (hsource : ∀ a b, N.TrueInternalQuotientCausalEdge W a b → b ∈ T → a ∈ T)
    (hparts : (∃ s : ActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ r : N.ActiveTrueInternalReactionClass α, Sum.inr r ∈ T))
    (v : {v : N.TrueInternalQuotientVertex α σ // v ∈ T}) :
    N.TrueInternalQuotientCausalEdge W v.1
      (N.trueInternalQuotientSourceStep W T hscc hsource hparts v).1 := by
  exact (Classical.choose_spec
    (N.exists_trueInternalQuotientSource_successor W T hscc hsource hparts v.1 v.2)).2

/-- The quotient source has a simple directed cycle, so no true-reaction class repeats along
that cycle. This addresses the channel-versus-class distinction before applying SR-cycle facts. -/
theorem exists_simple_directed_cycle_in_trueInternalQuotientSource (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalQuotientVertex α σ))
    (hscc : ∀ a ∈ T, ∀ b ∈ T,
      Relation.ReflTransGen (N.TrueInternalQuotientCausalEdge W) a b)
    (hsource : ∀ a b, N.TrueInternalQuotientCausalEdge W a b → b ∈ T → a ∈ T)
    (hparts : (∃ s : ActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ r : N.ActiveTrueInternalReactionClass α, Sum.inr r ∈ T)) :
    ∃ p : ℕ, 2 ≤ p ∧ Even p ∧
      ∃ c : Fin p → N.TrueInternalQuotientVertex α σ,
        Function.Injective c ∧ (∀ i, c i ∈ T) ∧
        (∀ i, N.TrueInternalQuotientCausalEdge W (c i) (c (finRotate p i))) := by
  classical
  let f := N.trueInternalQuotientSourceStep W T hscc hsource hparts
  letI : Nonempty {v : N.TrueInternalQuotientVertex α σ // v ∈ T} :=
    ⟨⟨Sum.inl hparts.1.choose, hparts.1.choose_spec⟩⟩
  obtain ⟨x, hxper⟩ := exists_periodic_point_finite f
  let p := Function.minimalPeriod f x
  have hp : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts hxper
  have hkind : ∀ k : ℕ,
      N.trueInternalQuotientVertexIsSpecies (f^[k] x).1 =
        if k % 2 = 0 then N.trueInternalQuotientVertexIsSpecies x.1
        else !N.trueInternalQuotientVertexIsSpecies x.1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hflip := N.trueInternalQuotientCausalEdge_flips_kind W
          (N.trueInternalQuotientSourceStep_edge W T hscc hsource hparts (f^[k] x))
        change N.trueInternalQuotientVertexIsSpecies (f (f^[k] x)).1 =
          !N.trueInternalQuotientVertexIsSpecies (f^[k] x).1 at hflip
        rw [Function.iterate_succ_apply']
        by_cases heven : k % 2 = 0
        · have hnext : (k + 1) % 2 = 1 := by omega
          simp [heven, hnext, ih, hflip]
        · have hnext : (k + 1) % 2 = 0 := by omega
          simp [heven, hnext, ih, hflip]
  have hperiodfix : f^[p] x = x := by simpa [p] using
    (Function.iterate_minimalPeriod (f := f) (x := x))
  have htagfix : N.trueInternalQuotientVertexIsSpecies (f^[p] x).1 =
      N.trueInternalQuotientVertexIsSpecies x.1 := congrArg
        (fun z : {v : N.TrueInternalQuotientVertex α σ // v ∈ T} =>
          N.trueInternalQuotientVertexIsSpecies z.1) hperiodfix
  have hpeven : Even p := by
    by_contra hnot
    have hmod : p % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hnot)
    have hbad : N.trueInternalQuotientVertexIsSpecies x.1 =
        !N.trueInternalQuotientVertexIsSpecies x.1 := by
      calc
        N.trueInternalQuotientVertexIsSpecies x.1 =
            N.trueInternalQuotientVertexIsSpecies (f^[p] x).1 := htagfix.symm
        _ = !N.trueInternalQuotientVertexIsSpecies x.1 := by
          rw [hkind p]
          simp [hmod]
    cases htag : N.trueInternalQuotientVertexIsSpecies x.1 <;> simp [htag] at hbad
  have hpne : p ≠ 1 := by
    intro hp1
    have hfix := Function.iterate_minimalPeriod (f := f) (x := x)
    have hp1' : Function.minimalPeriod f x = 1 := by simpa [p] using hp1
    rw [hp1', Function.iterate_one] at hfix
    have hstep := N.trueInternalQuotientSourceStep_edge W T hscc hsource hparts x
    change N.TrueInternalQuotientCausalEdge W x.1 (f x).1 at hstep
    exact N.trueInternalQuotientCausalEdge_irrefl W x.1
      (by simpa [hfix] using hstep)
  have hp2 : 2 ≤ p := by omega
  refine ⟨p, hp2, hpeven, fun i => (f^[i.1] x).1, ?_, ?_, ?_⟩
  · intro i j hij
    have hsub : (f^[i.1] x) = (f^[j.1] x) := Subtype.ext hij
    have hij' := Function.iterate_eq_iterate_iff_of_lt_minimalPeriod i.2 j.2
    exact Fin.ext (hij'.mp hsub)
  · intro i
    exact (f^[i.1] x).2
  · intro i
    letI : NeZero p := ⟨by omega⟩
    have hrot : (finRotate p i).1 = (i.1 + 1) % p := by
      rw [finRotate_apply]
      simp [Fin.add_def]
    have hed := N.trueInternalQuotientSourceStep_edge W T hscc hsource hparts
      (f^[i.1] x)
    change N.TrueInternalQuotientCausalEdge W (f^[i.1] x).1
      (f (f^[i.1] x)).1 at hed
    have hnext : f (f^[i.1] x) = f^[((i.1 + 1) % p)] x := by
      calc
        f (f^[i.1] x) = f^[i.1 + 1] x := by
          simpa [Nat.succ_eq_add_one] using
            (Function.iterate_succ_apply' f i.1 x).symm
        _ = f^[((i.1 + 1) % p)] x := by
          symm
          dsimp [p]
          exact Function.iterate_mod_minimalPeriod_eq
    change N.TrueInternalQuotientCausalEdge W (f^[i.1] x).1
      (f^[((finRotate p i).1)] x).1
    rw [hrot]
    rw [← congrArg Subtype.val hnext]
    exact hed

/-- A selected positive reaction term at a source species places its reaction vertex in the
same source component. -/
theorem trueInternalCauseReaction_mem_signSource (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalSignCausalVertex α σ))
    (hsource : ∀ a b, N.TrueInternalSignCausalEdge W a b → b ∈ T → a ∈ T)
    (s : ActiveSpecies σ) (hs : Sum.inl s ∈ T) :
    Sum.inr (N.trueInternalCauseReaction hflow W s) ∈ T := by
  apply hsource _ _ _ hs
  exact N.trueInternalCauseReaction_pos hflow W s

/-- The selected causal species step stays inside a sign-causality source. -/
theorem trueInternalCausalStep_mem_signSource (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalSignCausalVertex α σ))
    (hsource : ∀ a b, N.TrueInternalSignCausalEdge W a b → b ∈ T → a ∈ T)
    (s : ActiveSpecies σ) (hs : Sum.inl s ∈ T) :
    Sum.inl (N.trueInternalCausalSpeciesStep hflow W s) ∈ T := by
  let r := N.trueInternalCauseReaction hflow W s
  have hr : Sum.inr r ∈ T := by
    simpa [r] using N.trueInternalCauseReaction_mem_signSource hflow W T hsource s hs
  have hedge : N.TrueInternalSignCausalEdge W
      (Sum.inl (N.trueInternalCausalSpeciesStep hflow W s)) (Sum.inr r) := by
    change (α (Sum.inl r.1) * N.reactionVector r.1
      (N.trueInternalOppositeSpecies W r).1) * σ (N.trueInternalOppositeSpecies W r).1 < 0
    exact N.trueInternalOppositeSpecies_neg W r
  exact hsource _ _ hedge hr

private noncomputable def trueInternalSignSourceSpeciesStep (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalSignCausalVertex α σ))
    (hsource : ∀ a b, N.TrueInternalSignCausalEdge W a b → b ∈ T → a ∈ T) :
    {s : ActiveSpecies σ // Sum.inl s ∈ T} → {s : ActiveSpecies σ // Sum.inl s ∈ T} :=
  fun s => ⟨N.trueInternalCausalSpeciesStep hflow W s.1,
    N.trueInternalCausalStep_mem_signSource hflow W T hsource s.1 s.2⟩

private theorem trueInternalSignCausalEdge_irrefl (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (v : N.TrueInternalSignCausalVertex α σ) :
    ¬ N.TrueInternalSignCausalEdge W v v := by
  cases v with
  | inl s => exact id
  | inr r => exact id

private def trueInternalSignVertexIsSpecies (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} :
    N.TrueInternalSignCausalVertex α σ → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

private theorem trueInternalSignCausalEdge_flips_kind (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    {a b : N.TrueInternalSignCausalVertex α σ}
    (h : N.TrueInternalSignCausalEdge W a b) :
    N.trueInternalSignVertexIsSpecies b = !N.trueInternalSignVertexIsSpecies a := by
  cases a <;> cases b <;> simp_all [TrueInternalSignCausalEdge,
    trueInternalSignVertexIsSpecies]

private theorem exists_trueInternalSignSource_successor (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalSignCausalVertex α σ))
    (hscc : ∀ a ∈ T, ∀ b ∈ T,
      Relation.ReflTransGen (N.TrueInternalSignCausalEdge W) a b)
    (hsource : ∀ a b, N.TrueInternalSignCausalEdge W a b → b ∈ T → a ∈ T)
    (hparts : (∃ s : ActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ r : N.ActiveTrueInternalReaction α, Sum.inr r ∈ T))
    (v : N.TrueInternalSignCausalVertex α σ) (hv : v ∈ T) :
    ∃ w, w ∈ T ∧ N.TrueInternalSignCausalEdge W v w := by
  let target : N.TrueInternalSignCausalVertex α σ :=
    match v with
    | Sum.inl _ => Sum.inr hparts.2.choose
    | Sum.inr _ => Sum.inl hparts.1.choose
  have htarget : target ∈ T := by
    cases v with
    | inl s => exact hparts.2.choose_spec
    | inr r => exact hparts.1.choose_spec
  have hvne : v ≠ target := by
    cases v <;> simp [target]
  obtain ⟨w, hvw, hwt⟩ := exists_first_step_of_reflTransGen
    (hscc v hv target htarget) hvne
  exact ⟨w, CRNT.source_closed_under_predecessors hsource hwt htarget, hvw⟩

private noncomputable def trueInternalSignSourceStep (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalSignCausalVertex α σ))
    (hscc : ∀ a ∈ T, ∀ b ∈ T,
      Relation.ReflTransGen (N.TrueInternalSignCausalEdge W) a b)
    (hsource : ∀ a b, N.TrueInternalSignCausalEdge W a b → b ∈ T → a ∈ T)
    (hparts : (∃ s : ActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ r : N.ActiveTrueInternalReaction α, Sum.inr r ∈ T)) :
    {v : N.TrueInternalSignCausalVertex α σ // v ∈ T} →
      {v : N.TrueInternalSignCausalVertex α σ // v ∈ T} := by
  classical
  intro v
  let hout := N.exists_trueInternalSignSource_successor W T hscc hsource hparts v.1 v.2
  exact ⟨Classical.choose hout, (Classical.choose_spec hout).1⟩

private theorem trueInternalSignSourceStep_edge (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalSignCausalVertex α σ))
    (hscc : ∀ a ∈ T, ∀ b ∈ T,
      Relation.ReflTransGen (N.TrueInternalSignCausalEdge W) a b)
    (hsource : ∀ a b, N.TrueInternalSignCausalEdge W a b → b ∈ T → a ∈ T)
    (hparts : (∃ s : ActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ r : N.ActiveTrueInternalReaction α, Sum.inr r ∈ T))
    (v : {v : N.TrueInternalSignCausalVertex α σ // v ∈ T}) :
    N.TrueInternalSignCausalEdge W v.1
      (N.trueInternalSignSourceStep W T hscc hsource hparts v).1 := by
  exact (Classical.choose_spec
    (N.exists_trueInternalSignSource_successor W T hscc hsource hparts v.1 v.2)).2

/-- Every finite bipartite sign-causality source contains a simple directed cycle.  This
cycle lives in the original-channel graph; quotienting parallel or reverse channels into true
reaction vertices remains a separate step. -/
theorem exists_simple_directed_cycle_in_trueInternalSignSource (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalSignCausalVertex α σ))
    (hscc : ∀ a ∈ T, ∀ b ∈ T,
      Relation.ReflTransGen (N.TrueInternalSignCausalEdge W) a b)
    (hsource : ∀ a b, N.TrueInternalSignCausalEdge W a b → b ∈ T → a ∈ T)
    (hparts : (∃ s : ActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ r : N.ActiveTrueInternalReaction α, Sum.inr r ∈ T)) :
    ∃ p : ℕ, 4 ≤ p ∧ Even p ∧
      ∃ c : Fin p → N.TrueInternalSignCausalVertex α σ,
        Function.Injective c ∧ (∀ i, c i ∈ T) ∧
        (∀ i, N.TrueInternalSignCausalEdge W (c i) (c (finRotate p i))) := by
  classical
  let f := N.trueInternalSignSourceStep W T hscc hsource hparts
  letI : Nonempty {v : N.TrueInternalSignCausalVertex α σ // v ∈ T} :=
    ⟨⟨Sum.inl hparts.1.choose, hparts.1.choose_spec⟩⟩
  obtain ⟨x, hxper⟩ := exists_periodic_point_finite f
  let p := Function.minimalPeriod f x
  have hp : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts hxper
  have hkind : ∀ k : ℕ,
      N.trueInternalSignVertexIsSpecies (f^[k] x).1 =
        if k % 2 = 0 then N.trueInternalSignVertexIsSpecies x.1
        else !N.trueInternalSignVertexIsSpecies x.1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hflip := N.trueInternalSignCausalEdge_flips_kind
          W (N.trueInternalSignSourceStep_edge W T hscc hsource hparts (f^[k] x))
        change N.trueInternalSignVertexIsSpecies (f (f^[k] x)).1 =
          !N.trueInternalSignVertexIsSpecies (f^[k] x).1 at hflip
        rw [Function.iterate_succ_apply']
        by_cases heven : k % 2 = 0
        · have hnext : (k + 1) % 2 = 1 := by omega
          simp [heven, hnext, ih, hflip]
        · have hnext : (k + 1) % 2 = 0 := by omega
          simp [heven, hnext, ih, hflip]
  have hperiodfix : f^[p] x = x := by simpa [p] using
    (Function.iterate_minimalPeriod (f := f) (x := x))
  have htagfix : N.trueInternalSignVertexIsSpecies (f^[p] x).1 =
      N.trueInternalSignVertexIsSpecies x.1 := congrArg
        (fun z : {v : N.TrueInternalSignCausalVertex α σ // v ∈ T} =>
          N.trueInternalSignVertexIsSpecies z.1) hperiodfix
  have hpeven : Even p := by
    by_contra hnot
    have hmod : p % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hnot)
    have hbad : N.trueInternalSignVertexIsSpecies x.1 =
        !N.trueInternalSignVertexIsSpecies x.1 := by
      calc
        N.trueInternalSignVertexIsSpecies x.1 =
            N.trueInternalSignVertexIsSpecies (f^[p] x).1 := htagfix.symm
        _ = !N.trueInternalSignVertexIsSpecies x.1 := by
          rw [hkind p]
          simp [hmod]
    cases htag : N.trueInternalSignVertexIsSpecies x.1 <;> simp [htag] at hbad
  have hpne : p ≠ 1 := by
    intro hp1
    have hfix := Function.iterate_minimalPeriod (f := f) (x := x)
    have hp1' : Function.minimalPeriod f x = 1 := by simpa [p] using hp1
    rw [hp1', Function.iterate_one] at hfix
    have hloop : f x = x := hfix
    have hstep := N.trueInternalSignSourceStep_edge W T hscc hsource hparts x
    change N.TrueInternalSignCausalEdge W x.1 (f x).1 at hstep
    exact N.trueInternalSignCausalEdge_irrefl W x.1
      (by simpa [hloop] using hstep)
  have hp2 : 2 ≤ p := by omega
  have hpne2 : p ≠ 2 := by
    intro hpEq
    have hclose : f (f x) = x := by
      simpa [hpEq, Function.iterate_succ_apply'] using hperiodfix
    have hedge0 := N.trueInternalSignSourceStep_edge W T hscc hsource hparts x
    change N.TrueInternalSignCausalEdge W x.1 (f x).1 at hedge0
    have hedge1 := N.trueInternalSignSourceStep_edge W T hscc hsource hparts (f x)
    change N.TrueInternalSignCausalEdge W (f x).1 (f (f x)).1 at hedge1
    rw [hclose] at hedge1
    cases hx : x.1 with
    | inl s =>
        cases hy : (f x).1 with
        | inl t => simp [TrueInternalSignCausalEdge, hx, hy] at hedge0
        | inr r =>
            have hneg :
                (α (Sum.inl r.1) * N.reactionVector r.1 s.1) * σ s.1 < 0 := by
              simpa [TrueInternalSignCausalEdge, hx, hy] using hedge0
            have hpos :
                0 < (α (Sum.inl r.1) * N.reactionVector r.1 s.1) * σ s.1 := by
              simpa [TrueInternalSignCausalEdge, hx, hy, hclose] using hedge1
            linarith
    | inr r =>
        cases hy : (f x).1 with
        | inl s =>
            have hpos :
                0 < (α (Sum.inl r.1) * N.reactionVector r.1 s.1) * σ s.1 := by
              simpa [TrueInternalSignCausalEdge, hx, hy] using hedge0
            have hneg :
                (α (Sum.inl r.1) * N.reactionVector r.1 s.1) * σ s.1 < 0 := by
              simpa [TrueInternalSignCausalEdge, hx, hy, hclose] using hedge1
            linarith
        | inr q => simp [TrueInternalSignCausalEdge, hx, hy] at hedge0
  have hpmod : p % 2 = 0 := Nat.even_iff.mp hpeven
  have hp4 : 4 ≤ p := by omega
  refine ⟨p, hp4, hpeven, fun i => (f^[i.1] x).1, ?_, ?_, ?_⟩
  · intro i j hij
    have hsub : (f^[i.1] x) = (f^[j.1] x) := Subtype.ext hij
    have hij' := Function.iterate_eq_iterate_iff_of_lt_minimalPeriod i.2 j.2
    exact Fin.ext (hij'.mp hsub)
  · intro i
    exact (f^[i.1] x).2
  · intro i
    letI : NeZero p := ⟨by omega⟩
    have hp1' : 1 < p := by omega
    have hrot : (finRotate p i).1 = (i.1 + 1) % p := by
      rw [finRotate_apply]
      simp [Fin.add_def]
    have hed := N.trueInternalSignSourceStep_edge W T hscc hsource hparts
      (f^[i.1] x)
    change N.TrueInternalSignCausalEdge W (f^[i.1] x).1
      (f (f^[i.1] x)).1 at hed
    have hnext : f (f^[i.1] x) = f^[((i.1 + 1) % p)] x := by
      calc
        f (f^[i.1] x) = f^[i.1 + 1] x := by
          simpa [Nat.succ_eq_add_one] using
            (Function.iterate_succ_apply' f i.1 x).symm
        _ = f^[((i.1 + 1) % p)] x := by
          symm
          dsimp [p]
          exact Function.iterate_mod_minimalPeriod_eq
    change N.TrueInternalSignCausalEdge W (f^[i.1] x).1
      (f^[((finRotate p i).1)] x).1
    rw [hrot]
    rw [← congrArg Subtype.val hnext]
    exact hed

/-- The source component contains a periodic orbit of the selected causal species step. -/
theorem exists_periodic_trueInternalCausalSpecies_in_signSource (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalSignCausalVertex α σ))
    (hsource : ∀ a b, N.TrueInternalSignCausalEdge W a b → b ∈ T → a ∈ T)
    (hspecies : ∃ s : ActiveSpecies σ, Sum.inl s ∈ T) :
    ∃ s : ActiveSpecies σ, Sum.inl s ∈ T ∧
      s ∈ Function.periodicPts (N.trueInternalCausalSpeciesStep hflow W) := by
  classical
  let f := N.trueInternalCausalSpeciesStep hflow W
  let g := N.trueInternalSignSourceSpeciesStep hflow W T hsource
  letI : Nonempty {s : ActiveSpecies σ // Sum.inl s ∈ T} :=
    ⟨⟨Classical.choose hspecies, Classical.choose_spec hspecies⟩⟩
  obtain ⟨x, hx⟩ := exists_periodic_point_finite g
  rcases hx with ⟨n, hn, hfixed⟩
  have hiter : ∀ k, (g^[k] x).1 = f^[k] x.1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        calc
          (g^[k + 1] x).1 = (g (g^[k] x)).1 := by rw [Function.iterate_succ_apply']
          _ = f ((g^[k] x).1) := rfl
          _ = f (f^[k] x.1) := by rw [ih]
          _ = f^[k + 1] x.1 := by rw [Function.iterate_succ_apply']
  have hper : Function.IsPeriodicPt f n x.1 := by
    change f^[n] x.1 = x.1
    calc
      f^[n] x.1 = (g^[n] x).1 := (hiter n).symm
      _ = x.1 := congrArg Subtype.val hfixed
  exact ⟨x.1, x.2, Function.mk_mem_periodicPts hn hper⟩

/-- A source-contained periodic causal orbit has at least two species, and every selected
reaction vertex on its least-period orbit also lies in the bipartite source. -/
theorem exists_periodic_trueInternalCausalOrbit_in_signSource (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalSignCausalVertex α σ))
    (hsource : ∀ a b, N.TrueInternalSignCausalEdge W a b → b ∈ T → a ∈ T)
    (hspecies : ∃ s : ActiveSpecies σ, Sum.inl s ∈ T) :
    ∃ s : ActiveSpecies σ,
      Sum.inl s ∈ T ∧
      s ∈ Function.periodicPts (N.trueInternalCausalSpeciesStep hflow W) ∧
      2 ≤ Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s ∧
      ∀ i : Fin (Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s),
        Sum.inr (N.trueInternalCauseReaction hflow W
          ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)) ∈ T := by
  obtain ⟨s, hs, hsper⟩ := N.exists_periodic_trueInternalCausalSpecies_in_signSource
    hflow W T hsource hspecies
  refine ⟨s, hs, hsper, ?_, ?_⟩
  · have hp := Function.minimalPeriod_pos_of_mem_periodicPts hsper
    have hne1 : Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s ≠ 1 := by
      intro h1
      have hfix := Function.iterate_minimalPeriod
        (f := N.trueInternalCausalSpeciesStep hflow W) (x := s)
      rw [h1, Function.iterate_one] at hfix
      exact N.trueInternalCausalSpeciesStep_ne hflow W s hfix
    omega
  · intro i
    have hiter_mem : ∀ k : ℕ,
        Sum.inl ((N.trueInternalCausalSpeciesStep hflow W)^[k] s) ∈ T := by
      intro k
      induction k with
      | zero => simpa using hs
      | succ k ih =>
          rw [Function.iterate_succ_apply']
          exact N.trueInternalCausalStep_mem_signSource hflow W T hsource
            _ ih
    exact N.trueInternalCauseReaction_mem_signSource hflow W T hsource
      ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s) (hiter_mem i.1)

private theorem exists_periodic_active_species (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) :
    ∃ s : ActiveSpecies σ, Sum.inl s ∈ Function.periodicPts (causalStep N W) := by
  classical
  letI : Nonempty (ActiveSpecies σ) := activeSpecies_nonempty N W
  letI : Nonempty (ActiveSpecies σ ⊕ ActiveReaction N α) := ⟨Sum.inl (Classical.choice inferInstance)⟩
  obtain ⟨z, hz⟩ := exists_periodic_point_finite (causalStep N W)
  rcases z with s | r
  · exact ⟨s, hz⟩
  · rcases hz with ⟨n, hn, hper⟩
    refine ⟨oppositeSpecies N W r, Function.mk_mem_periodicPts hn ?_⟩
    exact hper.apply
private noncomputable def causalSpeciesStep (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) : ActiveSpecies σ → ActiveSpecies σ :=
  fun s => oppositeSpecies N W (causeReaction N W s)

private theorem causalStep_even_iterate (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) (k : ℕ) :
    (causalStep N W)^[2 * k] (Sum.inl s) =
      Sum.inl ((causalSpeciesStep N W)^[k] s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 + 2 * k by omega, Function.iterate_add_apply, ih]
      simp [Function.iterate_succ_apply', causalSpeciesStep]

private theorem causalStep_odd_iterate (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ) (k : ℕ) :
    (causalStep N W)^[2 * k + 1] (Sum.inl s) =
      Sum.inr (causeReaction N W ((causalSpeciesStep N W)^[k] s)) := by
  rw [show 2 * k + 1 = 1 + 2 * k by omega, Function.iterate_add_apply,
    causalStep_even_iterate N W s k]
  rfl

private theorem causal_period_even (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ)
    (hsper : Sum.inl s ∈ Function.periodicPts (causalStep N W)) :
    Even (Function.minimalPeriod (causalStep N W) (Sum.inl s)) := by
  rcases Nat.even_or_odd (Function.minimalPeriod (causalStep N W) (Sum.inl s)) with he | ho
  · exact he
  · rcases ho with ⟨k, hk⟩
    have hfix := Function.iterate_minimalPeriod (f := causalStep N W) (x := Sum.inl s)
    rw [hk, causalStep_odd_iterate N W s k] at hfix
    simp at hfix

private theorem four_le_causal_period (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (s : ActiveSpecies σ)
    (hsper : Sum.inl s ∈ Function.periodicPts (causalStep N W)) :
    4 ≤ Function.minimalPeriod (causalStep N W) (Sum.inl s) := by
  have hp : 0 < Function.minimalPeriod (causalStep N W) (Sum.inl s) :=
    Function.minimalPeriod_pos_of_mem_periodicPts hsper
  have he := causal_period_even N W s hsper
  have hne2 : Function.minimalPeriod (causalStep N W) (Sum.inl s) ≠ 2 := by
    intro h2
    have hfix := Function.iterate_minimalPeriod (f := causalStep N W) (x := Sum.inl s)
    rw [h2] at hfix
    exact causalStep_sq_species_ne N W s hfix
  rw [Nat.even_iff] at he
  omega


private theorem prod_pm_one_eq_neg_one_pow_card_neg
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hpm : ∀ i ∈ s, f i = 1 ∨ f i = -1) :
    ∏ i ∈ s, f i = (-1 : ℝ) ^ (s.filter (fun i => f i = -1)).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hfa := hpm a (by simp)
      have hs : ∀ i ∈ s, f i = 1 ∨ f i = -1 := fun i hi => hpm i (by simp [hi])
      rw [ih hs]
      rcases hfa with h1 | hn
      · norm_num [Finset.filter_insert, h1]
      · simp [Finset.filter_insert, hn, ha, pow_succ, mul_comm]

private theorem even_card_neg_of_prod_one
    {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hpm : ∀ i, f i = 1 ∨ f i = -1)
    (hprod : ∏ i, f i = 1) :
    Even ((Finset.univ.filter (fun i => f i = -1)).card) := by
  classical
  have h := prod_pm_one_eq_neg_one_pow_card_neg Finset.univ f (by simpa using hpm)
  rw [hprod] at h
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp h.symm

private theorem cyclic_sign_changes_even {n : ℕ} [NeZero n] (a : Fin n → ℝ)
    (hne : ∀ i, a i ≠ 0) :
    Even ((Finset.univ.filter (fun i => a i * a (finRotate n i) < 0)).card) := by
  classical
  let g : Fin n → ℝ := fun i => if 0 < a i then 1 else -1
  let f : Fin n → ℝ := fun i => g i * g (finRotate n i)
  have hg : ∀ i, g i = 1 ∨ g i = -1 := by
    intro i
    simp only [g]
    split <;> simp
  have hf : ∀ i, f i = 1 ∨ f i = -1 := by
    intro i
    rcases hg i with hi | hi <;> rcases hg (finRotate n i) with hj | hj
    · left; change g i * g (finRotate n i) = 1; rw [hi, hj]; norm_num
    · right; change g i * g (finRotate n i) = -1; rw [hi, hj]; norm_num
    · right; change g i * g (finRotate n i) = -1; rw [hi, hj]; norm_num
    · left; change g i * g (finRotate n i) = 1; rw [hi, hj]; norm_num
  have hrot : (∏ i, g (finRotate n i)) = ∏ i, g i := Equiv.prod_comp _ _
  have hprodg : (∏ i, g i) = 1 ∨ (∏ i, g i) = -1 := by
    have hp := prod_pm_one_eq_neg_one_pow_card_neg Finset.univ g (by simpa using hg)
    rw [hp]
    rcases Nat.even_or_odd ((Finset.univ.filter (fun i => g i = -1)).card) with he | ho
    · left; simp [Even.neg_one_pow he]
    · right; simpa using Odd.neg_one_pow ho
  have hprod : ∏ i, f i = 1 := by
    rw [show (∏ i, f i) = (∏ i, g i) * (∏ i, g (finRotate n i)) by
      simp [f, Finset.prod_mul_distrib], hrot]
    rcases hprodg with h | h <;> rw [h] <;> norm_num
  have he := even_card_neg_of_prod_one f hf hprod
  have hfilter : (Finset.univ.filter (fun i => f i = -1)) =
      Finset.univ.filter (fun i => a i * a (finRotate n i) < 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hai := hne i
    have haj := hne (finRotate n i)
    rcases lt_or_gt_of_ne hai with hi | hi <;> rcases lt_or_gt_of_ne haj with hj | hj
    · have hgi : g i = -1 := if_neg (not_lt.mpr hi.le)
      have hgj : g (finRotate n i) = -1 := if_neg (not_lt.mpr hj.le)
      have hp : 0 < a i * a (finRotate n i) := mul_pos_of_neg_of_neg hi hj
      change (g i * g (finRotate n i) = -1 ↔ a i * a (finRotate n i) < 0)
      rw [hgi, hgj]
      norm_num
      exact (by simpa only [finRotate_apply] using hp.le)
    · have hgi : g i = -1 := if_neg (not_lt.mpr hi.le)
      have hgj : g (finRotate n i) = 1 := if_pos hj
      have hp : a i * a (finRotate n i) < 0 := mul_neg_of_neg_of_pos hi hj
      change (g i * g (finRotate n i) = -1 ↔ a i * a (finRotate n i) < 0)
      rw [hgi, hgj]
      norm_num
      exact (by simpa only [finRotate_apply] using hp)
    · have hgi : g i = 1 := if_pos hi
      have hgj : g (finRotate n i) = -1 := if_neg (not_lt.mpr hj.le)
      have hp : a i * a (finRotate n i) < 0 := mul_neg_of_pos_of_neg hi hj
      change (g i * g (finRotate n i) = -1 ↔ a i * a (finRotate n i) < 0)
      rw [hgi, hgj]
      norm_num
      exact (by simpa only [finRotate_apply] using hp)
    · have hgi : g i = 1 := if_pos hi
      have hgj : g (finRotate n i) = 1 := if_pos hj
      have hp : 0 < a i * a (finRotate n i) := mul_pos hi hj
      change (g i * g (finRotate n i) = -1 ↔ a i * a (finRotate n i) < 0)
      rw [hgi, hgj]
      norm_num
      exact (by simpa only [finRotate_apply] using hp.le)
  rwa [hfilter] at he

/-- The species on a minimal periodic orbit are pairwise distinct before the period closes. -/
theorem trueInternalPeriodicSpecies_injective (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (s : ActiveSpecies σ)
    (hsper : s ∈ Function.periodicPts (N.trueInternalCausalSpeciesStep hflow W)) :
    Function.Injective (fun i : Fin (Function.minimalPeriod
      (N.trueInternalCausalSpeciesStep hflow W) s) =>
        ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s).1) := by
  intro i j hij
  have hsub : ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s) =
      ((N.trueInternalCausalSpeciesStep hflow W)^[j.1] s) := by
    apply Subtype.ext
    exact hij
  have hi : i.1 < Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s := i.2
  have hj : j.1 < Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s := j.2
  have := Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj
  exact Fin.ext (this.mp hsub)

/-- Along a periodic causal species orbit, iteration by one is the cyclic successor. -/
theorem trueInternalPeriodicSpecies_succ (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (s : ActiveSpecies σ)
    (hsper : s ∈ Function.periodicPts (N.trueInternalCausalSpeciesStep hflow W))
    (i : Fin (Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s)) :
    N.trueInternalCausalSpeciesStep hflow W
        ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s) =
      (N.trueInternalCausalSpeciesStep hflow W)^[((i.1 + 1) %
        Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s)] s := by
  let f := N.trueInternalCausalSpeciesStep hflow W
  calc
    f (f^[i.1] s) = f^[i.1 + 1] s := by
      simpa [Nat.succ_eq_add_one] using (Function.iterate_succ_apply' f i.1 s).symm
    _ = f^[((i.1 + 1) % Function.minimalPeriod f s)] s := by
      symm
      exact Function.iterate_mod_minimalPeriod_eq

/-- If the selected true-reaction vertices are pairwise distinct along a minimal periodic
causal orbit, the orbit itself is a simple true-SR cycle.  This isolates the other branch of
the classical source-block argument: repeated reaction vertices are exactly where the
no-S-to-R-intersection hypothesis is needed. -/
noncomputable def trueSRCycleOfPeriodicCausalOrbit (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (s : ActiveSpecies σ)
    (hsper : s ∈ Function.periodicPts (N.trueInternalCausalSpeciesStep hflow W))
    (hperiod : 2 ≤ Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s)
    (hreac : Function.Injective (fun i : Fin (Function.minimalPeriod
      (N.trueInternalCausalSpeciesStep hflow W) s) =>
        N.trueReaction (N.trueInternalCauseReaction hflow W
          ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)).1)) :
    N.TrueSRCycle (Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s) where
  nontrivial := hperiod
  species := fun i => ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s).1
  reaction := fun i => N.trueReaction (N.trueInternalCauseReaction hflow W
    ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)).1
  leftEdge := fun i => N.trueInternalCausalLeftEdge hflow W
    ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)
  rightEdge := fun i => N.trueInternalCausalRightEdge hflow W
    ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)
  left_species := by intro i; simp
  left_reaction := by intro i; simp [trueInternalCausalLeftEdge]
  right_species := by
    intro i
    simp only [trueInternalCausalRightEdge_species]
    exact congrArg Subtype.val (N.trueInternalPeriodicSpecies_succ hflow W s hsper i)
  right_reaction := by intro i; simp [trueInternalCausalRightEdge]
  species_injective := N.trueInternalPeriodicSpecies_injective hflow W s hsper
  reaction_injective := hreac

theorem trueSRCycleOfPeriodicCausalOrbit_even {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (s : {s : S // σ s ≠ 0})
    (hsper : s ∈ Function.periodicPts (N.trueInternalCausalSpeciesStep hflow W))
    (hperiod : 2 ≤ Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s)
    (hreac : Function.Injective (fun i : Fin (Function.minimalPeriod
      (N.trueInternalCausalSpeciesStep hflow W) s) =>
        N.trueReaction (N.trueInternalCauseReaction hflow W
          ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)).1)) :
    (N.trueSRCycleOfPeriodicCausalOrbit hflow W s hsper hperiod hreac).Even := by
  classical
  let p := Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s
  let C := N.trueSRCycleOfPeriodicCausalOrbit hflow W s hsper hperiod hreac
  let a : Fin p → ℝ := fun i => σ (C.species i)
  haveI : NeZero p := ⟨by omega⟩
  have hne : ∀ i, a i ≠ 0 := by
    intro i
    exact (((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s).2)
  have he := cyclic_sign_changes_even a hne
  rw [TrueSRCycle.Even, TrueSRCycle.numCPairs]
  rw [show (Finset.univ.filter C.isCPair) =
      Finset.univ.filter (fun i => a i * a (finRotate p i) < 0) by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hc := N.trueInternalCausalEdges_cPair_iff_signChange hflow W
      ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)
    have hrot : (finRotate p i).1 = (i.1 + 1) % p := by
      have hp1 : 1 < p := by dsimp [p]; omega
      have hh := congrArg Fin.val (finRotate_apply i)
      dsimp [p]; simpa [Fin.add_def, hp1] using hh
    have hstep := N.trueInternalPeriodicSpecies_succ hflow W s hsper i
    change C.isCPair i ↔ _
    rw [TrueSRCycle.isCPair]
    have hc' : (N.trueInternalCausalLeftEdge hflow W
          ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)).endpoint =
        (N.trueInternalCausalRightEdge hflow W
          ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)).endpoint ↔
        σ (((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s).1) *
          σ (N.trueInternalCausalSpeciesStep hflow W
            ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)).1 < 0 := by
      simpa [TrueSREdge.CPair, N.trueInternalCausalEdges_reaction hflow W
        ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)] using hc
    change (N.trueInternalCausalLeftEdge hflow W
          ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)).endpoint =
        (N.trueInternalCausalRightEdge hflow W
          ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)).endpoint ↔
        a i * a (finRotate p i) < 0
    rw [hc']
    unfold a C
    dsimp only [trueSRCycleOfPeriodicCausalOrbit]
    rw [hrot]
    exact iff_of_eq (congrArg (fun z =>
      σ (((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s).1) * σ z.1 < 0) hstep)]
  exact he


/-- A cyclic strict gain system cannot exist when the product of the edge gains is one.
This is the algebraic cancellation kernel for a degree-two source block: multiplying the strict
source inequalities around the block contradicts the `s`-cycle identity. -/
theorem cyclic_gain_no_strict {n : ℕ} [NeZero n]
    (e f a : Fin n → ℝ)
    (he : ∀ i, 0 < e i) (_hf : ∀ i, 0 < f i) (ha : ∀ i, 0 < a i)
    (hineq : ∀ i, e i * a i < f (finRotate n i) * a (finRotate n i))
    (hcycle : (∏ i, e i) = ∏ i, f i) : False := by
  have hp : (∏ i, e i * a i) < ∏ i, f (finRotate n i) * a (finRotate n i) := by
    exact Finset.prod_lt_prod₀ (fun i _ => mul_pos (he i) (ha i))
      (fun i _ => (hineq i).le) ⟨Classical.choice inferInstance, Finset.mem_univ _, hineq _⟩
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hp
  have hfrot : (∏ i, f (finRotate n i)) = ∏ i, f i := Equiv.prod_comp _ _
  have harot : (∏ i, a (finRotate n i)) = ∏ i, a i := Equiv.prod_comp _ _
  rw [hfrot, harot, hcycle] at hp
  exact lt_irrefl _ hp

/-- Mirror image of `cyclic_gain_no_strict`, with the rotation on the dominated side.

The two orientations are not interchangeable by re-indexing, because `finRotate` is not its own
inverse, so both are needed: the source argument of Shinar--Feinberg produces the inequality in
*this* direction.  At the species `s` reached by the reaction-to-species edge out of `Rᵢ`, the
incoming edge is causal and the outgoing edge to `Rᵢ₊₁` is opposing, so the *outgoing* label
paired with `Rᵢ₊₁` is what gets dominated. -/
theorem cyclic_gain_no_strict' {n : ℕ} [NeZero n]
    (e f a : Fin n → ℝ)
    (_he : ∀ i, 0 < e i) (hf : ∀ i, 0 < f i) (ha : ∀ i, 0 < a i)
    (hineq : ∀ i, e (finRotate n i) * a (finRotate n i) < f i * a i)
    (hcycle : (∏ i, e i) = ∏ i, f i) : False := by
  have hp : (∏ i, e (finRotate n i) * a (finRotate n i)) < ∏ i, f i * a i := by
    exact Finset.prod_lt_prod₀ (fun i _ => mul_pos (_he (finRotate n i)) (ha (finRotate n i)))
      (fun i _ => (hineq i).le) ⟨Classical.choice inferInstance, Finset.mem_univ _, hineq _⟩
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hp
  have herot : (∏ i, e (finRotate n i)) = ∏ i, e i := Equiv.prod_comp _ _
  have harot : (∏ i, a (finRotate n i)) = ∏ i, a i := Equiv.prod_comp _ _
  rw [herot, harot, hcycle] at hp
  exact lt_irrefl _ hp

/-- An `s`-cycle cannot support strict gain all the way around the cycle, in the orientation
produced by the source inequalities.  Pair this with `gain_of_two_term_flux` and
`edge_coeff_eq_abs_reactionVector`: the former gives, at each species of an end species-block,
`(outgoing label) * |α| < (incoming label) * |α|`, and the latter turns the net coefficients
into the `TrueSREdge.coeff` labels that `SCycle` speaks about. -/
theorem TrueSRCycle.no_strict_gain' (N : Network S) {n : ℕ} (C : N.TrueSRCycle n)
    (hsc : C.SCycle) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hineq : ∀ i, ((C.leftEdge (finRotate n i)).coeff : ℝ) * a (finRotate n i) <
      ((C.rightEdge i).coeff : ℝ) * a i) : False := by
  letI : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) C.nontrivial)⟩
  apply cyclic_gain_no_strict'
    (fun i => ((C.leftEdge i).coeff : ℝ))
    (fun i => ((C.rightEdge i).coeff : ℝ)) a
  · intro i; exact_mod_cast (C.leftEdge i).coeff_pos
  · intro i; exact_mod_cast (C.rightEdge i).coeff_pos
  · exact ha
  · exact hineq
  · exact_mod_cast hsc

/-- An `s`-cycle cannot support strict gain all the way around the cycle.  This packages the
multiplicative cancellation used when an end source block has degree two on its species side. -/
theorem TrueSRCycle.no_strict_gain (N : Network S) {n : ℕ} (C : N.TrueSRCycle n)
    (hsc : C.SCycle) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hineq : ∀ i, ((C.leftEdge i).coeff : ℝ) * a i <
      ((C.rightEdge (finRotate n i)).coeff : ℝ) * a (finRotate n i)) : False := by
  letI : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) C.nontrivial)⟩
  apply cyclic_gain_no_strict
    (fun i => ((C.leftEdge i).coeff : ℝ))
    (fun i => ((C.rightEdge i).coeff : ℝ)) a
  · intro i; exact_mod_cast (C.leftEdge i).coeff_pos
  · intro i; exact_mod_cast (C.rightEdge i).coeff_pos
  · exact ha
  · exact hineq
  · exact_mod_cast hsc

/-- Net-coefficient form of the cyclic-gain obstruction, in the orientation the source
inequalities produce.  This is the version the criterion now feeds, and it needs no
reactant/product separation: both the gain and the identity are in `netCoeff`.

Positivity of the edge net coefficients is a hypothesis rather than a consequence, because a
non-separated reaction with equal coefficients on the two sides has zero net coefficient at that
species.  Every edge produced by the causal construction has a nonzero reaction-vector
coordinate by construction, so this is discharged where the cycle is built. -/
theorem TrueSRCycle.no_strict_gain_net' (N : Network S) {n : ℕ} (C : N.TrueSRCycle n)
    (hsc : C.SCycleNet)
    (hLpos : ∀ i, 0 < (C.leftEdge i).netCoeff)
    (hRpos : ∀ i, 0 < (C.rightEdge i).netCoeff)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hineq : ∀ i, (C.leftEdge (finRotate n i)).netCoeff * a (finRotate n i) <
      (C.rightEdge i).netCoeff * a i) : False := by
  letI : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) C.nontrivial)⟩
  exact cyclic_gain_no_strict'
    (fun i => (C.leftEdge i).netCoeff)
    (fun i => (C.rightEdge i).netCoeff) a hLpos hRpos ha hineq hsc

/-- **Chaining the multiplier relation along a directed path.**

If positive multipliers satisfy `g i * m (i+1) ≤ m i` on every edge of a path, the product of
the gains along the path bounds the endpoint multiplier against the start:
`(∏ g) * m last ≤ m 0`.

This is the elementary step used repeatedly in the source-block arguments, and it is also what
shows the naive ear-decomposition route to Proposition 5.12 cannot work: chaining only ever
bounds `m start` from *above* in terms of `m end`, whereas extending multipliers across a new
directed ear requires a *lower* bound on the multiplier at the ear's tail.  The extremal
(shortest-path) solution is therefore not optional. -/
theorem multiplier_chain : ∀ (k : ℕ) (g : Fin k → ℝ) (m : Fin (k + 1) → ℝ),
    (∀ i, 0 < g i) → (∀ i, 0 < m i) →
    (∀ i : Fin k, g i * m i.succ ≤ m i.castSucc) →
    (∏ i, g i) * m (Fin.last k) ≤ m 0 := by
  intro k
  induction k with
  | zero =>
      intro g m _ _ _
      simp
  | succ k ih =>
      intro g m hg hm hrel
      have htail := ih (fun i => g i.succ) (fun i => m i.succ)
        (fun i => hg i.succ) (fun i => hm i.succ)
        (fun i => by simpa using hrel i.succ)
      have hfirst : g 0 * m (Fin.succ 0) ≤ m (Fin.castSucc 0) := hrel 0
      have hg0 : 0 < g 0 := hg 0
      rw [Fin.prod_univ_succ]
      have hlast : (Fin.last (k + 1)) = Fin.succ (Fin.last k) := rfl
      calc g 0 * (∏ i : Fin k, g i.succ) * m (Fin.last (k + 1))
          = g 0 * ((∏ i : Fin k, g i.succ) * m (Fin.succ (Fin.last k))) := by
            rw [hlast]; ring
        _ ≤ g 0 * m (Fin.succ 0) := mul_le_mul_of_nonneg_left htail (le_of_lt hg0)
        _ ≤ m 0 := by simpa using hfirst

/-- **Proposition 5.12 for a single directed cycle.**

Shinar--Feinberg need, for a reaction block with no stoichiometrically expansive directed cycle,
positive multipliers `M` satisfying `f * M(next) ≤ e * M(current)` on every causal unit.  For a
block that is a single directed cycle the multipliers can be written down: take the running
product of the reciprocal gains, `M k = ∏_{j < k} e j / f j`.

Every interior edge then satisfies the relation with *equality*, and the single wrap-around edge
is where the non-expansiveness hypothesis `∏ f ≤ ∏ e` is consumed.  Feeding these multipliers to
`weighted_source_inequalities_infeasible` closes the reaction-block case for single-cycle
blocks.

The general case (a strongly connected non-separable block that is not just a cycle) needs the
full "no positive-gain cycle implies a feasible potential" theorem, which Mathlib does not
have. -/
theorem exists_cycle_multipliers {n : ℕ} (hn : 2 ≤ n) (e f : Fin n → ℝ)
    (he : ∀ i, 0 < e i) (hf : ∀ i, 0 < f i)
    (hgain : (∏ i, f i) ≤ ∏ i, e i) :
    ∃ M : Fin n → ℝ, (∀ i, 0 < M i) ∧
      ∀ i, f i * M (finRotate n i) ≤ e i * M i := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  set g : ℕ → ℝ := fun j => if h : j < n then e ⟨j, h⟩ / f ⟨j, h⟩ else 1 with hg
  have hgpos : ∀ j, 0 < g j := by
    intro j
    by_cases h : j < n
    · simp only [hg, dif_pos h]; exact div_pos (he _) (hf _)
    · simp only [hg, dif_neg h]; norm_num
  set P : ℕ → ℝ := fun k => ∏ j ∈ Finset.range k, g j with hP
  have hPpos : ∀ k, 0 < P k := fun k => Finset.prod_pos (fun j _ => hgpos j)
  have hfprod : 0 < ∏ i, f i := Finset.prod_pos (fun i _ => hf i)
  have hPn : P n = (∏ i, e i) / ∏ i, f i := by
    simp only [hP]
    rw [← Fin.prod_univ_eq_prod_range g n]
    have hfun : ∀ i : Fin n, g i.1 = e i / f i := by
      intro i; simp only [hg, dif_pos i.isLt]
    rw [Finset.prod_congr rfl (fun i _ => hfun i), eq_div_iff (ne_of_gt hfprod),
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => div_mul_cancel₀ (e i) (ne_of_gt (hf i)))
  have hPn1 : (1 : ℝ) ≤ P n := by
    rw [hPn, le_div_iff₀ hfprod, one_mul]
    exact hgain
  refine ⟨fun i => P i.1, fun i => hPpos _, ?_⟩
  intro i
  have hn1 : 1 < n := by omega
  have hrot : (finRotate n i).1 = (i.1 + 1) % n := by
    have hh := congrArg Fin.val (finRotate_apply i)
    simpa [Fin.add_def, hn1] using hh
  have hstep : ∀ k (hk : k < n), P (k + 1) = P k * (e ⟨k, hk⟩ / f ⟨k, hk⟩) := by
    intro k hk
    simp only [hP, Finset.prod_range_succ]
    congr 1
    simp only [hg, dif_pos hk]
  rcases Nat.lt_or_ge (i.1 + 1) n with hc | hc
  · simp only [hrot, Nat.mod_eq_of_lt hc]
    have h := hstep i.1 i.isLt
    have hfi := hf i
    have hEq : P (i.1 + 1) = P i.1 * (e i / f i) := by simpa using h
    rw [hEq]
    have : f i * (P i.1 * (e i / f i)) = e i * P i.1 := by
      field_simp
    exact le_of_eq this
  · have hlast : i.1 + 1 = n := le_antisymm (Nat.succ_le_of_lt i.isLt) hc
    simp only [hrot, hlast, Nat.mod_self]
    have hP0 : P 0 = 1 := by simp [hP]
    rw [hP0, mul_one]
    have h := hstep i.1 i.isLt
    have hPn' : P (i.1 + 1) = P n := congrArg P hlast
    have hPnEq : P n = P i.1 * (e i / f i) := by
      rw [← hPn']; simpa using h
    have hfi := hf i
    have h2 : f i ≤ P i.1 * e i := by
      have hPn1' : (1 : ℝ) ≤ P i.1 * (e i / f i) := hPnEq ▸ hPn1
      have hmul := mul_le_mul_of_nonneg_right hPn1' (le_of_lt hfi)
      calc f i = 1 * f i := by ring
        _ ≤ (P i.1 * (e i / f i)) * f i := hmul
        _ = P i.1 * e i := by field_simp
    linarith [h2]

/-- **The multiplier contradiction (Shinar--Feinberg 5.8), as pure algebra.**

This is the engine of the end reaction-block argument, stated without any reaction-network
content so that it can be reused wherever the source inequalities appear.

`w r` is the magnitude `|α r|` carried by a reaction, `f s r` and `e s r` are the incoming and
outgoing stoichiometric weights of species `s` on reaction `r`, and `M` is a positive multiplier
per species.  If every species satisfies its source inequality (incoming strictly exceeds
outgoing) while every reaction satisfies the dual inequality against the multipliers (incoming
weighted by `M` is at most outgoing weighted by `M`), the two cannot hold together: multiplying
each species inequality by its multiplier and exchanging the order of summation turns the first
family into a statement the second family contradicts.

Shinar--Feinberg obtain the multipliers `M` from the absence of a stoichiometrically expansive
directed cycle (their Proposition 5.12); that existence result is what remains to be
formalized. -/
theorem weighted_source_inequalities_infeasible
    {Sp Rx : Type} [Fintype Sp] [Fintype Rx] [Nonempty Sp]
    (w : Rx → ℝ) (hw : ∀ r, 0 ≤ w r)
    (f e : Sp → Rx → ℝ)
    (M : Sp → ℝ) (hM : ∀ s, 0 < M s)
    (hsrc : ∀ s, (∑ r, e s r * w r) < ∑ r, f s r * w r)
    (hmult : ∀ r, (∑ s, f s r * M s) ≤ ∑ s, e s r * M s) :
    False := by
  classical
  -- Multiply each species inequality by its positive multiplier and add them up.
  have hstrict : (∑ s, M s * ∑ r, e s r * w r) < ∑ s, M s * ∑ r, f s r * w r := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty ?_
    intro s _
    exact (mul_lt_mul_of_pos_left (hsrc s) (hM s))
  -- Exchange the order of summation on both sides.
  have hswapF : (∑ s, M s * ∑ r, f s r * w r) = ∑ r, w r * ∑ s, f s r * M s := by
    calc (∑ s, M s * ∑ r, f s r * w r)
        = ∑ s, ∑ r, M s * (f s r * w r) := by simp [Finset.mul_sum]
      _ = ∑ r, ∑ s, M s * (f s r * w r) := Finset.sum_comm
      _ = ∑ r, w r * ∑ s, f s r * M s := by
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro s _
          ring
  have hswapE : (∑ s, M s * ∑ r, e s r * w r) = ∑ r, w r * ∑ s, e s r * M s := by
    calc (∑ s, M s * ∑ r, e s r * w r)
        = ∑ s, ∑ r, M s * (e s r * w r) := by simp [Finset.mul_sum]
      _ = ∑ r, ∑ s, M s * (e s r * w r) := Finset.sum_comm
      _ = ∑ r, w r * ∑ s, e s r * M s := by
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro s _
          ring
  -- The dual inequalities make the exchanged sums point the other way.
  have hle : (∑ r, w r * ∑ s, f s r * M s) ≤ ∑ r, w r * ∑ s, e s r * M s := by
    refine Finset.sum_le_sum ?_
    intro r _
    exact mul_le_mul_of_nonneg_left (hmult r) (hw r)
  rw [hswapF, hswapE] at hstrict
  exact absurd hstrict (not_lt.mpr hle)

/-- **The reaction-block source contradiction from cycle gains.**

Each reaction in an R-block contributes one directed causal unit from `source r` to `target r`.
Its outgoing and incoming edge labels are `e r` and `f r`, and `w r` is the reaction magnitude.
If the source inequality is strict at every species and every simple directed cycle has gain at
most one, the gain-potential theorem supplies positive species multipliers.  The resulting
reaction-wise inequalities contradict the source inequalities by
`weighted_source_inequalities_infeasible`.

Parallel causal units are retained: the gain of a species pair is the maximum over all reactions
joining that ordered pair.  A network-specific R-block proof only needs to establish the simple
cycle bound from the s-cycle condition. -/
theorem weighted_source_inequalities_infeasible_of_unit_graph
    {Sp Rx : Type} [Fintype Sp] [DecidableEq Sp] [Nonempty Sp]
    [Fintype Rx] [Nonempty Rx]
    (source target : Rx → Sp) (e f w : Rx → ℝ)
    (he : ∀ r, 0 < e r) (hf : ∀ r, 0 < f r) (hw : ∀ r, 0 ≤ w r)
    (hsrc : ∀ s,
      (∑ r, (if s = source r then e r else 0) * w r) <
        ∑ r, (if s = target r then f r else 0) * w r)
    (hsimple : ∀ (s : Sp) (q : List Sp), (s :: q).Nodup →
      CRNT.seqGain
        (fun u v => max 0 (Finset.univ.sup' Finset.univ_nonempty (fun r =>
          if source r = u ∧ target r = v then f r / e r else 0)))
        (s :: q ++ [s]) ≤ 1) :
    False := by
  classical
  let G : Sp → Sp → ℝ := fun u v =>
    max 0 (Finset.univ.sup' Finset.univ_nonempty (fun r =>
      if source r = u ∧ target r = v then f r / e r else 0))
  have hG : ∀ u v, 0 ≤ G u v := by
    intro u v
    exact le_max_left 0 _
  obtain ⟨M, hM, hmultG⟩ :=
    CRNT.exists_feasible_multipliers_of_simple G hG (by simpa [G] using hsimple)
  let ein : Sp → Rx → ℝ := fun s r => if s = target r then f r else 0
  let eout : Sp → Rx → ℝ := fun s r => if s = source r then e r else 0
  have hsourceGain (r : Rx) : f r / e r ≤ G (source r) (target r) := by
    dsimp [G]
    calc
      f r / e r ≤ Finset.univ.sup' Finset.univ_nonempty (fun q =>
          if source q = source r ∧ target q = target r then f q / e q else 0) := by
        have hle := Finset.le_sup' (fun q : Rx =>
            if source q = source r ∧ target q = target r then f q / e q else (0 : ℝ))
            (Finset.mem_univ r)
        have hEq : (if source r = source r ∧ target r = target r then
            f r / e r else (0 : ℝ)) = f r / e r := by simp
        rw [hEq] at hle
        exact hle
      _ ≤ max 0 _ := le_max_right _ _
  have hreactionBound (r : Rx) : f r * M (target r) ≤ e r * M (source r) := by
    have hgain : (f r / e r) * M (target r) ≤ M (source r) := by
      exact le_trans
        (mul_le_mul_of_nonneg_right (hsourceGain r) (le_of_lt (hM (target r))))
        (hmultG (source r) (target r))
    calc
      f r * M (target r) = e r * ((f r / e r) * M (target r)) := by
        field_simp [ne_of_gt (he r)]
      _ ≤ e r * M (source r) :=
        mul_le_mul_of_nonneg_left hgain (le_of_lt (he r))
  have hfin (r : Rx) : (∑ s, ein s r * M s) = f r * M (target r) := by
    rw [Finset.sum_eq_single (target r)]
    · simp [ein]
    · intro s _ hne
      simp [ein, hne]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  have hfout (r : Rx) : (∑ s, eout s r * M s) = e r * M (source r) := by
    rw [Finset.sum_eq_single (source r)]
    · simp [eout]
    · intro s _ hne
      simp [eout, hne]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  have hmult : ∀ r, (∑ s, ein s r * M s) ≤ ∑ s, eout s r * M s := by
    intro r
    rw [hfin, hfout]
    exact hreactionBound r
  exact weighted_source_inequalities_infeasible w hw ein eout M hM
    (by simpa [ein, eout] using hsrc) hmult

/-- **The end species-block contradiction (Shinar--Feinberg 5.7.1), formalized.**

Suppose a strong-concordance witness gives an even true-SR cycle along which, at each species,
one cycle reaction is causal and the other opposes it, while every remaining reaction contributes
nonpositively after multiplication by the species sign. Then no such witness exists. This permits
the off-block terms at a separating species that occur in the published source argument.

With an explicit net-cycle identity, the contradiction itself needs no reactant/product
separation. The full theorem still requires the graph decomposition that produces these local
sign conditions from a general source. -/
theorem no_degree_two_causal_cycle (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    {n : ℕ} (C : N.TrueSRCycle n) (hEven : C.Even)
    (hsc : C.SCycleNet)
    (hrep : ∀ i, (C.leftEdge i).representative = (C.rightEdge i).representative)
    (hσ : ∀ i, σ (C.species i) ≠ 0)
    (hcausal : ∀ i, 0 < (α (Sum.inl (C.rightEdge i).representative) *
        N.reactionVector (C.rightEdge i).representative (C.species (finRotate n i))) *
        σ (C.species (finRotate n i)))
    (hopp : ∀ i, (α (Sum.inl (C.leftEdge (finRotate n i)).representative) *
        N.reactionVector (C.leftEdge (finRotate n i)).representative
          (C.species (finRotate n i))) * σ (C.species (finRotate n i)) < 0)
    (hrest : ∀ i, ∀ r : N.R,
      r ≠ (C.rightEdge i).representative →
      r ≠ (C.leftEdge (finRotate n i)).representative →
      (α (Sum.inl r) * N.reactionVector r (C.species (finRotate n i))) *
        σ (C.species (finRotate n i)) ≤ 0) :
    False := by
  letI : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) C.nontrivial)⟩
  have hn2 : 2 ≤ n := C.nontrivial
  -- every edge's net coefficient is the absolute reaction-vector coordinate at its species
  have hnet : ∀ e : N.TrueSREdge,
      e.netCoeff = |N.reactionVector e.representative e.species| := by
    intro e; rw [TrueSREdge.netCoeff, reactionVector_apply]
  -- the rotation has no fixed point
  have hrot : ∀ i : Fin n, finRotate n i ≠ i := by
    intro i h
    have hv := congrArg Fin.val h
    rw [finRotate_apply] at hv
    have hn1 : 1 < n := by omega
    simp only [Fin.add_def, Fin.val_one', Nat.mod_eq_of_lt hn1] at hv
    have hlt : i.val < n := i.isLt
    rcases Nat.lt_or_ge (i.val + 1) n with hc | hc
    · rw [Nat.mod_eq_of_lt hc] at hv; omega
    · have : i.val + 1 = n := by omega
      rw [this, Nat.mod_self] at hv; omega
  -- the cycle's `right_species` field is phrased with an explicit `% n`; bridge it to `finRotate`
  have hrotEq : ∀ i : Fin n, finRotate n i =
      (⟨(i.1 + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) := by
    intro i
    apply Fin.ext
    have hn1 : 1 < n := by omega
    rw [finRotate_apply]
    simp [Fin.add_def, Nat.mod_eq_of_lt hn1]
  have hrightSp : ∀ i : Fin n, (C.rightEdge i).species = C.species (finRotate n i) := by
    intro i
    rw [C.right_species i, hrotEq i]
  -- distinct cycle positions carry distinct concrete representatives
  have hrepne : ∀ i : Fin n, (C.rightEdge i).representative ≠
      (C.leftEdge (finRotate n i)).representative := by
    intro i h
    have h1 : C.reaction i = C.reaction (finRotate n i) := by
      have hr := (C.rightEdge i).representative_class
      have hl := (C.leftEdge (finRotate n i)).representative_class
      rw [C.right_reaction i] at hr
      rw [C.left_reaction (finRotate n i)] at hl
      rw [← hr, ← hl, h]
    exact hrot i (C.reaction_injective h1.symm)
  set a : Fin n → ℝ := fun i => |α (Sum.inl (C.rightEdge i).representative)| with ha_def
  have hapos : ∀ i, 0 < a i := by
    intro i
    have h := hcausal i
    have hne : α (Sum.inl (C.rightEdge i).representative) ≠ 0 := by
      intro hz; rw [hz, zero_mul, zero_mul] at h; exact lt_irrefl 0 h
    simpa [ha_def] using abs_pos.mpr hne
  -- the right edges have positive net coefficient, from the causal term being nonzero
  have hRpos : ∀ i, 0 < (C.rightEdge i).netCoeff := by
    intro i
    rw [hnet, hrightSp i]
    refine abs_pos.mpr ?_
    intro hz
    have h := hcausal i
    rw [hz, mul_zero, zero_mul] at h
    exact lt_irrefl 0 h
  -- the left edges likewise, from the opposing term; rotation is surjective so every index
  -- is of the form `finRotate n i`
  have hLpos : ∀ j, 0 < (C.leftEdge j).netCoeff := by
    intro j
    obtain ⟨i, hi⟩ := (finRotate n).surjective j
    subst hi
    rw [hnet, C.left_species (finRotate n i)]
    refine abs_pos.mpr ?_
    intro hz
    have h := hopp i
    rw [hz, mul_zero, zero_mul] at h
    exact lt_irrefl 0 h
  have hgain : ∀ i, (C.leftEdge (finRotate n i)).netCoeff * a (finRotate n i) <
      (C.rightEdge i).netCoeff * a i := by
    intro i
    have hgt := N.gain_of_two_term_flux_of_nonpos_rest W (hσ (finRotate n i)) (hrepne i)
      (fun r h1 h2 => hrest i r h1 h2) (hcausal i) (hopp i)
    rw [hnet (C.leftEdge (finRotate n i)), hnet (C.rightEdge i),
      C.left_species (finRotate n i), hrightSp i, ha_def]
    simp only
    rw [hrep (finRotate n i)] at hgt ⊢
    ring_nf at hgt ⊢
    linarith [hgt]
  exact TrueSRCycle.no_strict_gain_net' N C hsc hLpos hRpos a hapos hgain

variable {S : Type} [DecidableEq S] [Fintype S]

noncomputable local instance instTrueReactionFintype (N : Network S) :
    Fintype N.TrueReaction := Fintype.ofFinite _

/-- The net witness flux at a species, after summing all non-flow channels in one true-reaction
class. -/
noncomputable def trueInternalClassFlux (N : Network S)
    (α : N.fullyOpen.R → ℝ) (ρ : N.TrueReaction) (s : S) : ℝ := by
  classical
  exact ∑ r ∈ N.nonflowOriginalChannels.filter (fun r => N.trueReaction r = ρ),
    α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r s

/-- Summing class fluxes recovers the complete internal-channel flux. -/
theorem sum_trueInternalClassFlux (N : Network S)
    (α : N.fullyOpen.R → ℝ) (s : S) :
    (∑ ρ : N.TrueReaction, N.trueInternalClassFlux α ρ s) =
      ∑ r ∈ N.nonflowOriginalChannels,
        α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r s := by
  classical
  unfold trueInternalClassFlux
  exact Finset.sum_fiberwise N.nonflowOriginalChannels N.trueReaction
    (fun r => α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r s)

/-- Strong concordance makes the sum of the internal class fluxes strictly positive at every
active species. Flow-channel terms have already been removed by the source lemma. -/
theorem trueInternalClassFlux_mul_sigma_pos (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) {s : S} (hs : σ s ≠ 0) :
    0 < ∑ ρ : N.TrueReaction,
      (N.trueInternalClassFlux α ρ s) * σ s := by
  calc
    0 < (∑ r ∈ N.nonflowOriginalChannels,
        (α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r s) * σ s) :=
      N.internal_flux_mul_sigma_pos_on_nonflow_channels hflow W hs
    _ = ∑ ρ : N.TrueReaction, (N.trueInternalClassFlux α ρ s) * σ s := by
      calc
        _ = (∑ r ∈ N.nonflowOriginalChannels,
            α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r s) * σ s := by
              rw [Finset.sum_mul]
        _ = (∑ ρ : N.TrueReaction, N.trueInternalClassFlux α ρ s) * σ s := by
              rw [N.sum_trueInternalClassFlux]
        _ = ∑ ρ : N.TrueReaction, (N.trueInternalClassFlux α ρ s) * σ s := by
              rw [Finset.sum_mul]

/-- In a positive source flux sum, a selected negative reaction-class term is smaller in
magnitude than a selected positive term when all remaining class terms are nonpositive. -/
theorem trueInternalClassFlux_two_term_gain (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} {s : S}
    (F : Finset N.TrueReaction) {ρpos ρneg : N.TrueReaction} (hne : ρpos ≠ ρneg)
    (hmemPos : ρpos ∈ F) (hmemNeg : ρneg ∈ F)
    (hrest : ∀ ρ ∈ F, ρ ≠ ρpos → ρ ≠ ρneg →
      (N.trueInternalClassFlux α ρ s) * σ s ≤ 0)
    (hsum : 0 < ∑ ρ ∈ F, (N.trueInternalClassFlux α ρ s) * σ s)
    (hpos : 0 < (N.trueInternalClassFlux α ρpos s) * σ s)
    (hneg : (N.trueInternalClassFlux α ρneg s) * σ s < 0) :
    |(N.trueInternalClassFlux α ρneg s) * σ s| <
      |(N.trueInternalClassFlux α ρpos s) * σ s| := by
  classical
  let pair : Finset N.TrueReaction := {ρpos, ρneg}
  have hpairSub : pair ⊆ F := by
    intro ρ hρ
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hρ
    rcases hρ with hρ | hρ
    · simpa [hρ] using hmemPos
    · simpa [hρ] using hmemNeg
  have hrestSum : (∑ ρ ∈ F \ pair,
      (N.trueInternalClassFlux α ρ s) * σ s) ≤ 0 := by
    apply Finset.sum_nonpos
    intro ρ hρ
    have hF : ρ ∈ F := (Finset.mem_sdiff.mp hρ).1
    have hpair : ρ ∉ pair := (Finset.mem_sdiff.mp hρ).2
    have hρpos : ρ ≠ ρpos := by
      intro heq
      apply hpair
      simp [pair, heq]
    have hρneg : ρ ≠ ρneg := by
      intro heq
      apply hpair
      simp [pair, heq]
    exact hrest ρ hF hρpos hρneg
  have hsplit : (∑ ρ ∈ F, (N.trueInternalClassFlux α ρ s) * σ s) =
      (∑ ρ ∈ pair, (N.trueInternalClassFlux α ρ s) * σ s) +
        (∑ ρ ∈ F \ pair, (N.trueInternalClassFlux α ρ s) * σ s) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff)]
    congr 1
    exact (Finset.union_sdiff_of_subset hpairSub).symm
  have hpairSum :
      (∑ ρ ∈ pair, (N.trueInternalClassFlux α ρ s) * σ s) =
        (N.trueInternalClassFlux α ρpos s) * σ s +
          (N.trueInternalClassFlux α ρneg s) * σ s := by
    simp only [pair, Finset.sum_pair hne]
  have hpairPos :
      0 < (N.trueInternalClassFlux α ρpos s) * σ s +
        (N.trueInternalClassFlux α ρneg s) * σ s := by
    rw [hsplit, hpairSum] at hsum
    linarith [hrestSum]
  rw [abs_of_pos hpos, abs_of_neg hneg]
  linarith

/-- Aggregate form of the degree-two source-block contradiction.  It works directly with
true-reaction fluxes: at each cycle species the selected incoming class is strictly positive,
the next class is strictly negative, and every other class in the source contributes
nonpositively.  The shared representative and scalar-vector relation transfer the strict
two-term comparison to the cycle's net edge labels. -/
theorem no_degree_two_aggregate_causal_cycle (N : Network S)
    (hsep : N.ReactantProductSeparated)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} {n : ℕ}
    (C : N.TrueSRCycle n) (hsc : C.SCycleNet)
    (F : Finset N.TrueReaction) (β : Fin n → ℝ)
    (hrep : ∀ i, (C.leftEdge i).representative = (C.rightEdge i).representative)
    (hbeta : ∀ i t, N.trueInternalClassFlux α (C.reaction i) t =
      β i * N.reactionVector (C.rightEdge i).representative t)
    (hclass : ∀ i, C.reaction i ∈ F)
    (hsum : ∀ i, 0 < ∑ ρ ∈ F,
      (N.trueInternalClassFlux α ρ (C.species (finRotate n i))) *
        σ (C.species (finRotate n i)))
    (hcausal : ∀ i, 0 < (N.trueInternalClassFlux α (C.reaction i)
      (C.species (finRotate n i))) * σ (C.species (finRotate n i)))
    (hopp : ∀ i, (N.trueInternalClassFlux α (C.reaction (finRotate n i))
      (C.species (finRotate n i))) * σ (C.species (finRotate n i)) < 0)
    (hrest : ∀ i ρ, ρ ∈ F → ρ ≠ C.reaction i →
      ρ ≠ C.reaction (finRotate n i) →
      (N.trueInternalClassFlux α ρ (C.species (finRotate n i))) *
        σ (C.species (finRotate n i)) ≤ 0) :
    False := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) C.nontrivial)⟩
  have hn2 : 2 ≤ n := C.nontrivial
  have hrotVal : ∀ i : Fin n, (finRotate n i).1 = (i.1 + 1) % n := by
    intro i
    have hn1 : 1 < n := by omega
    have h := congrArg Fin.val (finRotate_apply i)
    simpa [Fin.add_def, hn1] using h
  have hrotNe : ∀ i : Fin n, finRotate n i ≠ i := by
    intro i heq
    have hv := congrArg Fin.val heq
    rw [hrotVal i] at hv
    have hi := i.isLt
    rcases Nat.lt_or_ge (i.1 + 1) n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hv
      omega
    · have heq' : i.1 + 1 = n := by omega
      rw [heq', Nat.mod_self] at hv
      omega
  have hreactionNe : ∀ i : Fin n, C.reaction i ≠ C.reaction (finRotate n i) := by
    intro i heq
    apply hrotNe i
    exact (C.reaction_injective heq).symm
  have hnet : ∀ e : N.TrueSREdge,
      e.netCoeff = |N.reactionVector e.representative e.species| := by
    intro e
    rw [TrueSREdge.netCoeff, reactionVector_apply]
  have hnetPos (e : N.TrueSREdge) : 0 < e.netCoeff := by
    have hcoeff : 0 < (e.coeff : ℝ) := by exact_mod_cast e.coeff_pos
    have hcoeffEq := N.edge_coeff_eq_abs_reactionVector hsep e
    have hEq : e.netCoeff = (e.coeff : ℝ) := (hnet e).trans hcoeffEq.symm
    rw [hEq]
    exact hcoeff
  have hrightSpecies (i : Fin n) :
      (C.rightEdge i).species = C.species (finRotate n i) := by
    rw [C.right_species i]
    exact congrArg C.species (Fin.ext (hrotVal i).symm)
  have hLnet (i : Fin n) :
      (C.leftEdge (finRotate n i)).netCoeff =
        |N.reactionVector (C.rightEdge (finRotate n i)).representative
          (C.species (finRotate n i))| := by
    calc
      _ = |N.reactionVector (C.leftEdge (finRotate n i)).representative
          (C.leftEdge (finRotate n i)).species| := hnet _
      _ = |N.reactionVector (C.rightEdge (finRotate n i)).representative
          (C.species (finRotate n i))| := by
        rw [hrep (finRotate n i), C.left_species]
  have hRnet (i : Fin n) :
      (C.rightEdge i).netCoeff =
        |N.reactionVector (C.rightEdge i).representative
          (C.species (finRotate n i))| := by
    calc
      _ = |N.reactionVector (C.rightEdge i).representative
          (C.rightEdge i).species| := hnet _
      _ = |N.reactionVector (C.rightEdge i).representative
          (C.species (finRotate n i))| := by rw [hrightSpecies i]
  have hLpos : ∀ i, 0 < (C.leftEdge i).netCoeff := by
    intro i
    exact hnetPos (C.leftEdge i)
  have hRpos : ∀ i, 0 < (C.rightEdge i).netCoeff := by
    intro i
    exact hnetPos (C.rightEdge i)
  have hbetaNe : ∀ i : Fin n, β i ≠ 0 := by
    intro i hz
    have h := hcausal i
    rw [hbeta i (C.species (finRotate n i)), hz, zero_mul, zero_mul] at h
    exact (lt_irrefl 0) h
  have ha : ∀ i, 0 < |β i| := fun i => abs_pos.mpr (hbetaNe i)
  have hineq : ∀ i,
      (C.leftEdge (finRotate n i)).netCoeff * |β (finRotate n i)| <
        (C.rightEdge i).netCoeff * |β i| := by
    intro i
    have hsigma : σ (C.species (finRotate n i)) ≠ 0 := by
      intro hz
      have h := hcausal i
      rw [hz, mul_zero] at h
      exact (lt_irrefl 0) h
    have hterm := N.trueInternalClassFlux_two_term_gain F (hreactionNe i)
      (hclass i) (hclass (finRotate n i)) (hrest i) (hsum i)
      (hcausal i) (hopp i)
    have hflux :
        |N.trueInternalClassFlux α (C.reaction (finRotate n i))
          (C.species (finRotate n i))| <
        |N.trueInternalClassFlux α (C.reaction i)
          (C.species (finRotate n i))| := by
      rw [abs_mul, abs_mul] at hterm
      exact lt_of_mul_lt_mul_right hterm (le_of_lt (abs_pos.mpr hsigma))
    have hweighted := hflux
    rw [hbeta (finRotate n i) (C.species (finRotate n i)),
      hbeta i (C.species (finRotate n i)), abs_mul, abs_mul] at hweighted
    calc
      (C.leftEdge (finRotate n i)).netCoeff * |β (finRotate n i)| =
          |β (finRotate n i)| *
            |N.reactionVector (C.rightEdge (finRotate n i)).representative
              (C.species (finRotate n i))| := by rw [hLnet]; ring
      _ < |β i| * |N.reactionVector (C.rightEdge i).representative
            (C.species (finRotate n i))| := hweighted
      _ = (C.rightEdge i).netCoeff * |β i| := by rw [hRnet]; ring
  exact TrueSRCycle.no_strict_gain_net' N C hsc hLpos hRpos (fun i => |β i|) ha hineq

/-- A source cycle cannot account for all positive aggregate terms at its species.  Otherwise
the degree-two aggregate contradiction applies.  This is the first forced ear attachment that
the source-block argument must then analyze. -/
theorem exists_positive_off_cycle_aggregate_class (N : Network S)
    (hsep : N.ReactantProductSeparated)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} {n : ℕ}
    (C : N.TrueSRCycle n) (hsc : C.SCycleNet)
    (F : Finset N.TrueReaction) (β : Fin n → ℝ)
    (hrep : ∀ i, (C.leftEdge i).representative = (C.rightEdge i).representative)
    (hbeta : ∀ i t, N.trueInternalClassFlux α (C.reaction i) t =
      β i * N.reactionVector (C.rightEdge i).representative t)
    (hclass : ∀ i, C.reaction i ∈ F)
    (hsum : ∀ i, 0 < ∑ ρ ∈ F,
      (N.trueInternalClassFlux α ρ (C.species (finRotate n i))) *
        σ (C.species (finRotate n i)))
    (hcausal : ∀ i, 0 < (N.trueInternalClassFlux α (C.reaction i)
      (C.species (finRotate n i))) * σ (C.species (finRotate n i)))
    (hopp : ∀ i, (N.trueInternalClassFlux α (C.reaction (finRotate n i))
      (C.species (finRotate n i))) * σ (C.species (finRotate n i)) < 0) :
    ∃ i ρ, ρ ∈ F ∧ ρ ≠ C.reaction i ∧ ρ ≠ C.reaction (finRotate n i) ∧
      0 < (N.trueInternalClassFlux α ρ (C.species (finRotate n i))) *
        σ (C.species (finRotate n i)) := by
  classical
  by_contra hnone
  have hrest : ∀ i ρ, ρ ∈ F → ρ ≠ C.reaction i →
      ρ ≠ C.reaction (finRotate n i) →
      (N.trueInternalClassFlux α ρ (C.species (finRotate n i))) *
        σ (C.species (finRotate n i)) ≤ 0 := by
    intro i ρ hρ hneL hneR
    apply le_of_not_gt
    intro hpos
    apply hnone
    exact ⟨i, ρ, hρ, hneL, hneR, hpos⟩
  exact N.no_degree_two_aggregate_causal_cycle hsep C hsc F β hrep hbeta
    hclass hsum hcausal hopp hrest

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

/-- True-reaction classes represented by reaction vertices in a chosen aggregate source. -/
noncomputable def trueInternalAggregateSourceClasses (N : Network S)
    (α : N.fullyOpen.R → ℝ) (σ : S → ℝ)
    (T : Finset (N.TrueInternalAggregateVertex α σ)) : Finset N.TrueReaction := by
  classical
  exact Finset.univ.filter (fun ρ =>
    ∃ q : N.ActiveAggregateTrueReaction α σ, q.1 = ρ ∧ Sum.inr q ∈ T)

private theorem reactionVector_cross_eq_of_sameTrueReaction (N : Network S)
    {r q : N.R} (h : N.SameTrueReaction r q) (s t : S) :
    N.reactionVector r t * N.reactionVector q s =
      N.reactionVector r s * N.reactionVector q t := by
  rcases h with h | h
  · simp [reactionVector_apply, h.1, h.2] <;> ring
  · simp [reactionVector_apply, h.1, h.2] <;> ring

private theorem exists_finset_term_same_sign {ι : Type*} (A : Finset ι)
    (f : ι → ℝ) (h : (∑ i ∈ A, f i) ≠ 0) :
    ∃ i ∈ A, f i * (∑ i ∈ A, f i) > 0 := by
  classical
  by_cases hsum : 0 < ∑ i ∈ A, f i
  · by_contra hnone
    have hnonpos : ∀ i ∈ A, f i ≤ 0 := by
      intro i hi
      by_contra hnot
      have hpos : 0 < f i := lt_of_not_ge hnot
      exact hnone ⟨i, hi, mul_pos hpos hsum⟩
    have hle : (∑ i ∈ A, f i) ≤ 0 := Finset.sum_nonpos hnonpos
    linarith
  · have hsum' : ∑ i ∈ A, f i < 0 := lt_of_le_of_ne (le_of_not_gt hsum) h
    by_contra hnone
    have hnonneg : ∀ i ∈ A, 0 ≤ f i := by
      intro i hi
      by_contra hnot
      have hneg : f i < 0 := lt_of_not_ge hnot
      exact hnone ⟨i, hi, mul_pos_of_neg_of_neg hneg hsum'⟩
    have hge : 0 ≤ ∑ i ∈ A, f i := Finset.sum_nonneg hnonneg
    linarith

private theorem same_sign_product_preserves_neg {a b x : ℝ}
    (hab : 0 < a * b) (hax : a * x < 0) : b * x < 0 := by
  rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hx : x < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg hb hx
  · have hx : 0 < x := by nlinarith
    exact mul_neg_of_neg_of_pos hb hx

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
private theorem exists_trueSREdge_of_nonzero_trueInternalClassFlux (N : Network S)
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

/-- Every aggregate class-flux vector is a scalar multiple of any nonzero representative's
stoichiometric vector. This is the vector-level form of quotienting parallel and reverse
channels; it lets a single labeled SR reaction vertex represent the whole class. -/
private theorem exists_scalar_mul_reactionVector_eq_trueInternalClassFlux (N : Network S)
    {α : N.fullyOpen.R → ℝ} (ρ : N.TrueReaction) {r₀ : N.R} (s : S)
    (hr₀NF : r₀ ∈ N.nonflowOriginalChannels)
    (hr₀ρ : N.trueReaction r₀ = ρ)
    (hν₀ : N.reactionVector r₀ s ≠ 0) :
    ∃ β : ℝ, ∀ t : S,
      N.trueInternalClassFlux α ρ t = β * N.reactionVector r₀ t := by
  classical
  let A := N.nonflowOriginalChannels.filter (fun r => N.trueReaction r = ρ)
  have hr₀A : r₀ ∈ A := Finset.mem_filter.mpr ⟨hr₀NF, hr₀ρ⟩
  let c : N.R → ℝ := fun r =>
    (α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r s) /
      N.reactionVector r₀ s
  have hclassFlux_eq : ∀ t : S,
      N.trueInternalClassFlux α ρ t = (∑ r ∈ A, c r) * N.reactionVector r₀ t := by
    intro t
    unfold trueInternalClassFlux
    calc
      (∑ r ∈ A,
          α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r t) =
        ∑ r ∈ A, c r * N.reactionVector r₀ t := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrρ : N.trueReaction r = ρ := (Finset.mem_filter.mp hr).2
          have hsame : N.SameTrueReaction r r₀ :=
            Quotient.exact (hrρ.trans hr₀ρ.symm)
          have hcross := N.reactionVector_cross_eq_of_sameTrueReaction hsame t s
          dsimp [c]
          calc
            α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r t =
                (α (Sum.inl r : N.fullyOpen.R) *
                (N.reactionVector r t * N.reactionVector r₀ s)) /
                    N.reactionVector r₀ s := by
                  field_simp [hν₀]
            _ = (α (Sum.inl r : N.fullyOpen.R) *
                  (N.reactionVector r s * N.reactionVector r₀ t)) /
                    N.reactionVector r₀ s := by rw [hcross]
            _ = (α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r s /
                  N.reactionVector r₀ s) * N.reactionVector r₀ t := by
                  field_simp [hν₀]
      _ = (∑ r ∈ A, c r) * N.reactionVector r₀ t := by
        rw [Finset.sum_mul]
  exact ⟨∑ r ∈ A, c r, hclassFlux_eq⟩

private theorem activeAggregateTrueReaction_internal (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (ρ : N.ActiveAggregateTrueReaction α σ) :
    TrueReaction.Internal N ρ.1 := by
  obtain ⟨s, -, hflux⟩ := ρ.2
  obtain ⟨r, hrNF, hrρ, -⟩ := N.exists_nonzero_channel_of_trueInternalClassFlux ρ.1 s hflux
  have hnotflow : ¬ N.IsFlowChannel r := by
    simpa [nonflowOriginalChannels] using hrNF
  rw [← hrρ]
  change ¬ N.IsFlowChannel r
  exact hnotflow

/-- A nonzero aggregate class flux has a negative signed-flux coordinate.  The key point is to
sum coefficients after orienting every channel against one representative of its true-reaction
class; channel contributions with the opposite orientation cannot silently reverse this sign. -/
private theorem trueInternalClassFlux_has_negative_signed_term (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) (ρ : N.TrueReaction)
    (s : S) (hflux : N.trueInternalClassFlux α ρ s ≠ 0) :
    ∃ t, (N.trueInternalClassFlux α ρ t) * σ t < 0 := by
  classical
  let A := N.nonflowOriginalChannels.filter (fun r => N.trueReaction r = ρ)
  obtain ⟨r₀, hr₀NF, hr₀ρ, hterm₀⟩ :=
    N.exists_nonzero_channel_of_trueInternalClassFlux ρ s hflux
  have hν₀ : N.reactionVector r₀ s ≠ 0 := by
    intro hzero
    apply hterm₀
    rw [hzero, mul_zero]
  let c : N.R → ℝ := fun r =>
    (α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r s) /
      N.reactionVector r₀ s
  have hclassFlux_eq : ∀ t : S,
      N.trueInternalClassFlux α ρ t =
        (∑ r ∈ A, c r) * N.reactionVector r₀ t := by
    intro t
    unfold trueInternalClassFlux
    calc
      (∑ r ∈ A,
          α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r t) =
        ∑ r ∈ A, c r * N.reactionVector r₀ t := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrρ : N.trueReaction r = ρ := (Finset.mem_filter.mp hr).2
          have hsame : N.SameTrueReaction r r₀ :=
            Quotient.exact (hrρ.trans hr₀ρ.symm)
          have hcross := N.reactionVector_cross_eq_of_sameTrueReaction hsame t s
          dsimp [c]
          calc
            α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r t =
                (α (Sum.inl r : N.fullyOpen.R) *
                (N.reactionVector r t * N.reactionVector r₀ s)) /
                    N.reactionVector r₀ s := by
                  field_simp [hν₀]
            _ = (α (Sum.inl r : N.fullyOpen.R) *
                  (N.reactionVector r s * N.reactionVector r₀ t)) /
                    N.reactionVector r₀ s := by rw [hcross]
            _ = (α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r s /
                  N.reactionVector r₀ s) * N.reactionVector r₀ t := by
                  field_simp [hν₀]
      _ = (∑ r ∈ A, c r) * N.reactionVector r₀ t := by
        rw [Finset.sum_mul]
  have hcoeff : (∑ r ∈ A, c r) ≠ 0 := by
    intro hz
    apply hflux
    rw [hclassFlux_eq s, hz, zero_mul]
  obtain ⟨r, hrA, hsameSign⟩ := exists_finset_term_same_sign A c hcoeff
  have hα : α (Sum.inl r : N.fullyOpen.R) ≠ 0 := by
    intro hzero
    have hc : c r = 0 := by simp [c, hzero]
    rw [hc, zero_mul] at hsameSign
    exact (lt_irrefl 0 hsameSign)
  obtain ⟨t, hneg⟩ := N.exists_internal_opposite_species W hα
  have hcross_term :
      α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r t =
        c r * N.reactionVector r₀ t := by
    have hrρ : N.trueReaction r = ρ := (Finset.mem_filter.mp hrA).2
    have hsame : N.SameTrueReaction r r₀ :=
      Quotient.exact (hrρ.trans hr₀ρ.symm)
    have hcross := N.reactionVector_cross_eq_of_sameTrueReaction hsame t s
    dsimp [c]
    calc
      α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r t =
          (α (Sum.inl r : N.fullyOpen.R) *
            (N.reactionVector r t * N.reactionVector r₀ s)) /
              N.reactionVector r₀ s := by
                field_simp [hν₀]
      _ = (α (Sum.inl r : N.fullyOpen.R) *
            (N.reactionVector r s * N.reactionVector r₀ t)) /
              N.reactionVector r₀ s := by rw [hcross]
      _ = (α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r s /
            N.reactionVector r₀ s) * N.reactionVector r₀ t := by
              field_simp [hν₀]
  have hchannel_neg : c r *
      (N.reactionVector r₀ t * σ t) < 0 := by
    calc
      c r * (N.reactionVector r₀ t * σ t) =
          (c r * N.reactionVector r₀ t) * σ t := by ring
      _ = (α (Sum.inl r : N.fullyOpen.R) * N.reactionVector r t) * σ t := by
          rw [← hcross_term]
      _ < 0 := hneg
  have htotal_neg : (∑ r ∈ A, c r) *
      (N.reactionVector r₀ t * σ t) < 0 :=
    same_sign_product_preserves_neg hsameSign hchannel_neg
  refine ⟨t, ?_⟩
  rw [hclassFlux_eq t]
  calc
    ((∑ r ∈ A, c r) * N.reactionVector r₀ t) * σ t =
        (∑ r ∈ A, c r) * (N.reactionVector r₀ t * σ t) := by ring
    _ < 0 := htotal_neg

/-- Every active aggregate class has an incoming causal edge at some active species. -/
private theorem activeAggregateClass_has_negative_edge (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (ρ : N.ActiveAggregateTrueReaction α σ) :
    ∃ s : AggregateActiveSpecies σ,
      N.TrueInternalAggregateCausalEdge (Sum.inl s) (Sum.inr ρ) := by
  obtain ⟨s, hsσ, hflux⟩ := ρ.2
  obtain ⟨t, ht⟩ := N.trueInternalClassFlux_has_negative_signed_term W ρ.1 s hflux
  have htσ : σ t ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at ht
    exact (lt_irrefl 0 ht)
  exact ⟨⟨t, htσ⟩, ht⟩

/-- A negative causal neighbor of a reaction already in a predecessor-closed source lies in
that same source. This lets a class's positive attachment to a cycle and its negative endpoint
be analyzed within one source graph. -/
private theorem activeAggregateClass_negative_species_mem_source (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalAggregateVertex α σ))
    (hsource : ∀ a b, N.TrueInternalAggregateCausalEdge a b → b ∈ T → a ∈ T)
    (ρ : N.ActiveAggregateTrueReaction α σ) (hρT : Sum.inr ρ ∈ T) :
    ∃ s : AggregateActiveSpecies σ,
      N.TrueInternalAggregateCausalEdge (Sum.inl s) (Sum.inr ρ) ∧
        Sum.inl s ∈ T := by
  obtain ⟨s, hedge⟩ := N.activeAggregateClass_has_negative_edge W ρ
  exact ⟨s, hedge, hsource _ _ hedge hρT⟩

private def aggregateVertexToTrueSRVertex (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} :
    N.TrueInternalAggregateVertex α σ → N.TrueSRVertex
  | Sum.inl s => Sum.inl s.1
  | Sum.inr ρ => Sum.inr ⟨ρ.1, N.activeAggregateTrueReaction_internal ρ⟩

private theorem aggregateVertexToTrueSRVertex_injective (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} :
    Function.Injective (N.aggregateVertexToTrueSRVertex (α := α) (σ := σ)) := by
  intro a b hab
  cases a with
  | inl s =>
      cases b with
      | inl t =>
          apply congrArg Sum.inl
          exact Subtype.ext (Sum.inl.inj hab)
      | inr ρ => cases hab
  | inr ρ =>
      cases b with
      | inl s => cases hab
      | inr q =>
          apply congrArg Sum.inr
          apply Subtype.ext
          change
            Sum.inr (⟨ρ.1, N.activeAggregateTrueReaction_internal ρ⟩ :
              N.InternalTrueReaction) =
            Sum.inr (⟨q.1, N.activeAggregateTrueReaction_internal q⟩ :
              N.InternalTrueReaction) at hab
          have hinternal :
              (⟨ρ.1, N.activeAggregateTrueReaction_internal ρ⟩ : N.InternalTrueReaction) =
                ⟨q.1, N.activeAggregateTrueReaction_internal q⟩ := Sum.inr.inj hab
          exact congrArg (fun x : N.InternalTrueReaction => x.1) hinternal

/-- Every adjacency in the underlying aggregate source graph is witnessed by a labeled edge
of the true-chemistry SR graph. The causal orientation determines the sign, while the edge
itself is undirected. -/
private theorem aggregateSourceAdj_has_trueSREdge (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ))
    (u v : {x : N.TrueInternalAggregateVertex α σ // x ∈ T})
    (h : (CRNT.relationGraphOn
      (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T).Adj u v) :
    ∃ e : N.TrueSREdge,
      e.Connects (N.aggregateVertexToTrueSRVertex u.1)
        (N.aggregateVertexToTrueSRVertex v.1) := by
  change u.1 ≠ v.1 ∧
    (N.TrueInternalAggregateCausalEdge u.1 v.1 ∨
      N.TrueInternalAggregateCausalEdge v.1 u.1) at h
  rcases h with ⟨_, hrel⟩
  cases hu : u.1 with
  | inl s =>
      cases hv : v.1 with
      | inl s' =>
          have : False := by
            simpa [TrueInternalAggregateCausalEdge, hu, hv] using hrel
          exact this.elim
      | inr ρ =>
          have hflux : N.trueInternalClassFlux α ρ.1 s.1 ≠ 0 := by
            intro hz
            rcases hrel with hneg | hpos
            · have hneg' :
                N.trueInternalClassFlux α ρ.1 s.1 * σ s.1 < 0 := by
                  simpa [TrueInternalAggregateCausalEdge, hu, hv] using hneg
              rw [hz, zero_mul] at hneg'
              exact (lt_irrefl 0) hneg'
            · have hpos' :
                0 < N.trueInternalClassFlux α ρ.1 s.1 * σ s.1 := by
                  simpa [TrueInternalAggregateCausalEdge, hu, hv] using hpos
              rw [hz, zero_mul] at hpos'
              exact (lt_irrefl 0) hpos'
          obtain ⟨e, hes, her⟩ :=
            N.exists_trueSREdge_of_nonzero_trueInternalClassFlux ρ.1 s.1 hflux
          have hreaction :
              (⟨e.reaction, e.internal⟩ : N.InternalTrueReaction) =
                ⟨ρ.1, N.activeAggregateTrueReaction_internal ρ⟩ :=
            Subtype.ext her
          refine ⟨e, Or.inl ⟨?_, ?_⟩⟩
          · exact congrArg Sum.inl hes.symm
          · exact congrArg Sum.inr hreaction.symm
  | inr ρ =>
      cases hv : v.1 with
      | inl s =>
          have hflux : N.trueInternalClassFlux α ρ.1 s.1 ≠ 0 := by
            intro hz
            rcases hrel with hpos | hneg
            · have hpos' :
                0 < N.trueInternalClassFlux α ρ.1 s.1 * σ s.1 := by
                  simpa [TrueInternalAggregateCausalEdge, hu, hv] using hpos
              rw [hz, zero_mul] at hpos'
              exact (lt_irrefl 0) hpos'
            · have hneg' :
                N.trueInternalClassFlux α ρ.1 s.1 * σ s.1 < 0 := by
                  simpa [TrueInternalAggregateCausalEdge, hu, hv] using hneg
              rw [hz, zero_mul] at hneg'
              exact (lt_irrefl 0) hneg'
          obtain ⟨e, hes, her⟩ :=
            N.exists_trueSREdge_of_nonzero_trueInternalClassFlux ρ.1 s.1 hflux
          have hreaction :
              (⟨e.reaction, e.internal⟩ : N.InternalTrueReaction) =
                ⟨ρ.1, N.activeAggregateTrueReaction_internal ρ⟩ :=
            Subtype.ext her
          refine ⟨e, Or.inr ⟨?_, ?_⟩⟩
          · exact congrArg Sum.inr hreaction.symm
          · exact congrArg Sum.inl hes.symm
      | inr ρ' =>
          have : False := by
            simpa [TrueInternalAggregateCausalEdge, hu, hv] using hrel
          exact this.elim

/-- A simple path in the underlying aggregate source graph lifts to a labeled path in the
true-chemistry SR graph. This preserves vertex simplicity and records a concrete SR incidence
for each nonzero aggregate class flux. -/
private noncomputable def aggregateSourcePathToTrueSRPath (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ))
    {s : AggregateActiveSpecies σ} {ρ : N.ActiveAggregateTrueReaction α σ}
    (hsT : Sum.inl s ∈ T) (hρT : Sum.inr ρ ∈ T)
    (p : (CRNT.relationGraphOn
      (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T).Walk
        ⟨Sum.inl s, hsT⟩ ⟨Sum.inr ρ, hρT⟩)
    (hp : p.IsPath) : N.TrueSRPath p.length := by
  classical
  let vertex (i : Fin (p.length + 1)) : N.TrueSRVertex :=
    N.aggregateVertexToTrueSRVertex (p.getVert i.1).1
  let edgeWitness (i : Fin p.length) :=
    N.aggregateSourceAdj_has_trueSREdge T (p.getVert i.1) (p.getVert (i.1 + 1))
      (p.adj_getVert_succ i.2)
  let edge (i : Fin p.length) : N.TrueSREdge := Classical.choose (edgeWitness i)
  have hconnect (i : Fin p.length) :
      edge i |>.Connects
        (N.aggregateVertexToTrueSRVertex (p.getVert i.1).1)
        (N.aggregateVertexToTrueSRVertex (p.getVert (i.1 + 1)).1) :=
    Classical.choose_spec (edgeWitness i)
  have hstartEndNe :
      (⟨Sum.inl s, hsT⟩ : {x : N.TrueInternalAggregateVertex α σ // x ∈ T}) ≠
        ⟨Sum.inr ρ, hρT⟩ := by
    intro h
    exact Sum.inl_ne_inr (congrArg Subtype.val h)
  have hlength : 0 < p.length :=
    (SimpleGraph.Walk.not_nil_iff_lt_length).mp (p.not_nil_of_ne hstartEndNe)
  refine {
    length_pos := hlength
    edge := edge
    vertex := vertex
    connects := ?_
    edge_simple := ?_
    vertex_simple := ?_
    starts_at_species := ?_
    ends_at_reaction := ?_
  }
  · intro i
    simpa [edge, vertex, edgeWitness, Fin.castSucc, Fin.succ] using hconnect i
  · intro i j hsame
    have hspecies := hsame.1
    have hreac := hsame.2.1
    have hinternal :
        (⟨(edge i).reaction, (edge i).internal⟩ : N.InternalTrueReaction) =
          ⟨(edge j).reaction, (edge j).internal⟩ := Subtype.ext hreac
    have hci := hconnect i
    have hcj := hconnect j
    have hpairs :
        (vertex (Fin.castSucc i) = vertex (Fin.castSucc j) ∧
          vertex i.succ = vertex j.succ) ∨
        (vertex (Fin.castSucc i) = vertex j.succ ∧
          vertex i.succ = vertex (Fin.castSucc j)) := by
      rcases hci with ⟨hi0, hi1⟩ | ⟨hi0, hi1⟩ <;>
        rcases hcj with ⟨hj0, hj1⟩ | ⟨hj0, hj1⟩
      · exact Or.inl ⟨hi0.trans ((congrArg Sum.inl hspecies).trans hj0.symm),
          hi1.trans ((congrArg Sum.inr hinternal).trans hj1.symm)⟩
      · exact Or.inr ⟨hi0.trans ((congrArg Sum.inl hspecies).trans hj1.symm),
          hi1.trans ((congrArg Sum.inr hinternal).trans hj0.symm)⟩
      · exact Or.inr ⟨hi0.trans ((congrArg Sum.inr hinternal).trans hj1.symm),
          hi1.trans ((congrArg Sum.inl hspecies).trans hj0.symm)⟩
      · exact Or.inl ⟨hi0.trans ((congrArg Sum.inr hinternal).trans hj0.symm),
          hi1.trans ((congrArg Sum.inl hspecies).trans hj1.symm)⟩
    have hvertexEq (a b : Fin (p.length + 1)) (hab : vertex a = vertex b) :
        p.getVert a.1 = p.getVert b.1 := by
      apply Subtype.ext
      exact N.aggregateVertexToTrueSRVertex_injective (by simpa [vertex] using hab)
    rcases hpairs with ⟨h00, h11⟩ | ⟨h01, h10⟩
    · have hij := hp.getVert_injOn (Nat.le_of_lt i.2) (Nat.le_of_lt j.2)
        (hvertexEq (Fin.castSucc i) (Fin.castSucc j) h00)
      exact Fin.ext hij
    · have hcross₁ := hp.getVert_injOn (Nat.le_of_lt i.2) (Nat.succ_le_of_lt j.2)
        (hvertexEq (Fin.castSucc i) j.succ h01)
      have hcross₂ := hp.getVert_injOn (Nat.succ_le_of_lt i.2) (Nat.le_of_lt j.2)
        (hvertexEq i.succ (Fin.castSucc j) h10)
      have hi : i.1 = j.1 + 1 := by simpa using hcross₁
      have hj : i.1 + 1 = j.1 := by simpa using hcross₂
      omega
  · intro i j hij
    apply Fin.ext
    have hmap := N.aggregateVertexToTrueSRVertex_injective (by simpa [vertex] using hij)
    exact hp.getVert_injOn (Nat.le_of_lt_succ i.2) (Nat.le_of_lt_succ j.2)
      (Subtype.ext hmap)
  · refine ⟨s.1, ?_⟩
    change N.aggregateVertexToTrueSRVertex (p.getVert 0).1 = Sum.inl s.1
    rw [p.getVert_zero]
    rfl
  · refine ⟨⟨ρ.1, N.activeAggregateTrueReaction_internal ρ⟩, ?_⟩
    change N.aggregateVertexToTrueSRVertex (p.getVert p.length).1 =
      Sum.inr ⟨ρ.1, N.activeAggregateTrueReaction_internal ρ⟩
    rw [p.getVert_length]
    rfl




/-! ### Lifting a directed causal path

`aggregateSourcePathToTrueSRPath` and its species-ended sibling consume `SimpleGraph.Walk`s,
which forget the orientation of the causal relation.  The parity bookkeeping for an even chord
needs the orientation, so these two lift a `CRNT.RelPath` — a *directed* indexed path — instead.
Injectivity is a hypothesis here rather than a consequence of `IsPath`, and the adjacency at
each step comes from `RelPath.step` together with that injectivity. -/

private theorem relPathAdj (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ)) {k : ℕ}
    (P : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T k)
    (hinj : Function.Injective P.vertex) (i : Fin k) :
    (CRNT.relationGraphOn
      (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T).Adj
        ⟨P.vertex (Fin.castSucc i), P.mem _⟩ ⟨P.vertex i.succ, P.mem _⟩ := by
  refine ⟨?_, Or.inl (P.step i)⟩
  intro hveq
  have hv : (Fin.castSucc i).1 = (i.succ).1 := congrArg Fin.val (hinj hveq)
  have h1 : (Fin.castSucc i).1 = i.1 := rfl
  have h2 : (i.succ).1 = i.1 + 1 := rfl
  omega

/-- A directed causal path from a species vertex to a reaction vertex lifts to a labeled
species-to-reaction path of the true-chemistry SR graph. -/
private noncomputable def relPathToTrueSRPath (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ)) {k : ℕ}
    (P : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T k)
    (hinj : Function.Injective P.vertex) (hk : 0 < k)
    {s : AggregateActiveSpecies σ} {ρ : N.ActiveAggregateTrueReaction α σ}
    (h0 : P.vertex ⟨0, by omega⟩ = Sum.inl s)
    (hlast : P.vertex ⟨k, by omega⟩ = Sum.inr ρ) : N.TrueSRPath k := by
  classical
  let vertex (i : Fin (k + 1)) : N.TrueSRVertex :=
    N.aggregateVertexToTrueSRVertex (P.vertex i)
  let edgeWitness (i : Fin k) :=
    N.aggregateSourceAdj_has_trueSREdge T
      ⟨P.vertex (Fin.castSucc i), P.mem _⟩ ⟨P.vertex i.succ, P.mem _⟩
      (N.relPathAdj T P hinj i)
  let edge (i : Fin k) : N.TrueSREdge := Classical.choose (edgeWitness i)
  have hconnect (i : Fin k) :
      edge i |>.Connects (vertex (Fin.castSucc i)) (vertex i.succ) :=
    Classical.choose_spec (edgeWitness i)
  have hvertexInj : Function.Injective vertex := by
    intro a b hab
    exact hinj (N.aggregateVertexToTrueSRVertex_injective hab)
  refine {
    length_pos := hk
    edge := edge
    vertex := vertex
    connects := hconnect
    edge_simple := ?_
    vertex_simple := hvertexInj
    starts_at_species := ?_
    ends_at_reaction := ?_
  }
  · intro i j hsame
    have hspecies := hsame.1
    have hreac := hsame.2.1
    have hinternal :
        (⟨(edge i).reaction, (edge i).internal⟩ : N.InternalTrueReaction) =
          ⟨(edge j).reaction, (edge j).internal⟩ := Subtype.ext hreac
    have hci := hconnect i
    have hcj := hconnect j
    have hpairs :
        (vertex (Fin.castSucc i) = vertex (Fin.castSucc j) ∧
          vertex i.succ = vertex j.succ) ∨
        (vertex (Fin.castSucc i) = vertex j.succ ∧
          vertex i.succ = vertex (Fin.castSucc j)) := by
      rcases hci with ⟨hi0, hi1⟩ | ⟨hi0, hi1⟩ <;>
        rcases hcj with ⟨hj0, hj1⟩ | ⟨hj0, hj1⟩
      · exact Or.inl ⟨hi0.trans ((congrArg Sum.inl hspecies).trans hj0.symm),
          hi1.trans ((congrArg Sum.inr hinternal).trans hj1.symm)⟩
      · exact Or.inr ⟨hi0.trans ((congrArg Sum.inl hspecies).trans hj1.symm),
          hi1.trans ((congrArg Sum.inr hinternal).trans hj0.symm)⟩
      · exact Or.inr ⟨hi0.trans ((congrArg Sum.inr hinternal).trans hj1.symm),
          hi1.trans ((congrArg Sum.inl hspecies).trans hj0.symm)⟩
      · exact Or.inl ⟨hi0.trans ((congrArg Sum.inr hinternal).trans hj0.symm),
          hi1.trans ((congrArg Sum.inl hspecies).trans hj1.symm)⟩
    rcases hpairs with ⟨h00, _⟩ | ⟨h01, h10⟩
    · have h := hvertexInj h00
      have hv := congrArg Fin.val h
      have e1 : (Fin.castSucc i).1 = i.1 := rfl
      have e3 : (Fin.castSucc j).1 = j.1 := rfl
      exact Fin.ext (by omega)
    · have hx := congrArg Fin.val (hvertexInj h01)
      have hy := congrArg Fin.val (hvertexInj h10)
      have e1 : (Fin.castSucc i).1 = i.1 := rfl
      have e2 : (i.succ).1 = i.1 + 1 := rfl
      have e3 : (Fin.castSucc j).1 = j.1 := rfl
      have e4 : (j.succ).1 = j.1 + 1 := rfl
      omega
  · refine ⟨s.1, ?_⟩
    show N.aggregateVertexToTrueSRVertex (P.vertex 0) = Sum.inl s.1
    rw [show (0 : Fin (k + 1)) = ⟨0, by omega⟩ from Fin.ext rfl, h0]
    rfl
  · refine ⟨⟨ρ.1, N.activeAggregateTrueReaction_internal ρ⟩, ?_⟩
    show N.aggregateVertexToTrueSRVertex (P.vertex (Fin.last k)) =
      Sum.inr ⟨ρ.1, N.activeAggregateTrueReaction_internal ρ⟩
    rw [show (Fin.last k) = ⟨k, by omega⟩ from Fin.ext rfl, hlast]
    rfl

/-- A directed causal path between two species vertices lifts to a labeled
species-to-species path of the true-chemistry SR graph. -/
private noncomputable def relPathToTrueSRSSPath (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ)) {k : ℕ}
    (P : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T k)
    (hinj : Function.Injective P.vertex) (hk : 0 < k)
    {s s' : AggregateActiveSpecies σ}
    (h0 : P.vertex ⟨0, by omega⟩ = Sum.inl s)
    (hlast : P.vertex ⟨k, by omega⟩ = Sum.inl s') : N.TrueSRSSPath k := by
  classical
  let vertex (i : Fin (k + 1)) : N.TrueSRVertex :=
    N.aggregateVertexToTrueSRVertex (P.vertex i)
  let edgeWitness (i : Fin k) :=
    N.aggregateSourceAdj_has_trueSREdge T
      ⟨P.vertex (Fin.castSucc i), P.mem _⟩ ⟨P.vertex i.succ, P.mem _⟩
      (N.relPathAdj T P hinj i)
  let edge (i : Fin k) : N.TrueSREdge := Classical.choose (edgeWitness i)
  have hconnect (i : Fin k) :
      edge i |>.Connects (vertex (Fin.castSucc i)) (vertex i.succ) :=
    Classical.choose_spec (edgeWitness i)
  have hvertexInj : Function.Injective vertex := by
    intro a b hab
    exact hinj (N.aggregateVertexToTrueSRVertex_injective hab)
  refine {
    length_pos := hk
    edge := edge
    vertex := vertex
    connects := hconnect
    edge_simple := ?_
    vertex_simple := hvertexInj
    starts_at_species := ?_
    ends_at_species := ?_
  }
  · intro i j hsame
    have hspecies := hsame.1
    have hreac := hsame.2.1
    have hinternal :
        (⟨(edge i).reaction, (edge i).internal⟩ : N.InternalTrueReaction) =
          ⟨(edge j).reaction, (edge j).internal⟩ := Subtype.ext hreac
    have hci := hconnect i
    have hcj := hconnect j
    have hpairs :
        (vertex (Fin.castSucc i) = vertex (Fin.castSucc j) ∧
          vertex i.succ = vertex j.succ) ∨
        (vertex (Fin.castSucc i) = vertex j.succ ∧
          vertex i.succ = vertex (Fin.castSucc j)) := by
      rcases hci with ⟨hi0, hi1⟩ | ⟨hi0, hi1⟩ <;>
        rcases hcj with ⟨hj0, hj1⟩ | ⟨hj0, hj1⟩
      · exact Or.inl ⟨hi0.trans ((congrArg Sum.inl hspecies).trans hj0.symm),
          hi1.trans ((congrArg Sum.inr hinternal).trans hj1.symm)⟩
      · exact Or.inr ⟨hi0.trans ((congrArg Sum.inl hspecies).trans hj1.symm),
          hi1.trans ((congrArg Sum.inr hinternal).trans hj0.symm)⟩
      · exact Or.inr ⟨hi0.trans ((congrArg Sum.inr hinternal).trans hj1.symm),
          hi1.trans ((congrArg Sum.inl hspecies).trans hj0.symm)⟩
      · exact Or.inl ⟨hi0.trans ((congrArg Sum.inr hinternal).trans hj0.symm),
          hi1.trans ((congrArg Sum.inl hspecies).trans hj1.symm)⟩
    rcases hpairs with ⟨h00, _⟩ | ⟨h01, h10⟩
    · have h := hvertexInj h00
      have hv := congrArg Fin.val h
      have e1 : (Fin.castSucc i).1 = i.1 := rfl
      have e3 : (Fin.castSucc j).1 = j.1 := rfl
      exact Fin.ext (by omega)
    · have hx := congrArg Fin.val (hvertexInj h01)
      have hy := congrArg Fin.val (hvertexInj h10)
      have e1 : (Fin.castSucc i).1 = i.1 := rfl
      have e2 : (i.succ).1 = i.1 + 1 := rfl
      have e3 : (Fin.castSucc j).1 = j.1 := rfl
      have e4 : (j.succ).1 = j.1 + 1 := rfl
      omega
  · refine ⟨s.1, ?_⟩
    show N.aggregateVertexToTrueSRVertex (P.vertex 0) = Sum.inl s.1
    rw [show (0 : Fin (k + 1)) = ⟨0, by omega⟩ from Fin.ext rfl, h0]
    rfl
  · refine ⟨s'.1, ?_⟩
    show N.aggregateVertexToTrueSRVertex (P.vertex (Fin.last k)) = Sum.inl s'.1
    rw [show (Fin.last k) = ⟨k, by omega⟩ from Fin.ext rfl, hlast]
    rfl


/-- Adjacency of a directed path read backwards. -/
private theorem relPathAdjRev (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ)) {k : ℕ}
    (P : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T k)
    (hinj : Function.Injective P.vertex) (i : Fin k) :
    (CRNT.relationGraphOn
      (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T).Adj
        ⟨P.vertex ⟨k - (Fin.castSucc i).1, by have := i.isLt; omega⟩, P.mem _⟩
        ⟨P.vertex ⟨k - (i.succ).1, by have := i.isLt; omega⟩, P.mem _⟩ := by
  have hi := i.isLt
  have hcs : (Fin.castSucc i).1 = i.1 := rfl
  have hsu : (i.succ).1 = i.1 + 1 := rfl
  refine ⟨?_, Or.inr ?_⟩
  · intro hveq
    have hv := congrArg Fin.val (hinj hveq)
    simp only at hv
    omega
  · have hst := P.step ⟨k - (i.1 + 1), by omega⟩
    have e1 : (Fin.castSucc (⟨k - (i.1 + 1), by omega⟩ : Fin k))
        = (⟨k - (i.succ).1, by omega⟩ : Fin (k + 1)) :=
      Fin.ext (by show k - (i.1 + 1) = k - (i.succ).1; omega)
    have e2 : ((⟨k - (i.1 + 1), by omega⟩ : Fin k).succ)
        = (⟨k - (Fin.castSucc i).1, by omega⟩ : Fin (k + 1)) :=
      Fin.ext (by show k - (i.1 + 1) + 1 = k - (Fin.castSucc i).1; omega)
    rw [e1, e2] at hst
    exact hst

/-- A directed causal path from a reaction vertex to a species vertex, read backwards, lifts to
a species-to-reaction path of the true-chemistry SR graph.  The lifts read a path from its
species end, so a chord whose directed start is a reaction vertex needs this variant. -/
private noncomputable def relPathToTrueSRPathRev (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ)) {k : ℕ}
    (P : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T k)
    (hinj : Function.Injective P.vertex) (hk : 0 < k)
    {s : AggregateActiveSpecies σ} {ρ : N.ActiveAggregateTrueReaction α σ}
    (h0 : P.vertex ⟨k, by omega⟩ = Sum.inl s)
    (hlast : P.vertex ⟨0, by omega⟩ = Sum.inr ρ) : N.TrueSRPath k := by
  classical
  let vertex (i : Fin (k + 1)) : N.TrueSRVertex :=
    N.aggregateVertexToTrueSRVertex (P.vertex ⟨k - i.1, by have := i.isLt; omega⟩)
  let edgeWitness (i : Fin k) :=
    N.aggregateSourceAdj_has_trueSREdge T
      ⟨P.vertex ⟨k - (Fin.castSucc i).1, by have := i.isLt; omega⟩, P.mem _⟩
      ⟨P.vertex ⟨k - (i.succ).1, by have := i.isLt; omega⟩, P.mem _⟩
      (N.relPathAdjRev T P hinj i)
  let edge (i : Fin k) : N.TrueSREdge := Classical.choose (edgeWitness i)
  have hconnect (i : Fin k) :
      edge i |>.Connects (vertex (Fin.castSucc i)) (vertex i.succ) :=
    Classical.choose_spec (edgeWitness i)
  have hvertexInj : Function.Injective vertex := by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    have h := hinj (N.aggregateVertexToTrueSRVertex_injective hab)
    have hv := congrArg Fin.val h
    simp only at hv
    exact Fin.ext (by omega)
  refine {
    length_pos := hk
    edge := edge
    vertex := vertex
    connects := hconnect
    edge_simple := ?_
    vertex_simple := hvertexInj
    starts_at_species := ?_
    ends_at_reaction := ?_
  }
  · intro i j hsame
    have hspecies := hsame.1
    have hreac := hsame.2.1
    have hinternal :
        (⟨(edge i).reaction, (edge i).internal⟩ : N.InternalTrueReaction) =
          ⟨(edge j).reaction, (edge j).internal⟩ := Subtype.ext hreac
    have hci := hconnect i
    have hcj := hconnect j
    have hpairs :
        (vertex (Fin.castSucc i) = vertex (Fin.castSucc j) ∧
          vertex i.succ = vertex j.succ) ∨
        (vertex (Fin.castSucc i) = vertex j.succ ∧
          vertex i.succ = vertex (Fin.castSucc j)) := by
      rcases hci with ⟨hi0, hi1⟩ | ⟨hi0, hi1⟩ <;>
        rcases hcj with ⟨hj0, hj1⟩ | ⟨hj0, hj1⟩
      · exact Or.inl ⟨hi0.trans ((congrArg Sum.inl hspecies).trans hj0.symm),
          hi1.trans ((congrArg Sum.inr hinternal).trans hj1.symm)⟩
      · exact Or.inr ⟨hi0.trans ((congrArg Sum.inl hspecies).trans hj1.symm),
          hi1.trans ((congrArg Sum.inr hinternal).trans hj0.symm)⟩
      · exact Or.inr ⟨hi0.trans ((congrArg Sum.inr hinternal).trans hj1.symm),
          hi1.trans ((congrArg Sum.inl hspecies).trans hj0.symm)⟩
      · exact Or.inl ⟨hi0.trans ((congrArg Sum.inr hinternal).trans hj0.symm),
          hi1.trans ((congrArg Sum.inl hspecies).trans hj1.symm)⟩
    have hilt := i.isLt
    have hjlt := j.isLt
    rcases hpairs with ⟨h00, _⟩ | ⟨h01, h10⟩
    · have hv := congrArg Fin.val (hvertexInj h00)
      have e1 : (Fin.castSucc i).1 = i.1 := rfl
      have e3 : (Fin.castSucc j).1 = j.1 := rfl
      exact Fin.ext (by omega)
    · have hx := congrArg Fin.val (hvertexInj h01)
      have hy := congrArg Fin.val (hvertexInj h10)
      have e1 : (Fin.castSucc i).1 = i.1 := rfl
      have e2 : (i.succ).1 = i.1 + 1 := rfl
      have e3 : (Fin.castSucc j).1 = j.1 := rfl
      have e4 : (j.succ).1 = j.1 + 1 := rfl
      omega
  · refine ⟨s.1, ?_⟩
    show N.aggregateVertexToTrueSRVertex
      (P.vertex ⟨k - ((0 : Fin (k + 1))).1, by omega⟩) = Sum.inl s.1
    rw [show (⟨k - ((0 : Fin (k + 1))).1, by omega⟩ : Fin (k + 1)) = ⟨k, by omega⟩ from
      Fin.ext (by show k - 0 = k; omega), h0]
    rfl
  · refine ⟨⟨ρ.1, N.activeAggregateTrueReaction_internal ρ⟩, ?_⟩
    show N.aggregateVertexToTrueSRVertex
      (P.vertex ⟨k - (Fin.last k).1, by omega⟩) =
      Sum.inr ⟨ρ.1, N.activeAggregateTrueReaction_internal ρ⟩
    rw [show (⟨k - (Fin.last k).1, by omega⟩ : Fin (k + 1)) = ⟨0, by omega⟩ from
      Fin.ext (by show k - k = 0; omega), hlast]
    rfl

private theorem relPathToTrueSRPathRev_vertex (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ)) {k : ℕ}
    (P : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T k)
    (hinj : Function.Injective P.vertex) (hk : 0 < k)
    {s : AggregateActiveSpecies σ} {ρ : N.ActiveAggregateTrueReaction α σ}
    (h0 : P.vertex ⟨k, by omega⟩ = Sum.inl s)
    (hlast : P.vertex ⟨0, by omega⟩ = Sum.inr ρ) (i : Fin (k + 1)) :
    (N.relPathToTrueSRPathRev T P hinj hk h0 hlast).vertex i =
      N.aggregateVertexToTrueSRVertex
        (P.vertex ⟨k - i.1, by have := i.isLt; omega⟩) := rfl


/-- Prefix a source path from an off-cycle reaction class with its edge to a cycle species.
When all vertices of the source path before its terminal reaction avoid the cycle, this gives an
edge-disjoint chord whose interior avoids the cycle. -/
private theorem aggregateSourceReactionPath_prefix_chord (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} {n : ℕ}
    (T : Finset (N.TrueInternalAggregateVertex α σ))
    (C : N.TrueSRCycle n)
    {s : AggregateActiveSpecies σ} {q qC : N.ActiveAggregateTrueReaction α σ}
    (hsT : Sum.inl s ∈ T) (hqT : Sum.inr q ∈ T) (hqCT : Sum.inr qC ∈ T)
    (hsCycle : C.HasSpecies s.1) (hqCCycle : C.HasReaction qC.1)
    (hqOffCycle : ¬ C.HasReaction q.1)
    (hqs : N.TrueInternalAggregateCausalEdge (Sum.inr q) (Sum.inl s))
    (p : (CRNT.relationGraphOn
      (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T).Walk
        ⟨Sum.inr q, hqT⟩ ⟨Sum.inr qC, hqCT⟩)
    (hp : p.IsPath)
    (hinterior : ∀ j, j < p.length →
      ¬ C.HasVertex (N.aggregateVertexToTrueSRVertex (p.getVert j).1)) :
    ∃ P : N.TrueSRPath (p.length + 1),
      C.IsChord P ∧
      P.vertex 0 = Sum.inl s.1 ∧
      P.vertex (Fin.last (p.length + 1)) = Sum.inr
        ⟨qC.1, N.activeAggregateTrueReaction_internal qC⟩ ∧
      (∀ j : Fin (p.length + 1 + 1), j.1 ≠ 0 → j.1 ≠ p.length + 1 →
        ¬ C.HasVertex (P.vertex j)) := by
  classical
  have hn : 2 ≤ n := C.nontrivial
  let result : ℕ → Prop := fun m =>
    ∃ P : N.TrueSRPath m,
      C.IsChord P ∧
      P.vertex 0 = Sum.inl s.1 ∧
      P.vertex (Fin.last m) = Sum.inr
        ⟨qC.1, N.activeAggregateTrueReaction_internal qC⟩ ∧
      (∀ j : Fin (m + 1), j.1 ≠ 0 → j.1 ≠ m → ¬ C.HasVertex (P.vertex j))
  let qv : {v : N.TrueInternalAggregateVertex α σ // v ∈ T} := ⟨Sum.inr q, hqT⟩
  let sv : {v : N.TrueInternalAggregateVertex α σ // v ∈ T} := ⟨Sum.inl s, hsT⟩
  have hadj : (CRNT.relationGraphOn
      (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T).Adj sv qv := by
    refine ⟨?_, Or.inr hqs⟩
    exact Sum.inl_ne_inr
  let p' := SimpleGraph.Walk.cons hadj p
  have hsNotMem : sv ∉ p.support := by
    intro hmem
    obtain ⟨j, hjEq, hjle⟩ :=
      (SimpleGraph.Walk.mem_support_iff_exists_getVert (p := p)).mp hmem
    by_cases hj : j < p.length
    · apply hinterior j hj
      change C.HasVertex (N.aggregateVertexToTrueSRVertex (p.getVert j).1)
      rw [hjEq]
      change C.HasSpecies s.1
      exact hsCycle
    · have hjlen : j = p.length := by omega
      subst j
      have hval : Sum.inl s = Sum.inr qC := by
        have hEq : sv = p.getVert p.length := hjEq.symm
        have hEq' := hEq.trans p.getVert_length
        have hval := congrArg Subtype.val hEq'
        simpa [sv] using hval
      exact Sum.inl_ne_inr hval
  have hp' : p'.IsPath := (SimpleGraph.Walk.cons_isPath_iff hadj p).2 ⟨hp, hsNotMem⟩
  let P := N.aggregateSourcePathToTrueSRPath T hsT hqCT p' hp'
  have hlen : p'.length = p.length + 1 := by simp [p']
  have hstart : P.vertex 0 = Sum.inl s.1 := by
    change N.aggregateVertexToTrueSRVertex (p'.getVert 0).1 = Sum.inl s.1
    rw [p'.getVert_zero]
    rfl
  have hend : P.vertex (Fin.last p'.length) =
      Sum.inr ⟨qC.1, N.activeAggregateTrueReaction_internal qC⟩ := by
    change N.aggregateVertexToTrueSRVertex (p'.getVert p'.length).1 = _
    rw [p'.getVert_length]
    rfl
  have hqNeqC : q ≠ qC := by
    intro h
    apply hqOffCycle
    simpa [h] using hqCCycle
  have hsourceEndpointsNe :
      (⟨Sum.inr q, hqT⟩ : {v : N.TrueInternalAggregateVertex α σ // v ∈ T}) ≠
        ⟨Sum.inr qC, hqCT⟩ := by
    intro h
    apply hqNeqC
    exact Sum.inr.inj (congrArg Subtype.val h)
  have hpPositive : 0 < p.length :=
    (SimpleGraph.Walk.not_nil_iff_lt_length).mp (p.not_nil_of_ne hsourceEndpointsNe)
  have hinteriorP :
      ∀ j : Fin (p'.length + 1), j.1 ≠ 0 → j.1 ≠ p'.length →
        ¬ C.HasVertex (P.vertex j) := by
    intro j hj0 hjend hCj
    have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hj0
    have hjlt : j.1 - 1 < p.length := by
      have hjle : j.1 ≤ p'.length := by omega
      have hjltlen : j.1 < p'.length := by omega
      have hjltlen' : j.1 < p.length + 1 := by simpa [p'] using hjltlen
      omega
    have hget : p'.getVert j.1 = p.getVert (j.1 - 1) := by
      simpa [p'] using
        (SimpleGraph.Walk.getVert_cons p hadj (Nat.ne_of_gt hjpos))
    change C.HasVertex (N.aggregateVertexToTrueSRVertex (p'.getVert j.1).1) at hCj
    rw [hget] at hCj
    exact hinterior (j.1 - 1) hjlt hCj
  have hstartSpecies : C.HasSpecies P.startSpecies := by
    have hsEq : P.startSpecies = s.1 := by
      apply Sum.inl.inj
      calc
        Sum.inl P.startSpecies = P.vertex 0 := P.vertex_zero.symm
        _ = Sum.inl s.1 := hstart
    obtain ⟨j, hj⟩ := hsCycle
    exact ⟨j, hj.trans hsEq.symm⟩
  have hendReaction : C.HasReaction P.endReaction.1 := by
    have hrEq : P.endReaction =
        (⟨qC.1, N.activeAggregateTrueReaction_internal qC⟩ : N.InternalTrueReaction) := by
      apply Sum.inr.inj
      calc
        Sum.inr P.endReaction = P.vertex (Fin.last p'.length) := P.vertex_last.symm
        _ = Sum.inr ⟨qC.1, N.activeAggregateTrueReaction_internal qC⟩ := hend
    obtain ⟨j, hj⟩ := hqCCycle
    exact ⟨j, hj.trans (congrArg Subtype.val hrEq).symm⟩
  have hpathLengthAtLeastTwo : 2 ≤ p'.length := by
    rw [hlen]
    omega
  have hinteriorEndpoint : ∀ a : Fin p'.length,
      C.HasVertex (P.vertex (Fin.castSucc a)) →
      C.HasVertex (P.vertex a.succ) → False := by
    intro a hstartC hendC
    by_cases ha0 : a.1 = 0
    · have hj0 : (a.succ).1 ≠ 0 := by simp [ha0]
      have hjL : (a.succ).1 ≠ p'.length := by
        have hval : (a.succ).1 = 1 := by simp [ha0]
        rw [hval]
        omega
      exact (hinteriorP a.succ hj0 hjL) hendC
    · have hj0 : (Fin.castSucc a).1 ≠ 0 := by simpa using ha0
      have hjL : (Fin.castSucc a).1 ≠ p'.length := by
        have hlt := a.isLt
        simp only [Fin.coe_castSucc]
        omega
      exact (hinteriorP (Fin.castSucc a) hj0 hjL) hstartC
  have hcycleEdgeLeftDisjoint : ∀ a t,
      ¬ (P.edge a).SameIncidence (C.leftEdge t) := by
    intro a t hsame
    have hsp : C.HasVertex (Sum.inl (P.edge a).species) := by
      change C.HasSpecies (P.edge a).species
      exact ⟨t, (C.left_species t).symm.trans hsame.1.symm⟩
    have hrx : C.HasVertex
        (Sum.inr ⟨(P.edge a).reaction, (P.edge a).internal⟩) := by
      change C.HasReaction (P.edge a).reaction
      exact ⟨t, (C.left_reaction t).symm.trans hsame.2.1.symm⟩
    rcases P.connects a with ⟨ha0, ha1⟩ | ⟨ha0, ha1⟩
    · exact hinteriorEndpoint a (by rw [ha0]; exact hsp) (by rw [ha1]; exact hrx)
    · exact hinteriorEndpoint a (by rw [ha0]; exact hrx) (by rw [ha1]; exact hsp)
  have hcycleEdgeRightDisjoint : ∀ a t,
      ¬ (P.edge a).SameIncidence (C.rightEdge t) := by
    intro a t hsame
    have hsp : C.HasVertex (Sum.inl (P.edge a).species) := by
      change C.HasSpecies (P.edge a).species
      exact ⟨⟨(t.1 + 1) % n, Nat.mod_lt _ (by omega)⟩,
        (C.right_species t).symm.trans hsame.1.symm⟩
    have hrx : C.HasVertex
        (Sum.inr ⟨(P.edge a).reaction, (P.edge a).internal⟩) := by
      change C.HasReaction (P.edge a).reaction
      exact ⟨t, (C.right_reaction t).symm.trans hsame.2.1.symm⟩
    rcases P.connects a with ⟨ha0, ha1⟩ | ⟨ha0, ha1⟩
    · exact hinteriorEndpoint a (by rw [ha0]; exact hsp) (by rw [ha1]; exact hrx)
    · exact hinteriorEndpoint a (by rw [ha0]; exact hrx) (by rw [ha1]; exact hsp)
  have hchord : C.IsChord P :=
    ⟨hstartSpecies, hendReaction, hcycleEdgeLeftDisjoint, hcycleEdgeRightDisjoint⟩
  have hresult : result p'.length := by
    dsimp [result]
    exact ⟨P, hchord, hstart, hend, hinteriorP⟩
  change result (p.length + 1)
  exact hlen ▸ hresult

/-- At every active species, the strict total flux supplies a positive edge from an active
aggregate reaction class. -/
private theorem exists_positive_aggregateClass_predecessor (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (s : AggregateActiveSpecies σ) :
    ∃ ρ : N.ActiveAggregateTrueReaction α σ,
      N.TrueInternalAggregateCausalEdge (Sum.inr ρ) (Sum.inl s) := by
  classical
  have hsum : 0 < ∑ ρ : N.TrueReaction,
      (N.trueInternalClassFlux α ρ s.1) * σ s.1 :=
    N.trueInternalClassFlux_mul_sigma_pos hflow W s.2
  obtain ⟨ρ, -, hprod⟩ := exists_finset_term_same_sign Finset.univ
    (fun ρ : N.TrueReaction => N.trueInternalClassFlux α ρ s.1 * σ s.1)
    (ne_of_gt hsum)
  have hpos : 0 < N.trueInternalClassFlux α ρ s.1 * σ s.1 := by
    rcases mul_pos_iff.mp hprod with ⟨hterm, _⟩ | ⟨_, htot⟩
    · exact hterm
    · linarith
  have hflux : N.trueInternalClassFlux α ρ s.1 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hpos
    exact (lt_irrefl 0 hpos)
  let q : N.ActiveAggregateTrueReaction α σ := ⟨ρ, ⟨s.1, s.2, hflux⟩⟩
  exact ⟨q, hpos⟩

/-- Strict species flux remains strict when restricted to the reaction classes in a causal
source: a positive omitted class term would be an incoming edge and source closure would include
that class. -/
theorem trueInternalAggregateSource_flux_pos (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ)
    (T : Finset (N.TrueInternalAggregateVertex α σ))
    (hsource : ∀ a b, N.TrueInternalAggregateCausalEdge a b → b ∈ T → a ∈ T)
    (s : AggregateActiveSpecies σ) (hs : Sum.inl s ∈ T) :
    0 < ∑ ρ ∈ N.trueInternalAggregateSourceClasses α σ T,
      (N.trueInternalClassFlux α ρ s.1) * σ s.1 := by
  classical
  let f : N.TrueReaction → ℝ := fun ρ =>
    (N.trueInternalClassFlux α ρ s.1) * σ s.1
  let F := N.trueInternalAggregateSourceClasses α σ T
  have hglobal : 0 < ∑ ρ : N.TrueReaction, f ρ := by
    simpa [f] using N.trueInternalClassFlux_mul_sigma_pos hflow W s.2
  have houtside : ∀ ρ ∈ Fᶜ, f ρ ≤ 0 := by
    intro ρ hρ
    by_contra hnot
    have hpos : 0 < f ρ := lt_of_not_ge hnot
    have hflux : N.trueInternalClassFlux α ρ s.1 ≠ 0 := by
      intro hz
      dsimp [f] at hpos
      rw [hz, zero_mul] at hpos
      exact (lt_irrefl 0 hpos)
    let q : N.ActiveAggregateTrueReaction α σ := ⟨ρ, ⟨s.1, s.2, hflux⟩⟩
    have hedge : N.TrueInternalAggregateCausalEdge (Sum.inr q) (Sum.inl s) := hpos
    have hqT : Sum.inr q ∈ T := hsource _ _ hedge hs
    have hqF : ρ ∈ F := by
      change ρ ∈ Finset.univ.filter (fun ρ : N.TrueReaction =>
        ∃ q : N.ActiveAggregateTrueReaction α σ, q.1 = ρ ∧ Sum.inr q ∈ T)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨q, rfl, hqT⟩
    exact (Finset.mem_compl.mp hρ) hqF
  have hsum_outside : (∑ ρ ∈ Fᶜ, f ρ) ≤ 0 :=
    Finset.sum_nonpos houtside
  have hsplit : (∑ ρ : N.TrueReaction, f ρ) =
      (∑ ρ ∈ F, f ρ) + (∑ ρ ∈ Fᶜ, f ρ) := by
    rw [← Finset.sum_add_sum_compl F f]
  rw [show (∑ ρ ∈ N.trueInternalAggregateSourceClasses α σ T,
      (N.trueInternalClassFlux α ρ s.1) * σ s.1) = ∑ ρ ∈ F, f ρ by rfl]
  linarith [hglobal, hsplit]

/-- A finite source component of the aggregate sign-causality graph contains both species and
true-reaction vertices. Unlike an existential-channel quotient edge, every edge here uses the
net flux of its whole true-reaction class. -/
theorem exists_trueInternalAggregateCausalSource_data (N : Network S)
    (hflow : N.ZeroComplexReactionsAreFlows)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (W : N.fullyOpen.StrongConcordanceWitness α σ) :
    ∃ T : Finset (N.TrueInternalAggregateVertex α σ),
      T.Nonempty ∧
      (∀ a ∈ T, ∀ b ∈ T,
        Relation.ReflTransGen (N.TrueInternalAggregateCausalEdge) a b) ∧
      (∀ a b, N.TrueInternalAggregateCausalEdge a b → b ∈ T → a ∈ T) ∧
      (CRNT.relationGraphOn N.TrueInternalAggregateCausalEdge T).Connected ∧
      (∃ s : AggregateActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ ρ : N.ActiveAggregateTrueReaction α σ, Sum.inr ρ ∈ T) ∧
      (∀ s : AggregateActiveSpecies σ, Sum.inl s ∈ T →
        0 < ∑ ρ ∈ N.trueInternalAggregateSourceClasses α σ T,
          (N.trueInternalClassFlux α ρ s.1) * σ s.1) := by
  classical
  letI : Nonempty (AggregateActiveSpecies σ) := by
    by_contra h
    have hall : ∀ s : S, σ s = 0 := by
      intro s
      by_contra hs
      exact h ⟨⟨s, hs⟩⟩
    apply W.sigma_ne
    funext s
    exact hall s
  letI : Nonempty (N.TrueInternalAggregateVertex α σ) :=
    ⟨Sum.inl (Classical.choice inferInstance)⟩
  obtain ⟨T, hne, hscc, hsource⟩ :=
    CRNT.exists_finite_source (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ))
  have hconnected : (CRNT.relationGraphOn N.TrueInternalAggregateCausalEdge T).Connected :=
    CRNT.relationGraphOn_connected_of_source N.TrueInternalAggregateCausalEdge T
      hne hscc hsource
  obtain ⟨v, hv⟩ := hne
  cases v with
  | inl s =>
      have hspecies : ∃ s : AggregateActiveSpecies σ, Sum.inl s ∈ T := ⟨s, hv⟩
      obtain ⟨ρ, hedge⟩ := N.exists_positive_aggregateClass_predecessor hflow W s
      have hρ : Sum.inr ρ ∈ T := hsource _ _ hedge hv
      have hlocal : ∀ s : AggregateActiveSpecies σ, Sum.inl s ∈ T →
          0 < ∑ ρ ∈ N.trueInternalAggregateSourceClasses α σ T,
            (N.trueInternalClassFlux α ρ s.1) * σ s.1 := by
        intro s hs
        exact N.trueInternalAggregateSource_flux_pos hflow W T hsource s hs
      exact ⟨T, ⟨Sum.inl s, hv⟩, hscc, hsource, hconnected, hspecies, ⟨ρ, hρ⟩, hlocal⟩
  | inr ρ =>
      have hreaction : ∃ ρ : N.ActiveAggregateTrueReaction α σ, Sum.inr ρ ∈ T := ⟨ρ, hv⟩
      obtain ⟨s, hedge⟩ := N.activeAggregateClass_has_negative_edge W ρ
      have hs : Sum.inl s ∈ T := hsource _ _ hedge hv
      have hlocal : ∀ s : AggregateActiveSpecies σ, Sum.inl s ∈ T →
          0 < ∑ ρ ∈ N.trueInternalAggregateSourceClasses α σ T,
            (N.trueInternalClassFlux α ρ s.1) * σ s.1 := by
        intro s hs
        exact N.trueInternalAggregateSource_flux_pos hflow W T hsource s hs
      exact ⟨T, ⟨Sum.inr ρ, hv⟩, hscc, hsource, hconnected, ⟨s, hs⟩, hreaction, hlocal⟩

private def trueInternalAggregateVertexIsSpecies (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} :
    N.TrueInternalAggregateVertex α σ → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

private theorem trueInternalAggregateCausalEdge_flips_kind (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    {a b : N.TrueInternalAggregateVertex α σ}
    (h : N.TrueInternalAggregateCausalEdge a b) :
    N.trueInternalAggregateVertexIsSpecies b =
      !N.trueInternalAggregateVertexIsSpecies a := by
  cases a <;> cases b <;> simp_all [TrueInternalAggregateCausalEdge,
    trueInternalAggregateVertexIsSpecies]

private theorem trueInternalAggregateCausalEdge_irrefl (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (v : N.TrueInternalAggregateVertex α σ) :
    ¬ N.TrueInternalAggregateCausalEdge v v := by
  cases v <;> simp [TrueInternalAggregateCausalEdge]

private theorem exists_trueInternalAggregateSource_successor (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ))
    (hscc : ∀ a ∈ T, ∀ b ∈ T,
      Relation.ReflTransGen (N.TrueInternalAggregateCausalEdge) a b)
    (hsource : ∀ a b, N.TrueInternalAggregateCausalEdge a b → b ∈ T → a ∈ T)
    (hparts : (∃ s : AggregateActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ ρ : N.ActiveAggregateTrueReaction α σ, Sum.inr ρ ∈ T))
    (v : N.TrueInternalAggregateVertex α σ) (hv : v ∈ T) :
    ∃ w, w ∈ T ∧ N.TrueInternalAggregateCausalEdge v w := by
  let target : N.TrueInternalAggregateVertex α σ :=
    match v with
    | Sum.inl _ => Sum.inr hparts.2.choose
    | Sum.inr _ => Sum.inl hparts.1.choose
  have htarget : target ∈ T := by
    cases v with
    | inl _ => exact hparts.2.choose_spec
    | inr _ => exact hparts.1.choose_spec
  have hvne : v ≠ target := by cases v <;> simp [target]
  obtain ⟨w, hvw, hwt⟩ := exists_first_step_of_reflTransGen
    (hscc v hv target htarget) hvne
  exact ⟨w, CRNT.source_closed_under_predecessors hsource hwt htarget, hvw⟩

private noncomputable def trueInternalAggregateSourceStep (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ))
    (hscc : ∀ a ∈ T, ∀ b ∈ T,
      Relation.ReflTransGen (N.TrueInternalAggregateCausalEdge) a b)
    (hsource : ∀ a b, N.TrueInternalAggregateCausalEdge a b → b ∈ T → a ∈ T)
    (hparts : (∃ s : AggregateActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ ρ : N.ActiveAggregateTrueReaction α σ, Sum.inr ρ ∈ T)) :
    {v : N.TrueInternalAggregateVertex α σ // v ∈ T} →
      {v : N.TrueInternalAggregateVertex α σ // v ∈ T} := by
  classical
  intro v
  let hout := N.exists_trueInternalAggregateSource_successor T hscc hsource hparts v.1 v.2
  exact ⟨Classical.choose hout, (Classical.choose_spec hout).1⟩

private theorem trueInternalAggregateSourceStep_edge (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ))
    (hscc : ∀ a ∈ T, ∀ b ∈ T,
      Relation.ReflTransGen (N.TrueInternalAggregateCausalEdge) a b)
    (hsource : ∀ a b, N.TrueInternalAggregateCausalEdge a b → b ∈ T → a ∈ T)
    (hparts : (∃ s : AggregateActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ ρ : N.ActiveAggregateTrueReaction α σ, Sum.inr ρ ∈ T))
    (v : {v : N.TrueInternalAggregateVertex α σ // v ∈ T}) :
    N.TrueInternalAggregateCausalEdge v.1
      (N.trueInternalAggregateSourceStep T hscc hsource hparts v).1 := by
  exact (Classical.choose_spec
    (N.exists_trueInternalAggregateSource_successor T hscc hsource hparts v.1 v.2)).2

/-- Every finite aggregate sign-causality source contains a simple directed cycle. Its vertices
are true-reaction classes, so no reaction-class repetition is hidden by channel representatives. -/
theorem exists_simple_directed_cycle_in_trueInternalAggregateSource (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ))
    (hscc : ∀ a ∈ T, ∀ b ∈ T,
      Relation.ReflTransGen (N.TrueInternalAggregateCausalEdge) a b)
    (hsource : ∀ a b, N.TrueInternalAggregateCausalEdge a b → b ∈ T → a ∈ T)
    (hparts : (∃ s : AggregateActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ ρ : N.ActiveAggregateTrueReaction α σ, Sum.inr ρ ∈ T)) :
    ∃ p : ℕ, 2 ≤ p ∧ Even p ∧
      ∃ c : Fin p → N.TrueInternalAggregateVertex α σ,
        Function.Injective c ∧ (∀ i, c i ∈ T) ∧
        (∀ i, N.TrueInternalAggregateCausalEdge (c i) (c (finRotate p i))) := by
  classical
  let f := N.trueInternalAggregateSourceStep T hscc hsource hparts
  letI : Nonempty {v : N.TrueInternalAggregateVertex α σ // v ∈ T} :=
    ⟨⟨Sum.inl hparts.1.choose, hparts.1.choose_spec⟩⟩
  obtain ⟨x, hxper⟩ := exists_periodic_point_finite f
  let p := Function.minimalPeriod f x
  have hp : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts hxper
  have hkind : ∀ k : ℕ,
      N.trueInternalAggregateVertexIsSpecies (f^[k] x).1 =
        if k % 2 = 0 then N.trueInternalAggregateVertexIsSpecies x.1
        else !N.trueInternalAggregateVertexIsSpecies x.1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hflip := N.trueInternalAggregateCausalEdge_flips_kind
          (N.trueInternalAggregateSourceStep_edge T hscc hsource hparts (f^[k] x))
        change N.trueInternalAggregateVertexIsSpecies (f (f^[k] x)).1 =
          !N.trueInternalAggregateVertexIsSpecies (f^[k] x).1 at hflip
        rw [Function.iterate_succ_apply']
        by_cases heven : k % 2 = 0
        · have hnext : (k + 1) % 2 = 1 := by omega
          simp [heven, hnext, ih, hflip]
        · have hnext : (k + 1) % 2 = 0 := by omega
          simp [heven, hnext, ih, hflip]
  have hperiodfix : f^[p] x = x := by
    simpa [p] using (Function.iterate_minimalPeriod (f := f) (x := x))
  have htagfix : N.trueInternalAggregateVertexIsSpecies (f^[p] x).1 =
      N.trueInternalAggregateVertexIsSpecies x.1 := congrArg
        (fun z : {v : N.TrueInternalAggregateVertex α σ // v ∈ T} =>
          N.trueInternalAggregateVertexIsSpecies z.1) hperiodfix
  have hpeven : Even p := by
    by_contra hnot
    have hmod : p % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hnot)
    have hbad : N.trueInternalAggregateVertexIsSpecies x.1 =
        !N.trueInternalAggregateVertexIsSpecies x.1 := by
      calc
        N.trueInternalAggregateVertexIsSpecies x.1 =
            N.trueInternalAggregateVertexIsSpecies (f^[p] x).1 := htagfix.symm
        _ = !N.trueInternalAggregateVertexIsSpecies x.1 := by
          rw [hkind p]
          simp [hmod]
    cases htag : N.trueInternalAggregateVertexIsSpecies x.1 <;> simp [htag] at hbad
  have hpne : p ≠ 1 := by
    intro hp1
    have hfix := Function.iterate_minimalPeriod (f := f) (x := x)
    have hp1' : Function.minimalPeriod f x = 1 := by simpa [p] using hp1
    rw [hp1', Function.iterate_one] at hfix
    have hstep := N.trueInternalAggregateSourceStep_edge T hscc hsource hparts x
    change N.TrueInternalAggregateCausalEdge x.1 (f x).1 at hstep
    exact N.trueInternalAggregateCausalEdge_irrefl x.1 (by simpa [hfix] using hstep)
  have hp2 : 2 ≤ p := by omega
  refine ⟨p, hp2, hpeven, fun i => (f^[i.1] x).1, ?_, ?_, ?_⟩
  · intro i j hij
    have hsub : (f^[i.1] x) = (f^[j.1] x) := Subtype.ext hij
    have hij' := Function.iterate_eq_iterate_iff_of_lt_minimalPeriod i.2 j.2
    exact Fin.ext (hij'.mp hsub)
  · intro i
    exact (f^[i.1] x).2
  · intro i
    letI : NeZero p := ⟨by omega⟩
    have hrot : (finRotate p i).1 = (i.1 + 1) % p := by
      rw [finRotate_apply]
      simp [Fin.add_def]
    have hed := N.trueInternalAggregateSourceStep_edge T hscc hsource hparts
      (f^[i.1] x)
    change N.TrueInternalAggregateCausalEdge (f^[i.1] x).1
      (f (f^[i.1] x)).1 at hed
    have hnext : f (f^[i.1] x) = f^[((i.1 + 1) % p)] x := by
      calc
        f (f^[i.1] x) = f^[i.1 + 1] x := by
          simpa [Nat.succ_eq_add_one] using
            (Function.iterate_succ_apply' f i.1 x).symm
        _ = f^[((i.1 + 1) % p)] x := by
          symm
          dsimp [p]
          exact Function.iterate_mod_minimalPeriod_eq
    change N.TrueInternalAggregateCausalEdge (f^[i.1] x).1
      (f^[((finRotate p i).1)] x).1
    rw [hrot]
    rw [← congrArg Subtype.val hnext]
    exact hed

/-- Rotate a simple bipartite directed cycle, if needed, so that its first vertex is a species.
This leaves the cycle edges and vertex injectivity unchanged. -/
private theorem rotate_trueInternalAggregateCycle_to_species (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} {p : ℕ}
    (T : Finset (N.TrueInternalAggregateVertex α σ))
    (hp2 : 2 ≤ p) (c : Fin p → N.TrueInternalAggregateVertex α σ)
    (hcinj : Function.Injective c)
    (hcT : ∀ i, c i ∈ T)
    (hcedge : ∀ i, N.TrueInternalAggregateCausalEdge (c i) (c (finRotate p i))) :
    ∃ d : Fin p → N.TrueInternalAggregateVertex α σ,
      Function.Injective d ∧
      (∀ i, d i ∈ T) ∧
      (∃ s : AggregateActiveSpecies σ, d ⟨0, by omega⟩ = Sum.inl s) ∧
      (∀ i, N.TrueInternalAggregateCausalEdge (d i) (d (finRotate p i))) := by
  classical
  letI : NeZero p := ⟨by omega⟩
  by_cases hspecies : N.trueInternalAggregateVertexIsSpecies (c 0) = true
  · refine ⟨c, hcinj, ?_, ?_, hcedge⟩
    · exact hcT
    · cases h : c 0 with
      | inl s => exact ⟨s, by simpa using h⟩
      | inr ρ => simp [trueInternalAggregateVertexIsSpecies, h] at hspecies
  · have hreaction : N.trueInternalAggregateVertexIsSpecies (c 0) = false := by
      cases h : N.trueInternalAggregateVertexIsSpecies (c 0) <;> simp_all
    let d : Fin p → N.TrueInternalAggregateVertex α σ := fun i => c (finRotate p i)
    have hrot0 : finRotate p (0 : Fin p) = (1 : Fin p) := by
      apply Fin.ext
      have hp1 : 1 < p := by omega
      have h := congrArg Fin.val (finRotate_apply (0 : Fin p))
      simpa [Fin.add_def, hp1] using h
    have hflip := N.trueInternalAggregateCausalEdge_flips_kind (hcedge 0)
    change N.trueInternalAggregateVertexIsSpecies (c (finRotate p 0)) =
      !N.trueInternalAggregateVertexIsSpecies (c 0) at hflip
    rw [hrot0, hreaction] at hflip
    have hd0 : N.trueInternalAggregateVertexIsSpecies (d 0) = true := by
      simpa [d] using hflip
    refine ⟨d, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      apply (finRotate p).injective
      apply hcinj
      exact hij
    · intro i
      exact hcT (finRotate p i)
    · cases h : d 0 with
      | inl s => exact ⟨s, by simpa using h⟩
      | inr ρ => simp [trueInternalAggregateVertexIsSpecies, h] at hd0
    · intro i
      exact hcedge (finRotate p i)

private theorem trueInternalAggregateCycle_length_even_half (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} {p : ℕ}
    (hp2 : 2 ≤ p) (hpeven : Even p)
    (c : Fin p → N.TrueInternalAggregateVertex α σ)
    (hstart : ∃ s : AggregateActiveSpecies σ,
      c ⟨0, by omega⟩ = Sum.inl s)
    (hcedge : ∀ i, N.TrueInternalAggregateCausalEdge (c i) (c (finRotate p i))) :
    ∃ n : ℕ, p = 2 * n ∧ 2 ≤ n := by
  classical
  have hp4 : 4 ≤ p := by
    by_contra hnot
    have hlt : p < 4 := Nat.lt_of_not_ge hnot
    have hpeq : p = 2 := by
      have hmod := Nat.even_iff.mp hpeven
      omega
    subst p
    letI : NeZero 2 := ⟨by decide⟩
    have hrot0 : finRotate 2 (0 : Fin 2) = 1 := by
      apply Fin.ext
      have h := congrArg Fin.val (finRotate_apply (0 : Fin 2))
      norm_num [Fin.add_def] at h ⊢
    have hrot1 : finRotate 2 (1 : Fin 2) = 0 := by
      apply Fin.ext
      have h := congrArg Fin.val (finRotate_apply (1 : Fin 2))
      norm_num [Fin.add_def] at h ⊢
    obtain ⟨s, hs⟩ := hstart
    have hs' : c (0 : Fin 2) = Sum.inl s := by simpa using hs
    have h01 := hcedge (0 : Fin 2)
    rw [hs', hrot0] at h01
    cases hq : c 1 with
    | inl t => rw [hq] at h01; simp [TrueInternalAggregateCausalEdge] at h01
    | inr q =>
        rw [hq] at h01
        have hneg :
            N.trueInternalClassFlux α q.1 s.1 * σ s.1 < 0 := by
          change N.trueInternalClassFlux α q.1 s.1 * σ s.1 < 0 at h01
          exact h01
        have h10 := hcedge (1 : Fin 2)
        rw [hq, hrot1, hs'] at h10
        have hpos :
            0 < N.trueInternalClassFlux α q.1 s.1 * σ s.1 := by
          change 0 < N.trueInternalClassFlux α q.1 s.1 * σ s.1 at h10
          exact h10
        linarith
  refine ⟨p / 2, ?_, ?_⟩
  · have hmod := Nat.even_iff.mp hpeven
    omega
  · omega

private def aggregateEvenCycleIndex (n : ℕ) (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.1, by omega⟩

private def aggregateOddCycleIndex (n : ℕ) (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.1 + 1, by omega⟩

private theorem finRotate_aggregateEvenIndex (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    finRotate (2 * n) (aggregateEvenCycleIndex n i) = aggregateOddCycleIndex n i := by
  letI : NeZero n := ⟨by omega⟩
  letI : NeZero (2 * n) := ⟨by omega⟩
  apply Fin.ext
  have hrot :
      (finRotate (2 * n) (aggregateEvenCycleIndex n i)).1 =
        (2 * i.1 + 1) % (2 * n) := by
    rw [finRotate_apply]
    simp [Fin.add_def, aggregateEvenCycleIndex, aggregateOddCycleIndex]
  rw [hrot, Nat.mod_eq_of_lt (by omega)]
  simp [aggregateOddCycleIndex]

private theorem finRotate_aggregateOddIndex (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    finRotate (2 * n) (aggregateOddCycleIndex n i) =
      aggregateEvenCycleIndex n (finRotate n i) := by
  letI : NeZero n := ⟨by omega⟩
  letI : NeZero (2 * n) := ⟨by omega⟩
  apply Fin.ext
  have hn1 : 1 < n := by omega
  have hp1 : 1 < 2 * n := by omega
  have hsmall : (finRotate n i).1 = (i.1 + 1) % n := by
    have h := congrArg Fin.val (finRotate_apply i)
    simpa [Fin.add_def, hn1] using h
  have hlarge :
      (finRotate (2 * n) (aggregateOddCycleIndex n i)).1 =
        (2 * i.1 + 2) % (2 * n) := by
    have h := congrArg Fin.val (finRotate_apply (aggregateOddCycleIndex n i))
    simpa [aggregateOddCycleIndex, Fin.add_def, hp1] using h
  change (finRotate (2 * n) (aggregateOddCycleIndex n i)).1 =
    2 * (finRotate n i).1
  rcases Nat.lt_or_ge (i.1 + 1) n with hlt | hge
  · have hsmall' : (finRotate n i).1 = i.1 + 1 := by
      rw [Nat.mod_eq_of_lt hlt] at hsmall
      exact hsmall
    rw [hlarge, hsmall', Nat.mod_eq_of_lt (by omega)]
    rfl
  · have heq : i.1 + 1 = n := by omega
    have hsmall' : (finRotate n i).1 = 0 := by
      rw [heq, Nat.mod_self] at hsmall
      exact hsmall
    rw [hlarge, hsmall']
    rw [show 2 * i.1 + 2 = 2 * n by omega]
    rw [Nat.mod_self]

private theorem trueSRCycle_of_simple_aggregate_cycle (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} {p : ℕ}
    (hp2 : 2 ≤ p) (hpeven : Even p)
    (c : Fin p → N.TrueInternalAggregateVertex α σ)
    (hcinj : Function.Injective c)
    (T : Finset (N.TrueInternalAggregateVertex α σ))
    (hcT : ∀ i, c i ∈ T)
    (hstart : ∃ s : AggregateActiveSpecies σ,
      c ⟨0, by omega⟩ = Sum.inl s)
    (hcedge : ∀ i, N.TrueInternalAggregateCausalEdge (c i) (c (finRotate p i))) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ C : N.TrueSRCycle n,
      ∃ heq : p = 2 * n,
      C.Even ∧
      (∀ i, C.isCPair i ↔
        σ (C.species i) * σ (C.species (finRotate n i)) < 0) ∧
      (∀ i, (C.leftEdge i).representative = (C.rightEdge i).representative) ∧
      (∀ i, ∃ s : AggregateActiveSpecies σ,
        s.1 = C.species i ∧ Sum.inl s ∈ T) ∧
      (∀ i, C.reaction i ∈ N.trueInternalAggregateSourceClasses α σ T) ∧
      (∀ i, N.aggregateVertexToTrueSRVertex
        (c (Fin.cast heq.symm (aggregateEvenCycleIndex n i))) = Sum.inl (C.species i)) ∧
      (∀ i, N.aggregateVertexToTrueSRVertex
        (c (Fin.cast heq.symm (aggregateOddCycleIndex n i))) =
          Sum.inr ⟨C.reaction i, C.reaction_internal i⟩) ∧
      ∃ β : Fin n → ℝ,
        (∀ i t, N.trueInternalClassFlux α (C.reaction i) t =
          β i * N.reactionVector (C.rightEdge i).representative t) ∧
        (∀ i, N.trueInternalClassFlux α (C.reaction i) (C.species i) *
          σ (C.species i) < 0) ∧
        (∀ i, 0 < N.trueInternalClassFlux α (C.reaction i)
          (C.species (finRotate n i)) * σ (C.species (finRotate n i))) := by
  classical
  obtain ⟨n, hpn, hn2⟩ :=
    N.trueInternalAggregateCycle_length_even_half hp2 hpeven c hstart hcedge
  subst p
  letI : NeZero n := ⟨by omega⟩
  letI : NeZero (2 * n) := ⟨by omega⟩
  have hkind : ∀ k : ℕ, ∀ hk : k < 2 * n,
      N.trueInternalAggregateVertexIsSpecies (c ⟨k, hk⟩) =
        if k % 2 = 0 then true else false := by
    intro k
    induction k with
    | zero =>
        intro hk
        obtain ⟨s, hs⟩ := hstart
        have hzero : (⟨0, hk⟩ : Fin (2 * n)) = ⟨0, by omega⟩ := by
          apply Fin.ext
          rfl
        rw [hzero, hs]
        simp [trueInternalAggregateVertexIsSpecies]
    | succ k ih =>
        intro hk
        have hklt : k < 2 * n := by omega
        have hrot : finRotate (2 * n) ⟨k, hklt⟩ = ⟨k + 1, hk⟩ := by
          apply Fin.ext
          rw [finRotate_apply]
          simp [Fin.add_def, Nat.mod_eq_of_lt hk]
        have hflip := N.trueInternalAggregateCausalEdge_flips_kind
          (hcedge ⟨k, hklt⟩)
        change N.trueInternalAggregateVertexIsSpecies
            (c (finRotate (2 * n) ⟨k, hklt⟩)) =
          !N.trueInternalAggregateVertexIsSpecies (c ⟨k, hklt⟩) at hflip
        rw [hrot, ih hklt] at hflip
        by_cases heven : k % 2 = 0
        · have hnext : (k + 1) % 2 = 1 := by omega
          simpa [heven, hnext] using hflip
        · have hnext : (k + 1) % 2 = 0 := by omega
          simpa [heven, hnext] using hflip
  have hspeciesAt : ∀ i : Fin n,
      ∃ s : AggregateActiveSpecies σ,
        c (aggregateEvenCycleIndex n i) = Sum.inl s := by
    intro i
    have htag : N.trueInternalAggregateVertexIsSpecies
        (c (aggregateEvenCycleIndex n i)) = true := by
      have h := hkind (2 * i.1) (by omega)
      simpa [aggregateEvenCycleIndex] using h
    cases hv : c (aggregateEvenCycleIndex n i) with
    | inl s => exact ⟨s, rfl⟩
    | inr ρ => simp [trueInternalAggregateVertexIsSpecies, hv] at htag
  have hreactionAt : ∀ i : Fin n,
      ∃ ρ : N.ActiveAggregateTrueReaction α σ,
        c (aggregateOddCycleIndex n i) = Sum.inr ρ := by
    intro i
    have htag : N.trueInternalAggregateVertexIsSpecies
        (c (aggregateOddCycleIndex n i)) = false := by
      have h := hkind (2 * i.1 + 1) (by omega)
      simpa [aggregateOddCycleIndex] using h
    cases hv : c (aggregateOddCycleIndex n i) with
    | inl s => simp [trueInternalAggregateVertexIsSpecies, hv] at htag
    | inr ρ => exact ⟨ρ, rfl⟩
  let sp : Fin n → AggregateActiveSpecies σ := fun i => Classical.choose (hspeciesAt i)
  let rx : Fin n → N.ActiveAggregateTrueReaction α σ :=
    fun i => Classical.choose (hreactionAt i)
  have hsp : ∀ i, c (aggregateEvenCycleIndex n i) = Sum.inl (sp i) :=
    fun i => Classical.choose_spec (hspeciesAt i)
  have hrx : ∀ i, c (aggregateOddCycleIndex n i) = Sum.inr (rx i) :=
    fun i => Classical.choose_spec (hreactionAt i)
  have hspT : ∀ i, Sum.inl (sp i) ∈ T := by
    intro i
    have h := hcT (aggregateEvenCycleIndex n i)
    rw [hsp i] at h
    exact h
  have hrxT : ∀ i, Sum.inr (rx i) ∈ T := by
    intro i
    have h := hcT (aggregateOddCycleIndex n i)
    rw [hrx i] at h
    exact h
  have hneg : ∀ i : Fin n,
      N.trueInternalClassFlux α (rx i).1 (sp i).1 * σ (sp i).1 < 0 := by
    intro i
    have hedge := hcedge (aggregateEvenCycleIndex n i)
    rw [hsp i, finRotate_aggregateEvenIndex n hn2 i, hrx i] at hedge
    change N.trueInternalClassFlux α (rx i).1 (sp i).1 * σ (sp i).1 < 0 at hedge
    exact hedge
  have hpos : ∀ i : Fin n,
      0 < N.trueInternalClassFlux α (rx i).1 (sp (finRotate n i)).1 *
        σ (sp (finRotate n i)).1 := by
    intro i
    have hedge := hcedge (aggregateOddCycleIndex n i)
    rw [hrx i, finRotate_aggregateOddIndex n hn2 i,
      hsp (finRotate n i)] at hedge
    change 0 < N.trueInternalClassFlux α (rx i).1 (sp (finRotate n i)).1 *
      σ (sp (finRotate n i)).1 at hedge
    exact hedge
  let repWitness (i : Fin n) :=
    N.exists_nonzero_channel_of_trueInternalClassFlux (rx i).1 (sp i).1
      (by
        intro hz
        have hneg_i := hneg i
        rw [hz, zero_mul] at hneg_i
        exact (lt_irrefl (0 : ℝ)) hneg_i)
  let rep (i : Fin n) : N.R := Classical.choose (repWitness i)
  have hrepSpec (i : Fin n) := Classical.choose_spec (repWitness i)
  have hrepNF (i : Fin n) : rep i ∈ N.nonflowOriginalChannels := (hrepSpec i).1
  have hrepClass (i : Fin n) : N.trueReaction (rep i) = (rx i).1 := (hrepSpec i).2.1
  have hterm (i : Fin n) :
      α (Sum.inl (rep i) : N.fullyOpen.R) *
        N.reactionVector (rep i) (sp i).1 ≠ 0 := (hrepSpec i).2.2
  have hνleft (i : Fin n) : N.reactionVector (rep i) (sp i).1 ≠ 0 := by
    intro hz
    apply hterm i
    rw [hz, mul_zero]
  have hscalar (i : Fin n) : ∃ β : ℝ, ∀ t : S,
      N.trueInternalClassFlux α (rx i).1 t = β * N.reactionVector (rep i) t :=
    N.exists_scalar_mul_reactionVector_eq_trueInternalClassFlux (rx i).1
      (sp i).1 (hrepNF i) (hrepClass i) (hνleft i)
  let beta (i : Fin n) : ℝ := Classical.choose (hscalar i)
  have hbeta (i : Fin n) (t : S) :
      N.trueInternalClassFlux α (rx i).1 t = beta i * N.reactionVector (rep i) t :=
    Classical.choose_spec (hscalar i) t
  have hbetaNe (i : Fin n) : beta i ≠ 0 := by
    intro hz
    have hflux : N.trueInternalClassFlux α (rx i).1 (sp i).1 ≠ 0 := by
      intro hz0
      have hneg_i := hneg i
      rw [hz0, zero_mul] at hneg_i
      exact (lt_irrefl (0 : ℝ)) hneg_i
    have hzero : N.trueInternalClassFlux α (rx i).1 (sp i).1 = 0 := by
      rw [hbeta i (sp i).1, hz]
      simp
    exact hflux hzero
  have hνright (i : Fin n) :
      N.reactionVector (rep i) (sp (finRotate n i)).1 ≠ 0 := by
    intro hz
    have hposi := hpos i
    rw [hbeta i (sp (finRotate n i)).1, hz, mul_zero, zero_mul] at hposi
    exact (lt_irrefl (0 : ℝ)) hposi
  have hnotflow (i : Fin n) : ¬ N.IsFlowChannel (rep i) := by
    simpa [nonflowOriginalChannels] using hrepNF i
  let leftE (i : Fin n) : N.TrueSREdge :=
    N.trueSREdgeOfReactionVectorNe (rep i) (hnotflow i) (sp i).1 (hνleft i)
  let rightE (i : Fin n) : N.TrueSREdge :=
    N.trueSREdgeOfReactionVectorNe (rep i) (hnotflow i)
      (sp (finRotate n i)).1 (hνright i)
  let C : N.TrueSRCycle n := {
    nontrivial := hn2
    species := fun i => (sp i).1
    reaction := fun i => (rx i).1
    leftEdge := leftE
    rightEdge := rightE
    left_species := by intro i; simp [leftE]
    left_reaction := by
      intro i
      rw [N.trueSREdgeOfReactionVectorNe_reaction, hrepClass]
    right_species := by
      intro i
      simp only [rightE, trueSREdgeOfReactionVectorNe_species]
      have hrot : finRotate n i =
          (⟨(i.1 + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) := by
        apply Fin.ext
        rw [finRotate_apply]
        simp [Fin.add_def]
      rw [hrot]
    right_reaction := by
      intro i
      rw [N.trueSREdgeOfReactionVectorNe_reaction, hrepClass]
    species_injective := by
      intro i j hij
      have hvertices : c (aggregateEvenCycleIndex n i) =
          c (aggregateEvenCycleIndex n j) := by
        rw [hsp i, hsp j]
        exact congrArg Sum.inl (Subtype.ext hij)
      have hidx := hcinj hvertices
      apply Fin.ext
      have hv := congrArg Fin.val hidx
      simpa [aggregateEvenCycleIndex] using hv
    reaction_injective := by
      intro i j hij
      have hvertices : c (aggregateOddCycleIndex n i) =
          c (aggregateOddCycleIndex n j) := by
        rw [hrx i, hrx j]
        exact congrArg Sum.inr (Subtype.ext hij)
      have hidx := hcinj hvertices
      apply Fin.ext
      have hv := congrArg Fin.val hidx
      simpa [aggregateOddCycleIndex] using hv
  }
  have hpairRV : ∀ i : Fin n,
      ((leftE i).endpoint = (rightE i).endpoint) ↔
        0 < N.reactionVector (rep i) (sp i).1 *
          N.reactionVector (rep i) (sp (finRotate n i)).1 := by
    intro i
    have hsame := N.trueSREdge_sameEndpoint_iff_direction_mul_pos
      (rep i) (hnotflow i) (sp i).1 (sp (finRotate n i)).1
      (hνleft i) (hνright i)
    have hdirL : N.reactionDirectionSign (rep i) (sp i).1 =
        -N.reactionVector (rep i) (sp i).1 := by
      simp [reactionDirectionSign, reactionVector_apply]
    have hdirR : N.reactionDirectionSign (rep i) (sp (finRotate n i)).1 =
        -N.reactionVector (rep i) (sp (finRotate n i)).1 := by
      simp [reactionDirectionSign, reactionVector_apply]
    rw [hdirL, hdirR] at hsame
    have hnegmul :
        (0 < (-N.reactionVector (rep i) (sp i).1) *
          (-N.reactionVector (rep i) (sp (finRotate n i)).1)) ↔
        0 < N.reactionVector (rep i) (sp i).1 *
          N.reactionVector (rep i) (sp (finRotate n i)).1 := by
      constructor <;> intro h <;> nlinarith
    simpa [leftE, rightE] using hsame.trans hnegmul
  have hfluxProduct : ∀ i : Fin n,
      (N.reactionVector (rep i) (sp i).1 * σ (sp i).1) *
        (N.reactionVector (rep i) (sp (finRotate n i)).1 *
          σ (sp (finRotate n i)).1) < 0 := by
    intro i
    have hneg' : beta i *
        (N.reactionVector (rep i) (sp i).1 * σ (sp i).1) < 0 := by
      calc
        beta i * (N.reactionVector (rep i) (sp i).1 * σ (sp i).1) =
            (beta i * N.reactionVector (rep i) (sp i).1) * σ (sp i).1 := by ring
        _ = N.trueInternalClassFlux α (rx i).1 (sp i).1 * σ (sp i).1 := by
          rw [hbeta i]
        _ < 0 := hneg i
    have hpos' : beta i *
        (N.reactionVector (rep i) (sp (finRotate n i)).1 *
          σ (sp (finRotate n i)).1) > 0 := by
      calc
        beta i * (N.reactionVector (rep i) (sp (finRotate n i)).1 *
            σ (sp (finRotate n i)).1) =
            (beta i * N.reactionVector (rep i) (sp (finRotate n i)).1) *
              σ (sp (finRotate n i)).1 := by ring
        _ = N.trueInternalClassFlux α (rx i).1
              (sp (finRotate n i)).1 * σ (sp (finRotate n i)).1 := by
          rw [hbeta i]
        _ > 0 := hpos i
    rcases lt_or_gt_of_ne (hbetaNe i) with hbneg | hbpos
    · have hleft : 0 < N.reactionVector (rep i) (sp i).1 * σ (sp i).1 := by
        by_contra h
        have hle : N.reactionVector (rep i) (sp i).1 * σ (sp i).1 ≤ 0 :=
          le_of_not_gt h
        have hnonneg := mul_nonneg_of_nonpos_of_nonpos hbneg.le hle
        exact (not_lt_of_ge hnonneg) hneg'
      have hright : N.reactionVector (rep i) (sp (finRotate n i)).1 *
          σ (sp (finRotate n i)).1 < 0 := by
        by_contra h
        have hge : 0 ≤ N.reactionVector (rep i) (sp (finRotate n i)).1 *
            σ (sp (finRotate n i)).1 := le_of_not_gt h
        have hnonpos := mul_nonpos_of_nonpos_of_nonneg hbneg.le hge
        exact (not_lt_of_ge hnonpos) hpos'
      exact mul_neg_of_pos_of_neg hleft hright
    · have hleft : N.reactionVector (rep i) (sp i).1 * σ (sp i).1 < 0 := by
        by_contra h
        have hge : 0 ≤ N.reactionVector (rep i) (sp i).1 * σ (sp i).1 :=
          le_of_not_gt h
        have hnonneg := mul_nonneg hbpos.le hge
        exact (not_lt_of_ge hnonneg) hneg'
      have hright : 0 < N.reactionVector (rep i) (sp (finRotate n i)).1 *
          σ (sp (finRotate n i)).1 := by
        by_contra h
        have hle : N.reactionVector (rep i) (sp (finRotate n i)).1 *
            σ (sp (finRotate n i)).1 ≤ 0 := le_of_not_gt h
        have hnonpos := mul_nonpos_of_nonneg_of_nonpos hbpos.le hle
        exact (not_lt_of_ge hnonpos) hpos'
      exact mul_neg_of_neg_of_pos hleft hright
  have hsignPair : ∀ i : Fin n,
      (0 < N.reactionVector (rep i) (sp i).1 *
        N.reactionVector (rep i) (sp (finRotate n i)).1) ↔
      σ (sp i).1 * σ (sp (finRotate n i)).1 < 0 := by
    intro i
    have hprod :
        (N.reactionVector (rep i) (sp i).1 *
          N.reactionVector (rep i) (sp (finRotate n i)).1) *
        (σ (sp i).1 * σ (sp (finRotate n i)).1) < 0 := by
      calc
        _ = (N.reactionVector (rep i) (sp i).1 * σ (sp i).1) *
            (N.reactionVector (rep i) (sp (finRotate n i)).1 *
              σ (sp (finRotate n i)).1) := by ring
        _ < 0 := hfluxProduct i
    have hνne : N.reactionVector (rep i) (sp i).1 *
        N.reactionVector (rep i) (sp (finRotate n i)).1 ≠ 0 :=
      mul_ne_zero (hνleft i) (hνright i)
    constructor
    · intro hνpos
      by_contra hσ
      have hσge : 0 ≤ σ (sp i).1 * σ (sp (finRotate n i)).1 := le_of_not_gt hσ
      exact (not_lt_of_ge
        (mul_nonneg (le_of_lt hνpos) hσge)) hprod
    · intro hσneg
      rcases lt_or_gt_of_ne hνne with hνneg | hνpos
      · have hnonneg := mul_nonneg_of_nonpos_of_nonpos
          (le_of_lt hνneg) (le_of_lt hσneg)
        exact False.elim ((not_lt_of_ge hnonneg) hprod)
      · exact hνpos
  have hpair : ∀ i : Fin n,
      C.isCPair i ↔ σ (C.species i) * σ (C.species (finRotate n i)) < 0 := by
    intro i
    change (C.leftEdge i).endpoint = (C.rightEdge i).endpoint ↔ _
    change (leftE i).endpoint = (rightE i).endpoint ↔ _
    rw [hpairRV i, hsignPair i]
  have hspeciesNonzero : ∀ i : Fin n, σ (C.species i) ≠ 0 := by
    intro i
    exact (sp i).2
  have heven : C.Even := by
    change Even ((Finset.univ.filter C.isCPair).card)
    rw [show Finset.univ.filter C.isCPair =
        Finset.univ.filter
          (fun i => σ (C.species i) * σ (C.species (finRotate n i)) < 0) by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hpair i]
    exact cyclic_sign_changes_even (fun i => σ (C.species i)) hspeciesNonzero
  refine ⟨n, hn2, C, rfl, heven, hpair, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [C, leftE, rightE]
  · intro i
    refine ⟨sp i, ?_, hspT i⟩
    simp [C]
  · intro i
    change (rx i).1 ∈ N.trueInternalAggregateSourceClasses α σ T
    change (rx i).1 ∈ Finset.univ.filter (fun ρ : N.TrueReaction =>
      ∃ q : N.ActiveAggregateTrueReaction α σ, q.1 = ρ ∧ Sum.inr q ∈ T)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨rx i, rfl, hrxT i⟩
  · intro i
    simpa [aggregateVertexToTrueSRVertex, hsp, C]
  · intro i
    simpa [aggregateVertexToTrueSRVertex, hrx, C]
  · refine ⟨beta, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i t
      simpa [C, rightE] using hbeta i t
    · intro i
      simpa [C] using hneg i
    · intro i
      simpa [C] using hpos i

/-- A simple directed aggregate path from a species to a reaction class closes to an even
true-SR cycle when that reaction has a causal edge back to the start species. This packages
the cycle extraction needed for the degenerate directed-chord case. -/
private theorem trueSRCycle_of_directed_species_loop (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    {T : Finset (N.TrueInternalAggregateVertex α σ)} {m : ℕ}
    (P : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T m)
    (hinj : Function.Injective P.vertex)
    {s : AggregateActiveSpecies σ} {q : N.ActiveAggregateTrueReaction α σ}
    (hstart : P.vertex ⟨0, by omega⟩ = Sum.inl s)
    (hend : P.vertex ⟨m, by omega⟩ = Sum.inr q)
    (hclose : N.TrueInternalAggregateCausalEdge (Sum.inr q) (Sum.inl s)) :
    ∃ n, 2 ≤ n ∧ ∃ C : N.TrueSRCycle n, C.Even := by
  classical
  have hmpos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    subst m
    have hval : Sum.inl s = Sum.inr q := by
      calc
        Sum.inl s = P.vertex ⟨0, by omega⟩ := hstart.symm
        _ = P.vertex ⟨0, by omega⟩ := rfl
        _ = Sum.inr q := hend
    exact Sum.inl_ne_inr hval
  let R := N.relPathToTrueSRPath T P hinj hmpos hstart hend
  have hOdd : Odd m := R.odd_length
  have hmEven : Even (m + 1) := by
    obtain ⟨k, hk⟩ := hOdd
    exact ⟨k + 1, by omega⟩
  let c : Fin (m + 1) → N.TrueInternalAggregateVertex α σ :=
    fun i => P.vertex ⟨i.1, by have := i.isLt; omega⟩
  have hcinj : Function.Injective c := by
    intro i j hij
    apply Fin.ext
    have hidx : (⟨i.1, by omega⟩ : Fin (m + 1)) = ⟨j.1, by omega⟩ := by
      exact hinj (by simpa [c] using hij)
    exact congrArg Fin.val hidx
  have hcT : ∀ i, c i ∈ T := by
    intro i
    exact P.mem ⟨i.1, by have := i.isLt; omega⟩
  have hstartC : ∃ s' : AggregateActiveSpecies σ,
      c ⟨0, by omega⟩ = Sum.inl s' := ⟨s, by simpa [c] using hstart⟩
  have hcedge : ∀ i, N.TrueInternalAggregateCausalEdge (c i)
      (c (finRotate (m + 1) i)) := by
    intro i
    have hi := i.isLt
    by_cases hlt : i.1 < m
    · let j : Fin m := ⟨i.1, hlt⟩
      have hi1 : i.1 + 1 < m + 1 := by omega
      have hrot : finRotate (m + 1) i = ⟨i.1 + 1, by omega⟩ := by
        apply Fin.ext
        have h := congrArg Fin.val (finRotate_apply i)
        simpa [Fin.add_def, Nat.mod_eq_of_lt hi1] using h
      have hleft : i = Fin.castSucc j := Fin.ext rfl
      have hright : (⟨i.1 + 1, by omega⟩ : Fin (m + 1)) = j.succ := Fin.ext rfl
      have hleftV : P.vertex i = P.vertex (Fin.castSucc j) := congrArg P.vertex hleft
      have hrightV : P.vertex (finRotate (m + 1) i) = P.vertex j.succ :=
        congrArg P.vertex (hrot.trans hright)
      change N.TrueInternalAggregateCausalEdge (P.vertex i)
        (P.vertex (finRotate (m + 1) i))
      rw [hleftV, hrightV]
      exact P.step j
    · have hiM : i.1 = m := by omega
      have hlast : i = Fin.last m := Fin.ext hiM
      have hrot : finRotate (m + 1) (Fin.last m) = (⟨0, by omega⟩ : Fin (m + 1)) := by
        apply Fin.ext
        have h := congrArg Fin.val (finRotate_apply (Fin.last m))
        simpa [Fin.add_def] using h
      rw [hlast, hrot]
      change N.TrueInternalAggregateCausalEdge
        (P.vertex ⟨m, by omega⟩) (P.vertex ⟨0, by omega⟩)
      rw [hend, hstart]
      exact hclose
  obtain ⟨n, hn, C, _, hC, _⟩ :=
    N.trueSRCycle_of_simple_aggregate_cycle (by omega) hmEven c hcinj T hcT
      hstartC hcedge
  exact ⟨n, hn, C, hC⟩

/-- The sign-change certificate for a causal cycle is invariant under cycle rotation. -/
private theorem rotated_trueSRCycle_pair_iff_signChange (N : Network S)
    {σ : S → ℝ} {n : ℕ} (C : N.TrueSRCycle n)
    (hpair : ∀ i, C.isCPair i ↔
      σ (C.species i) * σ (C.species (finRotate n i)) < 0)
    (r : ℕ) (i : Fin n) :
    (C.rotate r).isCPair i ↔
      σ ((C.rotate r).species i) *
        σ ((C.rotate r).species (finRotate n i)) < 0 := by
  let j : Fin n := ⟨(i.1 + r) % n,
    Nat.mod_lt _ (by have := C.nontrivial; omega)⟩
  have hidx := C.rotateIndex_successor r i
  change C.isCPair j ↔ _
  rw [hpair j]
  change σ (C.species j) * σ (C.species (finRotate n j)) < 0 ↔ _
  rw [← hidx]
  rfl

private theorem trueSRCycle_even_of_signChange (N : Network S) {n : ℕ}
    (C : N.TrueSRCycle n) (σ : S → ℝ)
    (hσ : ∀ i, σ (C.species i) ≠ 0)
    (hpair : ∀ i, C.isCPair i ↔
      σ (C.species i) * σ (C.species (finRotate n i)) < 0) : C.Even := by
  classical
  let a : Fin n → ℝ := fun i => σ (C.species i)
  haveI : NeZero n := ⟨by have := C.nontrivial; omega⟩
  have hne : ∀ i, a i ≠ 0 := hσ
  have hEven := cyclic_sign_changes_even a hne
  rw [TrueSRCycle.Even, TrueSRCycle.numCPairs]
  rw [show (Finset.univ.filter C.isCPair) =
      Finset.univ.filter (fun i => a i * a (finRotate n i) < 0) by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, a]
    exact hpair i]
  exact hEven

/-- At a reaction used with opposite causal signs at two species, reactant/product separation
identifies a c-pair exactly with a sign change of the species values. -/
private theorem class_flux_pair_iff_signChange (N : Network S)
    (hsep : N.ReactantProductSeparated)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} (ρ : N.TrueReaction)
    (r : N.R) (hr : ¬ N.IsFlowChannel r) (β : ℝ) (s t : S)
    (hbeta : ∀ u, N.trueInternalClassFlux α ρ u = β * N.reactionVector r u)
    (hpos : 0 < N.trueInternalClassFlux α ρ s * σ s)
    (hneg : N.trueInternalClassFlux α ρ t * σ t < 0) :
    (N.trueSREdgeOfReactionVectorNe r hr t
    (by
        intro hz
        rw [hbeta t, hz] at hneg
        simp at hneg)).endpoint =
      (N.trueSREdgeOfReactionVectorNe r hr s
        (by
          intro hz
          rw [hbeta s, hz] at hpos
          simp at hpos)).endpoint ↔ σ t * σ s < 0 := by
  have ht : N.reactionVector r t ≠ 0 := by
    intro hz
    rw [hbeta t, hz] at hneg
    simp at hneg
  have hs : N.reactionVector r s ≠ 0 := by
    intro hz
    rw [hbeta s, hz] at hpos
    simp at hpos
  have hprod := signProduct_causal_iff
    (by simpa [hbeta s, mul_assoc] using hpos)
    (by simpa [hbeta t, mul_assoc] using hneg)
  have hsame := N.trueSREdge_sameEndpoint_iff_direction_mul_pos r hr t s ht hs
  have hdt : N.reactionDirectionSign r t = -N.reactionVector r t := by
    simp [reactionDirectionSign, reactionVector_apply]
  have hds : N.reactionDirectionSign r s = -N.reactionVector r s := by
    simp [reactionDirectionSign, reactionVector_apply]
  rw [hdt, hds] at hsame
  have hvec :
      (0 < (-N.reactionVector r t) * (-N.reactionVector r s)) ↔
        0 < N.reactionVector r t * N.reactionVector r s := by
    constructor <;> intro h <;> nlinarith
  calc
    _ ↔ 0 < N.reactionVector r t * N.reactionVector r s := hsame.trans hvec
    _ ↔ σ t * σ s < 0 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hprod

private theorem finRotate_eq_succ_of_lt {n : ℕ} (i : Fin n)
    (hi : i.1 + 1 < n) : finRotate n i = ⟨i.1 + 1, hi⟩ := by
  apply Fin.ext
  have h := congrArg Fin.val (finRotate_apply i)
  simpa [Fin.add_def, Nat.mod_eq_of_lt hi] using h

private theorem finRotate_last_zero (k : ℕ) :
    finRotate (k + 1) (Fin.last k) = ⟨0, by omega⟩ := by
  apply Fin.ext
  have h := congrArg Fin.val (finRotate_apply (Fin.last k))
  simpa [Fin.add_def] using h

/-- A chord from a cycle species to a nonadjacent reaction, when its reaction is causal at the
start and opposing at the other end of the arc, closes an even cycle sharing an S-to-R path with
the original. This is the concrete `hSR.2` obstruction for an extra class that lies on the cycle. -/
private theorem no_nonneighbor_chord (N : Network S)
    (hsep : N.ReactantProductSeparated) (hSR : N.TrueSRStrongCriterion)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} (C : N.TrueSRCycle n)
    (i0 : Fin n) (hi0 : i0.1 = 0)
    (hσ : ∀ i, σ (C.species i) ≠ 0)
    (hpair : ∀ i, C.isCPair i ↔
      σ (C.species i) * σ (C.species (finRotate n i)) < 0)
    (k : Fin n) (e : N.TrueSREdge)
    (hes : e.species = C.species i0) (her : e.reaction = C.reaction k)
    (hk0 : k ≠ i0) (hklast : k ≠ (⟨n - 1, by have := C.nontrivial; omega⟩ : Fin n))
    (β : ℝ)
    (hbeta : ∀ u, N.trueInternalClassFlux α (C.reaction k) u =
      β * N.reactionVector (C.rightEdge k).representative u)
    (hpos : 0 < N.trueInternalClassFlux α (C.reaction k) (C.species i0) * σ (C.species i0))
    (hneg : N.trueInternalClassFlux α (C.reaction k) (C.species k) * σ (C.species k) < 0) :
    False := by
  classical
  have hidx0 : i0 = ⟨0, by have := C.nontrivial; omega⟩ := Fin.ext hi0
  have hkpos : 0 < k.1 := by
    by_contra h
    have hkval : k.1 = 0 := by omega
    exact hk0 (Fin.ext (by rw [hi0]; exact hkval))
  have hkn : k.1 < n := k.isLt
  let r := (C.rightEdge k).representative
  have hr : ¬ N.IsFlowChannel r := by
    have hi : TrueReaction.Internal N (N.trueReaction r) := by
      rw [(C.rightEdge k).representative_class]
      exact (C.rightEdge k).internal
    change ¬ N.IsFlowChannel r at hi
    exact hi
  have hfluxS : N.trueInternalClassFlux α (C.reaction k) (C.species i0) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hpos
    exact (lt_irrefl 0) hpos
  have hfluxT : N.trueInternalClassFlux α (C.reaction k) (C.species k) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hneg
    exact (lt_irrefl 0) hneg
  have hrvecS : N.reactionVector r (C.species i0) ≠ 0 := by
    intro hz
    apply hfluxS
    rw [hbeta, hz]
    simp
  have hrvecT : N.reactionVector r (C.species k) ≠ 0 := by
    intro hz
    apply hfluxT
    rw [hbeta, hz]
    simp
  let es := N.trueSREdgeOfReactionVectorNe r hr (C.species i0) hrvecS
  let et := N.trueSREdgeOfReactionVectorNe r hr (C.species k) hrvecT
  have hesS : es.species = C.species i0 := by simp [es]
  have hetS : et.species = C.species k := by simp [et]
  have hesR : es.reaction = C.reaction k := by
    rw [Network.trueSREdgeOfReactionVectorNe_reaction]
    exact (C.rightEdge k).representative_class.trans (C.right_reaction k)
  have hetR : et.reaction = C.reaction k := by
    rw [Network.trueSREdgeOfReactionVectorNe_reaction]
    exact (C.rightEdge k).representative_class.trans (C.right_reaction k)
  have hEndS : e.endpoint = es.endpoint :=
    N.trueSREdge_endpoint_eq_of_same_class_and_species hsep e es
      (her.trans hesR.symm) (hes.trans hesS.symm)
  have hEndT : (C.leftEdge k).endpoint = et.endpoint :=
    N.trueSREdge_endpoint_eq_of_same_class_and_species hsep (C.leftEdge k) et
      ((C.left_reaction k).trans hetR.symm) (by rw [C.left_species k, hetS])
  have hpairChord : et.endpoint = es.endpoint ↔
      σ (C.species k) * σ (C.species i0) < 0 := by
    have hpos' : 0 < N.trueInternalClassFlux α (C.reaction k)
        (C.species i0) * σ (C.species i0) := hpos
    exact N.class_flux_pair_iff_signChange hsep (C.reaction k) r hr β
      (C.species i0) (C.species k) hbeta hpos' hneg
  have hes0 : e.species = C.species (⟨0, by have := C.nontrivial; omega⟩ : Fin n) := by
    simpa [hidx0] using hes
  let D := C.closeInitialArcWithChord k.1 hkn hkpos e hes0 her
  have hDpair : ∀ j, D.isCPair j ↔
      σ (D.species j) * σ (D.species (finRotate (k.1 + 1) j)) < 0 := by
    intro j
    by_cases hj : j.1 < k.1
    · let idx : Fin n := ⟨j.1, by omega⟩
      have hidxlt : idx.1 + 1 < n := by change j.1 + 1 < n; omega
      have hidxSucc : finRotate n idx = ⟨j.1 + 1, hidxlt⟩ :=
        finRotate_eq_succ_of_lt idx hidxlt
      have hjSucc : finRotate (k.1 + 1) j = ⟨j.1 + 1, by omega⟩ :=
        finRotate_eq_succ_of_lt j (by omega)
      have hfields : D.isCPair j ↔ C.isCPair idx := by
        simp [TrueSRCycle.isCPair, D, idx, hj,
          Network.TrueSRCycle.closeInitialArcWithChord_leftEdge,
          Network.TrueSRCycle.closeInitialArcWithChord_rightEdge]
      have hspecies : D.species j = C.species idx := by
        simp [D, idx, Network.TrueSRCycle.closeInitialArcWithChord_species]
      have hnext : D.species (finRotate (k.1 + 1) j) =
          C.species (finRotate n idx) := by
        rw [hjSucc, hidxSucc]
        simp [D, idx, Network.TrueSRCycle.closeInitialArcWithChord_species]
      rw [hfields, hpair idx, hspecies, hnext]
    · have hjlast : j = Fin.last k.1 := by
        apply Fin.ext
        change j.1 = k.1
        have := j.isLt
        omega
      have hspeciesLast : D.species j = C.species k := by
        rw [hjlast]
        simp [D, Network.TrueSRCycle.closeInitialArcWithChord_species]
      have hnextLast : D.species (finRotate (k.1 + 1) j) = C.species i0 := by
        rw [hjlast, finRotate_last_zero]
        simp [D, Network.TrueSRCycle.closeInitialArcWithChord_species, hidx0]
      have hpairLast : D.isCPair j ↔ et.endpoint = es.endpoint := by
        rw [hjlast, TrueSRCycle.isCPair]
        simp only [D, Network.TrueSRCycle.closeInitialArcWithChord_leftEdge,
          Network.TrueSRCycle.closeInitialArcWithChord_rightEdge]
        simpa [hEndT, hEndS]
      rw [hpairLast, hpairChord, hspeciesLast, hnextLast]
  have hDσ : ∀ j, σ (D.species j) ≠ 0 := by
    intro j
    let idx : Fin n := ⟨j.1, by have := j.isLt; omega⟩
    have hsp : D.species j = C.species idx := by
      simp [D, idx, Network.TrueSRCycle.closeInitialArcWithChord_species]
    rw [hsp]
    exact hσ idx
  have hCEven := N.trueSRCycle_even_of_signChange C σ hσ hpair
  have hDEven := N.trueSRCycle_even_of_signChange D σ hDσ hDpair
  have hnot : ¬ C.ContainsEdge e := by
    intro hcontains
    rcases hcontains with ⟨j, hinc⟩ | ⟨j, hinc⟩
    · have hreaction : C.reaction j = C.reaction k := by
        calc
          C.reaction j = (C.leftEdge j).reaction := (C.left_reaction j).symm
          _ = e.reaction := hinc.2.1.symm
          _ = C.reaction k := her
      have hidx : j = k := C.reaction_injective hreaction
      have hspecies : C.species i0 = C.species j := by
        calc
          C.species i0 = e.species := hes.symm
          _ = (C.leftEdge j).species := hinc.1
          _ = C.species j := C.left_species j
      have hzero : i0 = j := C.species_injective hspecies
      exact hk0 (hidx.symm.trans hzero.symm)
    · have hreaction : C.reaction j = C.reaction k := by
        calc
          C.reaction j = (C.rightEdge j).reaction := (C.right_reaction j).symm
          _ = e.reaction := hinc.2.1.symm
          _ = C.reaction k := her
      have hidx : j = k := C.reaction_injective hreaction
      have hspecies : i0 = finRotate n k := by
        have hsp0 : e.species = C.species i0 := hes
        have hsp1 := hinc.1
        have hnext : finRotate n k =
            (⟨(k.1 + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) := by
          apply Fin.ext
          have h := congrArg Fin.val (finRotate_apply k)
          simpa [Fin.add_def] using h
        rw [hidx, C.right_species k] at hsp1
        rw [← hnext] at hsp1
        exact C.species_injective (hsp0.symm.trans hsp1)
      have hkval : k.1 + 1 < n := by
        have hklastVal : k.1 ≠ n - 1 := by
          intro hval
          apply hklast
          apply Fin.ext
          exact hval
        have hn := C.nontrivial
        omega
      have hrotVal : (finRotate n k).1 = k.1 + 1 := by
        have h := congrArg Fin.val (finRotate_apply k)
        simpa [Fin.add_def, Nat.mod_eq_of_lt hkval] using h
      have hzero := congrArg Fin.val hspecies
      rw [hrotVal] at hzero
      omega
  exact TrueSRCycle.no_close_arc_chord_of_trueSRCriterion N hSR C hCEven k.1 hkn hkpos e hes0 her hnot hDEven

/-! A clean species-to-reaction chord across the cycle's right edge is forbidden.  This is the
path form of `no_nonneighbor_chord`: the endpoints are a cycle species and its predecessor
reaction, while the chord itself may have any length. -/
private theorem no_clean_predecessor_chord_of_trueSRCriterion (N : Network S)
    (hSR : N.TrueSRStrongCriterion) {n L : ℕ}
    (C : N.TrueSRCycle n) (hCeven : C.Even) (i : Fin n)
    (P : N.TrueSRPath L) (hchord : C.IsChord P)
    (hclean : ∀ p : Fin (L + 1), p.1 ≠ 0 → p.1 ≠ L →
      ¬ C.HasVertex (P.vertex p))
    (hstart : P.vertex 0 = Sum.inl (C.species (finRotate n i)))
    (hend : P.vertex (Fin.last L) =
      Sum.inr ⟨C.reaction i, C.reaction_internal i⟩)
    (hlarge : 2 ≤ L) : False := by
  classical
  obtain ⟨k, hn⟩ : ∃ k : ℕ, n = k + 2 := by
    refine ⟨n - 2, ?_⟩
    have := C.nontrivial
    omega
  subst n
  let startIdx : Fin (k + 2) := finRotate (k + 2) i
  let zeroIdx : Fin (k + 2) := ⟨0, by omega⟩
  let lastIdx : Fin (k + 2) := Fin.last (k + 1)
  let rotIdx (a : Fin (k + 2)) : Fin (k + 2) := a + startIdx
  have hstartIdx : startIdx = i + 1 := finRotate_apply i
  have hlast : lastIdx = -1 := by
    apply Fin.ext
    have hlt : k + 1 < k + 2 := by omega
    have hlt1 : 1 < k + 2 := by omega
    simp [lastIdx, Fin.neg_def]
  have hrotlast : rotIdx lastIdx = i := by
    dsimp [rotIdx]
    calc
      lastIdx + startIdx = -1 + (i + 1) := by rw [hlast, hstartIdx]
      _ = i := by abel
  have hrotzero : rotIdx zeroIdx = startIdx := by
    dsimp [rotIdx, zeroIdx]
    exact zero_add startIdx
  let Crot : N.TrueSRCycle (k + 2) := C.rotate startIdx.1
  have hrotSpecies (a : Fin (k + 2)) : Crot.species a = C.species (rotIdx a) := by
    simp [Crot, rotIdx, Fin.add_def]
  have hrotReaction (a : Fin (k + 2)) : Crot.reaction a = C.reaction (rotIdx a) := by
    simp [Crot, rotIdx, Fin.add_def]
  have hrotLeft (a : Fin (k + 2)) : Crot.leftEdge a = C.leftEdge (rotIdx a) := by
    simp [Crot, rotIdx, Fin.add_def]
  have hrotRight (a : Fin (k + 2)) : Crot.rightEdge a = C.rightEdge (rotIdx a) := by
    simp [Crot, rotIdx, Fin.add_def]
  have hrotSurj (b : Fin (k + 2)) : ∃ a, rotIdx a = b := by
    refine ⟨b - startIdx, ?_⟩
    dsimp [rotIdx]
    exact sub_add_cancel b startIdx
  have hspeciesIff (s : S) : Crot.HasSpecies s ↔ C.HasSpecies s := by
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨rotIdx a, (hrotSpecies a).trans ha⟩
    · rintro ⟨b, hb⟩
      obtain ⟨a, ha⟩ := hrotSurj b
      exact ⟨a, by rw [hrotSpecies, ha, hb]⟩
  have hreactionsIff (ρ : N.TrueReaction) : Crot.HasReaction ρ ↔ C.HasReaction ρ := by
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨rotIdx a, (hrotReaction a).trans ha⟩
    · rintro ⟨b, hb⟩
      obtain ⟨a, ha⟩ := hrotSurj b
      exact ⟨a, by rw [hrotReaction, ha, hb]⟩
  have hverticesIff (v : N.TrueSRVertex) : Crot.HasVertex v ↔ C.HasVertex v := by
    cases v with
    | inl s => exact hspeciesIff s
    | inr ρ => exact hreactionsIff ρ.1
  have hchordRot : Crot.IsChord P := by
    rcases hchord with ⟨hs, hρ, hleft, hright⟩
    refine ⟨(hspeciesIff _).2 hs, (hreactionsIff _).2 hρ, ?_, ?_⟩
    · intro p a hsame
      apply hleft p (rotIdx a)
      simpa [hrotLeft a] using hsame
    · intro p a hsame
      apply hright p (rotIdx a)
      simpa [hrotRight a] using hsame
  have hcleanRot : ∀ p : Fin (L + 1), p.1 ≠ 0 → p.1 ≠ L →
      ¬ Crot.HasVertex (P.vertex p) := by
    intro p hp0 hpL hon
    exact hclean p hp0 hpL ((hverticesIff _).mp hon)
  have hCrotEven : Crot.Even := C.rotate_even startIdx.1 hCeven
  have hCrotStart : Crot.species zeroIdx = C.species (finRotate (k + 2) i) := by
    rw [hrotSpecies, hrotzero]
  have hPstart : P.vertex 0 = Sum.inl (Crot.species zeroIdx) := by
    rw [hstart, hCrotStart]
  have hCrotEnd : Crot.reaction lastIdx = C.reaction i := by
    rw [hrotReaction, hrotlast]
  have hPend : P.vertex (Fin.last L) =
      Sum.inr ⟨Crot.reaction lastIdx, Crot.reaction_internal lastIdx⟩ := by
    calc
      P.vertex (Fin.last L) = Sum.inr ⟨C.reaction i, C.reaction_internal i⟩ := hend
      _ = Sum.inr ⟨Crot.reaction lastIdx, Crot.reaction_internal lastIdx⟩ := by
        apply congrArg Sum.inr
        apply Subtype.ext
        exact hCrotEnd.symm
  have hPstartBase : P.startSpecies = Crot.species zeroIdx := by
    have hz := P.vertex_zero
    exact Sum.inl.inj (hz.symm.trans hPstart)
  have hPendBase : P.endReaction.1 = Crot.reaction lastIdx := by
    have hz := P.vertex_last
    have heq := Sum.inr.inj (hz.symm.trans hPend)
    exact congrArg Subtype.val heq
  exact N.no_arc_chord_of_trueSRCriterion hSR Crot hCrotEven P hchordRot
    hcleanRot hPstartBase hPendBase hlarge

/-- **Minimal escape from an off-cycle vertex.**  If some vertex of `T` sits on the cycle and
`u` does not, then among the paths leaving `u` for the cycle there is one whose every vertex
but the last misses the cycle: take a shortest such path, and cutting it at an earlier
cycle vertex would give a shorter one. -/
private theorem exists_minimal_escape (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ))
    (OnC : N.TrueSRVertex → Prop)
    (u v₀ : {x : N.TrueInternalAggregateVertex α σ // x ∈ T})
    (hu : ¬ OnC (N.aggregateVertexToTrueSRVertex u.1))
    (hv₀ : OnC (N.aggregateVertexToTrueSRVertex v₀.1))
    (W₀ : (CRNT.relationGraphOn
      (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T).Walk u v₀)
    (hW₀ : W₀.IsPath) :
    ∃ (v : {x : N.TrueInternalAggregateVertex α σ // x ∈ T})
      (W : (CRNT.relationGraphOn
        (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T).Walk u v),
      OnC (N.aggregateVertexToTrueSRVertex v.1) ∧ W.IsPath ∧
        ∀ i, i < W.length →
          ¬ OnC (N.aggregateVertexToTrueSRVertex (W.getVert i).1) := by
  classical
  suffices H : ∀ k : ℕ, ∀ (w : {x : N.TrueInternalAggregateVertex α σ // x ∈ T})
      (W : (CRNT.relationGraphOn
        (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T).Walk u w),
      W.length = k → OnC (N.aggregateVertexToTrueSRVertex w.1) → W.IsPath →
      ∃ (v : {x : N.TrueInternalAggregateVertex α σ // x ∈ T})
        (W' : (CRNT.relationGraphOn
          (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T).Walk u v),
        OnC (N.aggregateVertexToTrueSRVertex v.1) ∧ W'.IsPath ∧
          ∀ i, i < W'.length →
            ¬ OnC (N.aggregateVertexToTrueSRVertex (W'.getVert i).1) by
    exact H W₀.length v₀ W₀ rfl hv₀ hW₀
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro w W hk hw hWp
    by_cases hclean : ∀ i, i < W.length →
        ¬ OnC (N.aggregateVertexToTrueSRVertex (W.getVert i).1)
    · exact ⟨w, W, hw, hWp, hclean⟩
    · push_neg at hclean
      obtain ⟨i, hi, hOn⟩ := hclean
      have hmem : W.getVert i ∈ W.support := W.getVert_mem_support i
      have hne : W.getVert i ≠ w := by
        intro heq
        have heq' : W.getVert i = W.getVert W.length := by rw [heq, W.getVert_length]
        have := hWp.getVert_injOn (Set.mem_setOf.mpr (le_of_lt hi))
          (Set.mem_setOf.mpr (le_refl W.length)) heq'
        omega
      have hsplit : (W.takeUntil (W.getVert i) hmem).length
          + (W.dropUntil (W.getVert i) hmem).length = W.length := by
        rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec]
      have hdrop : 0 < (W.dropUntil (W.getVert i) hmem).length :=
        SimpleGraph.Walk.not_nil_iff_lt_length.mp
          ((W.dropUntil (W.getVert i) hmem).not_nil_of_ne hne)
      exact ih (W.takeUntil (W.getVert i) hmem).length (by omega) (W.getVert i)
        (W.takeUntil (W.getVert i) hmem) rfl hOn (hWp.takeUntil hmem)



/-- **The directed chord into an off-cycle reaction class.**

Take a shortest *directed* causal path from a distinguished (`Good`, i.e. on-cycle) vertex to
the off-cycle class `q`, and extend it by the attachment edge `q → s`.  By
`exists_minimal_relPath` the path is injective and meets `Good` only at its start, so the
extension is injective too (the new vertex `Sum.inl s` is `Good`, hence not already on the
path) and its interior misses `Good` entirely.

Running the path *into* `q` rather than out of it is what makes the orientation work out: `q`
then has one incoming and one outgoing chord edge, so its two SR edges c-pair exactly when `σ`
changes sign, which is what `trueSRCycle_even_of_signChange` consumes.

The second alternative is the degenerate one: the shortest path may already start at `s`, in
which case the extension closes a loop rather than forming a chord. -/
private theorem exists_directed_chord (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ))
    (hsource : ∀ a b : N.TrueInternalAggregateVertex α σ,
      N.TrueInternalAggregateCausalEdge a b → b ∈ T → a ∈ T)
    (Good : N.TrueInternalAggregateVertex α σ → Prop)
    {q : N.ActiveAggregateTrueReaction α σ} {s : AggregateActiveSpecies σ}
    (hqT : Sum.inr q ∈ T) (hsT : Sum.inl s ∈ T)
    (hqOff : ¬ Good (Sum.inr q)) (hsOn : Good (Sum.inl s))
    (hatt : N.TrueInternalAggregateCausalEdge (Sum.inr q) (Sum.inl s))
    {a₀ : N.TrueInternalAggregateVertex α σ} (ha₀ : Good a₀)
    (hreach : Relation.ReflTransGen
      (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) a₀ (Sum.inr q)) :
    (∃ (m : ℕ) (P : CRNT.RelPath
        (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T m),
      2 ≤ m ∧ Function.Injective P.vertex ∧ Good (P.vertex ⟨0, by omega⟩) ∧
        P.vertex ⟨m, by omega⟩ = Sum.inl s ∧
        (∃ i : Fin (m + 1), i.1 + 1 = m ∧ P.vertex i = Sum.inr q) ∧
        ∀ i : Fin (m + 1), i.1 ≠ 0 → i.1 ≠ m → ¬ Good (P.vertex i))
    ∨ (∃ (m : ℕ) (Q : CRNT.RelPath
        (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T m),
      Q.vertex ⟨0, by omega⟩ = Sum.inl s ∧ Q.vertex ⟨m, by omega⟩ = Sum.inr q ∧
        ∀ i : Fin (m + 1), i.1 ≠ 0 → ¬ Good (Q.vertex i)) := by
  classical
  obtain ⟨m, Q, hg0, hqm, hinj, hlate⟩ :=
    CRNT.exists_minimal_relPath Good hsource hqT ha₀ hreach
  by_cases hstart : Q.vertex ⟨0, by omega⟩ = Sum.inl s
  · exact Or.inr ⟨m, Q, hstart, hqm, hlate⟩
  · have hnew : ∀ i, Q.vertex i ≠ Sum.inl s := by
      intro i hi
      by_cases hi0 : i.1 = 0
      · refine hstart ?_
        rw [show (⟨0, by omega⟩ : Fin (m + 1)) = i from
          Fin.ext (by show (0 : ℕ) = i.1; omega)]
        exact hi
      · exact hlate i hi0 (by rw [hi]; exact hsOn)
    have hstep : N.TrueInternalAggregateCausalEdge (Q.vertex ⟨m, by omega⟩) (Sum.inl s) := by
      rw [hqm]; exact hatt
    have hmpos : 0 < m := by
      by_contra hmpos
      have hm0 : m = 0 := by omega
      subst m
      have hidx : (⟨0, by omega⟩ : Fin (0 + 1)) = ⟨0, by omega⟩ := rfl
      have hqeq : Q.vertex ⟨0, by omega⟩ = Sum.inr q := by
        rw [hidx]
        exact hqm
      exact hqOff (by rw [← hqeq]; exact hg0)
    refine Or.inl ⟨m + 1, Q.concat (Sum.inl s) hsT hstep, by omega,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact Q.concat_injective (Sum.inl s) hsT hstep hinj hnew
    · rw [Q.concat_vertex_le (Sum.inl s) hsT hstep ⟨0, by omega⟩
        (show ((⟨0, by omega⟩ : Fin (m + 1 + 1))).1 ≤ m by show (0 : ℕ) ≤ m; omega)]
      exact hg0
    · exact Q.concat_vertex_last (Sum.inl s) hsT hstep
    · refine ⟨Fin.castSucc (Fin.last m), by simp, ?_⟩
      exact (Q.concat_vertex_le (Sum.inl s) hsT hstep
        (Fin.castSucc (Fin.last m)) (by simp)).trans hqm
    · intro i hi0 him
      have hilt := i.isLt
      rw [Q.concat_vertex_le (Sum.inl s) hsT hstep i (by omega)]
      exact hlate ⟨i.1, by omega⟩ (by simpa using hi0)


/-- Each species-to-species glued cycle has exactly the edges of its two defining paths. -/
private theorem ssGlueCycle_containsEdge_iff_speciesPaths {N : Network S} {i j : ℕ}
    (P : N.TrueSRSSPath (2 * j + 2)) (Q : N.TrueSRSSPath (2 * i + 2))
    (h : TrueSRSSPath.SSGluable P Q) (e : N.TrueSREdge) :
    (TrueSRSSPath.ssGlueCycle P Q h).ContainsEdge e ↔
      (∃ p, e.SameIncidence (P.edge p)) ∨ (∃ q, e.SameIncidence (Q.edge q)) := by
  simp only [TrueSRSSPath.ssGlueCycle_eq, TrueSRPath.glueCycle_containsEdge_iff]
  constructor
  · rintro (⟨p, hp⟩ | ⟨q, hq⟩)
    · left
      exact ⟨⟨p.1, by have := p.isLt; have := P.two_le_length; omega⟩, by
        simpa [TrueSRSSPath.toPath_edge] using hp⟩
    · by_cases hlt : q.1 < 2 * i + 2
      · right
        exact ⟨⟨q.1, hlt⟩, by
          have hq' := hq
          rw [TrueSRSSPath.partner,
            TrueSRSSPath.extend_edge_lt Q P.lastEdge
              (TrueSRSSPath.extend_hes P Q h)
              (TrueSRSSPath.extend_hnew P Q h)
              (TrueSRSSPath.extend_hedge P Q h) q (by omega)] at hq'
          simpa using hq'⟩
      · left
        have hlast : q.1 = 2 * i + 2 := by
          have := q.isLt
          omega
        have hqidx : q = ⟨2 * i + 2, by omega⟩ := Fin.ext hlast
        rw [hqidx] at hq
        refine ⟨⟨2 * j + 1, by omega⟩, ?_⟩
        rw [TrueSRSSPath.partner,
          TrueSRSSPath.extend_edge_last Q P.lastEdge
            (TrueSRSSPath.extend_hes P Q h)
            (TrueSRSSPath.extend_hnew P Q h)
            (TrueSRSSPath.extend_hedge P Q h) ⟨2 * i + 2, by omega⟩ (by omega),
          TrueSRSSPath.lastEdge] at hq
        simpa [hlast] using hq
  · rintro (⟨p, hp⟩ | ⟨q, hq⟩)
    · by_cases hlt : p.1 < 2 * j + 1
      · left
        exact ⟨⟨p.1, by omega⟩, by
          simpa [TrueSRSSPath.toPath_edge] using hp⟩
      · right
        have hlast : p.1 = 2 * j + 1 := by
          have := p.isLt
          omega
        refine ⟨⟨2 * i + 2, by omega⟩, ?_⟩
        let r : Fin (2 * i + 2 + 1) := Fin.last (2 * i + 2)
        have hr : r = (⟨2 * i + 2, by omega⟩ : Fin (2 * i + 2 + 1)) := by
          apply Fin.ext
          rfl
        rw [← hr]
        rw [TrueSRSSPath.partner,
          TrueSRSSPath.extend_edge_last Q P.lastEdge
            (TrueSRSSPath.extend_hes P Q h)
            (TrueSRSSPath.extend_hnew P Q h)
            (TrueSRSSPath.extend_hedge P Q h) r (by simp [r]),
          TrueSRSSPath.lastEdge]
        have hlastEdge : p = ⟨2 * j + 1, by omega⟩ := Fin.ext hlast
        rw [hlastEdge] at hp
        simpa using hp
    · right
      have hqL : q.1 < 2 * i + 2 := q.isLt
      let r : Fin (2 * i + 2 + 1) := ⟨q.1, by omega⟩
      exact ⟨⟨q.1, by omega⟩, by
        rw [TrueSRSSPath.partner,
          TrueSRSSPath.extend_edge_lt Q P.lastEdge
            (TrueSRSSPath.extend_hes P Q h)
            (TrueSRSSPath.extend_hnew P Q h)
            (TrueSRSSPath.extend_hedge P Q h) r hqL]
        simpa [r] using hq⟩

/-- Two cycles glued from three pairwise compatible species-to-species paths have exactly
the first path as their common edge set. The common path's endpoints are both species. -/
private theorem speciesEar_glue_common_edges {N : Network S} {i j k : ℕ}
    (P : N.TrueSRSSPath (2 * j + 2))
    (Q : N.TrueSRSSPath (2 * i + 2))
    (R : N.TrueSRSSPath (2 * k + 2))
    (hPQ : TrueSRSSPath.SSGluable P Q)
    (hPR : TrueSRSSPath.SSGluable P R)
    (hQR : TrueSRSSPath.SSGluable Q R) :
    let D₁ := TrueSRSSPath.ssGlueCycle P Q hPQ
    let D₂ := TrueSRSSPath.ssGlueCycle P R hPR
    (∀ p : Fin (2 * j + 2), D₁.ContainsEdge (P.edge p) ∧ D₂.ContainsEdge (P.edge p)) ∧
    (∀ e, D₁.ContainsEdge e → D₂.ContainsEdge e →
      ∃ p : Fin (2 * j + 2), e.SameIncidence (P.edge p)) ∧
    (∃ s₀ s₁, P.vertex 0 = Sum.inl s₀ ∧
      P.vertex (Fin.last (2 * j + 2)) = Sum.inl s₁) := by
  classical
  let D₁ := TrueSRSSPath.ssGlueCycle P Q hPQ
  let D₂ := TrueSRSSPath.ssGlueCycle P R hPR
  change (∀ p : Fin (2 * j + 2), D₁.ContainsEdge (P.edge p) ∧ D₂.ContainsEdge (P.edge p)) ∧ _
  constructor
  · intro p
    constructor
    · exact (ssGlueCycle_containsEdge_iff_speciesPaths P Q hPQ (P.edge p)).2
        (Or.inl ⟨p, TrueSREdge.SameIncidence.refl _⟩)
    · exact (ssGlueCycle_containsEdge_iff_speciesPaths P R hPR (P.edge p)).2
        (Or.inl ⟨p, TrueSREdge.SameIncidence.refl _⟩)
  · constructor
    · intro e he₁ he₂
      rcases (ssGlueCycle_containsEdge_iff_speciesPaths P Q hPQ e).1 he₁ with hP | hQ
      · exact hP
      · rcases (ssGlueCycle_containsEdge_iff_speciesPaths P R hPR e).1 he₂ with hP | hR
        · exact False.elim (hPQ.edge_disjoint hP.choose hQ.choose
            (TrueSREdge.SameIncidence.trans (TrueSREdge.SameIncidence.symm hP.choose_spec)
              hQ.choose_spec))
        · exact False.elim (hQR.edge_disjoint hQ.choose hR.choose
            (TrueSREdge.SameIncidence.trans (TrueSREdge.SameIncidence.symm hQ.choose_spec)
              hR.choose_spec))
    · exact ⟨P.starts_at_species.choose, P.ends_at_species.choose,
        P.starts_at_species.choose_spec, P.ends_at_species.choose_spec⟩

/-- **Shinar--Feinberg true-SR strong-concordance theorem.**

Reactant/product separation is required to identify true-SR edge labels with net stoichiometric
coefficients. The hypothesis is necessary; see `CRNT/Examples/TrueSRNetCoeffCounterexample.lean`.
-/
theorem stronglyConcordant_fullyOpen_of_trueSRCriterion
    (N : Network S) (hsep : N.ReactantProductSeparated)
    (hflow : N.ZeroComplexReactionsAreFlows)
    (hSR : N.TrueSRStrongCriterion) :
    N.fullyOpen.StronglyConcordant := by
  classical
  unfold StronglyConcordant
  by_contra hnot
  obtain ⟨α, σ, W⟩ := hnot
  obtain ⟨T, hne, hscc, hsource, hconnected, hspecies, hreactions, hlocal⟩ :=
    N.exists_trueInternalAggregateCausalSource_data hflow W
  have hparts : (∃ s : AggregateActiveSpecies σ, Sum.inl s ∈ T) ∧
      (∃ ρ : N.ActiveAggregateTrueReaction α σ, Sum.inr ρ ∈ T) :=
    ⟨hspecies, hreactions⟩
  obtain ⟨p, hp2, hpeven, c, hcinj, hcT, hcedge⟩ :=
    N.exists_simple_directed_cycle_in_trueInternalAggregateSource T hscc hsource hparts
  obtain ⟨d, hdinj, hdT, hdstart, hdedge⟩ :=
    N.rotate_trueInternalAggregateCycle_to_species T hp2 c hcinj hcT hcedge
  obtain ⟨n, hn2, C, hcycleEq, hCeven, hCpair, hrep, hCspT, hCrxnT,
      hcycleVertexSp, hcycleVertexRx, beta, hbeta, hneg, hpos⟩ :=
    N.trueSRCycle_of_simple_aggregate_cycle hp2 hpeven d hdinj T hdT hdstart hdedge
  have hSCycle : C.SCycle := hSR.1 C hCeven
  have hSCycleNet : C.SCycleNet :=
    (TrueSRCycle.sCycleNet_iff_sCycle_of_separated N hsep C).mpr hSCycle
  let F := N.trueInternalAggregateSourceClasses α σ T
  have hsum : ∀ i, 0 < ∑ ρ ∈ F,
      (N.trueInternalClassFlux α ρ (C.species (finRotate n i))) *
        σ (C.species (finRotate n i)) := by
    intro i
    obtain ⟨s, hsSpecies, hsT⟩ := hCspT (finRotate n i)
    have h := hlocal s hsT
    simpa [F, hsSpecies] using h
  have hclass : ∀ i, C.reaction i ∈ F := hCrxnT
  have hcausal : ∀ i, 0 <
      (N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i))) *
        σ (C.species (finRotate n i)) := hpos
  have hopp : ∀ i,
      (N.trueInternalClassFlux α (C.reaction (finRotate n i))
        (C.species (finRotate n i))) * σ (C.species (finRotate n i)) < 0 := by
    intro i
    exact hneg (finRotate n i)
  obtain ⟨i, ρ, hρF, hρneLeft, hρneRight, hρpos⟩ :=
    N.exists_positive_off_cycle_aggregate_class hsep C hSCycleNet F beta hrep hbeta
      hclass hsum hcausal hopp
  have hσi : σ (C.species (finRotate n i)) ≠ 0 := by
    intro hz
    have h := hcausal i
    rw [hz, mul_zero] at h
    exact (lt_irrefl 0) h
  let s : AggregateActiveSpecies σ := ⟨C.species (finRotate n i), hσi⟩
  have hclassInT :
      ∃ q : N.ActiveAggregateTrueReaction α σ, q.1 = ρ ∧ Sum.inr q ∈ T := by
    simpa [F, trueInternalAggregateSourceClasses] using hρF
  obtain ⟨q, hqρ, hqT⟩ := hclassInT
  have hattachment :
      N.TrueInternalAggregateCausalEdge (Sum.inr q) (Sum.inl s) := by
    change 0 < N.trueInternalClassFlux α q.1 s.1 * σ s.1
    rw [hqρ]
    exact hρpos
  obtain ⟨t, htailEdge, htT⟩ :=
    N.activeAggregateClass_negative_species_mem_source W T hsource q hqT
  have htail := htailEdge
  change N.trueInternalClassFlux α q.1 t.1 * σ t.1 < 0 at htail
  have hhead : 0 < N.trueInternalClassFlux α q.1 s.1 * σ s.1 := by
    simpa [s, hqρ] using hρpos
  have htailNeHead : t.1 ≠ s.1 := by
    intro heq
    have hnegAtHead :
        N.trueInternalClassFlux α q.1 s.1 * σ s.1 < 0 := by
      simpa [heq] using htail
    linarith
  have hcycleReactionT :
      ∃ qC : N.ActiveAggregateTrueReaction α σ,
        qC.1 = C.reaction i ∧ Sum.inr qC ∈ T := by
    simpa [F, trueInternalAggregateSourceClasses] using hCrxnT i
  obtain ⟨qC, hqC, hqCT⟩ := hcycleReactionT
  have htailCycleReactionNe :
      (⟨Sum.inl t, htT⟩ : {v : N.TrueInternalAggregateVertex α σ // v ∈ T}) ≠
        ⟨Sum.inr qC, hqCT⟩ := by
    intro heq
    have hval := congrArg Subtype.val heq
    exact Sum.inl_ne_inr hval
  obtain ⟨sourcePath, hsourcePath⟩ :=
    CRNT.relationGraphOn_exists_isPath_of_source
      (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T hne hscc hsource
      (Sum.inl t) (Sum.inr qC) htT hqCT
  let sourceSRPath : N.TrueSRPath sourcePath.length :=
    N.aggregateSourcePathToTrueSRPath T htT hqCT sourcePath hsourcePath
  have hsourceSRPathOdd : Odd sourcePath.length := sourceSRPath.odd_length
  have hsourcePathNonempty : 0 < sourcePath.length := by
    obtain ⟨k, hk⟩ := hsourceSRPathOdd
    omega
  have htailFlux : N.trueInternalClassFlux α q.1 t.1 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at htail
    exact (lt_irrefl 0) htail
  have hheadFlux : N.trueInternalClassFlux α q.1 s.1 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hhead
    exact (lt_irrefl 0) hhead
  obtain ⟨eTail, heTailSpecies, heTailReaction⟩ :=
    N.exists_trueSREdge_of_nonzero_trueInternalClassFlux q.1 t.1 htailFlux
  obtain ⟨eHead, heHeadSpecies, heHeadReaction⟩ :=
    N.exists_trueSREdge_of_nonzero_trueInternalClassFlux q.1 s.1 hheadFlux
  have hspeciesTailHead : eTail.species ≠ eHead.species := by
    rw [heTailSpecies, heHeadSpecies]
    exact htailNeHead
  have hsameReaction : eTail.reaction = eHead.reaction :=
    heTailReaction.trans heHeadReaction.symm
  have hσC : ∀ j, σ (C.species j) ≠ 0 := by
    intro j
    obtain ⟨s, hs, _⟩ := hCspT j
    rw [← hs]
    exact s.2
  have hρnotCycle : ∀ j, C.reaction j ≠ ρ := by
    intro j hρj
    letI : NeZero n := ⟨by have := C.nontrivial; omega⟩
    let startIdx : Fin n := finRotate n i
    let Crot : N.TrueSRCycle n := C.rotate startIdx.1
    let zeroIdx : Fin n := ⟨0, by have := C.nontrivial; omega⟩
    let lastIdx : Fin n := ⟨n - 1, by have := C.nontrivial; omega⟩
    let rotIdx (a : Fin n) : Fin n := a + startIdx
    let k : Fin n := j - startIdx
    have hrotk : rotIdx k = j := by
      dsimp [rotIdx, k]
      exact sub_add_cancel j startIdx
    have hrotzero : rotIdx zeroIdx = startIdx := by
      dsimp [rotIdx, zeroIdx]
      exact zero_add startIdx
    have hstart : startIdx = i + 1 := by
      exact finRotate_apply i
    have hlast : lastIdx = -1 := by
      apply Fin.ext
      have hlt : n - 1 < n := by have := C.nontrivial; omega
      have hlt1 : 1 < n := by have := C.nontrivial; omega
      simp [lastIdx, Fin.neg_def]
      rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt]
    have hrotlast : rotIdx lastIdx = i := by
      dsimp [rotIdx]
      calc
        lastIdx + startIdx = -1 + (i + 1) := by rw [hlast, hstart]
        _ = i := by abel
    have hCrotSpecies (a : Fin n) : Crot.species a = C.species (rotIdx a) := by
      simp [Crot, rotIdx, Fin.add_def]
    have hCrotReaction (a : Fin n) : Crot.reaction a = C.reaction (rotIdx a) := by
      simp [Crot, rotIdx, Fin.add_def]
    have hCrotRightRep (a : Fin n) :
        (Crot.rightEdge a).representative = (C.rightEdge (rotIdx a)).representative := by
      simp [Crot, rotIdx, Fin.add_def]
    have hRρ : Crot.reaction k = ρ := by
      rw [hCrotReaction, hrotk, hρj]
    have hk0 : k ≠ zeroIdx := by
      intro hk
      apply hρneRight
      calc
        ρ = Crot.reaction k := hRρ.symm
        _ = Crot.reaction zeroIdx := congrArg Crot.reaction hk
        _ = C.reaction (finRotate n i) := by
          rw [hCrotReaction, hrotzero]
    have hklast : k ≠ lastIdx := by
      intro hk
      apply hρneLeft
      calc
        ρ = Crot.reaction k := hRρ.symm
        _ = Crot.reaction lastIdx := congrArg Crot.reaction hk
        _ = C.reaction i := by rw [hCrotReaction, hrotlast]
    have hσrot : ∀ a, σ (Crot.species a) ≠ 0 := by
      intro a
      rw [hCrotSpecies]
      exact hσC (rotIdx a)
    have hpairrot : ∀ a, Crot.isCPair a ↔
        σ (Crot.species a) * σ (Crot.species (finRotate n a)) < 0 := by
      intro a
      simpa [Crot] using
        N.rotated_trueSRCycle_pair_iff_signChange C hCpair startIdx.1 a
    let βrot : Fin n → ℝ := fun a => beta (rotIdx a)
    have hbetaRot : ∀ a u, N.trueInternalClassFlux α (Crot.reaction a) u =
        βrot a * N.reactionVector (Crot.rightEdge a).representative u := by
      intro a u
      rw [hCrotReaction, hCrotRightRep]
      exact hbeta (rotIdx a) u
    have hposrot : 0 < N.trueInternalClassFlux α (Crot.reaction k)
        (Crot.species zeroIdx) * σ (Crot.species zeroIdx) := by
      rw [hCrotReaction, hrotk, hρj, hCrotSpecies, hrotzero]
      exact hρpos
    let jprev : Fin n := (finRotate n).symm j
    have hjprev : finRotate n jprev = j := Equiv.apply_symm_apply (finRotate n) j
    have hnegOriginal :
        N.trueInternalClassFlux α (C.reaction j) (C.species j) * σ (C.species j) < 0 := by
      simpa [jprev, hjprev] using hopp jprev
    have hnegrot :  N.trueInternalClassFlux α (Crot.reaction k)
        (Crot.species k) * σ (Crot.species k) < 0 := by
      simpa [hCrotReaction, hCrotSpecies, hrotk, hρj] using hnegOriginal
    have heHeadSpecies' : eHead.species = Crot.species zeroIdx := by
      rw [heHeadSpecies]
      simp [s, Crot, zeroIdx, startIdx, finRotate_apply, Fin.add_def]
    have heHeadReaction' : eHead.reaction = Crot.reaction k :=
      heHeadReaction.trans (hqρ.trans hRρ.symm)
    exact N.no_nonneighbor_chord hsep hSR Crot zeroIdx rfl hσrot hpairrot
      k eHead heHeadSpecies' heHeadReaction' hk0 hklast (βrot k) (hbetaRot k)
      hposrot hnegrot
  have hqOffCycle : ¬ C.HasReaction q.1 := by
    rintro ⟨j, hj⟩
    apply hρnotCycle j
    calc
      C.reaction j = q.1 := hj
      _ = ρ := hqρ
  have hsT : Sum.inl s ∈ T := by
    obtain ⟨s', hsSpecies, hsT⟩ := hCspT (finRotate n i)
    have hsEq : s' = s := by
      apply Subtype.ext
      exact hsSpecies
    simpa [hsEq] using hsT
  have hsCycle : C.HasSpecies s.1 := by
    refine ⟨finRotate n i, ?_⟩
    rfl
  have hqCCycle : C.HasReaction qC.1 := ⟨i, hqC.symm⟩
  have hqNeC : q.1 ≠ qC.1 := by
    intro heq
    apply hρnotCycle i
    calc
      C.reaction i = qC.1 := hqC.symm
      _ = q.1 := heq.symm
      _ = ρ := hqρ
  have hqPathEndpointsNe :
      (⟨Sum.inr q, hqT⟩ : {v : N.TrueInternalAggregateVertex α σ // v ∈ T}) ≠
        ⟨Sum.inr qC, hqCT⟩ := by
    intro heq
    have hqeq : q = qC := by
      injection (congrArg Subtype.val heq)
    exact hqNeC (congrArg (fun x : N.ActiveAggregateTrueReaction α σ => x.1) hqeq)
  obtain ⟨qPath, hqPath⟩ :=
    CRNT.relationGraphOn_exists_isPath_of_source
      (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T hne hscc hsource
      (Sum.inr q) (Sum.inr qC) hqT hqCT
  have hqPathNonempty : 0 < qPath.length :=
    (SimpleGraph.Walk.not_nil_iff_lt_length).mp (qPath.not_nil_of_ne hqPathEndpointsNe)
  by_cases hqPathClean : ∀ j, j < qPath.length →
      ¬ C.HasVertex (N.aggregateVertexToTrueSRVertex (qPath.getVert j).1)
  · obtain ⟨P, hPChord, hPStartRaw, hPEndRaw, hPclean⟩ :=
      N.aggregateSourceReactionPath_prefix_chord T C hsT hqT hqCT hsCycle hqCCycle
        hqOffCycle hattachment qPath hqPath hqPathClean
    have hPstart : P.vertex 0 = Sum.inl (C.species (finRotate n i)) := by
      simpa [s] using hPStartRaw
    have hPend : P.vertex (Fin.last (qPath.length + 1)) =
        Sum.inr ⟨C.reaction i, C.reaction_internal i⟩ := by
      calc
        P.vertex (Fin.last (qPath.length + 1)) =
            Sum.inr ⟨qC.1, N.activeAggregateTrueReaction_internal qC⟩ := hPEndRaw
        _ = Sum.inr ⟨C.reaction i, C.reaction_internal i⟩ := by
          apply congrArg Sum.inr
          apply Subtype.ext
          exact hqC
    have hPlarge : 2 ≤ qPath.length + 1 := by omega
    exact N.no_clean_predecessor_chord_of_trueSRCriterion hSR C hCeven i P
      hPChord hPclean hPstart hPend hPlarge
  · have hspan : ∃ (M : ℕ) (Q : N.TrueSRPath M),
        C.HasVertex (Q.vertex ⟨0, by omega⟩) ∧
        C.HasVertex (Q.vertex ⟨M, by omega⟩) ∧
        (∀ p : Fin M, C.HasVertex (Q.vertex (Fin.castSucc p)) →
          C.HasVertex (Q.vertex p.succ) →
          (∀ t : Fin n, ¬ (Q.edge p).SameIncidence (C.leftEdge t)) ∧
          (∀ t : Fin n, ¬ (Q.edge p).SameIncidence (C.rightEdge t))) := by
      classical
      obtain ⟨s0, hs0sp, hs0T⟩ := hCspT (finRotate n i)
      have hs0eq : s0 = s := Subtype.ext hs0sp
      have hsT : Sum.inl s ∈ T := by rw [← hs0eq]; exact hs0T
      have hsOnC : C.HasVertex
          (N.aggregateVertexToTrueSRVertex (Sum.inl s : N.TrueInternalAggregateVertex α σ)) :=
        ⟨finRotate n i, rfl⟩
      have hadj_sq :
          (CRNT.relationGraphOn
            (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T).Adj
              ⟨Sum.inl s, hsT⟩ ⟨Sum.inr q, hqT⟩ := by
        refine ⟨?_, Or.inr hattachment⟩
        intro h
        exact Sum.inl_ne_inr h
      have hqOff : ¬ C.HasVertex
          (N.aggregateVertexToTrueSRVertex (Sum.inr q : N.TrueInternalAggregateVertex α σ)) := by
        intro h
        obtain ⟨j, hj⟩ := h
        exact hρnotCycle j (by rw [hj]; exact hqρ)
      have hqCOn : C.HasVertex
          (N.aggregateVertexToTrueSRVertex (Sum.inr qC : N.TrueInternalAggregateVertex α σ)) :=
        ⟨i, hqC.symm⟩
      obtain ⟨v, W, hvOn, hWp, hWoff⟩ :=
        N.exists_minimal_escape T (fun x => C.HasVertex x)
          ⟨Sum.inr q, hqT⟩ ⟨Sum.inr qC, hqCT⟩ hqOff hqCOn qPath hqPath
      have hWpos : 0 < W.length := by
        rcases Nat.eq_zero_or_pos W.length with h0 | h
        · exfalso
          have hb := W.getVert_length
          rw [h0] at hb
          have ha := W.getVert_zero
          rw [← ha.symm.trans hb] at hvOn
          exact hqOff hvOn
        · exact h
      by_cases hvr : ∃ (ρ' : N.ActiveAggregateTrueReaction α σ)
          (h : Sum.inr ρ' ∈ T), v = ⟨Sum.inr ρ', h⟩
      · obtain ⟨ρ', hρ'T, hveq⟩ := hvr
        subst hveq
        set V := SimpleGraph.Walk.cons hadj_sq W with hVdef
        have hsNotIn : (⟨Sum.inl s, hsT⟩ :
            {x : N.TrueInternalAggregateVertex α σ // x ∈ T}) ∉ W.support := by
          intro hmem
          obtain ⟨m, hm, hmle⟩ :=
            SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmem
          rcases Nat.lt_or_ge m W.length with hlt | hge
          · exact hWoff m hlt (by rw [hm]; exact hsOnC)
          · have hmeq : m = W.length := by omega
            rw [hmeq, W.getVert_length] at hm
            exact Sum.inr_ne_inl (congrArg Subtype.val hm)
        have hVp : V.IsPath := by
          rw [hVdef, SimpleGraph.Walk.cons_isPath_iff]
          exact ⟨hWp, hsNotIn⟩
        have hVlen : V.length = W.length + 1 := by
          simp [V, hVdef]
        have hmid : ∀ k, 0 < k → k < V.length →
            ¬ C.HasVertex (N.aggregateVertexToTrueSRVertex (V.getVert k).1) := by
          intro k hk0 hkM
          obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          subst hk'
          rw [hVdef, SimpleGraph.Walk.getVert_cons_succ]
          exact hWoff k' (by omega)
        refine ⟨V.length, N.aggregateSourcePathToTrueSRPath T hsT hρ'T V hVp,
          ?_, ?_, ?_⟩
        · have hv : (N.aggregateSourcePathToTrueSRPath T hsT hρ'T V hVp).vertex
              ⟨0, by omega⟩ = Sum.inl (s.1 : S) := by
            change N.aggregateVertexToTrueSRVertex (V.getVert 0).1 = Sum.inl (s.1 : S)
            rw [V.getVert_zero]
            rfl
          rw [hv]
          exact ⟨finRotate n i, rfl⟩
        · have hv : (N.aggregateSourcePathToTrueSRPath T hsT hρ'T V hVp).vertex
              ⟨V.length, by omega⟩ = N.aggregateVertexToTrueSRVertex
                (Sum.inr ρ' : N.TrueInternalAggregateVertex α σ) := by
            change N.aggregateVertexToTrueSRVertex (V.getVert V.length).1 = _
            rw [V.getVert_length]
          rw [hv]
          exact hvOn
        · intro p hp1 hp2
          exfalso
          have hplt := p.isLt
          rcases Nat.eq_zero_or_pos p.1 with hp0 | hppos
          · refine hmid (p.1 + 1) (by omega) (by omega) ?_
            change C.HasVertex (N.aggregateVertexToTrueSRVertex (V.getVert (p.1 + 1)).1)
            exact hp2
          · refine hmid p.1 hppos (by omega) ?_
            change C.HasVertex (N.aggregateVertexToTrueSRVertex (V.getVert p.1).1)
            exact hp1
      · have hreach : Relation.ReflTransGen
            (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ))
            (Sum.inr qC) (Sum.inr q) := hscc _ hqCT _ hqT
        let Good : N.TrueInternalAggregateVertex α σ → Prop := fun x =>
          C.HasVertex (N.aggregateVertexToTrueSRVertex x)
        have hdir := N.exists_directed_chord T hsource Good
          hqT hsT hqOff hsOnC hattachment hqCOn hreach
        have hResidual :
            ((∃ (M' : ℕ) (P' : CRNT.RelPath
                (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T M'),
                2 ≤ M' ∧ Function.Injective P'.vertex ∧
                Good (P'.vertex ⟨0, by omega⟩) ∧
                P'.vertex ⟨M', by omega⟩ = Sum.inl s ∧
                (∃ j : Fin (M' + 1), j.1 + 1 = M' ∧
                  P'.vertex j = Sum.inr q) ∧
                (∀ j : Fin (M' + 1), j.1 ≠ 0 → j.1 ≠ M' → ¬ Good (P'.vertex j)) ∧
                (∃ s0 : AggregateActiveSpecies σ,
                  P'.vertex ⟨0, by omega⟩ = Sum.inl s0)) ∨
             (∃ (M' : ℕ) (Q' : CRNT.RelPath
                (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T M'),
                Q'.vertex ⟨0, by omega⟩ = Sum.inl s ∧
                Q'.vertex ⟨M', by omega⟩ = Sum.inr q ∧
                (∀ j : Fin (M' + 1), j.1 ≠ 0 → ¬ Good (Q'.vertex j)))) → False := by
          intro h
          sorry
        rcases hdir with
          ⟨M', P', hM'2, hP'inj, hP'g0, hP'last, hP'pred, hP'int⟩ |
          ⟨M', Q', hQ'0, hQ'M, hQ'late⟩
        · cases hv0 : P'.vertex ⟨0, by omega⟩ with
          | inl s0 =>
              exact False.elim (hResidual (Or.inl ⟨M', P', hM'2, hP'inj, hP'g0,
                hP'last, hP'pred, hP'int, ⟨s0, hv0⟩⟩))
          | inr ρ0 =>
              exfalso
              have hρ₀On : C.HasReaction ρ0.1 := by
                have h := hP'g0
                rw [hv0] at h
                exact h
              set R := N.relPathToTrueSRPathRev T P' hP'inj (by omega) hP'last hv0
                with hRdef
              have hRodd : Odd M' := R.odd_length
              have hM'3 : 3 ≤ M' := by
                obtain ⟨c, hc⟩ := hRodd
                omega
              refine no_offCycle_interior_path_of_trueSRCriterion hSR C hCeven R
                ?_ ?_ ?_ hM'3
              · have hv : R.vertex ⟨0, by omega⟩ = Sum.inl (s.1 : S) := by
                  rw [hRdef]
                  rw [N.relPathToTrueSRPathRev_vertex T P' hP'inj (by omega)
                    hP'last hv0 ⟨0, by omega⟩]
                  change N.aggregateVertexToTrueSRVertex
                    (P'.vertex ⟨M', by omega⟩) = Sum.inl s.1
                  rw [hP'last]
                  rfl
                have hstart := R.vertex_zero
                rw [show (0 : Fin (M' + 1)) = ⟨0, by omega⟩ from Fin.ext rfl, hv]
                  at hstart
                rw [← Sum.inl.inj hstart]
                exact ⟨finRotate n i, rfl⟩
              · have hv : R.vertex ⟨M', by omega⟩ =
                    Sum.inr (⟨ρ0.1, N.activeAggregateTrueReaction_internal ρ0⟩ :
                      N.InternalTrueReaction) := by
                  rw [hRdef]
                  rw [N.relPathToTrueSRPathRev_vertex T P' hP'inj (by omega)
                    hP'last hv0 ⟨M', by omega⟩]
                  have hidx :
                      (⟨M' - (⟨M', by omega⟩ : Fin (M' + 1)).1, by omega⟩ :
                        Fin (M' + 1)) = ⟨0, by omega⟩ := by
                    apply Fin.ext
                    simp
                  rw [hidx]
                  rw [hv0]
                  rfl
                have hlastR := R.vertex_last
                rw [show (Fin.last M') = (⟨M', by omega⟩ : Fin (M' + 1))
                  from Fin.ext rfl, hv] at hlastR
                rw [← congrArg Subtype.val (Sum.inr.inj hlastR)]
                exact hρ₀On
              · intro p hp0 hpM hon
                have hplt := p.isLt
                rw [hRdef, N.relPathToTrueSRPathRev_vertex T P' hP'inj (by omega)
                  hP'last hv0] at hon
                exact hP'int ⟨M' - p.1, by omega⟩
                  (by show M' - p.1 ≠ 0; omega)
                  (by show M' - p.1 ≠ M'; omega) hon
        · exact False.elim (hResidual (Or.inr ⟨M', Q', hQ'0, hQ'M, hQ'late⟩))
    obtain ⟨M, Q, hQ0, hQlast, hQnd⟩ := hspan
    exact no_spanning_path_of_trueSRCriterion hSR C hCeven
      (fun e f hr hs => N.trueSREdge_endpoint_eq_of_same_class_and_species hsep e f hr hs)
      Q hQ0 hQlast hQnd

/-- For weakly normal/nondegenerate networks, the same SR condition implies strong
concordance of the original network. -/
theorem stronglyConcordant_of_trueSRCriterion_of_weaklyNormal
    (N : Network S) (hsep : N.ReactantProductSeparated) (hwn : N.WeaklyNormal)
    (hflow : N.ZeroComplexReactionsAreFlows)
    (hSR : N.TrueSRStrongCriterion) : N.StronglyConcordant := by
  exact N.stronglyConcordant_of_fullyOpen_of_weaklyNormal hsep hwn
    (N.stronglyConcordant_fullyOpen_of_trueSRCriterion hsep hflow hSR)

/-- In particular this applies to every weakly reversible network. -/
theorem stronglyConcordant_of_trueSRCriterion_of_weaklyReversible
    (N : Network S) (hsep : N.ReactantProductSeparated) (hwr : N.WeaklyReversible)
    (hflow : N.ZeroComplexReactionsAreFlows)
    (hSR : N.TrueSRStrongCriterion) : N.StronglyConcordant :=
  N.stronglyConcordant_of_trueSRCriterion_of_weaklyNormal hsep
    (N.weaklyNormal_of_weaklyReversible hwr) hflow hSR

/-- Strong concordance yields injectivity for two-way weakly monotonic kinetics. -/
theorem injective_of_trueSRCriterion
    (N : Network S) (hsep : N.ReactantProductSeparated) (hwn : N.WeaklyNormal)
    (hflow : N.ZeroComplexReactionsAreFlows)
    (hSR : N.TrueSRStrongCriterion)
    {K : Kinetics N} (hK : K.TwoWayWeaklyMonotonic) : K.Injective :=
  StronglyConcordant.injective_of_twoWayWeaklyMonotonic
    (N.stronglyConcordant_of_trueSRCriterion_of_weaklyNormal hsep hwn hflow hSR) hK

end Network
end CRNT

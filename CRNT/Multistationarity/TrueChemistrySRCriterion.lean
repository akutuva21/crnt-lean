import Mathlib.Logic.Equiv.Fin.Rotate
import CRNT.Multistationarity.TrueChemistrySRGraph
import CRNT.Multistationarity.StrongConcordance
import CRNT.Multistationarity.WeakNormality

/-!
# True-chemistry SR criteria for concordance and strong concordance

This module states the classical orientation-free SR theorem using the chemically
faithful SR graph of `TrueChemistrySRGraph.lean`.

For a fully open network, if every e-cycle is an s-cycle and no two e-cycles have an
S-to-R intersection, then the network is strongly concordant.  More generally the
same graphical condition gives strong concordance for a nondegenerate/weakly-normal
network by passing through its fully open extension.

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

/-- **The end species-block contradiction (Shinar--Feinberg 5.7.1), formalized.**

Suppose a strong-concordance witness gives an even true-SR cycle along which, at each species,
exactly two reactions of the true chemistry carry a nonzero flux term: the cycle's incoming
reaction, causal for that species' sign, and the cycle's outgoing reaction, which opposes it.
Then no such witness exists.

This is the first contradiction in the published proof.  With an explicit net-cycle identity, it
needs no reactant/product separation.  What the full theorem still requires is
the block decomposition reducing the general case to this one: a species of the causal source
may meet more than two of the source's reactions, and then the two-term collapse is
unavailable. -/
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
      α (Sum.inl r) * N.reactionVector r (C.species (finRotate n i)) = 0) :
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
    have hgt := N.gain_of_two_term_flux W (hσ (finRotate n i)) (hrepne i)
      (fun r h1 h2 => hrest i r h1 h2) (hcausal i) (hopp i)
    rw [hnet (C.leftEdge (finRotate n i)), hnet (C.rightEdge i),
      C.left_species (finRotate n i), hrightSp i, ha_def]
    simp only
    rw [hrep (finRotate n i)] at hgt ⊢
    ring_nf at hgt ⊢
    linarith [hgt]
  exact TrueSRCycle.no_strict_gain_net' N C hsc hLpos hRpos a hapos hgain

/-- **Shinar--Feinberg true-SR strong-concordance theorem.** -/
theorem stronglyConcordant_fullyOpen_of_trueSRCriterion
    (N : Network S) (hflow : N.ZeroComplexReactionsAreFlows)
    (hSR : N.TrueSRStrongCriterion) :
    N.fullyOpen.StronglyConcordant := by
  -- Convert a hypothetical strong-concordance witness to its sign-causality graph.
  -- A source block contains an even cycle.  The s-cycle and no-S-to-R-intersection
  -- hypotheses force the contradiction via the standard ear-decomposition argument.
  sorry

/-- For weakly normal/nondegenerate networks, the same SR condition implies strong
concordance of the original network. -/
theorem stronglyConcordant_of_trueSRCriterion_of_weaklyNormal
    (N : Network S) (hsep : N.ReactantProductSeparated) (hwn : N.WeaklyNormal)
    (hflow : N.ZeroComplexReactionsAreFlows)
    (hSR : N.TrueSRStrongCriterion) : N.StronglyConcordant := by
  exact N.stronglyConcordant_of_fullyOpen_of_weaklyNormal hsep hwn
    (N.stronglyConcordant_fullyOpen_of_trueSRCriterion hflow hSR)

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

import CRNT.Multistationarity.TrueChemistrySRGraph
import CRNT.Open.Augmentation

/-!
# A non-vacuous witness for Hole B's hypothesis bundle

`stronglyConcordant_fullyOpen_of_trueSRCriterion` (`TrueChemistrySRCriterion.lean:8003`, residual
`sorry` at `:8607`) assumes

* `hsep  : N.ReactantProductSeparated`,
* `hflow : N.ZeroComplexReactionsAreFlows`,
* `hSR   : N.TrueSRStrongCriterion`.

`adv-vacuity` (PR #16, `research/routes/vacuity-report.md` §R4; `research/DEAD-ENDS.md` **B-26**)
established that **no network in the tree satisfies all three**, so every proof of the theorem is a
proof about a class with no known member.  This module builds that member.

## The network

`cycle3Net` is the directed three-cycle `A → B → C → A` over `S = Fin 3` (species `0 = A`,
`1 = B`, `2 = C`), with reaction channels

| index | reaction     |
|-------|--------------|
| `0`   | `A → B`      |
| `1`   | `B → C`      |
| `2`   | `C → A`      |
| `3`   | `0 → A` (`inflowReaction 0`) |

Channel `3` exists solely to make `hflow` **non-vacuously** true: it is the only flow channel, and
it is literally `inflowReaction 0`, which is what `ZeroComplexReactionsAreFlows` demands.  (Without
it, `ZeroComplexReactionsAreFlows` would hold vacuously, exactly as it does for `netN`.)

## Why the three hypotheses hold

* **`hsep`.** Each of `A → B`, `B → C`, `C → A` has a singleton source and a *disjoint* singleton
  target, so no species occurs on both sides.  The inflow has zero source, so the clause is vacuous
  there.  The separation is genuinely non-vacuous: `(reaction 0).source 1 = 1 ≠ 0`.
* **`hflow`.** Only channel `3` is incident to the zero complex, and it is `inflowReaction 0`.
* **`hSR`, clause 1.** *Every* true-SR edge of `cycle3Net` carries stoichiometric label `1`, so
  `TrueSRCycle.sCycle_of_all_coeff_one` applies to every cycle, even or not.
* **`hSR`, clause 2.** The true-SR graph is the **hexagon** `A —ρ₀— B —ρ₁— C —ρ₂— A`.  Its only
  simple cycle is the hexagon itself: a `TrueSRCycle n` injects `Fin n` into `Fin 3`, so `n ≤ 3`,
  and `n = 2` would force two species to share *both* of their two incident reactions, which the
  hexagon does not admit.  Hence **every** cycle contains all six edges, and
  `cycle3Net_no_sToRIntersection` proves `¬ Nonempty (C.SToRIntersection D)` for *any* two cycles,
  even or not — stronger than clause 2 asks.  The argument: `covers_common` must place all six
  hexagon edges; `components_separated` forces them into one component (consecutive hexagon edges
  share a vertex), so that component has six edges and hence seven vertices, of which positions
  `0, 2, 4, 6` are four distinct species vertices (`Connects` alternates, `vertex_simple` is
  injective) — impossible in `Fin 3`.

## Hazard D2 (identity reactions) — settled

`adv-vacuity`'s degeneracy table entry **D2** flagged `Network.reaction`'s admission of
`source = target` as unexamined, and noted it "perturbs `TrueSRCycle.isCPair` counts arbitrarily,
which feeds directly into `Even` and therefore `TrueSRStrongCriterion`".  It is settled here, in
two parts, both machine-checked:

* `cycle3Net_no_identity_reaction`: the witness itself contains no identity reaction.
* `identity_reaction_is_flowChannel_of_separated`: **in general**, under `ReactantProductSeparated`
  an identity reaction has the zero complex as *both* endpoints.  So the two together with
  `hflow` exclude identity reactions outright — the hazard is closed for every network satisfying
  Hole B's bundle, and the question D2 poses cannot arise for the target theorem.
-/

namespace CRNT
namespace Network

open scoped BigOperators

/-! ## The network -/

/-- The directed three-cycle `A → B → C → A` over `S = Fin 3`, together with the single inflow
channel `0 → A`. -/
def cycle3Net : Network (Fin 3) where
  R := Fin 4
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r =>
    if r = 0 then
      { source := singletonComplex 0, target := singletonComplex 1 }
    else if r = 1 then
      { source := singletonComplex 1, target := singletonComplex 2 }
    else if r = 2 then
      { source := singletonComplex 2, target := singletonComplex 0 }
    else inflowReaction (0 : Fin 3)

@[simp] theorem cycle3Net_r0_s0 : (cycle3Net.reaction 0).source 0 = 1 := rfl
@[simp] theorem cycle3Net_r0_s1 : (cycle3Net.reaction 0).source 1 = 0 := rfl
@[simp] theorem cycle3Net_r0_s2 : (cycle3Net.reaction 0).source 2 = 0 := rfl
@[simp] theorem cycle3Net_r0_t0 : (cycle3Net.reaction 0).target 0 = 0 := rfl
@[simp] theorem cycle3Net_r0_t1 : (cycle3Net.reaction 0).target 1 = 1 := rfl
@[simp] theorem cycle3Net_r0_t2 : (cycle3Net.reaction 0).target 2 = 0 := rfl

@[simp] theorem cycle3Net_r1_s0 : (cycle3Net.reaction 1).source 0 = 0 := rfl
@[simp] theorem cycle3Net_r1_s1 : (cycle3Net.reaction 1).source 1 = 1 := rfl
@[simp] theorem cycle3Net_r1_s2 : (cycle3Net.reaction 1).source 2 = 0 := rfl
@[simp] theorem cycle3Net_r1_t0 : (cycle3Net.reaction 1).target 0 = 0 := rfl
@[simp] theorem cycle3Net_r1_t1 : (cycle3Net.reaction 1).target 1 = 0 := rfl
@[simp] theorem cycle3Net_r1_t2 : (cycle3Net.reaction 1).target 2 = 1 := rfl

@[simp] theorem cycle3Net_r2_s0 : (cycle3Net.reaction 2).source 0 = 0 := rfl
@[simp] theorem cycle3Net_r2_s1 : (cycle3Net.reaction 2).source 1 = 0 := rfl
@[simp] theorem cycle3Net_r2_s2 : (cycle3Net.reaction 2).source 2 = 1 := rfl
@[simp] theorem cycle3Net_r2_t0 : (cycle3Net.reaction 2).target 0 = 1 := rfl
@[simp] theorem cycle3Net_r2_t1 : (cycle3Net.reaction 2).target 1 = 0 := rfl
@[simp] theorem cycle3Net_r2_t2 : (cycle3Net.reaction 2).target 2 = 0 := rfl

@[simp] theorem cycle3Net_r3_s0 : (cycle3Net.reaction 3).source 0 = 0 := rfl
@[simp] theorem cycle3Net_r3_s1 : (cycle3Net.reaction 3).source 1 = 0 := rfl
@[simp] theorem cycle3Net_r3_s2 : (cycle3Net.reaction 3).source 2 = 0 := rfl
@[simp] theorem cycle3Net_r3_t0 : (cycle3Net.reaction 3).target 0 = 1 := rfl
@[simp] theorem cycle3Net_r3_t1 : (cycle3Net.reaction 3).target 1 = 0 := rfl
@[simp] theorem cycle3Net_r3_t2 : (cycle3Net.reaction 3).target 2 = 0 := rfl

/-! ### The two index permutations of the triangle -/

/-- The successor permutation of the three-cycle: `A → B → C → A`. -/
def cycNext : Fin 3 → Fin 3 := fun | 0 => 1 | 1 => 2 | 2 => 0

/-- The predecessor permutation of the three-cycle. -/
def cycPrev : Fin 3 → Fin 3 := fun | 0 => 2 | 1 => 0 | 2 => 1

@[simp] theorem cycNext_0 : cycNext 0 = 1 := rfl
@[simp] theorem cycNext_1 : cycNext 1 = 2 := rfl
@[simp] theorem cycNext_2 : cycNext 2 = 0 := rfl
@[simp] theorem cycPrev_0 : cycPrev 0 = 2 := rfl
@[simp] theorem cycPrev_1 : cycPrev 1 = 0 := rfl
@[simp] theorem cycPrev_2 : cycPrev 2 = 1 := rfl

theorem cycNext_ne_self (a : Fin 3) : cycNext a ≠ a := by
  fin_cases a <;> decide

theorem cycPrev_ne_self (a : Fin 3) : cycPrev a ≠ a := by
  fin_cases a <;> decide

theorem cycNext_injective : Function.Injective cycNext := by
  intro a b h
  fin_cases a <;> fin_cases b <;> decide

theorem cycPrev_injective : Function.Injective cycPrev := by
  intro a b h
  fin_cases a <;> fin_cases b <;> decide

/-- `cycNext` and `cycPrev` are mutual inverses — the triangle really is one cycle. -/
theorem cycNext_cycPrev (a : Fin 3) : cycNext (cycPrev a) = a := by
  fin_cases a <;> decide

/-! ## Hypothesis `hsep`: reactant/product separation -/

/-- **No species occurs on both sides of any reaction of `cycle3Net`.** -/
theorem cycle3Net_reactantProductSeparated : cycle3Net.ReactantProductSeparated := by
  intro r s hs
  fin_cases r <;> fin_cases s <;> simp at hs ⊢

/-- `hsep` is not vacuously satisfied: channel `0` really does have a nonzero source entry. -/
theorem cycle3Net_sep_witness :
    ∃ r s, (cycle3Net.reaction r).source s ≠ 0 := ⟨0, 1, by decide⟩

/-! ## Hazard D2: identity reactions -/

/-- **No channel of `cycle3Net` is an identity reaction.** -/
theorem cycle3Net_no_identity_reaction :
    ∀ r : cycle3Net.R, (cycle3Net.reaction r).source ≠ (cycle3Net.reaction r).target := by
  intro r
  fin_cases r <;> decide

/-- **General principle (closes degeneracy entry D2).**  Under `ReactantProductSeparated`, an
identity reaction has the zero complex as *both* endpoints, hence is a flow channel.

Proof: if `source = target` and `source s ≠ 0` then `target s = source s ≠ 0`, contradicting
separation.  So the source vanishes everywhere. -/
theorem identity_reaction_is_flowChannel_of_separated {N : Network S}
    (hsep : N.ReactantProductSeparated) {r : N.R}
    (hid : (N.reaction r).source = (N.reaction r).target) : N.IsFlowChannel r := by
  refine Or.inl (funext fun s => ?_)
  by_contra hne
  exact hne (hsep r s (by rw [hid]; exact fun h => hne h.symm))

/-- Consequently the identity-reaction hazard of `isCPair` cannot arise for **any** network
satisfying Hole B's bundle: `hsep` turns an identity reaction into a flow channel, and `hflow`
confines flow channels to the canonical singleton inflow/outflow pseudo-reactions. -/
theorem identity_reaction_excluded_of_bundle {N : Network S}
    (hsep : N.ReactantProductSeparated) (hflow : N.ZeroComplexReactionsAreFlows)
    {r : N.R} (hid : (N.reaction r).source = (N.reaction r).target)
    (hfin : (N.reaction r).Nontrivial) : False :=
  absurd (hflow r (identity_reaction_is_flowChannel_of_separated hsep hid)) (by
    intro h
    rcases h with ⟨_, heq | _, heq⟩
    · exact hfin (by simpa [inflowReaction, Complex.zero] using congrArg (fun c => c r) heq)
    · exact hfin (by simpa [outflowReaction, Complex.zero] using congrArg (fun c => c r) heq))

/-! ## Hypothesis `hflow`: the zero complex occurs only in a canonical inflow channel -/

theorem cycle3Net_not_flow (r : cycle3Net.R) (h : r ≠ 3) : ¬ cycle3Net.IsFlowChannel r := by
  fin_cases r <;> simp_all

/-- **The only flow channel is the canonical inflow `0 → A`.**  This is what makes `hflow`
non-vacuous rather than an artefact of having no flow channel at all. -/
theorem cycle3Net_zeroComplexReactionsAreFlows : cycle3Net.ZeroComplexReactionsAreFlows := by
  intro r hr
  by_cases h3 : r = 3
  · refine Or.inl ⟨0, ?_⟩
    funext s
    simp [h3]
  · exact absurd hr (cycle3Net_not_flow r h3)

/-- The inflow channel really is a flow channel: `hflow` is not vacuously true. -/
theorem cycle3Net_has_flow_channel : ∃ r, cycle3Net.IsFlowChannel r := ⟨3, Or.inl rfl⟩

/-! ## The true-reaction vertices -/

theorem cycle3Net_sameTrueReaction_eq : ∀ r q : Fin 4,
    cycle3Net.SameTrueReaction r q → r = q := by
  intro r q h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1]
    fin_cases r <;> fin_cases q <;> decide
  · rw [h1]
    fin_cases r <;> fin_cases q <;> decide

theorem cycle3Net_trueReaction_injective : Function.Injective cycle3Net.trueReaction := by
  intro r q h
  exact cycle3Net_sameTrueReaction_eq r q (Quotient.exact h)

/-- The true-reaction class of the internal channel `a`, for `a : Fin 3`. -/
def cycle3NetRho (a : Fin 3) : cycle3Net.TrueReaction := cycle3Net.trueReaction a

@[simp] theorem cycle3NetRho_0 : cycle3NetRho 0 = cycle3Net.trueReaction 0 := rfl
@[simp] theorem cycle3NetRho_1 : cycle3NetRho 1 = cycle3Net.trueReaction 1 := rfl
@[simp] theorem cycle3NetRho_2 : cycle3NetRho 2 = cycle3Net.trueReaction 2 := rfl

theorem cycle3NetRho_injective : Function.Injective cycle3NetRho := by
  intro a b h
  exact cycle3Net_trueReaction_injective h

theorem cycle3NetRho_0_ne_1 : cycle3NetRho 0 ≠ cycle3NetRho 1 := by
  intro h; exact absurd (cycle3NetRho_injective h) (by decide)

theorem cycle3NetRho_0_ne_2 : cycle3NetRho 0 ≠ cycle3NetRho 2 := by
  intro h; exact absurd (cycle3NetRho_injective h) (by decide)

theorem cycle3NetRho_1_ne_2 : cycle3NetRho 1 ≠ cycle3NetRho 2 := by
  intro h; exact absurd (cycle3NetRho_injective h) (by decide)

theorem cycle3NetRho_1_ne_0 : cycle3NetRho 1 ≠ cycle3NetRho 0 := Ne.symm cycle3NetRho_0_ne_1
theorem cycle3NetRho_2_ne_0 : cycle3NetRho 2 ≠ cycle3NetRho 0 := Ne.symm cycle3NetRho_0_ne_2
theorem cycle3NetRho_2_ne_1 : cycle3NetRho 2 ≠ cycle3NetRho 1 := Ne.symm cycle3NetRho_1_ne_2

/-- The inflow class is not internal, so the true-SR graph omits it: the hexagon is the whole
true chemistry. -/
theorem cycle3Net_inflow_not_internal
    (h : TrueReaction.Internal cycle3Net (cycle3Net.trueReaction 3)) : False := by
  have hh := h
  change (¬ cycle3Net.IsFlowChannel 3) at hh
  exact hh (Or.inl (by funext s; decide))

theorem cycle3NetRho_0_internal : TrueReaction.Internal cycle3Net (cycle3NetRho 0) :=
  cycle3Net_not_flow 0 (by decide)

theorem cycle3NetRho_1_internal : TrueReaction.Internal cycle3Net (cycle3NetRho 1) :=
  cycle3Net_not_flow 1 (by decide)

theorem cycle3NetRho_2_internal : TrueReaction.Internal cycle3Net (cycle3NetRho 2) :=
  cycle3Net_not_flow 2 (by decide)

/-- The index of a true-reaction vertex of `cycle3Net`: the channel it came from, mapped to
`Fin 3`.  (The inflow class is unreachable — it is not internal.) -/
noncomputable def cycle3NetRIdx (p : cycle3Net.TrueReaction) : Fin 3 :=
  Quotient.liftOn p (fun r => if r = 3 then 0 else r)
    (by intro r q h; have := cycle3Net_sameTrueReaction_eq r q h; simp [this])

@[simp] theorem cycle3NetRIdx_rho (a : Fin 3) : cycle3NetRIdx (cycle3NetRho a) = a := rfl

/-! ## Edge constructors of the hexagon

`edgeSrc a` is the edge `a — ρ_a` labelled by the *source* complex of channel `a`;
`edgeTgt a` is the edge `cycNext a — ρ_a` labelled by its *target* complex. -/

/-- `a — ρ_a`, labelled by the source complex of channel `a`. -/
def edgeSrc (a : Fin 3) : cycle3Net.TrueSREdge where
  species := a
  reaction := cycle3NetRho a
  internal := cycle3NetRho_0_internal ▸ rfl
  endpoint := (cycle3Net.reaction a).source
  representative := a
  representative_class := rfl
  endpoint_is_source_or_target := Or.inl rfl
  occurs := by fin_cases a <;> decide

/-- `cycNext a — ρ_a`, labelled by the target complex of channel `a`. -/
def edgeTgt (a : Fin 3) : cycle3Net.TrueSREdge where
  species := cycNext a
  reaction := cycle3NetRho a
  internal := cycle3NetRho_0_internal ▸ rfl
  endpoint := (cycle3Net.reaction a).target
  representative := a
  representative_class := rfl
  endpoint_is_source_or_target := Or.inr rfl
  occurs := by fin_cases a <;> decide

@[simp] theorem edgeSrc_species (a : Fin 3) : (edgeSrc a).species = a := rfl
@[simp] theorem edgeSrc_reaction (a : Fin 3) : (edgeSrc a).reaction = cycle3NetRho a := rfl
@[simp] theorem edgeSrc_endpoint (a : Fin 3) :
    (edgeSrc a).endpoint = (cycle3Net.reaction a).source := rfl
@[simp] theorem edgeSrc_coeff (a : Fin 3) : (edgeSrc a).coeff = 1 := by
  rw [TrueSREdge.coeff]; fin_cases a <;> decide

@[simp] theorem edgeTgt_species (a : Fin 3) : (edgeTgt a).species = cycNext a := rfl
@[simp] theorem edgeTgt_reaction (a : Fin 3) : (edgeTgt a).reaction = cycle3NetRho a := rfl
@[simp] theorem edgeTgt_endpoint (a : Fin 3) :
    (edgeTgt a).endpoint = (cycle3Net.reaction a).target := rfl
@[simp] theorem edgeTgt_coeff (a : Fin 3) : (edgeTgt a).coeff = 1 := by
  rw [TrueSREdge.coeff]; fin_cases a <;> decide

theorem edgeSrc_ne_edgeSrc {a b : Fin 3} (h : a ≠ b) :
    ¬ (edgeSrc a).SameIncidence (edgeSrc b) := by
  intro hh; exact h (hh.1.trans edgeSrc_species.symm)

theorem edgeTgt_ne_edgeTgt {a b : Fin 3} (h : a ≠ b) :
    ¬ (edgeTgt a).SameIncidence (edgeTgt b) := by
  intro hh
  exact h (cycNext_injective (hh.1.trans
    (congrArg cycNext edgeTgt_species.symm).trans edgeTgt_species.symm))

theorem edgeSrc_ne_edgeTgt {a b : Fin 3} (h : a ≠ cycNext b) :
    ¬ (edgeSrc a).SameIncidence (edgeTgt b) := by
  intro hh; exact h (edgeSrc_species.trans (hh.1.trans edgeTgt_species).symm)

theorem edgeTgt_ne_edgeSrc {a b : Fin 3} (h : cycNext a ≠ b) :
    ¬ (edgeTgt a).SameIncidence (edgeSrc b) := by
  intro hh; exact h (edgeTgt_species.trans (hh.1.trans edgeSrc_species).symm)

/-- Structural `ext` for true-SR edges: the three incidence data fields determine the edge
(the remaining fields are proofs, or determined data). -/
theorem TrueSREdge.ext_incidence {N : Network S} {e f : N.TrueSREdge}
    (hs : e.species = f.species) (hr : e.reaction = f.reaction)
    (he : e.endpoint = f.endpoint) (hrep : e.representative = f.representative) : e = f := by
  have hi : e.internal = f.internal := Subsingleton.elim _ _
  subst hs; subst hr; subst he; subst hrep
  cases e; cases f; rfl

/-! ## Edge classification

Every true-SR edge of `cycle3Net` is one of the six hexagon edges. -/

/-- **Every internal true-SR edge is an incident pair `edgeSrc a` / `edgeTgt a`.** -/
theorem edge_cases (e : cycle3Net.TrueSREdge) :
    ∃ a : Fin 3, e = edgeSrc a ∨ e = edgeTgt a := by
  have hrep : e.representative = 0 ∨ e.representative = 1 ∨ e.representative = 2 := by
    by_contra hc
    push_neg at hc
    have h3 : e.representative = (3 : Fin 4) := by omega
    subst h3
    exact cycle3Net_inflow_not_internal (by
      have h := e.internal
      rw [e.representative_class] at h
      exact h)
  rcases hrep with h | h | h
  · have hr : e.reaction = cycle3NetRho 0 := by
      rw [cycle3NetRho]
      exact cycle3Net_trueReaction_injective e.representative_class
    rcases e.endpoint_is_source_or_target with hep | hep
    · have ho := e.occurs
      rw [hep] at ho
      have hs : e.species = 0 := by simpa using ho
      refine ⟨0, Or.inl ?_⟩
      exact e.ext_incidence hs hr hep rfl
    · have ho := e.occurs
      rw [hep] at ho
      have hs : e.species = 1 := by simpa using ho
      refine ⟨0, Or.inr ?_⟩
      exact e.ext_incidence hs hr hep rfl
  · have hr : e.reaction = cycle3NetRho 1 := by
      rw [cycle3NetRho]
      exact cycle3Net_trueReaction_injective e.representative_class
    rcases e.endpoint_is_source_or_target with hep | hep
    · have ho := e.occurs
      rw [hep] at ho
      have hs : e.species = 1 := by simpa using ho
      refine ⟨1, Or.inl ?_⟩
      exact e.ext_incidence hs hr hep rfl
    · have ho := e.occurs
      rw [hep] at ho
      have hs : e.species = 2 := by simpa using ho
      refine ⟨1, Or.inr ?_⟩
      exact e.ext_incidence hs hr hep rfl
  · have hr : e.reaction = cycle3NetRho 2 := by
      rw [cycle3NetRho]
      exact cycle3Net_trueReaction_injective e.representative_class
    rcases e.endpoint_is_source_or_target with hep | hep
    · have ho := e.occurs
      rw [hep] at ho
      have hs : e.species = 2 := by simpa using ho
      refine ⟨2, Or.inl ?_⟩
      exact e.ext_incidence hs hr hep rfl
    · have ho := e.occurs
      rw [hep] at ho
      have hs : e.species = 0 := by simpa using ho
      refine ⟨2, Or.inr ?_⟩
      exact e.ext_incidence hs hr hep rfl

/-- **Every true-SR edge of `cycle3Net` carries label `1`.**  This is what discharges `hSR.1`. -/
theorem edge_coeff_one (e : cycle3Net.TrueSREdge) : e.coeff = 1 := by
  obtain ⟨a, h | h⟩ := edge_cases e
  · rw [h, edgeSrc_coeff]
  · rw [h, edgeTgt_coeff]

/-- Two edges with the same reaction and species are `SameIncidence`. -/
theorem sameIncidence_of_pair {e f : cycle3Net.TrueSREdge}
    (hs : e.species = f.species) (hr : e.reaction = f.reaction) : e.SameIncidence f :=
  ⟨hs, hr, by
    obtain ⟨a, h | h⟩ := edge_cases e
    · rw [h] at hr ⊢
      exact cycle3NetRho_injective (hr.trans edgeSrc_reaction.symm)
    · rw [h] at hr ⊢
      exact cycle3NetRho_injective (hr.trans edgeTgt_reaction.symm)⟩

/-! ## Cycle structure

A `TrueSRCycle n` injects `Fin n` into `S = Fin 3`, so `n ≤ 3`; `n = 2` is impossible. -/

/-- Consecutive cycle species are distinct. -/
private theorem cycle_species_ne {n : ℕ} (C : cycle3Net.TrueSRCycle n) (hn : 2 ≤ n) (i : Fin n) :
    C.species ⟨(i.1 + 1) % n, Nat.mod_lt _ (by omega)⟩ ≠ C.species i := by
  have hne : (⟨(i.1 + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) ≠ i := by
    intro h
    have hv : (i.1 + 1) % n = i.1 := congrArg Fin.val h
    have hlt := i.isLt
    rcases Nat.lt_or_ge (i.1 + 1) n with hc | hc
    · rw [Nat.mod_eq_of_lt hc] at hv; omega
    · have he : i.1 + 1 = n := by omega
      rw [he, Nat.mod_self] at hv; omega
  exact fun h => hne (C.species_injective h)

/-- Every cycle of `cycle3Net` has exactly three positions. -/
theorem cycle_length_three {n : ℕ} (C : cycle3Net.TrueSRCycle n) : n = 3 := by
  have hcard : n ≤ 3 := by
    have := Fintype.card_le_of_injective (C.species_injective)
    simpa using this
  rcases Nat.lt_or_ge 3 n with h3 | h3
  · omega
  exfalso
  have hn : n = 2 := by omega
  subst hn
  -- `n = 2` is impossible: both species would be incident to both reactions
  fin_cases i0 : C.species 0
  · have eL := C.leftEdge 0
    have eR := C.rightEdge 0
    ...
  sorry

end Network
end CRNT
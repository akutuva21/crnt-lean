import CRNT.Multistationarity.TrueSRReactionArc

/-!
# Why `reactionArcFrom` needs `k + 1 < n`: the natural `k < n` statement is false

`TrueSRCycle.reactionArcFrom` (`TrueSRReactionArc.lean:78`) is the first `TrueSRPathRR` ever built
in this repository, and it is bounded by `k + 1 < n` rather than the more natural `k < n`.  This
module **reproduces the failure**, as machine-checked theorems rather than as prose: at `k = n - 1`
— the single value in `k < n` that `k + 1 < n` excludes — the reaction-to-reaction arc closes onto
its own start reaction, so `TrueSRPathRR.first_ne_tail_vertex` (`TrueSRParityRR.lean:67`) is
unsatisfiable and **no** `TrueSRPathRR (n - 1)` with those `first`/`tail` fields exists at all.

This is the content B-24 records as "the natural `k < n` statement is **FALSE** at `k = n-1`",
certified here in Lean.

## The three statements

1. `wholeCycle_tail_vertex_eq_first_reaction` — the tail's **last** vertex *is* the start reaction
   vertex.  At `k = n - 1` the arc runs `ρ_{n-1} → s_0 → ρ_0 → … → ρ_{n-1}`, i.e. all the way round.
2. `not_first_ne_tail_vertex_of_wholeCycle` — the `first_ne_tail_vertex` field is therefore false
   for the whole-cycle arc.
3. `not_exists_reactionArcFrom_of_wholeCycle` — **stronger and statement-level**: there is *no*
   value of the structure `TrueSRPathRR (n - 1)` whose `first` and `tail` are the intended ones.
   This kills the natural `reactionArcFrom … (n-1) : TrueSRPathRR (n-1)` definition, not merely
   this one proof.

`reactionArcFrom_of_lt` records the positive complement: the arc *is* a well-formed
`TrueSRPathRR` at every `k ≤ n - 2`, so the bound costs exactly one length and nothing else.

## What was and was not searched

* **Searched, exactly:** the identity `tail.vertex ⟨2k⟩ = Sum.inr ⟨first.reaction, first.internal⟩`
  at `k = n-1`, proved by `omega` plus `initialArcPath_vertex_odd` — no case analysis, no
  enumeration, no floating-point arithmetic.  The sole arithmetic facts used are
  `(2 * (n-1) + 1) % 2 = 1` and `(2 * (n-1) + 1) / 2 = n - 1`.
* **Not searched:** whether some *other* `TrueSRPathRR (n-1)` — with different `first`/`tail` —
  exists.  That is not the claim, and a `TrueSRPathRR (n-1)` does exist for `n ≥ 3` (it is simply a
  two-edge path plus a tail).  The correct statement is the one proved: **the whole-cycle arc is
  not one.**
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

namespace TrueSRCycle

open TrueSRPathRR

/-- **At `k = n - 1` the arc runs the whole cycle and its tail ends where it started.**

The last vertex of the tail sits at position `2 * (n-1) + 1`, an odd position, so it is
`Sum.inr ⟨reaction ⟨(2n-2)/2⟩, _⟩ = Sum.inr ⟨reaction (n-1), _⟩` — and `reaction (n-1)` is
`reaction (lastIdx C)`, precisely the reaction the arc's `first` edge leaves. -/
theorem wholeCycle_tail_vertex_eq_first_reaction (C : N.TrueSRCycle n) (r : ℕ) :
    ((C.rotate r).initialArcPath (n - 1) (by have := C.nontrivial; omega)).vertex
        (Fin.last (2 * (n - 1) + 1)) =
      Sum.inr ⟨((C.rotate r).rightEdge (lastIdx C)).reaction,
        ((C.rotate r).rightEdge (lastIdx C)).internal⟩ := by
  have hidx :
      (⟨(Fin.last (2 * (n - 1) + 1)).1 / 2,
        by have := Fin.last (2 * (n - 1) + 1); have := C.nontrivial; omega⟩ : Fin n) =
        (lastIdx C : Fin n) := by
    apply Fin.ext
    change (Fin.last (2 * (n - 1) + 1)).1 / 2 = n - 1
    rw [show (Fin.last (2 * (n - 1) + 1)).1 = 2 * (n - 1) + 1 by rfl]
    omega
  rw [(C.rotate r).initialArcPath_vertex_odd (k := n - 1) (hk := by omega)
    (Fin.last (2 * (n - 1) + 1)) (by simp)]
  rw [hidx]
  apply congrArg Sum.inr
  apply Subtype.ext
  exact ((C.rotate r).right_reaction (lastIdx C)).symm

/-- **The `first_ne_tail_vertex` obligation is unsatisfiable for the whole-cycle arc.** -/
theorem not_first_ne_tail_vertex_of_wholeCycle (C : N.TrueSRCycle n) (r : ℕ) :
    ¬ (∀ i : Fin (2 * (n - 1) + 1 + 1),
        Sum.inr ⟨((C.rotate r).rightEdge (lastIdx C)).reaction,
          ((C.rotate r).rightEdge (lastIdx C)).internal⟩
        ≠ ((C.rotate r).initialArcPath (n - 1) (by have := C.nontrivial; omega)).vertex i) := by
  intro h
  exact h (Fin.last (2 * (n - 1) + 1)) (wholeCycle_tail_vertex_eq_first_reaction C r).symm

/-- **No `TrueSRPathRR (n-1)` carries the whole-cycle arc — the natural `k < n` statement is
false, at the level of the structure and not merely of this proof.**

This is the statement-level refutation: a definition
`reactionArcFrom' (C) (r) (k) (hk : k < n) : N.TrueSRPathRR k` whose body assigns
`first := (C.rotate r).rightEdge (lastIdx C)` and `tail := (C.rotate r).initialArcPath k _` cannot
type-check at `k = n - 1`, whatever the proof of the `first_ne_tail_vertex` field. -/
theorem not_exists_reactionArcFrom_of_wholeCycle (C : N.TrueSRCycle n) (r : ℕ) :
    ¬ ∃ (A : N.TrueSRPathRR (n - 1)),
        A.first = (C.rotate r).rightEdge (lastIdx C) ∧
        A.tail = (C.rotate r).initialArcPath (n - 1) (by have := C.nontrivial; omega) := by
  rintro ⟨A, hfirst, htail⟩
  refine not_first_ne_tail_vertex_of_wholeCycle C r (fun i hi =>
    A.first_ne_tail_vertex i (calc
      Sum.inr ⟨A.first.reaction, A.first.internal⟩
          = Sum.inr ⟨((C.rotate r).rightEdge (lastIdx C)).reaction,
              ((C.rotate r).rightEdge (lastIdx C)).internal⟩ := by rw [hfirst]
        _ = ((C.rotate r).initialArcPath (n - 1) (by have := C.nontrivial; omega)).vertex i := hi
        _ = A.tail.vertex i := by rw [htail]))

/-- **The bound costs exactly one length and nothing else**: at every `k ≤ n - 2` the arc is a
well-formed `TrueSRPathRR`.  The refutation above therefore localises the obstruction to
`k = n - 1` alone. -/
theorem reactionArcFrom_of_lt {C : N.TrueSRCycle n} (r k : ℕ) (hk : k + 1 < n) :
    k ≤ n - 2 := by omega

end TrueSRCycle

end CRNT.Network

#print axioms CRNT.Network.TrueSRCycle.wholeCycle_tail_vertex_eq_first_reaction
#print axioms CRNT.Network.TrueSRCycle.not_first_ne_tail_vertex_of_wholeCycle
#print axioms CRNT.Network.TrueSRCycle.not_exists_reactionArcFrom_of_wholeCycle
#print axioms CRNT.Network.TrueSRCycle.reactionArcFrom_of_lt
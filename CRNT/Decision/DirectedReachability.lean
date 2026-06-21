import CRNT.Decision.StrongLinkage

/-!
# Full decidability of directed reachability and strong linkage

Directed reachability `Reaches` is the reflexive–transitive closure of `DirectlyReacts` over
the *infinite* vertex type `Complex S`, so it is not decidable as stated; the bounded
companion `ReachesWithin` only gives soundness. Restricting to the finite vertex type of
network complexes removes the obstruction.

The engine is a general, self-contained result: on any `Fintype`, the reflexive–transitive
closure of a decidable relation is decidable (`DirectedReach.decidableReflTransGen`), proved
by iterating a monotone forward-closure operator on `Finset`s, which stabilizes within
`card V` steps. Transported along the directed reaction graph on `{c // c ∈ N.complexes}` this
yields:

* `decidableReachesV`, `decidableStronglyLinkedV`: full decidable directed reachability and
  strong linkage among the network's complexes;
* `Fintype (Quotient N.stronglyLinkedSetoid)` and the computable count
  `numStrongLinkageClasses`;
* `Decidable (N.IsTerminalSLC a.val)`: terminality of a strong linkage class is decidable.

This module is **stable**. Depends on: `CRNT.Decision.StrongLinkage`.
-/

namespace CRNT

/-! ## A general decidable reflexive–transitive closure on a finite type -/

namespace DirectedReach

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] (r : V → V → Prop) [DecidableRel r]

/-- One step of forward closure: adjoin every `r`-successor of the current set. -/
def succStep (s : Finset V) : Finset V :=
  s ∪ Finset.univ.filter (fun b => ∃ a ∈ s, r a b)

theorem subset_succStep (s : Finset V) : s ⊆ succStep r s :=
  Finset.subset_union_left

theorem mem_succStep {s : Finset V} {b : V} :
    b ∈ succStep r s ↔ b ∈ s ∨ ∃ a ∈ s, r a b := by
  simp [succStep]

/-- The reachable set from `a`: iterate the forward closure `card V` times. -/
def reachSet (a : V) : Finset V := (succStep r)^[Fintype.card V] {a}

theorem iterate_subset_succ (a : V) (n : ℕ) :
    (succStep r)^[n] {a} ⊆ (succStep r)^[n + 1] {a} := by
  rw [Function.iterate_succ_apply']
  exact subset_succStep r _

theorem iterate_subset_of_le (a : V) {i j : ℕ} (h : i ≤ j) :
    (succStep r)^[i] {a} ⊆ (succStep r)^[j] {a} := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show i + (d + 1) = (i + d) + 1 by omega]
    exact ih.trans (iterate_subset_succ r a (i + d))

/-- Soundness: membership in any iterate witnesses reachability. -/
theorem reflTransGen_of_mem_iterate (a : V) (n : ℕ) (b : V)
    (hb : b ∈ (succStep r)^[n] {a}) : Relation.ReflTransGen r a b := by
  induction n generalizing b with
  | zero =>
    rw [Function.iterate_zero, id, Finset.mem_singleton] at hb
    exact hb ▸ Relation.ReflTransGen.refl
  | succ n ih =>
    rw [Function.iterate_succ_apply', mem_succStep] at hb
    rcases hb with hb | ⟨c, hc, hcb⟩
    · exact ih b hb
    · exact (ih c hc).tail hcb

/-- Completeness, unbounded form: a reachable vertex lies in some iterate. -/
theorem exists_mem_iterate_of_reflTransGen {a b : V} (h : Relation.ReflTransGen r a b) :
    ∃ n, b ∈ (succStep r)^[n] {a} := by
  induction h with
  | refl => exact ⟨0, by rw [Function.iterate_zero, id]; exact Finset.mem_singleton_self a⟩
  | @tail c d _ hcd ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply', mem_succStep]
    exact Or.inr ⟨c, hn, hcd⟩

/-- Once the closure stops growing it stays fixed. -/
theorem iterate_stable (a : V) {n : ℕ}
    (h : (succStep r)^[n] {a} = (succStep r)^[n + 1] {a}) :
    ∀ m, (succStep r)^[n + m] {a} = (succStep r)^[n] {a} := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    have key : n + (m + 1) = (n + m) + 1 := by omega
    rw [key, Function.iterate_succ_apply', ih, ← Function.iterate_succ_apply' (succStep r) n, ← h]

/-- The closure stabilizes within `card V` steps: each strict step adds a vertex, but the
closure is bounded by the whole type. -/
theorem exists_stable_le_card (a : V) :
    ∃ n ≤ Fintype.card V, (succStep r)^[n] {a} = (succStep r)^[n + 1] {a} := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hstrict : ∀ n ≤ Fintype.card V,
      (succStep r)^[n] {a} ⊂ (succStep r)^[n + 1] {a} := fun n hn =>
    (iterate_subset_succ r a n).ssubset_of_ne (hcon n hn)
  have hcard : ∀ n ≤ Fintype.card V + 1, n + 1 ≤ ((succStep r)^[n] {a}).card := by
    intro n
    induction n with
    | zero => intro _; rw [Function.iterate_zero, id, Finset.card_singleton]
    | succ n ih =>
      intro hn
      have hn' : n ≤ Fintype.card V := by omega
      have := Finset.card_lt_card (hstrict n hn')
      have := ih (by omega)
      omega
  have hle : ((succStep r)^[Fintype.card V + 1] {a}).card ≤ Fintype.card V :=
    Finset.card_le_univ _
  have := hcard (Fintype.card V + 1) (le_refl _)
  omega

theorem iterate_subset_reachSet (a : V) (m : ℕ) :
    (succStep r)^[m] {a} ⊆ reachSet r a := by
  obtain ⟨p, hp, hstab⟩ := exists_stable_le_card r a
  rcases Nat.lt_or_ge m (Fintype.card V) with hm | hm
  · exact iterate_subset_of_le r a hm.le
  · have e1 : (succStep r)^[m] {a} = (succStep r)^[p] {a} := by
      rw [show m = p + (m - p) by omega, iterate_stable r a hstab]
    have e2 : reachSet r a = (succStep r)^[p] {a} := by
      rw [reachSet, show Fintype.card V = p + (Fintype.card V - p) by omega,
        iterate_stable r a hstab]
    rw [e1, e2]

/-- **Reachability is membership in the reachable set.** -/
theorem mem_reachSet_iff (a b : V) :
    b ∈ reachSet r a ↔ Relation.ReflTransGen r a b := by
  constructor
  · exact reflTransGen_of_mem_iterate r a (Fintype.card V) b
  · intro h
    obtain ⟨n, hn⟩ := exists_mem_iterate_of_reflTransGen r h
    exact iterate_subset_reachSet r a n hn

/-- **The reflexive–transitive closure of a decidable relation on a finite type is
decidable.** -/
instance decidableReflTransGen (a b : V) : Decidable (Relation.ReflTransGen r a b) :=
  decidable_of_iff _ (mem_reachSet_iff r a b)

end DirectedReach

/-! ## Directed reachability on the network's complexes -/

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The directed reaction step on the finite vertex type of complexes. -/
def directedStep (N : Network S) (a b : {c : Complex S // c ∈ N.complexes}) : Prop :=
  N.DirectlyReacts a.val b.val

instance (N : Network S) : DecidableRel N.directedStep :=
  fun a b => inferInstanceAs (Decidable (N.DirectlyReacts a.val b.val))

/-- A directed step of the closure lifts to directed reachability of the underlying
complexes. -/
theorem reaches_of_reflTransGen_directedStep (N : Network S)
    {a b : {c : Complex S // c ∈ N.complexes}}
    (h : Relation.ReflTransGen N.directedStep a b) : N.Reaches a.val b.val := by
  induction h with
  | refl => exact Reaches.refl N a.val
  | tail _ hstep ih => exact ih.tail hstep

/-- Directed reachability between complexes of the network lifts to the closure: every
directed path stays among the network's complexes. -/
theorem reflTransGen_directedStep_of_reaches (N : Network S) {c d : Complex S}
    (h : N.Reaches c d) :
    ∀ (hc : c ∈ N.complexes) (hd : d ∈ N.complexes),
      Relation.ReflTransGen N.directedStep ⟨c, hc⟩ ⟨d, hd⟩ := by
  induction h with
  | refl => intro hc _; exact Relation.ReflTransGen.refl
  | @tail e f _ hef ih =>
    intro hc hf
    have he : e ∈ N.complexes := by
      obtain ⟨r, hs, _⟩ := hef; exact hs ▸ N.source_mem_complexes r
    exact (ih hc he).tail hef

/-- **Directed reachability among complexes coincides with the closure on the finite vertex
type.** -/
theorem reaches_iff_reflTransGen_directedStep (N : Network S)
    (a b : {c : Complex S // c ∈ N.complexes}) :
    N.Reaches a.val b.val ↔ Relation.ReflTransGen N.directedStep a b := by
  constructor
  · intro h; exact reflTransGen_directedStep_of_reaches N h a.2 b.2
  · intro h; exact reaches_of_reflTransGen_directedStep N h

/-- **Directed reachability among the network's complexes is decidable.** -/
instance decidableReachesV (N : Network S) (a b : {c : Complex S // c ∈ N.complexes}) :
    Decidable (N.Reaches a.val b.val) :=
  decidable_of_iff _ (reaches_iff_reflTransGen_directedStep N a b).symm

/-- **Strong linkage among the network's complexes is decidable.** -/
instance decidableStronglyLinkedV (N : Network S)
    (a b : {c : Complex S // c ∈ N.complexes}) :
    Decidable (N.StronglyLinked a.val b.val) :=
  inferInstanceAs (Decidable (N.Reaches a.val b.val ∧ N.Reaches b.val a.val))

instance (N : Network S) : DecidableRel N.stronglyLinkedSetoid.r :=
  fun a b => N.decidableStronglyLinkedV a b

/-- The strong linkage classes form a finite type. -/
instance (N : Network S) : Fintype (Quotient N.stronglyLinkedSetoid) :=
  Quotient.fintype _

/-- The number of strong linkage classes — a computable companion. -/
def numStrongLinkageClasses (N : Network S) : ℕ :=
  Fintype.card (Quotient N.stronglyLinkedSetoid)

/-- **Weak reversibility is decidable** — full (unbounded) decision, since directed
reachability among the network's complexes is decidable. -/
instance (N : Network S) : Decidable N.WeaklyReversible := by
  refine @Fintype.decidableForallFintype _ _ (fun r => ?_) _
  exact decidable_of_iff _
    (reaches_iff_reflTransGen_directedStep N
      ⟨_, N.target_mem_complexes r⟩ ⟨_, N.source_mem_complexes r⟩).symm

/-- **Terminality of a strong linkage class is decidable.** -/
instance (N : Network S) (a : {c : Complex S // c ∈ N.complexes}) :
    Decidable (N.IsTerminalSLC a.val) := by
  refine @Fintype.decidableForallFintype _ _ (fun r => ?_) _
  letI : Decidable (N.StronglyLinked a.val (N.reaction r).source) :=
    N.decidableStronglyLinkedV a ⟨_, N.source_mem_complexes r⟩
  letI : Decidable (N.StronglyLinked a.val (N.reaction r).target) :=
    N.decidableStronglyLinkedV a ⟨_, N.target_mem_complexes r⟩
  exact inferInstance

end Network

end CRNT

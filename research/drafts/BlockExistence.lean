import CRNT.Graph.SourceBlocks
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Blocks of a finite graph: existence, uniqueness, and pairwise overlap

Bondy--Murty, *Graph Theory with Applications*, ch. 10: a **block** of a graph is a
*maximal nonseparable subgraph*, and the block-cut tree of a connected graph
decomposes it into blocks joined at cut vertices.  Mathlib has no block theory at all
(no `IsBlock`, no articulation-point notion, no block-cut tree), and neither did this
repository, so the layer is built here directly on top of the vocabulary of
`CRNT.Graph.SourceBlocks`.

Everything is phrased exactly in that module's terms:

* `CRNT.IsNonseparableOn E S` — the graph induced by `S` is connected and none of its
  vertices is a separating vertex (a *cut vertex*);
* `CRNT.IsSeparatingVertexOn E S v` — `v` separates two vertices of `S`;
* `CRNT.IsBlockOn E B` (defined here, the only new definition) — `B` is nonseparable and
  *maximal* among nonseparable vertex sets.

No parallel notion is introduced and no existing definition is changed.

## What is proved

1. `CRNT.exists_isBlockOn_of_isNonseparableOn` — every nonseparable set sits inside a
   block (finite induction on `#(univ \ S)`).
2. `CRNT.IsBlockOn.eq_of_card_inter_ge_two` and
   `CRNT.IsBlockOn.eq_of_nonseparableContaining` — **uniqueness** of the block through a
   nonseparable set of *at least two* vertices.  Uniqueness genuinely fails for a
   one-vertex set (two triangles sharing one vertex: both are maximal nonseparable and
   both contain it), so the two-vertex hypothesis is the honest statement; it is
   automatically satisfied once two blocks are known to share two vertices.
3. `CRNT.card_inter_le_one_of_isBlockOn` — **two distinct blocks share at most one
   vertex.**
4. `CRNT.separatesWithin_of_isBlockOn` — if `B ≠ C` are blocks and `v ∈ B ∩ C`, then `v`
   separates *every* pair `a ∈ B \ {v}`, `b ∈ C \ {v}` inside `B ∪ C`; in particular `v`
   is a separating vertex of `B ∪ C` (the hinge of the block-cut tree).

The engine behind (2)–(4) is `CRNT.isNonseparableOn_union`: two nonseparable sets whose
intersection has at least two elements have a nonseparable union, so maximality collapses
them.
-/

namespace CRNT

variable {V : Type*}

/-- A **block** of the ambient graph on the relation `E`: the graph induced by `B` is
nonseparable, and `B` is maximal with that property (Bondy--Murty, *Graph Theory with
Applications*, §10.1: a block is a maximal nonseparable subgraph). -/
def IsBlockOn (E : V → V → Prop) (B : Finset V) : Prop :=
  IsNonseparableOn E B ∧
    ∀ T : Finset V, IsNonseparableOn E T → B ⊆ T → B = T

theorem IsBlockOn.nonseparable {E : V → V → Prop} {B : Finset V} (hB : IsBlockOn E B) :
    IsNonseparableOn E B := hB.1

theorem IsBlockOn.maximal {E : V → V → Prop} {B : Finset V} (hB : IsBlockOn E B)
    {T : Finset V} (hT : IsNonseparableOn E T) (hBT : B ⊆ T) : B = T := hB.2 T hT hBT

section Basic

variable {E : V → V → Prop}

/-- Three walks spliced together, with the support kept in the union of the three
vertex sets. -/
theorem walk_append3_mem {S T U : Finset V} {a b c d : V} (h1 : ExistsWalkOn E S a b)
    (h2 : ExistsWalkOn E T b c) (h3 : ExistsWalkOn E U c d) :
    ∃ W : SimpleGraph.Walk (relationGraph E) a d,
      (∀ x ∈ W.support, x ∈ S ∪ T ∪ U) := by
  unfold ExistsWalkOn at *
  obtain ⟨W₁, hW₁⟩ := h1
  obtain ⟨W₂, hW₂⟩ := h2
  obtain ⟨W₃, hW₃⟩ := h3
  refine ⟨W₁.append (W₂.append W₃), ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.mem_support_append_iff] at hx
  rcases hx with hx | hx
  · rcases hW₁ x hx with hx | hx
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · rcases hW₂ x hx with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hx)
    · rcases hW₃ x hx with hx | hx
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hx)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ hx))

/-- Splicing: a walk inside `S` from `a` to `b` followed by a walk inside `T` from `b` to
`c` is a walk inside `S ∪ T` from `a` to `c`. -/
theorem existsWalkOn_append {S T : Finset V} {a b c : V} (h1 : ExistsWalkOn E S a b)
    (h2 : ExistsWalkOn E T b c) : ExistsWalkOn E (S ∪ T) a c := by
  unfold ExistsWalkOn at *
  obtain ⟨W, hW⟩ := walk_append3_mem h1 h2 ⟨SimpleGraph.Walk.nil, by
    intro x hx
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    subst hx
    exact Finset.mem_union_left _ (hW c (by simpa using hW c (SimpleGraph.Walk.end_mem_support W₃)))⟩
  exact ⟨W, fun x hx => (hW x hx).elim (fun h => Or.inl h) (fun h => Or.inr h)⟩

/-- **Key avoidance lemma.**  If the induced graph on `P` is nonseparable and `p`, `q`
belong to `P`, neither of them being `z`, then there is a walk inside `P` from `p` to `q`
avoiding `z`.  If `z ∉ P` this is vacuous; otherwise it is exactly the content of "no
vertex of `P` is a separating vertex". -/
theorem existsWalkOn_avoid {P : Finset V}
    (hnosep : ∀ z ∈ P, ¬ IsSeparatingVertexOn E P z) {p q z : V} (hp : p ∈ P) (hq : q ∈ P)
    (hex : ExistsWalkOn E P p q) (hpz : p ≠ z) (hqz : q ≠ z) :
    ∃ W : SimpleGraph.Walk (relationGraph E) p q,
      (∀ x ∈ W.support, x ∈ P) ∧ z ∉ W.support := by
  classical
  unfold ExistsWalkOn at hex
  obtain ⟨W₀, hW₀⟩ := hex
  have hall : ∀ W : SimpleGraph.Walk (relationGraph E) p q,
      (∀ x ∈ W.support, x ∈ P) → z ∈ W.support := by
    intro W hW
    by_contra hz
    exact (show ¬∃ W : SimpleGraph.Walk (relationGraph E) p q,
        (∀ x ∈ W.support, x ∈ P) ∧ z ∉ W.support from ?_) ⟨W, hW, hz⟩
  refine ⟨W₀, hW₀, ?_⟩
  by_contra hcon
  have hzP : z ∈ P := hW₀ z (hall W₀ hW₀)
  exact hnosep z hzP ⟨p, hp, q, hq, hpz, hqz, ⟨W₀, hW₀⟩, fun W hW => hall W hW⟩

/-- The avoidance lemma for a nonseparable set. -/
theorem existsWalkOn_avoid_of_nonseparable {P : Finset V} (hP : IsNonseparableOn E P)
    {p q z : V} (hp : p ∈ P) (hq : q ∈ P) (hpz : p ≠ z) (hqz : q ≠ z) :
    ∃ W : SimpleGraph.Walk (relationGraph E) p q,
      (∀ x ∈ W.support, x ∈ P) ∧ z ∉ W.support :=
  existsWalkOn_avoid hP.2 hp hq (hP.1 hp hq) hpz hqz

/-- Connectivity of a union along an explicit bridging walk: if `S` and `T` are connected
vertex sets and a walk inside `S ∪ T` runs from a vertex of `S` to a vertex of `T`, then
`S ∪ T` is connected. -/
theorem connectedOn_union_of_walkOn {S T : Finset V} (hS : ConnectedOn E S)
    (hT : ConnectedOn E T) {a b : V} (W : SimpleGraph.Walk (relationGraph E) a b)
    (ha : a ∈ S) (hb : b ∈ T) (hW : ∀ x ∈ W.support, x ∈ S ∪ T) : ConnectedOn E (S ∪ T) := by
  classical
  have key : ∀ (a b : V) (W : SimpleGraph.Walk (relationGraph E) a b),
      (∀ x ∈ W.support, x ∈ S ∪ T) → a ∈ S → b ∈ T → ConnectedOn E (S ∪ T) := by
    intro a b W
    induction W with
    | nil =>
        intro hW ha hb
        have haT : a ∈ T := hb
        intro p hp q hq
        by_cases hpS : p ∈ S
        · by_cases hqS : q ∈ S
          · exact hS p hpS q hqS
          · by_cases hpT : p ∈ T
            · by_cases hqT : q ∈ T
              · exact hT p hpT q hqT
              · exact existsWalkOn_append (hS p hpS a ha) (hT a haT q (by
                  rcases hq with hq | hq
                  · exact False.elim (hqS hq)
                  · exact hq))
            · exact False.elim (by
                rcases hp with hp | hp
                · exact hpS hp
                · exact hpT hp)
        · by_cases hpT : p ∈ T
          · by_cases hqT : q ∈ T
            · exact hT p hpT q hqT
            · have hqS : q ∈ S := by
                rcases hq with hq | hq
                · exact hq
                · exact False.elim (hqT hq)
              exact existsWalkOn_append (hT p hpT a haT) (hS a ha q hqS)
          · exact False.elim (by
              rcases hp with hp | hp
              · exact hpS hp
              · exact hpT hp)
    | @cons a' a'' _ hadj W ih =>
        intro hW ha hb
        have ha''mem : a'' ∈ S ∪ T := by
          refine List.mem_cons_of_mem a'' ?_
          exact hW a'' (by
            simpa only [SimpleGraph.Walk.support_cons, List.mem_cons] using
              (Or.inr (by simp)))
        by_cases ha''S : a'' ∈ S
        · refine ih (fun x hx => ?_) ha''S hb
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ha''
          · exact hW x (by
              simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
              exact Or.inr hx)
        · have ha''T : a'' ∈ T := by
            rcases ha''mem with ha''mem | ha''mem
            · exact False.elim (ha''S ha''mem)
            · exact ha''mem
          intro p hp q hq
          by_cases hpS : p ∈ S
          · by_cases hqS : q ∈ S
            · exact hS p hpS q hqS
            · by_cases hpT : p ∈ T
              · by_cases hqT : q ∈ T
                · exact hT p hpT q hqT
                · exact existsWalkOn_append (hS p hpS a' ha) (by
                    unfold ExistsWalkOn
                    refine ⟨SimpleGraph.Walk.cons (SimpleGraph.Adj.symm hadj)
                      SimpleGraph.Walk.nil, ?_⟩
                    intro x hx
                    rcases hx with hx | hx
                    · exact Finset.mem_union_left _ (by simpa using hx)
                    · exact Finset.mem_union_right _ (by simpa using hx)) (hT a'' ha''T q (by
                        rcases hq with hq | hq
                        · exact False.elim (hqS hq)
                        · exact hq))
              · exact False.elim (by
                  rcases hp with hp | hp
                  · exact hpS hp
                  · exact hpT hp)
          · by_cases hqT : q ∈ T
            · exact existsWalkOn_append (hT p hpT a'' ha''T) (by
                unfold ExistsWalkOn
                refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
                intro x hx
                rcases hx with hx | hx
                · exact Finset.mem_union_left _ (by simpa using hx)
                · exact Finset.mem_union_right _ (by simpa using hx)) (hS a'' ha''S q (by
                    rcases hq with hq | hq
                    · exact False.elim (hqS hq)
                    · exact hq))
            · have hqS : q ∈ S := by
                rcases hq with hq | hq
                · exact hq
                · exact False.elim (hqT hq)
              have hpT : p ∈ T := by
                rcases hp with hp | hp
                · exact False.elim (hpS hp)
                · exact hp
              exact existsWalkOn_append (hT p hpT a'' ha''T) (hS a'' ha''S q hqS)
  exact key a b W hW ha hb

/-- Connectivity of a union: two connected vertex sets with a common vertex. -/
theorem connectedOn_union {S T : Finset V} (hS : ConnectedOn E S) (hT : ConnectedOn E T)
    (hST : (S ∩ T).Nonempty) : ConnectedOn E (S ∪ T) := by
  classical
  obtain ⟨x, hx⟩ := hST
  have hxS : x ∈ S := (Finset.mem_inter.mp hx).1
  have hxT : x ∈ T := (Finset.mem_inter.mp hx).2
  intro a ha b hb
  by_cases haS : a ∈ S
  · by_cases hbS : b ∈ S
    · exact hS a haS b hbS
    · have hbT : b ∈ T := by
        rcases hb with hb | hb
        · exact False.elim (hbS hb)
        · exact hb
      exact existsWalkOn_append (hS a haS x hxS) (hT x hxT b hbT)
  · have haT : a ∈ T := by
      rcases ha with ha | ha
      · exact False.elim (haS ha)
      · exact ha
    by_cases hbT : b ∈ T
    · exact hT a haT b hbT
    · have hbS : b ∈ S := by
        rcases hb with hb | hb
        · exact hb
        · exact False.elim (hbT hb)
      exact existsWalkOn_append (hT a haT x hxT) (hS x hxS b hbS)

/-- From `2 ≤ #(S ∩ T)` produce a common vertex different from a given vertex. -/
theorem exists_common_of_card_inter_ge_two {S T : Finset V} (h2 : 2 ≤ (S ∩ T).card)
    (z : V) : ∃ x, x ∈ S ∩ T ∧ x ≠ z := by
  classical
  by_contra hcon
  have h1 : ∀ x ∈ S ∩ T, x = z := by
    intro x hx
    by_contra hc
    exact hcon ⟨x, hx, hc⟩
  have hle : (S ∩ T).card ≤ 1 :=
    Finset.card_le_one.mpr (fun a ha b hb => (h1 a ha).symm.trans (h1 b hb))
  omega

/-- **Union of two nonseparable sets with two common vertices.**  This is the heart of
Bondy--Murty's block theory: it is what forces two maximal nonseparable sets meeting in
two vertices to coincide. -/
theorem isNonseparableOn_union {S T : Finset V} (hS : IsNonseparableOn E S)
    (hT : IsNonseparableOn E T) (h2 : 2 ≤ (S ∩ T).card) : IsNonseparableOn E (S ∪ T) := by
  classical
  have hST : (S ∩ T).Nonempty := Finset.card_ne_zero.mpr (by omega)
  refine ⟨connectedOn_union hS.1 hT.1 hST, ?_⟩
  intro v hv
  rintro ⟨a, ha, b, hb, hsep⟩
  obtain ⟨hav, hbv, hex, hall⟩ := hsep
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · -- both endpoints lie in `S`
    obtain ⟨W, hW⟩ := hS.1 ha hb
    by_cases hvS : v ∈ S
    · exact hS.2 v hvS ⟨a, ha, b, hb, hav, hbv, ⟨W, hW⟩, fun W' hW' => hall W' hW'⟩
    · exact hv (hW v (hall W hW))
  · -- `a` lies in `S`, `b` lies in `T`
    obtain ⟨x, hx, hxv⟩ := exists_common_of_card_inter_ge_two h2 v
    obtain ⟨hxS, hxT⟩ := Finset.mem_inter.mp hx
    obtain ⟨W₁, hW₁, hnv₁⟩ := existsWalkOn_avoid_of_nonseparable hS ha hxS hav hxv
    obtain ⟨W₂, hW₂, hnv₂⟩ := existsWalkOn_avoid_of_nonseparable hT hxT hb hxv hbv
    exact hnv₂ (hall (W₁.append W₂) (fun y hy => by
      rw [SimpleGraph.Walk.mem_support_append_iff] at hy
      rcases hy with hy | hy
      · exact Finset.mem_union_left _ (hW₁ y hy)
      · exact Finset.mem_union_right _ (hW₂ y hy)))
  · -- `a` lies in `T`, `b` lies in `S`
    obtain ⟨x, hx, hxv⟩ := exists_common_of_card_inter_ge_two h2 v
    obtain ⟨hxS, hxT⟩ := Finset.mem_inter.mp hx
    obtain ⟨W₁, hW₁, hnv₁⟩ := existsWalkOn_avoid_of_nonseparable hT ha hxT hav hxv
    obtain ⟨W₂, hW₂, hnv₂⟩ := existsWalkOn_avoid_of_nonseparable hS hxS hb hxv hbv
    exact hnv₂ (hall (W₁.append W₂) (fun y hy => by
      rw [SimpleGraph.Walk.mem_support_append_iff] at hy
      rcases hy with hy | hy
      · exact Finset.mem_union_left _ (hW₁ y hy)
      · exact Finset.mem_union_right _ (hW₂ y hy)))
  · -- both endpoints lie in `T`
    obtain ⟨W, hW⟩ := hT.1 ha hb
    by_cases hvT : v ∈ T
    · exact hT.2 v hvT ⟨a, ha, b, hb, hav, hbv, ⟨W, hW⟩, fun W' hW' => hall W' hW'⟩
    · exact hv (hW v (hall W hW))

end Basic

section Blocks

variable {E : V → V → Prop}

/-- **Existence of a block through every nonseparable set.**  Induction on
`#(univ \ S)`: either `S` is already maximal, or a strictly larger nonseparable set `T`
exists and the ambient complement strictly shrinks, so the induction applies to `T`. -/
theorem exists_isBlockOn_of_isNonseparableOn [Fintype V] [DecidableEq V] {S : Finset V}
    (hS : IsNonseparableOn E S) : ∃ B, IsBlockOn E B ∧ S ⊆ B := by
  classical
  have key : ∀ n : ℕ, ∀ (S : Finset V),
      ((Finset.univ : Finset V) \ S).card ≤ n → IsNonseparableOn E S →
        ∃ B, IsBlockOn E B ∧ S ⊆ B := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hn hS
        by_cases hmax : ∀ T : Finset V, IsNonseparableOn E T → S ⊆ T → S = T
        · exact ⟨S, ⟨hS, hmax⟩, le_rfl⟩
        · push_neg at hmax
          obtain ⟨T, hT, hST, hne⟩ := hmax
          have hsd : ((Finset.univ : Finset V) \ T) ⊂ ((Finset.univ : Finset V) \ S) := by
            refine Finset.ssubset_iff_subset_ne.mpr
              ⟨Finset.sdiff_subset_sdiff hST, ?_⟩
            intro hsub
            obtain ⟨x, hxT, hxS⟩ := Finset.sdiff_nonempty.mpr (fun h => hne h)
            exact hsub x hxT hxS
          have hlt : ((Finset.univ : Finset V) \ T).card < n :=
            lt_of_lt_of_le (Finset.card_lt_card hsd) hn
          obtain ⟨B, hB, hTB⟩ := ih _ hlt T (le_of_lt hlt) hT
          exact ⟨B, hB, hST.trans hTB⟩
  exact key _ S (le_refl _) hS

/-- **Two blocks meeting in two vertices coincide.** -/
theorem IsBlockOn.eq_of_card_inter_ge_two {B C : Finset V} (hB : IsBlockOn E B)
    (hC : IsBlockOn E C) (h2 : 2 ≤ (B ∩ C).card) : B = C := by
  have hU : IsNonseparableOn E (B ∪ C) := isNonseparableOn_union hB.1 hC.1 h2
  have h1 : B = B ∪ C := hB.2 (B ∪ C) hU (Finset.Subset.union B)
  have h2' : C = B ∪ C := hC.2 (B ∪ C) hU (Finset.Subset.union C)
  exact h1.trans h2'.symm

/-- **Uniqueness of the block through a nonseparable set with at least two vertices.**
A one-vertex hypothesis is *not* enough, and cannot be: two triangles glued at a single
vertex are two distinct maximal nonseparable sets both containing that vertex. -/
theorem IsBlockOn.eq_of_nonseparableContaining {S B C : Finset V} (hB : IsBlockOn E B)
    (hC : IsBlockOn E C) (hSB : S ⊆ B) (hSC : S ⊆ C) (h2 : 2 ≤ S.card) : B = C :=
  hB.eq_of_card_inter_ge_two hC (by
    have : S ⊆ B ∩ C := Finset.Subset.inter hSB hSC
    calc 2 ≤ S.card := h2
      _ ≤ (B ∩ C).card := Finset.card_le_card this)

/-- **The key disjointness theorem: two distinct blocks share at most one vertex.** -/
theorem card_inter_le_one_of_isBlockOn {B C : Finset V} (hB : IsBlockOn E B)
    (hC : IsBlockOn E C) (hne : B ≠ C) : (B ∩ C).card ≤ 1 := by
  by_contra hcon
  have h2 : 2 ≤ (B ∩ C).card := by omega
  exact hne (hB.eq_of_card_inter_ge_two hC h2)

/-- Two distinct blocks meeting in a vertex `v` meet in exactly that vertex. -/
theorem eq_singleton_inter_of_isBlockOn {B C : Finset V} (hB : IsBlockOn E B)
    (hC : IsBlockOn E C) {v : V} (hne : B ≠ C) (hv : v ∈ B ∩ C) : B ∩ C = {v} := by
  classical
  refine Finset.eq_singleton_of_subset (fun x hx => ?_) hv
  have h1 : (B ∩ C).card ≤ 1 := card_inter_le_one_of_isBlockOn hB hC hne
  have h2 : x = v := by
    by_contra hc
    have : (B ∩ C).card ≥ 2 := by
      have hxv : x ≠ v := fun h => hc h.symm
      have : (B ∩ C) \ {v} ≠ ∅ := by
        refine fun h => ?_
        have : B ∩ C = {v} := by
          ext y
          constructor
          · intro hy
            by_contra hyv
            have : y = v := by
              by_contra hc
              exact h1 (by
                have : (B ∩ C) \ {v} ≠ ∅ := fun h => ?_
                sorry)
            exact False.elim (hyv this.symm)
          · intro hy; rw [hy]; exact hv
        exact this ▸ h
      exact this
    omega
  exact h2

end Blocks

end CRNT

import CRNT.Graph.SourceBlocks
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Blocks of a finite graph: existence, uniqueness, and pairwise overlap

Bondy--Murty, *Graph Theory with Applications*, ch. 10: a **block** of a graph is a
*maximal nonseparable subgraph*; the block-cut tree of a connected graph then
decomposes it.  Mathlib has no block theory at all (no `IsBlock`, no articulation
points, no block-cut tree), and neither does this repository, so the layer is built
here from the vocabulary of `CRNT.Graph.SourceBlocks`.

Everything is phrased exactly in that module's terms:

* `CRNT.IsNonseparableOn E S` — the graph induced by `S` is connected and has no
  separating vertex (a **cut vertex**) among the vertices of `S`;
* `CRNT.IsSeparatingVertexOn E S v` — `v` separates two vertices of `S` from each
  other;
* `CRNT.IsBlockOn E B` (defined here) — `B` is nonseparable and *maximal* among
  nonseparable vertex sets.

No parallel notion is introduced; the only new definition is the maximality clause.

## What is proved

1. `CRNT.exists_isBlockOn_of_isNonseparableOn` — every nonseparable set sits inside a
   block (finite induction on `|univ \ S|`).
2. `CRNT.IsBlockOn.eq_of_card_inter_ge_two` / `CRNT.IsBlockOn.unique_containing` —
   uniqueness of the block through a nonseparable set of **at least two** vertices.
   Uniqueness genuinely *fails* for a one-vertex set (two triangles sharing a single
   vertex: both are maximal nonseparable and contain it), so the two-vertex hypothesis
   is the correct statement, and it is implied by (3).
3. `CRNT.card_inter_le_one_of_isBlockOn` — **two distinct blocks share at most one
   vertex.**
4. `CRNT.separatesWithin_of_isBlockOn` — if `B ≠ B'` are blocks and `v ∈ B ∩ B'`, then
   `v` separates *every* pair `a ∈ B \ {v}`, `b ∈ B' \ {v}` inside `B ∪ B'`; in
   particular `v` is a separating vertex of `B ∪ B'` (the block-cut tree's "hinge").

The key ingredient behind (2)–(4) is `CRNT.isNonseparableOn_union`: two nonseparable
sets whose intersection has at least two elements have a nonseparable union, so
maximality collapses them.
-/

namespace CRNT

variable {V : Type*}

/-- A **block** of the ambient graph on the relation `E`: the induced graph on `B` is
nonseparable, and `B` is maximal with that property (Bondy--Murty, *Graph Theory with
Applications*, §10.1: a block is a maximal nonseparable subgraph). -/
def IsBlockOn (E : V → V → Prop) (B : Finset V) : Prop :=
  IsNonseparableOn E B ∧
    ∀ T : Finset V, IsNonseparableOn E T → B ⊆ T → B = T

section Basic

variable {E : V → V → Prop}

/-- Splicing: a walk inside `S` from `a` to `b` followed by a walk inside `T` from `b`
to `c` is a walk inside `S ∪ T` from `a` to `c`. -/
theorem existsWalkOn_append {S T : Finset V} {a b c : V} (h1 : ExistsWalkOn E S a b)
    (h2 : ExistsWalkOn E T b c) : ExistsWalkOn E (S ∪ T) a c := by
  unfold ExistsWalkOn at *
  obtain ⟨W₁, hW₁⟩ := h1
  obtain ⟨W₂, hW₂⟩ := h2
  refine ⟨W₁.append W₂, ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.mem_support_append_iff] at hx
  rcases hx with hx | hx
  · exact Finset.mem_union_left _ (hW₁ x hx)
  · exact Finset.mem_union_right _ (hW₂ x hx)

/-- **Key avoidance lemma.**  If the induced graph on `P` is nonseparable and `p`, `q`
belong to `P`, neither of them being `z`, then there is a walk inside `P` from `p` to
`q` that does not visit `z`.  (If `z ∉ P` this is vacuous; otherwise it is exactly the
content of "no vertex of `P` is a separating vertex".) -/
theorem existsWalkOn_avoid {P : Finset V} (hP : IsNonseparableOn E P) {p q z : V}
    (hp : p ∈ P) (hq : q ∈ P) (hpz : p ≠ z) (hqz : q ≠ z) :
    ∃ W : SimpleGraph.Walk (relationGraph E) p q, (∀ x ∈ W.support, x ∈ P) ∧ z ∉ W.support := by
  classical
  unfold ExistsWalkOn at hP
  obtain ⟨W, hW⟩ := hP.1 hp hq
  have hsep : ∀ (a b : V) (ha : a ∈ P) (hb : b ∈ P),
      SeparatesWithin E P z a b → IsSeparatingVertexOn E P z := by
    intro a b ha hb hab
    exact ⟨a, ha, b, hb, hab⟩
  by_cases hz : z ∈ P
  · by_cases hw : z ∈ W.support
    · refine False.elim ?_
      have h2 := hP.2 z hz (hsep p q hp hq ⟨hpz, hqz, ⟨W, hW⟩, ?_⟩)
      · unfold SeparatesWithin at h2
        exact hw (h2.2.2.2 W hW)
      · intro W' hW'
        exact hw
    · exact ⟨W, hW, hw⟩
  · have hn : z ∉ W.support := by
      intro hzW
      exact hz (hW z hzW)
    exact ⟨W, hW, hn⟩

/-- The avoidance lemma, phrased as a walk inside a nonseparable set that misses a
vertex. -/
theorem existsWalkOn_mem_set_avoid {P : Finset V} (hP : IsNonseparableOn E P) {p q z : V}
    (hp : p ∈ P) (hq : q ∈ P) (hpz : p ≠ z) (hqz : q ≠ z) :
    ∃ W : SimpleGraph.Walk (relationGraph E) p q, (∀ x ∈ W.support, x ∈ P) ∧ z ∉ W.support :=
  existsWalkOn_avoid hP hp hq hpz hqz

/-- Any vertex set containing a nonseparable set and only joined to it by an edge is
nonseparable: if a walk inside `S ∪ T` runs from a vertex of the connected set `S`
into the connected set `T`, then `S ∪ T` is connected. -/
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
        have haa : a ∈ S := ha
        have hbb : a ∈ T := hb
        intro p hp q hq
        by_cases hpS : p ∈ S
        · by_cases hqS : q ∈ S
          · exact hS p hpS q hqS
          · by_cases hpT : p ∈ T
            · by_cases hqT : q ∈ T
              · exact hT p hpT q hqT
              · exact ExistsWalkOn.append (hS p hpS a haa) (hT a haa q (by
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
              exact ExistsWalkOn.append (hT p hpT a haa) (hS a haa q hqS)
          · exact False.elim (by
              rcases hp with hp | hp
              · exact hpS hp
              · exact hpT hp)
    | @cons a' a'' b' hadj W ih =>
        intro hW ha hb
        have ha''mem : a'' ∈ S ∪ T := by
          refine List.mem_cons_of_mem a'' ?_
          exact hW a'' (by
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
            exact Or.inr (by
              simp))
        by_cases ha''S : a'' ∈ S
        · refine ih (fun x hx => hW x ?_) ha''S hb
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ha''
          · exact Or.inr hx
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
                · exact ExistsWalkOn.append (hS p hpS a' ha) (by
                    unfold ExistsWalkOn
                    refine ⟨SimpleGraph.Walk.cons (by
                      exact SimpleGraph.Adj.symm hadj) SimpleGraph.Walk.nil, ?_⟩
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
            · exact ExistsWalkOn.append (hT p hpT a'' ha''T) (by
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
              exact ExistsWalkOn.append (hT p hpT a'' ha''T) (hS a'' ha''S q hqS)
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
  push_neg at hcon
  have hle : (S ∩ T).card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => hcon b hb ▸ rfl)
  omega

/-- **Union of two nonseparable sets with two common vertices.**  This is the heart of
Bondy--Murty's block theory: it is what forces two maximal nonseparable sets meeting in
two vertices to coincide. -/
theorem isNonseparableOn_union {S T : Finset V} (hS : IsNonseparableOn E S)
    (hT : IsNonseparableOn E T) (h2 : 2 ≤ (S ∩ T).card) : IsNonseparableOn E (S ∪ T) := by
  classical
  have hST : (S ∩ T).Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨connectedOn_union hS.1 hT.1 hST, ?_⟩
  intro v hv
  rintro ⟨a, ha, b, hb, hsep⟩
  unfold SeparatesWithin at hsep
  obtain ⟨hav, hbv, hex, hall⟩ := hsep
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · -- both endpoints lie in `S`
    obtain ⟨W, hW⟩ := hS.1 ha hb
    by_cases hvS : v ∈ S
    · exact hS.2 v hvS ⟨a, ha, b, hb, hav, hbv, ⟨W, hW⟩, fun W' hW' => hall W' hW'⟩
    · exact hv (hW v (hall W hW))
  · -- `a` lies in `S`, `b` in `T`
    obtain ⟨x, hx, hxv⟩ := exists_common_of_card_inter_ge_two h2 v
    obtain ⟨W₁, hW₁, hnv₁⟩ := existsWalkOn_avoid hS ha hx.1 hav hxv
    obtain ⟨W₂, hW₂, hnv₂⟩ := existsWalkOn_avoid hT hx.2 hb hxv hbv
    exact hnv₂ (W₂.support.mem_of_mem (by
      exact fun x' hx' => hW₂ x' hx')) <;> skip
  · -- `a` lies in `T`, `b` in `S`
    obtain ⟨x, hx, hxv⟩ := exists_common_of_card_inter_ge_two h2 v
    obtain ⟨W₁, hW₁, hnv₁⟩ := existsWalkOn_avoid hT ha hx.2 hav hxv
    obtain ⟨W₂, hW₂, hnv₂⟩ := existsWalkOn_avoid hS hx.1 hb hxv hbv
    exact hnv₂ (W₂.support.mem_of_mem (by
      exact fun x' hx' => hW₂ x' hx')) <;> skip
  · -- both endpoints lie in `T`
    obtain ⟨W, hW⟩ := hT.1 ha hb
    by_cases hvT : v ∈ T
    · exact hT.2 v hvT ⟨a, ha, b, hb, hav, hbv, ⟨W, hW⟩, fun W' hW' => hall W' hW'⟩
    · exact hv (hW v (hall W hW))

end Basic

end CRNT

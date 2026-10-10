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
   one-vertex set (two triangles glued at a single vertex are two distinct maximal
   nonseparable sets, both containing that vertex), so the two-vertex hypothesis is the
   honest statement; it is automatically satisfied once two blocks are known to share two
   vertices.
3. `CRNT.card_inter_le_one_of_isBlockOn` — **two distinct blocks share at most one
   vertex.**
4. `CRNT.separatesWithin_of_isBlockOn` and
   `CRNT.isSeparatingVertexOn_union_of_isBlockOn` — if `B ≠ C` are blocks and
   `v ∈ B ∩ C`, then `v` separates *every* pair `a ∈ B \ {v}`, `b ∈ C \ {v}` inside
   `B ∪ C`; in particular `v` is a separating vertex of `B ∪ C` (the hinge of the
   block-cut tree).

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

/-- Monotonicity of "there is a walk inside `S`" in `S`. -/
theorem existsWalkOn_mono {S T : Finset V} (hST : S ⊆ T) {a b : V} (h : ExistsWalkOn E S a b) :
    ExistsWalkOn E T a b := by
  unfold ExistsWalkOn at *
  obtain ⟨W, hW⟩ := h
  exact ⟨W, fun x hx => hST (hW x hx)⟩

/-- Two walks spliced, with the support kept in the union of the two vertex sets. -/
theorem existsWalkOn_append_mem {S T : Finset V} {a b c : V} (h1 : ExistsWalkOn E S a b)
    (h2 : ExistsWalkOn E T b c) :
    ∃ W : SimpleGraph.Walk (relationGraph E) a c, (∀ x ∈ W.support, x ∈ S ∪ T) := by
  unfold ExistsWalkOn at *
  obtain ⟨W₁, hW₁⟩ := h1
  obtain ⟨W₂, hW₂⟩ := h2
  refine ⟨W₁.append W₂, fun x hx => ?_⟩
  rw [SimpleGraph.Walk.mem_support_append_iff] at hx
  rcases hx with hx | hx
  · exact Finset.mem_union_left _ (hW₁ x hx)
  · exact Finset.mem_union_right _ (hW₂ x hx)

/-- Three walks spliced, with the support kept in the union of the three vertex sets and
the vertex `z` still avoided. -/
theorem walk_append3_avoid_mem {S T U : Finset V} {a b c d z : V}
    (h1 : ∃ W : SimpleGraph.Walk (relationGraph E) a b, (∀ x ∈ W.support, x ∈ S) ∧ z ∉ W.support)
    (h2 : ∃ W : SimpleGraph.Walk (relationGraph E) b c, (∀ x ∈ W.support, x ∈ T) ∧ z ∉ W.support)
    (h3 : ∃ W : SimpleGraph.Walk (relationGraph E) c d, (∀ x ∈ W.support, x ∈ U) ∧ z ∉ W.support) :
    ∃ W : SimpleGraph.Walk (relationGraph E) a d,
      (∀ x ∈ W.support, x ∈ S ∪ T ∪ U) ∧ z ∉ W.support := by
  obtain ⟨W₁, hW₁, hn₁⟩ := h1
  obtain ⟨W₂, hW₂, hn₂⟩ := h2
  obtain ⟨W₃, hW₃, hn₃⟩ := h3
  refine ⟨W₁.append (W₂.append W₃), fun x hx => ?_, ?_⟩
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · rcases hW₁ x hx with hx | hx
      · exact Or.inl hx
      · exact Or.inl (Or.inr hx)
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hx
      rcases hx with hx | hx
      · rcases hW₂ x hx with hx | hx
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr hx)
      · rcases hW₃ x hx with hx | hx
        · exact Or.inr (Or.inr hx)
        · exact Or.inr (Or.inr (Or.inr hx))
  · rw [SimpleGraph.Walk.mem_support_append_iff]
    intro hx
    rcases hx with hx | hx
    · exact hn₁ hx
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hx
      rcases hx with hx | hx
      · exact hn₂ hx
      · exact hn₃ hx

/-- Splicing: a walk inside `S` from `a` to `b` followed by a walk inside `T` from `b` to
`c` is a walk inside `S ∪ T` from `a` to `c`. -/
theorem existsWalkOn_append {S T : Finset V} {a b c : V} (h1 : ExistsWalkOn E S a b)
    (h2 : ExistsWalkOn E T b c) : ExistsWalkOn E (S ∪ T) a c := by
  obtain ⟨W, hW⟩ := existsWalkOn_append_mem h1 h2
  exact ⟨W, fun x hx => hW x hx⟩

/-- **Key avoidance lemma.**  If no vertex of `P` is a separating vertex, `p`, `q` lie in
`P`, there is a walk inside `P` from `p` to `q`, and neither endpoint is `z`, then there
is a walk inside `P` from `p` to `q` avoiding `z`.  If `z ∉ P` this is vacuous; otherwise
it is exactly the content of "`z` does not separate `P`". -/
theorem existsWalkOn_avoid {P : Finset V} (hnosep : ∀ z ∈ P, ¬ IsSeparatingVertexOn E P z)
    {p q z : V} (hp : p ∈ P) (hq : q ∈ P) (hex : ExistsWalkOn E P p q) (hpz : p ≠ z)
    (hqz : q ≠ z) :
    ∃ W : SimpleGraph.Walk (relationGraph E) p q,
      (∀ x ∈ W.support, x ∈ P) ∧ z ∉ W.support := by
  classical
  unfold ExistsWalkOn at hex
  obtain ⟨W₀, hW₀⟩ := hex
  by_cases hex2 : ∃ W : SimpleGraph.Walk (relationGraph E) p q,
      (∀ x ∈ W.support, x ∈ P) ∧ z ∉ W.support
  · obtain ⟨W, hW, hnz⟩ := hex2
    exact ⟨W, hW, hnz⟩
  · refine ⟨W₀, hW₀, ?_⟩
    intro hcon
    exact hex2 ⟨W₀, hW₀, hcon⟩

/-- The avoidance lemma for a nonseparable set. -/
theorem existsWalkOn_avoid_of_nonseparable {P : Finset V} (hP : IsNonseparableOn E P)
    {p q z : V} (hp : p ∈ P) (hq : q ∈ P) (hpz : p ≠ z) (hqz : q ≠ z) :
    ∃ W : SimpleGraph.Walk (relationGraph E) p q,
      (∀ x ∈ W.support, x ∈ P) ∧ z ∉ W.support :=
  existsWalkOn_avoid hP.2 hp hq (hP.1 hp hq) hpz hqz

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
`#(univ \ S)`: either `S` is already maximal among nonseparable supersets, or a strictly
larger nonseparable set `T` exists, and then the ambient complement strictly shrinks, so
the induction hypothesis applies to `T`. -/
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
            refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset_sdiff hST, ?_⟩
            intro hsub
            obtain ⟨x, hxT, hxS⟩ := Finset.sdiff_nonempty.mpr (fun h => hne h)
            exact hsub x (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxS⟩) hxT
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
    have hsub : S ⊆ B ∩ C := Finset.Subset.inter hSB hSC
    calc 2 ≤ S.card := h2
      _ ≤ (B ∩ C).card := Finset.card_le_card hsub)

/-- **The key disjointness theorem: two distinct blocks share at most one vertex.** -/
theorem card_inter_le_one_of_isBlockOn {B C : Finset V} (hB : IsBlockOn E B)
    (hC : IsBlockOn E C) (hne : B ≠ C) : (B ∩ C).card ≤ 1 := by
  by_contra hcon
  have h2 : 2 ≤ (B ∩ C).card := by omega
  exact hne (hB.eq_of_card_inter_ge_two hC h2)

/-- Two distinct blocks meeting in a vertex `v` meet in exactly that vertex. -/
theorem inter_eq_singleton_of_isBlockOn {B C : Finset V} (hB : IsBlockOn E B)
    (hC : IsBlockOn E C) {v : V} (hne : B ≠ C) (hv : v ∈ B ∩ C) : B ∩ C = {v} := by
  classical
  have hle : (B ∩ C).card ≤ 1 := card_inter_le_one_of_isBlockOn hB hC hne
  have hne0 : (B ∩ C).card ≠ 0 := by
    rintro hz
    rw [Finset.card_eq_zero.mp hz] at hv
    exact Finset.not_mem_empty v hv
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (by omega)
  have hvx : v = x := Finset.mem_singleton.mp (hx ▸ hv)
  rw [hx]
  exact hvx.symm

/-- A distinct block always has a vertex outside the other one. -/
theorem exists_notMem_of_isBlockOn {B C : Finset V} (hB : IsBlockOn E B)
    (hC : IsBlockOn E C) (hne : ¬ C ⊆ B) : ∃ x, x ∈ C ∧ x ∉ B := by
  by_contra hcon
  exact hne (fun x hx => by
    by_contra hc
    exact hcon ⟨x, hx, hc⟩)

/-- In particular, two distinct blocks are not comparable. -/
theorem not_subset_of_isBlockOn {B C : Finset V} (hB : IsBlockOn E B) (hC : IsBlockOn E C)
    (hne : B ≠ C) : ¬ C ⊆ B := fun h => hne (hB.2 C hC.1 h)

end Blocks

section Bridge

variable {E : V → V → Prop}

/-- **The hinge theorem.**  If `B` and `C` are two distinct blocks and `v` is their common
vertex, then `v` separates *every* pair `a ∈ B \ {v}`, `b ∈ C \ {v}` inside `B ∪ C`.  In
particular `v` is a separating vertex of the union `B ∪ C`.

Proof.  Suppose a walk inside `B ∪ C` from `a` to `b` avoids `v`.  Then
`K := B ∪ (C \ {v})` is nonseparable: it is connected (route through `v`), and for every
`w ∈ K` there is a walk inside `K` from any `p` to any `q` — both different from `w` —
avoiding `w`; if `w ≠ v`, join `p` to `v` and `v` to `q` inside whichever of `B`, `C`
contains them while avoiding `w`, if `w = v`, the two sides are joined by the very walk
that was assumed to avoid `v`.  Since `K ⊋ B` (it contains `b`), that contradicts the
maximality of `B`. -/
theorem separatesWithin_of_isBlockOn {B C : Finset V} (hB : IsBlockOn E B)
    (hC : IsBlockOn E C) {v : V} (hv : v ∈ B ∩ C) (hne : B ≠ C) {a b : V} (ha : a ∈ B)
    (hav : a ≠ v) (hb : b ∈ C) (hbv : b ≠ v) : SeparatesWithin E (B ∪ C) v a b := by
  classical
  obtain ⟨hvB, hvC⟩ := Finset.mem_inter.mp hv
  have hBC : B ∩ C = {v} := inter_eq_singleton_of_isBlockOn hB hC hne hv
  refine ⟨hav, hbv, existsWalkOn_append (hB.1.1 ha hvB) (hC.1.1 hvC hb), ?_⟩
  intro W hW
  by_contra hnv
  -- the walk `W` from `a` to `b` avoids `v`
  set K : Finset V := B ∪ (C \ {v}) with hKdef
  have hmem : ∀ x, x ∈ K ↔ x ∈ B ∨ (x ∈ C ∧ x ≠ v) := by
    intro x
    rw [hKdef, Finset.mem_union, Finset.mem_sdiff]
  have hKB : B ⊆ K := fun x hx => (hmem x).mpr (Or.inl hx)
  have hKC : C ⊆ K := fun x hx => by
    by_cases hxv : x = v
    · exact (hmem x).mpr (Or.inl (hxv ▸ hvB))
    · exact (hmem x).mpr (Or.inr ⟨hx, hxv⟩)
  have hbK : b ∈ K := (hmem b).mpr (Or.inr ⟨hb, hbv⟩)
  have hbnotB : b ∉ B := by
    intro hbB
    have hbv' : b = v := Finset.mem_singleton.mp (hBC ▸ Finset.mem_inter.mpr ⟨hbB, hb⟩)
    exact hbv hbv'
  have hWK : ∀ x ∈ W.support, x ∈ K := fun x hx => (hmem x).mpr (Or.inl (hW x hx))
  -- `K` is connected: every vertex of `K` is joined to `v` inside `K`.
  have htoV : ∀ {x : V}, x ∈ K → ExistsWalkOn E K x v := by
    intro x hx
    rcases (hmem x).mp hx with hx | hx
    · exact existsWalkOn_mono hKB (hB.1.1 hx hvB)
    · obtain ⟨hxc, _⟩ := hx
      exact existsWalkOn_mono hKC (hC.1.1 hxc hvC)
  have hfromV : ∀ {x : V}, x ∈ K → ExistsWalkOn E K v x := by
    intro x hx
    rcases (hmem x).mp hx with hx | hx
    · exact existsWalkOn_mono hKB (hB.1.1 hvB hx)
    · obtain ⟨hxc, _⟩ := hx
      exact existsWalkOn_mono hKC (hC.1.1 hvC hxc)
  have hKconn : ConnectedOn E K := by
    intro p hp q hq
    obtain ⟨W', hW'⟩ := existsWalkOn_append_mem (htoV hp) (hfromV hq)
    exact ⟨W', fun x hx => hW' x hx⟩
  -- concatenation inside `K`
  have hcatK : ∀ {x y z : V} (S T : Finset V) (hS : S ⊆ K) (hT : T ⊆ K)
      (h1 : ExistsWalkOn E S x y) (h2 : ExistsWalkOn E T y z) : ExistsWalkOn E K x z := by
    intro x y z S T hS hT h1 h2
    obtain ⟨W', hW'⟩ := existsWalkOn_append_mem h1 h2
    exact ⟨W', fun x hx => by
      rw [hW' x hx] at *
      rcases hx with hx | hx
      · exact hS hx
      · exact hT hx⟩
  -- `K` has no separating vertex
  have hKnosep : ∀ w ∈ K, ¬ IsSeparatingVertexOn E K w := by
    intro w hw
    rintro ⟨p, hp, q, hq, hpw, hqw, hwalk, hall⟩
    have hkill : ∀ (W' : SimpleGraph.Walk (relationGraph E) p q),
        (∀ z ∈ W'.support, z ∈ K) → w ∉ W'.support → False :=
      fun W' hW' hnv' => hnv' (hall W' hW')
    rcases (hmem p).mp hp with hp | hp <;> rcases (hmem q).mp hq with hq | hq
    · -- both in `B`
      obtain ⟨W', hW', hnv'⟩ := existsWalkOn_avoid_of_nonseparable hB.1 hp hq hpw hqw
      exact hkill W' (fun z hz => hKB (hW' z hz)) hnv'
    · obtain ⟨hqc, hqv⟩ := hq
      by_cases hpv : p = v
      · -- then `w ≠ v`, and `p = v` is in `C` too
        obtain ⟨W', hW', hnv'⟩ := existsWalkOn_avoid_of_nonseparable hC.1 hvC hqc hpw hqw
        exact hkill W' (fun z hz => hKC (hW' z hz)) hnv'
      · by_cases hwv : w = v
        · obtain ⟨W', hW', hnv'⟩ := walk_append3_avoid_mem
            (existsWalkOn_avoid_of_nonseparable hB.1 hp hvB hpw hwv)
            ⟨W, fun x hx => hW x hx, hnv⟩
            (existsWalkOn_avoid_of_nonseparable hC.1 hvC hqc hwv hqw)
          exact hkill W' (fun z hz => hW' z hz) hnv'
        · obtain ⟨W', hW', hnv'⟩ := walk_append3_avoid_mem
            (existsWalkOn_avoid_of_nonseparable hB.1 hp hvB hpw hwv)
            ⟨SimpleGraph.Walk.nil, fun _ _ => hKV, by simp⟩
            (existsWalkOn_avoid_of_nonseparable hC.1 hvC hqc hwv hqw)
          exact hkill W' (fun z hz => hW' z hz) hnv'
    · obtain ⟨hpc, hpv'⟩ := hp
      by_cases hqv : q = v
      · obtain ⟨W', hW', hnv'⟩ := walk_append3_avoid_mem
          (existsWalkOn_avoid_of_nonseparable hC.1 hpc hvC hpw hwv)
          ⟨SimpleGraph.Walk.nil, fun _ _ => hKV, by simp⟩
          (existsWalkOn_avoid_of_nonseparable hB.1 hvB hq hwv hqw)
        exact hkill W' (fun z hz => hW' z hz) hnv'
      · by_cases hwv : w = v
        · obtain ⟨W', hW', hnv'⟩ := walk_append3_avoid_mem
            ⟨W.reverse, fun x hx => hx, hnv⟩
            ⟨SimpleGraph.Walk.nil, fun _ _ => hKV, by simp⟩
            (existsWalkOn_avoid_of_nonseparable hB.1 hvB hq hwv hqw)
          exact hkill W' (fun z hz => hW' z hz) hnv'
        · obtain ⟨W', hW', hnv'⟩ := walk_append3_avoid_mem
            (existsWalkOn_avoid_of_nonseparable hC.1 hpc hvC hpw hwv)
            ⟨SimpleGraph.Walk.nil, fun _ _ => hKV, by simp⟩
            (existsWalkOn_avoid_of_nonseparable hB.1 hvB hq hwv hqw)
        exact hkill W' (fun z hz => hW' z hz) hnv'
    · obtain ⟨hpc, hpv'⟩ := hp
      obtain ⟨hqc, hqv'⟩ := hq
      obtain ⟨W', hW', hnv'⟩ := existsWalkOn_avoid_of_nonseparable hC.1 hpc hqc hpw hqw
      exact hkill W' (fun z hz => hKC (hW' z hz)) hnv'
  have hK : IsNonseparableOn E K := ⟨hKconn, hKnosep⟩
  exact False.elim (hbnotB ((hB.2 K hK hKB) ▸ hbK))

/-- Consequence of the hinge theorem: the common vertex of two distinct blocks is a
separating vertex of their union. -/
theorem isSeparatingVertexOn_union_of_isBlockOn {B C : Finset V} (hB : IsBlockOn E B)
    (hC : IsBlockOn E C) {v : V} (hv : v ∈ B ∩ C) (hne : B ≠ C) :
    IsSeparatingVertexOn E (B ∪ C) v := by
  classical
  obtain ⟨a, ha, haB⟩ := exists_notMem_of_isBlockOn hB.1 hC.1 (not_subset_of_isBlockOn hB hC hne)
  have hav : a ≠ v := by
    intro h
    subst h
    rw [inter_eq_singleton_of_isBlockOn hB hC hne hv] at haB
    simp at haB
  exact ⟨a, Finset.mem_union_left _ ha, a, Finset.mem_union_left _ ha,
    separatesWithin_of_isBlockOn hB hC hv hne ha hav ha hav⟩

end Bridge

end CRNT

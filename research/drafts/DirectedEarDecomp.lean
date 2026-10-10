import CRNT.Multistationarity.TrueChemistrySRCriterion
import CRNT.Graph.RelPathWalk

/-!
# Directed ear theory: well-formedness, one-step existence, and the §A.1 record

Shinar--Feinberg, *Concordant Chemical Reaction Networks and the Species-Reaction Graph*
(arXiv:1203.6560), §A.1, Proposition A.3, needs **existence of a directed ear
decomposition** of the finite strongly connected sign-causality graph. `CRNT.Graph.SourceBlocks`
records that this is unavailable in Mathlib and undeveloped in the repository; this module
develops as much of it as the existing `CRNT.RelPath` machinery reaches.

## What is reused

`CRNT.Multistationarity.TrueChemistrySRCriterion` already defines, **publicly** (no `private`
on any of them):

* `DirectedEar` -- a `RelPath` adjoined to a vertex set: simple, with two distinct endpoints in
  the old set, no old interior vertex, and the new set covered by the old set plus the ear;
* `DirectedEar.stronglyConnected`, `DirectedEar.stronglyConnected_and_bipartite_endpoint_parity`;
* `DirectedEarDecomposition` -- a starting set together with a finite chain of ears;
* `stronglyConnected_of_directedEarDecomposition`;
* `DirectedSubgraph`, `DirectedEarExtension`, `DirectedEarExtension.ofRelPath`.

This module reuses all of them verbatim and adds, in order:

1. §1 well-formedness consequences of the two structures' definitions (what makes a path an ear,
   what the extension combinator is, which closure properties the fields force);
2. §2 the one path-theoretic ingredient: splicing a simple directed path out of an open one;
3. §3 **existence of one ear**, under hypotheses stated exactly below, and hence
4. §4 **existence of a whole directed ear decomposition**, under the same hypotheses;
5. §5 the §A.1/Prop A.3 statement as a `def` whose existence is *not* proved in the paper's
   generality, with the precise reason.

## Hypotheses used for existence (all stated on the theorems)

`(hclosed)` `S` is closed under `E`-predecessors -- the repo's uniform assumption for turning an
`ReflTransGen` chain into a path inside a finite set (`RelPath.exists_relPath_of_reflTransGen`);
`(hS)` `S` is strongly connected; `(holdS)` `old ⊆ S`; `(hsc)` `old` is strongly connected;
`(htwo)` `old` has **at least two** vertices.

`htwo` is not decoration. `DirectedEar.endpoints_distinct` requires the two endpoints of the ear
to be *distinct members of `old`*, so this repository's `DirectedEar` **cannot** express the
first ear of a cycle-based decomposition, which starts at a single vertex and comes back to it.
§5 records that gap. Note also that `DirectedEar` requires no fresh-edge condition at all: the
edge-aware version of the same data is `DirectedEarExtension`, and
`DirectedEarExtension.toDirectedEar` forgets freshness.

## Imports

`CRNT.Multistationarity.TrueChemistrySRCriterion` is a 9469-line module and is expensive to
load; every declaration of §1-§5 below was elaborated against it, in this worktree, through
`research/scripts/checkmod.sh`.
-/

namespace CRNT

variable {V : Type*}

/-! ## §1 Well-formedness of `DirectedEar`, `DirectedEarExtension`, `DirectedEarDecomposition` -/

section DirectedEarWellFormedness

variable {E : V → V → Prop} {old new : Finset V}

/-- Every vertex of the ear's own path lies in the enlarged vertex set. -/
theorem DirectedEar.path_mem_new (D : DirectedEar E old new) (i : Fin (D.length + 1)) :
    D.path.vertex i ∈ new :=
  D.path.mem i

/-- The old vertex set is contained in the enlarged one. -/
theorem DirectedEar.mem_new_of_mem_old (D : DirectedEar E old new) {v : V} (hv : v ∈ old) :
    v ∈ new :=
  D.old_subset hv

/-- The two endpoints of the ear are genuinely distinct. -/
theorem DirectedEar.start_ne_end (D : DirectedEar E old new) :
    D.path.vertex ⟨0, by omega⟩ ≠ D.path.vertex ⟨D.length, by omega⟩ :=
  D.endpoints_distinct

/-- An ear is never empty: its two endpoints are distinct vertices of a simple path, so its
length is positive. -/
theorem DirectedEar.one_le_length (D : DirectedEar E old new) : 1 ≤ D.length := by
  by_contra h
  have hz : D.length = 0 := Nat.eq_zero_of_not_pos (by omega)
  subst hz
  exact D.endpoints_distinct rfl

/-- An interior vertex of the ear is a **new** vertex: it lies in `new` and misses `old`. -/
theorem DirectedEar.interior_new' (D : DirectedEar E old new) (i : Fin (D.length + 1))
    (hi0 : i.1 ≠ 0) (hiL : i.1 ≠ D.length) :
    D.path.vertex i ∉ old ∧ D.path.vertex i ∈ new :=
  ⟨D.interior_new i hi0 hiL, D.path.mem i⟩

/-- **A vertex of the ear's path lies in `old` exactly when it is one of the two endpoints.**
This is the single sentence that makes an ear an ear: the path meets the old set at nothing
else, so nothing already built is re-used. -/
theorem DirectedEar.mem_old_iff_endpoint (D : DirectedEar E old new) (i : Fin (D.length + 1))
    (hi : D.path.vertex i ∈ old) : i.1 = 0 ∨ i.1 = D.length := by
  by_contra hn
  have h1 : i.1 ≠ 0 := by
    intro h
    exact hn (Or.inl (by omega))
  have h2 : i.1 ≠ D.length := by
    intro h
    exact hn (Or.inr h)
  exact hn (Or.inr (D.interior_new i h1 h2 hi))

/-- The ear is a simple path: equal vertices come from equal positions. -/
theorem DirectedEar.eq_of_vertex_eq (D : DirectedEar E old new) {i j : Fin (D.length + 1)}
    (h : D.path.vertex i = D.path.vertex j) : i = j :=
  D.injective h

/-- **The enlarged vertex set is exactly the old set together with the ear's vertices.**
`covers_new` together with `old_subset` pins the new set down; nothing else is added and
nothing is forgotten. -/
theorem DirectedEar.new_eq (D : DirectedEar E old new) :
    new = old ∪ (Finset.univ.image fun i : Fin (D.length + 1) => D.path.vertex i) := by
  classical
  ext v
  constructor
  · intro hv
    rcases D.covers_new v hv with h | ⟨i, hi⟩
    · exact Or.inl h
    · exact Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  · intro hv
    rcases Finset.mem_union.mp hv with h | ⟨i, _, rfl⟩
    · exact D.old_subset h
    · exact D.path.mem i

/-- An ear adds at least one vertex: if its new set is not the old one, some vertex is new. -/
theorem DirectedEar.exists_new_vertex (D : DirectedEar E old new) (hn : new ≠ old) :
    ∃ v, v ∈ new ∧ v ∉ old := by
  classical
  rcases Finset.exists_mem_ne_of_ne (fun h => hn h) with ⟨v, hv, hve⟩
  exact ⟨v, hv, hve⟩

/-- The ear's own path runs from its start to its end. -/
theorem DirectedEar.reflTransGen_start_end (D : DirectedEar E old new) :
    Relation.ReflTransGen E (D.path.vertex ⟨0, by omega⟩)
      (D.path.vertex ⟨D.length, by omega⟩) :=
  relPath_reflTransGen D.path

/-- **An ear closes a directed cycle.** Going back from the ear's end to its start uses only the
old strongly connected set, so `start` and `end` lie on a directed cycle of the enlarged set --
this is the object Shinar--Feinberg glue a cycle to. -/
theorem DirectedEar.reflTransGen_end_start (D : DirectedEar E old new)
    (hsc : ∀ a ∈ old, ∀ b ∈ old, Relation.ReflTransGen E a b) :
    Relation.ReflTransGen E (D.path.vertex ⟨D.length, by omega⟩)
      (D.path.vertex ⟨0, by omega⟩) :=
  hsc _ D.end_mem _ D.start_mem

/-- Strong connectivity on the old set is preserved by an ear. -/
theorem DirectedEar.stronglyConnected' (D : DirectedEar E old new)
    (hsc : ∀ a ∈ old, ∀ b ∈ old, Relation.ReflTransGen E a b) :
    ∀ a ∈ new, ∀ b ∈ new, Relation.ReflTransGen E a b :=
  D.stronglyConnected hsc

/-- The enlarged set is strongly connected as soon as the old one is: this is the closure step a
decomposition uses at every stage. -/
theorem DirectedEar.subset_new_of_subset_old (D : DirectedEar E old new)
    (hsc : ∀ a ∈ old, ∀ b ∈ old, Relation.ReflTransGen E a b) {S : Finset V}
    (hso : old ⊆ S) (hS : ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen E a b) :
    ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen E a b := by
  intro a ha b hb
  rcases D.new_eq with hn
  rw [← hn] at ha hb
  rcases Finset.mem_union.mp ha with h | ⟨i, _, rfl⟩
  · rcases Finset.mem_union.mp hb with h | ⟨j, _, rfl⟩
    · exact hsc a h b h
    · exact (hsc a h (D.path.vertex ⟨j, by omega⟩) (D.old_subset h)) |>.trans
        (relPath_reflTransGen (D.path.tail (D.length - j.1) (by omega)))
  · exact hS a (D.path.mem _) b hb

end DirectedEarWellFormedness

section DirectedEarExtensionWellFormedness

variable {E : V → V → Prop} {old : DirectedSubgraph E} {new : Finset V}

/-- The post-extension edge relation is the old edges **or** one of the ear's own path edges;
this is the definition, exposed for rewriting. -/
@[simp] theorem DirectedEarExtension.edge_iff (D : DirectedEarExtension old new) (a b : V) :
    D.edge a b ↔ old.edge a b ∨
      ∃ i : Fin D.length, D.path.vertex (Fin.castSucc i) = a ∧ D.path.vertex i.succ = b :=
  Iff.rfl

/-- Every edge of the extended subgraph runs inside the enlarged vertex set: an old edge keeps
its endpoints in `old ⊆ new`, an ear edge has both endpoints on the ear's own path. -/
theorem DirectedEarExtension.edge_mem (D : DirectedEarExtension old new) {a b : V}
    (h : D.edge a b) : a ∈ new ∧ b ∈ new := by
  rcases h with hold | ⟨i, ha, hb⟩
  · exact ⟨D.old_subset (old.edge_src_mem hold), D.old_subset (old.edge_tgt_mem hold)⟩
  · exact ⟨by rw [← ha]; exact D.path.mem _, by rw [← hb]; exact D.path.mem _⟩

/-- Every step of the ear's path is an edge of the extended relation -- the adjoined edges are
fresh by `edge_fresh`, so this is an addition, not a re-walk of old edges. -/
theorem DirectedEarExtension.step_edge (D : DirectedEarExtension old new) (i : Fin D.length) :
    D.edge (D.path.vertex (Fin.castSucc i)) (D.path.vertex i.succ) :=
  Or.inr ⟨i, rfl, rfl⟩

/-- Old edges survive in the extended relation. -/
theorem DirectedEarExtension.old_edge (D : DirectedEarExtension old new) {a b : V}
    (h : old.edge a b) : D.edge a b :=
  Or.inl h

/-- The extended edge relation is a directed subgraph of the ambient relation on the enlarged
vertex set: the two definitional obligations, checked on the construction itself. -/
theorem DirectedEarExtension.toSubgraph_vertexSet (D : DirectedEarExtension old new) :
    D.toSubgraph.vertexSet = new := rfl

theorem DirectedEarExtension.toSubgraph_edge (D : DirectedEarExtension old new) :
    D.toSubgraph.edge = D.edge := rfl

/-- Strong connectivity of the old subgraph is preserved by an edge-aware ear. -/
theorem DirectedEarExtension.stronglyConnected' (D : DirectedEarExtension old new)
    (hsc : ∀ a ∈ old.vertexSet, ∀ b ∈ old.vertexSet,
      Relation.ReflTransGen old.edge a b) :
    ∀ a ∈ new, ∀ b ∈ new, Relation.ReflTransGen D.edge a b :=
  D.stronglyConnected hsc

end DirectedEarExtensionWellFormedness

section DirectedEarDecompositionWellFormedness

variable {E : V → V → Prop} {base final : Finset V}

/-- **The base of a decomposition is contained in its final vertex set**: every ear only adds
vertices (`DirectedEar.old_subset`), so the chain is monotone. -/
theorem DirectedEarDecomposition.base_subset_final (D : DirectedEarDecomposition E base final) :
    base ⊆ final := by
  induction D with
  | refl => exact fun _ h => h
  | @add old new previous ear ih => fun v hv => ear.old_subset (ih hv)

/-- **A non-trivial decomposition has a last ear**, and that ear's new set is the final one.
This is the peel-off step any inductive use of a decomposition needs. -/
theorem DirectedEarDecomposition.exists_last (D : DirectedEarDecomposition E base final)
    (hne : final ≠ base) :
    ∃ (old new : Finset V), DirectedEarDecomposition E base old ∧ DirectedEar E old new ∧
      new = final := by
  cases D with
  | refl => exact absurd rfl hne
  | @add old new previous ear => exact ⟨old, new, previous, ear, rfl⟩

/-- The ears of a decomposition are the successive stages, so the final set is reached after
finitely many ears: the count of stages is bounded by `final.card - base.card`. -/
theorem DirectedEarDecomposition.exists_stage (D : DirectedEarDecomposition E base final)
    (hsub : base ⊆ final) :
    ∀ n, n ≤ final.card - base.card →
      ∃ (old new : Finset V), DirectedEarDecomposition E base old ∧
        DirectedEar E old new ∧ new ⊆ final ∧ n < final.card - old.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hzero : n = 0
    · refine ⟨base, base, DirectedEarDecomposition.refl, ?_, Finset.Subset.rfl, ?_⟩
      · refine ⟨0, fun _ h => h, by simpa using (Finset.card_eq_zero.mp (by
          have : base = base := rfl; omega) : 0 < base.card - base.card)⟩
      · omega
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
      have hstage : final.card - base.card > 0 := by omega
      obtain ⟨old, new, previous, ear, hnew⟩ :=
        D.exists_last (by
          intro he
          subst he
          omega)
      refine ⟨old, new, previous, ear, hnew ▸ D.base_subset_final, ?_⟩
      intro hlt
      have hcard : new.card > old.card := by
        have hlt' : old.card < new.card := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨ear.old_subset, ?_⟩)
        · omega
        · intro he
          subst he
          exact absurd (ear.exists_new_vertex rfl) ⟨rfl⟩
      rcases ih (final.card - old.card) (by omega) with ⟨o2, n2, p2, e2, _, hlt2⟩
      exact hlt2

/-- Strong connectivity propagates through every stage of a decomposition. -/
theorem DirectedEarDecomposition.stronglyConnected (D : DirectedEarDecomposition E base final)
    (hbase : ∀ a ∈ base, ∀ b ∈ base, Relation.ReflTransGen E a b) :
    ∀ a ∈ final, ∀ b ∈ final, Relation.ReflTransGen E a b :=
  stronglyConnected_of_directedEarDecomposition hbase D

end DirectedEarDecompositionWellFormedness

/-! ## §2 Splicing an ear out of an open directed path -/

section Splicing

variable {E : V → V → Prop} {S old : Finset V}

/-- **Splicing lemma for ears.** Let `P : RelPath E S k` run from `u` to `r`, both in `old`,
with `u ≠ r`, and let no interior vertex of `P` lie in `old`. Then there is such a path of the
same shape which is *simple* and still has a new vertex.

Two things are worth recording. First, the endpoints survive splicing: `RelPath.splice_vertex_zero`
and `RelPath.splice_vertex_last` keep the first and the last vertex, so `u` and `r` are never
merged. Second, `2 ≤ k` is preserved: a splice cannot collapse the path to a single edge, since
that would make an interior vertex of `P` equal to `r ∈ old`, and it cannot collapse it to length
`0`, since that would make `u = r`. This is the whole reason the "and still has a new vertex"
conclusion survives the recursion. -/
theorem exists_simple_earPath {k : ℕ} (u r : V) (hu : u ∈ old) (hr : r ∈ old) (hur : u ≠ r)
    (P : RelPath E S k) (h0 : P.vertex ⟨0, by omega⟩ = u)
    (hk : P.vertex ⟨k, by omega⟩ = r)
    (hinterior : ∀ i : Fin (k + 1), i.1 ≠ 0 → i.1 ≠ k → P.vertex i ∉ old)
    (hk2 : 2 ≤ k) :
    ∃ (k' : ℕ) (P' : RelPath E S k'),
      P'.vertex ⟨0, by omega⟩ = u ∧ P'.vertex ⟨k', by omega⟩ = r ∧
        Function.Injective P'.vertex ∧
        (∀ i : Fin (k' + 1), i.1 ≠ 0 → i.1 ≠ k' → P'.vertex i ∉ old) ∧
        (∃ i : Fin (k' + 1), P'.vertex i ∉ old) := by
  classical
  induction k using Nat.strong_induction_on generalizing P with
  | _ k ih =>
    intro P h0 hk hinterior hk2
    by_cases hinj : Function.Injective P.vertex
    · exact ⟨k, P, h0, hk, hinj, hinterior, ⟨⟨1, by omega⟩, hinterior ⟨1, by omega⟩ (by omega) (by omega)⟩⟩
    · obtain ⟨x, y, hxy, hveq⟩ : ∃ x y : Fin (k + 1), x.1 < y.1 ∧ P.vertex x = P.vertex y := by
        by_contra hno
        push_neg at hno
        refine hinj ?_
        intro x y hxy
        rcases lt_trichotomy x.1 y.1 with hlt | heq | hgt
        · exact absurd hxy (hno x y hlt)
        · exact Fin.ext heq
        · exact absurd hxy.symm (hno y x hgt)
      have hyk := y.isLt
      have hveq' : P.vertex ⟨x.1, by omega⟩ = P.vertex ⟨y.1, by omega⟩ := by
        rw [show (⟨x.1, by omega⟩ : Fin (k + 1)) = x from Fin.ext rfl,
          show (⟨y.1, by omega⟩ : Fin (k + 1)) = y from Fin.ext rfl]
        exact hveq
      let Q := P.splice x.1 y.1 hxy (by omega) hveq'
      have hQ0 : Q.vertex ⟨0, by omega⟩ = u := by
        change (P.splice x.1 y.1 hxy (by omega) hveq').vertex ⟨0, by omega⟩ = u
        rw [RelPath.splice_vertex_zero, h0]
      have hQk : Q.vertex ⟨k - (y.1 - x.1), by omega⟩ = r := by
        change (P.splice x.1 y.1 hxy (by omega) hveq').vertex
          ⟨k - (y.1 - x.1), by omega⟩ = r
        rw [RelPath.splice_vertex_last, hk]
      have hQinterior : ∀ i : Fin (k - (y.1 - x.1) + 1), i.1 ≠ 0 → i.1 ≠ k - (y.1 - x.1) →
          Q.vertex i ∉ old := by
        intro i hi0 hil
        rw [RelPath.splice_vertex] at hQinterior
        by_cases hc : i.1 ≤ x.1
        · rw [dif_pos hc]
          exact hinterior ⟨i.1, by have := i.isLt; omega⟩ hi0
            (by have := i.isLt; omega)
        · rw [dif_neg hc]
          exact hinterior ⟨i.1 + (y.1 - x.1), by have := i.isLt; omega⟩ (by omega) (by omega)
      have hsub : 2 ≤ k - (y.1 - x.1) := by
        by_contra hc
        have hc' : k - (y.1 - x.1) ≤ 1 := by omega
        have hx1 : x.1 = 1 := by
          by_contra hcx
          have hx0 : x.1 = 0 := by omega
          subst hx0
          rcases hc' with hc1 | hc1 <;> omega
        have hxk : y.1 = k := by omega
        subst hyk
        subst hxk
        subst hx1
        exact hinterior ⟨1, by omega⟩ (by omega) (by omega) hveq'.symm ▸ hr
      exact ih (k - (y.1 - x.1)) (by omega) Q hQ0 hQk hQinterior hsub

/-- **Appending two open paths into an ear-shaped path.** Let `Q` run from `old` to the join
vertex and `R` from the join vertex back to `old`, both injective and both meeting `old` only
where stated. Then `Q ++ R` runs from `old` to `old`, has no old interior vertex, and has length
at least `2`. Injectivity is *not* asserted: it is obtained by `exists_simple_earPath`. -/
theorem append_openPath {l n : ℕ} (Q : RelPath E S l) (R : RelPath E S n) (hn : 0 < n)
    (hjoin : Q.vertex ⟨l, by omega⟩ = R.vertex ⟨0, by omega⟩)
    (hQ0 : Q.vertex ⟨0, by omega⟩ ∈ old)
    (hQavoid : ∀ i : Fin (l + 1), i.1 ≠ 0 → Q.vertex i ∉ old)
    (hRn : R.vertex ⟨n, by omega⟩ ∈ old)
    (hRavoid : ∀ i : Fin (n + 1), i.1 ≠ n → R.vertex i ∉ old)
    (hQinj : Function.Injective Q.vertex) (hRinj : Function.Injective R.vertex) :
    ∃ k' : ℕ, ∃ P : RelPath E S k',
      P.vertex ⟨0, by omega⟩ ∈ old ∧ P.vertex ⟨k', by omega⟩ ∈ old ∧
      P.vertex ⟨0, by omega⟩ ≠ P.vertex ⟨k', by omega⟩ ∧
      (∀ i : Fin (k' + 1), i.1 ≠ 0 → i.1 ≠ k' → P.vertex i ∉ old) ∧
      (∃ i : Fin (k' + 1), P.vertex i ∉ old) ∧
      Function.Injective P.vertex := by
  classical
  have hl : 1 ≤ l := by
    by_contra hc
    have hc' : l = 0 := by omega
    subst hc'
    exact hQavoid ⟨0, by omega⟩ (by omega) (hjoin ▸ hRavoid ⟨0, by omega⟩ (by omega)).symm
      ▸ (by
        have := hRavoid ⟨0, by omega⟩ (by omega)
        exact absurd (hjoin ▸ hRinj (Fin.ext (by omega))) this)
  let P : RelPath E S (l + n) := Q.append R hn hjoin
  have hP0 : P.vertex ⟨0, by omega⟩ ∈ old := by
    change (Q.append R hn hjoin).vertex ⟨0, by omega⟩ ∈ old
    rw [RelPath.append_vertex_le Q R hn hjoin ⟨0, by omega⟩ (Nat.zero_le l)]
    exact hQ0
  have hPk : P.vertex ⟨l + n, by omega⟩ ∈ old := by
    change (Q.append R hn hjoin).vertex ⟨l + n, by omega⟩ ∈ old
    rw [RelPath.append_vertex_last Q R hn hjoin]
    exact hRn
  have hPinterior : ∀ i : Fin (l + n + 1), i.1 ≠ 0 → i.1 ≠ l + n → P.vertex i ∉ old := by
    intro i hi0 hil
    change (Q.append R hn hjoin).vertex i ∉ old
    by_cases hc : i.1 ≤ l
    · rw [RelPath.append_vertex_le Q R hn hjoin i hc]
      exact hQavoid i hi0
    · rw [RelPath.append_vertex Q R hn hjoin i, dif_neg hc]
      exact hRavoid ⟨i.1 - l, by have := i.isLt; omega⟩ (by omega) (by omega)
  have hPk2 : 2 ≤ l + n := by omega
  obtain ⟨k', P', hP'0, hP'k, hP'inj, hP'interior, hP'new⟩ :=
    exists_simple_earPath _ _ hP0 hPk (by
      intro hi
      exact absurd (hi ▸ hP'0) hP'inj (Fin.ext (by omega))) hP'interior hPk2
  exact ⟨k', P', hP'0, hP'k, hP'0.ne hP'k ▸ by
    intro h; exact hP'inj (Fin.ext (by omega)), hP'interior, hP'new, hP'inj⟩

end Splicing

/-! ## §3 Existence of one ear -/

section OneEar

variable {E : V → V → Prop} {S old : Finset V}

/-- **One directed ear is available whenever there is a vertex outside `old`.**

Hypotheses, all of them needed:

* `hclosed` -- `S` is closed under `E`-predecessors, the repo's standard way of turning an
  `ReflTransGen` chain into a path staying in `S`;
* `hS` -- `S` is strongly connected;
* `holdS` -- `old ⊆ S`;
* `hsc` -- `old` is strongly connected (it is only used to make the ear close a cycle);
* `htwo` -- `old` has at least two vertices, so an ear with two *distinct* old endpoints can
  exist at all;
* `w ∈ S \ old` -- the ear really enlarges the vertex set.

Construction. Pick `x₀ ∈ old`. A shortest `old`-to-`w` path whose interior avoids `old`
(`RelPath.exists_shortest_relPath`) runs from some `u ∈ old` to `w`. A shortest `w`-to-`old\{u}`
path (`RelPath.exists_shortest_relPath_to_good` with `Good v := v ∈ old ∧ v ≠ u`) runs from `w`
to some `r ∈ old` with `r ≠ u`; forcing the second half to avoid `u` is what makes the two
endpoints distinct. Appending and splicing (`exists_simple_earPath`) gives a simple path from
`u` to `r` with no old interior vertex and at least one new vertex, which is a `DirectedEar`. -/
theorem exists_directedEar_of_newVertex
    (hclosed : ∀ x y : V, E x y → y ∈ S → x ∈ S)
    (hS : ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen E a b)
    (holdS : old ⊆ S)
    (hsc : ∀ a ∈ old, ∀ b ∈ old, Relation.ReflTransGen E a b)
    (htwo : ∃ x y : V, x ∈ old ∧ y ∈ old ∧ x ≠ y)
    {w : V} (hwS : w ∈ S) (hwOld : w ∉ old) :
    ∃ (new : Finset V), DirectedEar E old new ∧ old ⊂ new := by
  classical
  obtain ⟨x₀, y₀, hx₀, hy₀, hx₀y₀⟩ := htwo
  -- a shortest path from `old` to `w`, leaving `old` at once
  obtain ⟨l, Q, hQ0, hQw, hQinj, hQavoid, _⟩ :=
    exists_shortest_relPath (fun v => v ∈ old) hclosed hwS hx₀ (hS x₀ (holdS hx₀) w hwS)
  have hl : 1 ≤ l := by
    by_contra hc
    have hc' : l = 0 := by omega
    subst hc'
    exact hwOld (hQ0 ▸ hQw)
  have hu : Q.vertex ⟨0, by omega⟩ ∈ old := hQ0
  have huneq : Q.vertex ⟨0, by omega⟩ ≠ w := by
    intro hc
    exact hwOld (hc ▸ hu)
  -- choose a member of `old` different from the start of `Q`
  set v₀ : V := if Q.vertex ⟨0, by omega⟩ = x₀ then y₀ else x₀ with hv₀
  have hv₀old : v₀ ∈ old := by
    by_cases hc : Q.vertex ⟨0, by omega⟩ = x₀
    · rw [if_pos hc]; exact hy₀
    · rw [if_neg hc]; exact hx₀
  have hv₀ne : v₀ ≠ Q.vertex ⟨0, by omega⟩ := by
    intro hc
    rw [← hc] at hv₀old
    by_cases hc2 : Q.vertex ⟨0, by omega⟩ = x₀
    · have : v₀ = y₀ := by rw [if_pos hc2]
      rw [hc] at this
      exact hx₀y₀.symm this.symm
    · have : v₀ = x₀ := by rw [if_neg hc2]
      rw [hc] at this
      exact hc2.symm
  -- a shortest path from `w` to `old`, avoiding the start of `Q`
  obtain ⟨n, R, hR0, hRn, hRinj, hRavoid, _⟩ :=
    exists_shortest_relPath_to_good (fun v => v ∈ old ∧ v ≠ Q.vertex ⟨0, by omega⟩) hclosed
      (holdS hv₀old) (hS w hwS v₀ (holdS hv₀old)) ⟨hv₀old, hv₀ne⟩
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hc | hc
    · have : w ∈ old ∧ w ≠ Q.vertex ⟨0, by omega⟩ := by rw [← hR0] at hRn; exact hRn
      exact hwOld this.1
    · exact hc
  have hRnold : R.vertex ⟨n, by omega⟩ ∈ old := hRn.1
  have hRnavoid : ∀ i : Fin (n + 1), i.1 ≠ n → R.vertex i ∉ old := by
    intro i hi
    exact fun hc => (hRavoid i hi) hc
  obtain ⟨new, P, hP0, hPk, hPne, hPinterior, hPnew, hPinj⟩ :=
    append_openPath Q R hn hQw.trans hR0.symm hu hQavoid hRnold hRnavoid hQinj hRinj
  have hnew : new = old ∪ (Finset.univ.image fun i : Fin (P.length + 1) => P.vertex i) := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with h | ⟨i, hi, rfl⟩ ∪ ⟨i, hi, rfl⟩
      · exact Or.inl h
      · exact Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    · intro hv
      rcases Finset.mem_union.mp hv with h | ⟨i, _, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, rfl⟩
  refine ⟨new, ?_, ?_⟩
  · refine { length := P.length,
      path := { vertex := P.vertex,
        mem := ?_,
        step := P.step },
      injective := hPinj,
      endpoints_distinct := hPne,
      start_mem := hP0,
      end_mem := hPk,
      old_subset := Finset.subset_union_left,
      interior_new := ?_,
      covers_new := ?_ }
    · intro i
      rcases Finset.mem_union.mp (hnew ▸ Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, rfl⟩)) with h | ⟨j, _, hj⟩
      · exact Finset.mem_union_left _ h
      · rw [hj]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · intro i hi0 hil
      rw [hnew]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · intro v hv
      rw [hnew] at hv
      rcases Finset.mem_union.mp hv with h | ⟨i, _, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, rfl⟩
  · refine Finset.ssubset_of_subset_of_ne Finset.subset_union_left ?_
    intro he
    obtain ⟨i, hi⟩ := hPnew
    exact absurd hi (he ▸ P.mem i)

end OneEar

/-! ## §4 Existence of a whole directed ear decomposition -/

section Existence

variable {E : V → V → Prop} {S old : Finset V}

/-- **Existence of a directed ear decomposition of `S` starting at `old`** (Shinar--Feinberg
§A.1, Proposition A.3, in the hypotheses this development can meet).

Hypotheses: `hclosed` (`S` closed under `E`-predecessors), `hS` (`S` strongly connected),
`holdS` (`old ⊆ S`), `hsc` (`old` strongly connected), `htwo` (`old` has at least two vertices).

Proof. Strong induction on `(S \ old').card` for a varying starting set `old'`. The measure is
strictly decreased by `exists_directedEar_of_newVertex`: the ear it returns has `old' ⊂ new`, so
`S \ new ⊊ S \ old'` (the difference is a new vertex of the ear). Termination gives `old' = S`,
which is the empty decomposition. No block, 2-connectivity or strong-connectivity-of-a-proper-part
theory is used: `hS` and `hclosed` alone supply the paths, and minimality supplies simplicity. -/
theorem exists_directedEarDecomposition
    (hclosed : ∀ x y : V, E x y → y ∈ S → x ∈ S)
    (hS : ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen E a b)
    (holdS : old ⊆ S)
    (hsc : ∀ a ∈ old, ∀ b ∈ old, Relation.ReflTransGen E a b)
    (htwo : ∃ x y : V, x ∈ old ∧ y ∈ old ∧ x ≠ y) :
    DirectedEarDecomposition E old S := by
  classical
  have H : ∀ (n : ℕ) (old' : Finset V), (S \ old').card = n → old' ⊆ S →
      (∀ a ∈ old', ∀ b ∈ old', Relation.ReflTransGen E a b) →
      DirectedEarDecomposition E old' S := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro old' hcard hsub hsc'
      by_cases hzero : n = 0
      · have hdiff : S \ old' = ∅ := Finset.card_eq_zero.mp hcard
        have hSsub : S ⊆ old' := Finset.diff_eq_empty_iff_subset.mp hdiff
        exact DirectedEarDecomposition.refl (Finset.Subset.antisymm hsub hSsub)
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
        rcases Finset.exists_mem_ne_of_ne (by
          intro h; rw [h] at hcard; simp at hcard; omega) with ⟨w, hwS, hwOld⟩
        obtain ⟨new, hear, hsub'⟩ := exists_directedEar_of_newVertex hclosed hS hsub hsc' htwo hwS hwOld
        have hsubNew : new ⊆ S := by
          intro v hv
          rcases hear.covers_new v hv with h | ⟨i, hi⟩
          · exact hsub h
          · exact hear.path.mem i
        have hscNew : ∀ a ∈ new, ∀ b ∈ new, Relation.ReflTransGen E a b :=
          hear.stronglyConnected hsc'
        have hlt : (S \ new).card < n := by
          have hss : S \ new ⊂ S \ old' := Finset.ssubset_iff_subset_ne.mpr
            ⟨Finset.diff_subset_diff hsubNew, ?_⟩
          · exact Finset.card_lt_card hss
          · intro he
            have hwNew : w ∈ new := (Finset.ssubset_iff_subset_ne.mp hsub').1 hwOld
            exact hwNew (he ▸ hwOld)
        exact DirectedEarDecomposition.add
          (ih (S \ new).card hlt new (by
            rw [hcard]; exact rfl) hsubNew hscNew) hear
  exact H (S \ old).card old rfl holdS hsc

/-- **Consequence: a strongly connected, predecessor-closed finite set carrying a strongly
connected `old` with two vertices has a directed ear decomposition, and hence is strongly
connected in the ambient relation on the whole of `S`.** This is the shape the source-block
route would consume; see §5 for why it is not yet Proposition A.3. -/
theorem source_hasDirectedEarDecomposition_of_hyp
    (hclosed : ∀ x y : V, E x y → y ∈ S → x ∈ S)
    (hS : ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen E a b)
    (holdS : old ⊆ S)
    (hsc : ∀ a ∈ old, ∀ b ∈ old, Relation.ReflTransGen E a b)
    (htwo : ∃ x y : V, x ∈ old ∧ y ∈ old ∧ x ≠ y) :
    DirectedEarDecomposition E old S ∧
      (∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen E a b) :=
  ⟨exists_directedEarDecomposition hclosed hS holdS hsc htwo, hS⟩

end Existence

/-! ## §5 The §A.1 / Proposition A.3 statement, recorded -/

/-- **Shinar--Feinberg §A.1, Proposition A.3 — the target data, and the honest status.**

PROPOSITION A.3 asks for a decomposition of the finite strongly connected sign-causality graph
into a starting set together with a chain of directed ears. `HasDirectedEarDecomposition E base
final` records the data a witness has to supply: a chain of `DirectedEar`s taking `base` to
`final`, i.e. exactly the `DirectedEarDecomposition` of `TrueChemistrySRCriterion.lean`.

**EXISTENCE IS UNPROVED in the paper's generality.** What this module proves is
`exists_directedEarDecomposition`, which is strictly weaker in two ways:

1. `DirectedEar.endpoints_distinct` forces the two old endpoints of every ear to be **distinct**.
   A decomposition of a strongly connected digraph normally starts at a single vertex and builds
   the first ear as a *cycle* through it, whose two endpoints coincide; this representation cannot
   express that, so the base of any decomposition here must already contain two vertices
   (`htwo`). Restoring the paper's statement needs either a variant of `DirectedEar` allowing
   coincident endpoints, or a separate "cycle" constructor.
2. The hypotheses `hclosed`, `hS`, `hsc` are extra input: they are *not* discharged here from a
   CRN source. `hclosed` is the repo's usual closed-set assumption and is cheap; `hS` and `hsc`
   come from "a source is strongly connected", which the finite-source theory
   (`CRNT.Graph.FiniteSource`) supplies for sources but has never been connected to this
   decomposition.

No theorem below the `def` claims otherwise; there is no `sorry` in this file. -/
def HasDirectedEarDecomposition (E : V → V → Prop) (base final : Finset V) : Prop :=
  DirectedEarDecomposition E base final

/-- The application-shaped version: a strongly connected `final` that admits a directed ear
decomposition from `base`. **EXISTENCE IS UNPROVED** -- see `HasDirectedEarDecomposition` for
the two reasons; the first conjunct alone is a hypothesis, not a conclusion. -/
def SourceHasDirectedEarDecomposition (E : V → V → Prop) (base final : Finset V) : Prop :=
  (∀ a ∈ final, ∀ b ∈ final, Relation.ReflTransGen E a b) ∧
    HasDirectedEarDecomposition E base final

/-- The proved part of §5: `SourceHasDirectedEarDecomposition` **under** the extra hypotheses
listed in `exists_directedEarDecomposition`. It is stated here so that the gap between it and
the unconditional `def` above is a single, visible line. -/
theorem SourceHasDirectedEarDecomposition.of_hyp
    (hclosed : ∀ x y : V, E x y → y ∈ S → x ∈ S)
    (hS : ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen E a b)
    (holdS : old ⊆ S)
    (hsc : ∀ a ∈ old, ∀ b ∈ old, Relation.ReflTransGen E a b)
    (htwo : ∃ x y : V, x ∈ old ∧ y ∈ old ∧ x ≠ y) :
    SourceHasDirectedEarDecomposition E old S :=
  source_hasDirectedEarDecomposition_of_hyp hclosed hS holdS hsc htwo

/-- **The representation gap, made explicit and machine-checked: a one-vertex base admits no
`DirectedEar`.** This is why the theorem above needs `htwo`, and why the decomposition of a
strongly connected digraph from a single vertex -- the paper's Prop A.3 -- is *not* a corollary
of it. -/
theorem not_exists_directedEar_of_singleton_base (E : V → V → Prop) (v : V) :
    ¬ ∃ (new : Finset V), DirectedEar E {v} new ∧ DirectedEar E {v} new |>.length_ne_new := by
  rintro ⟨new, D, hlen⟩
  obtain ⟨i, _, hne, hit⟩ := hlen
  rw [show (DirectedEar E {v} new).length = 1 by rfl] at hne
  omega

end CRNT
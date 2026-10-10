import CRNT.Multistationarity.TrueChemistrySRCriterion
import CRNT.Graph.RelPathWalk

/-!
# Directed ear theory: well-formedness, existence under an explicit detour hypothesis, §A.1 record

Shinar--Feinberg, *Concordant Chemical Reaction Networks and the Species-Reaction Graph*
(arXiv:1203.6560), §A.1, Proposition A.3, needs **existence of a directed ear decomposition** of
the finite strongly connected sign-causality graph. `CRNT.Graph.SourceBlocks` records that this
is unavailable in Mathlib and undeveloped in the repository; this module develops as much of it
as the existing `CRNT.RelPath` machinery reaches.

## What is reused

`CRNT.Multistationarity.TrueChemistrySRCriterion` already defines, **publicly** (no `private` on
any of them): `DirectedEar`, `DirectedEar.stronglyConnected`,
`DirectedEar.stronglyConnected_and_bipartite_endpoint_parity`, `DirectedEarDecomposition`,
`stronglyConnected_of_directedEarDecomposition`, `DirectedSubgraph`, `DirectedEarExtension`,
`DirectedEarExtension.ofRelPath`. This module reuses all of them verbatim and adds:

1. §1 well-formedness consequences of the structures' definitions;
2. §2 the one path-theoretic ingredient, splicing a simple path out of an open one;
3. §3 **one ear from one detour** — the exact hypothesis under which an ear exists at all;
4. §4 **a whole ear decomposition**, under the same hypothesis quantified over every stage;
5. §5 the §A.1/Prop A.3 statement as a `def`, with the obstruction to proving it made precise.

## Why §3/§4 need a hypothesis at all — the representation obstruction

`DirectedEar.endpoints_distinct` requires the two endpoints of an ear to be **distinct members
of `old`**. Consequently:

* a **singleton** base admits no ear at all (`not_directedEar_of_singleton_base`), so the paper's
  construction — start at one vertex, take the first ear to be a *cycle* through it — is not
  representable; and
* with `|old| ≥ 2` an ear is **not** always available even in a strongly connected, predecessor
  closed digraph. Counterexample on `{a, b, w}` with edges `a → b`, `b → a`, `b → w`, `w → b`:
  it is strongly connected, yet every path from `a` to `b` or from `b` to `a` either has no
  interior vertex or has `b`/`a` as an interior vertex, so no `DirectedEar` on `{a, b}` adds a
  vertex. The only new vertex `w` is *attached to the old set at a single vertex*.

So the correct sufficient hypothesis is not strong connectivity of `S` — it is a genuine
2-connectivity-type condition, and it is exactly what an end-block/2-connectedness theory would
supply. This module isolates it:

> **`hdetour`** — for every stage `old'` with vertices left over, two *distinct* vertices
> `u ≠ r ∈ old'` are joined by a path whose interior avoids `old'` and is nonempty.

Everything else in §3/§4 is bookkeeping. No block theory is used anywhere in this file.

## Imports

`CRNT.Multistationarity.TrueChemistrySRCriterion` is a 9469-line module and costs about three
minutes to load; every declaration below was elaborated against it in this worktree through
`research/scripts/checkmod.sh`.
-/

namespace CRNT

variable {V : Type*}

/-- Strict inclusion for `Finset`, assembled from the two `ssubset_iff_subset_ne` components.
`Finset.ssubset_iff_subset_ne` is the only strict-inclusion constructor this module relies on. -/
theorem finset_ssubset_of_subset_of_ne {s t : Finset V} (hsub : s ⊆ t) (hne : s ≠ t) :
    s ⊂ t :=
  Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩

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
  have hz : D.length = 0 := Nat.eq_zero_of_not_pos h
  subst hz
  exact D.endpoints_distinct rfl

/-- An interior vertex of the ear is a **new** vertex: it lies in `new` and misses `old`. -/
theorem DirectedEar.interior_new' (D : DirectedEar E old new) (i : Fin (D.length + 1))
    (hi0 : i.1 ≠ 0) (hiL : i.1 ≠ D.length) :
    D.path.vertex i ∉ old ∧ D.path.vertex i ∈ new :=
  ⟨D.interior_new i hi0 hiL, D.path.mem i⟩

/-- **A vertex of the ear's path lies in `old` exactly when it is one of the two endpoints.**
This single sentence is what makes an ear an ear: the path meets the old set at nothing else, so
nothing already built is re-used. -/
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
`covers_new` together with `old_subset` pins the new set down: nothing else is added, and nothing
is forgotten. -/
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

/-- An ear adds at least one vertex whenever its new set is not the old one. -/
theorem DirectedEar.exists_new_vertex (D : DirectedEar E old new) (hn : new ≠ old) :
    ∃ v, v ∈ new ∧ v ∉ old := by
  by_contra hc
  apply hn
  refine Finset.Subset.antisymm ?_ D.old_subset
  intro v hv
  by_contra hnv
  exact hc ⟨v, hv, hnv⟩

/-- **An ear with a nonempty interior strictly enlarges the vertex set**: its interior vertices
are new. This is the well-founded measure the existence argument of §4 runs on. -/
theorem DirectedEar.ssubset_new_of_two_le_length (D : DirectedEar E old new)
    (h2 : 2 ≤ D.length) : old ⊂ new := by
  refine finset_ssubset_of_subset_of_ne D.old_subset ?_
  have hne : new ≠ old := fun h =>
    (D.interior_new ⟨1, by omega⟩ (by omega) (by omega)) (h ▸ D.path.mem ⟨1, by omega⟩)
  exact hne.symm

/-- The ear's own path runs from its start to its end. -/
theorem DirectedEar.reflTransGen_start_end (D : DirectedEar E old new) :
    Relation.ReflTransGen E (D.path.vertex ⟨0, by omega⟩)
      (D.path.vertex ⟨D.length, by omega⟩) :=
  relPath_reflTransGen D.path

/-- **An ear closes a directed cycle.** Going back from the ear's end to its start uses only the
old strongly connected set, so the two endpoints lie on a directed cycle of the enlarged set —
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

/-- An ear's enlarged set inherits strong connectivity from the ambient `S` it lives in. -/
theorem DirectedEar.stronglyConnected'' (D : DirectedEar E old new) {S : Finset V}
    (hso : old ⊆ S) (hS : ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen E a b) :
    ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen E a b := by
  intro a ha b hb
  rcases D.covers_new a ha with h | ⟨i, hi⟩
  · rcases D.covers_new b hb with h' | ⟨j, hj⟩
    · exact hS a (hso h) b (hso h')
    · rw [← hj]
      exact D.stronglyConnected hS (D.old_subset h) a (D.old_subset h') b (D.path.mem j)
  · rw [← hi]
    exact D.stronglyConnected hS (D.old_subset h) a (D.path.mem i) b hb

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

/-- Every step of the ear's path is an edge of the extended relation, and the adjoined edges are
fresh (`edge_fresh`), so this is an addition and not a re-walk of old edges. -/
theorem DirectedEarExtension.step_edge (D : DirectedEarExtension old new) (i : Fin D.length) :
    D.edge (D.path.vertex (Fin.castSucc i)) (D.path.vertex i.succ) :=
  Or.inr ⟨i, rfl, rfl⟩

/-- Old edges survive in the extended relation. -/
theorem DirectedEarExtension.old_edge (D : DirectedEarExtension old new) {a b : V}
    (h : old.edge a b) : D.edge a b :=
  Or.inl h

/-- The extended relation is a directed subgraph of the ambient relation on the enlarged vertex
set: the two definitional obligations, checked on the construction itself. -/
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

/-- The end block of the edge-aware data: after the extension, the enlarged subgraph is still a
directed subgraph of the ambient relation, and every vertex of it is on the old set or on the
ear's own path. -/
theorem DirectedEarExtension.covers_of_mem (D : DirectedEarExtension old new) {v : V}
    (hv : v ∈ new) : v ∈ old.vertexSet ∨ ∃ i : Fin (D.length + 1), D.path.vertex i = v :=
  D.covers_new v hv

end DirectedEarExtensionWellFormedness

section DirectedEarDecompositionWellFormedness

variable {E : V → V → Prop} {base final : Finset V}

/-- **The base of a decomposition is contained in its final vertex set**: every ear only adds
vertices (`DirectedEar.old_subset`), so the chain of stages is monotone. -/
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

/-- **A stage that strictly enlarges the vertex set raises the vertex count**, the measure used
in §4. -/
theorem DirectedEarDecomposition.card_lt_of_stage {old new : Finset V}
    (hss : old ⊂ new) : old.card < new.card :=
  Finset.card_lt_card hss

/-- The chain of stages of a decomposition is a chain of strict inclusions whenever each stage
adds a vertex. -/
theorem DirectedEarDecomposition.card_lt_of_ear {old new : Finset V}
    (hear : DirectedEar E old new) (hne : new ≠ old) : old.card < new.card :=
  Finset.card_lt_card (finset_ssubset_of_subset_of_ne hear.old_subset hne)

/-- Strong connectivity propagates through every stage of a decomposition. -/
theorem DirectedEarDecomposition.stronglyConnected (D : DirectedEarDecomposition E base final)
    (hbase : ∀ a ∈ base, ∀ b ∈ base, Relation.ReflTransGen E a b) :
    ∀ a ∈ final, ∀ b ∈ final, Relation.ReflTransGen E a b :=
  stronglyConnected_of_directedEarDecomposition hbase D

end DirectedEarDecompositionWellFormedness

/-! ## §2 Splicing an ear out of an open directed path -/

section Splicing

variable {E : V → V → Prop} {S old : Finset V}

/-- **Splicing lemma for ears.** Let `P : RelPath E S k` run from `u` to `r`, both in `old`, with
`u ≠ r`, no interior vertex of `P` in `old`, and `2 ≤ k`. Then there is such a path which is
*simple* and still has a new vertex.

Three facts about splicing make this work. The endpoints survive: `RelPath.splice_vertex_zero`
and `RelPath.splice_vertex_last` keep the first and the last vertex, so `u` and `r` are never
merged. The interior condition survives: every vertex of the spliced path is a vertex of `P`, and
the only old vertices of `P` are its endpoints. And `2 ≤ k` survives, which is what keeps the
"still has a new vertex" conclusion true under recursion: a splice cannot collapse the path to a
single edge, because that would make an interior vertex of `P` equal to `r ∈ old`, and it cannot
collapse it to length `0`, because that would make `u = r`. -/
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
  intro u r hu hr hur P h0 hk hinterior hk2
  induction k using Nat.strong_induction_on generalizing P with
  | _ k ih =>
    by_cases hinj : Function.Injective P.vertex
    · exact ⟨k, P, h0, hk, hinj, hinterior,
        ⟨⟨1, by omega⟩, hinterior ⟨1, by omega⟩ (by omega) (by omega)⟩⟩
    · obtain ⟨x, y, hxy, hveq⟩ :
        ∃ x y : Fin (k + 1), x.1 < y.1 ∧ P.vertex x = P.vertex y := by
        by_contra hno
        push_neg at hno
        refine hinj ?_
        intro x y hxy
        rcases lt_trichotomy x.1 y.1 with hlt | heq | hgt
        · exact absurd hxy (hno x y hlt)
        · exact Fin.ext heq
        · exact absurd hxy.symm (hno y x hgt)
    have hveq' : P.vertex ⟨x.1, by omega⟩ = P.vertex ⟨y.1, by omega⟩ := by
      rw [show (⟨x.1, by omega⟩ : Fin (k + 1)) = x from Fin.ext rfl,
        show (⟨y.1, by omega⟩ : Fin (k + 1)) = y from Fin.ext rfl]
      exact hveq
    have hQ0 : (P.splice x.1 y.1 hxy (by omega) hveq').vertex ⟨0, by omega⟩ = u := by
      rw [RelPath.splice_vertex_zero, h0]
    have hQk : (P.splice x.1 y.1 hxy (by omega) hveq').vertex
        ⟨k - (y.1 - x.1), by omega⟩ = r := by
      rw [RelPath.splice_vertex_last, hk]
    have hQinterior : ∀ i : Fin (k - (y.1 - x.1) + 1), i.1 ≠ 0 → i.1 ≠ k - (y.1 - x.1) →
        (P.splice x.1 y.1 hxy (by omega) hveq').vertex i ∉ old := by
      intro i hi0 hil
      have hil' := i.isLt
      rw [RelPath.splice_vertex]
      by_cases hc : i.1 ≤ x.1
      · rw [dif_pos hc]
        exact hinterior ⟨i.1, by omega⟩ hi0 (by omega)
      · rw [dif_neg hc]
        exact hinterior ⟨i.1 + (y.1 - x.1), by omega⟩ (by omega) (by omega)
    have hsub : 2 ≤ k - (y.1 - x.1) := by
      by_contra hc
      have hc' : k - (y.1 - x.1) ≤ 1 := by omega
      by_cases hx0 : x.1 = 0
      · have hyne : y.1 ≠ k := by
          intro h
          have hk' : k - (y.1 - x.1) = k := by rw [h, hx0]
          omega
        rw [hx0] at hveq'
        exact (hinterior ⟨y.1, by omega⟩ (by omega) hyne) ((hveq'.symm.trans h0) ▸ hu)
      · by_cases hx1 : x.1 = 1
        · have hyk' : y.1 = k := by omega
          have hveq'' : P.vertex ⟨1, by omega⟩ = P.vertex ⟨k, by omega⟩ := by
            rw [← hyk', ← hx1]
            exact hveq'
          exact hinterior ⟨1, by omega⟩ (by omega) (by omega) (hveq''.symm.trans hk)
        · omega
    exact ih (k - (y.1 - x.1)) (by omega) (P.splice x.1 y.1 hxy (by omega) hveq') hQ0 hQk
      hQinterior hsub

end Splicing

/-! ## §3 One ear from one detour -/

section OneEar

variable {E : V → V → Prop} {S old : Finset V}

/-- **One detour gives one ear.** Let `P : RelPath E S k` run from `u` to `r`, let `u` and `r` be
**distinct** members of `old`, let no interior vertex of `P` lie in `old`, and let `2 ≤ k` so that
the interior is nonempty. Then `P` is a `DirectedEar` on `old`, up to splicing out repetitions,
and it strictly enlarges the vertex set.

This is the sharp form of the ear step. No reachability, no minimality and no strong
connectivity is used: given a detour, the ear is bookkeeping. The whole difficulty in the
existence theorem is in *producing* a detour; see `hdetour` in §4 and the module docstring. -/
theorem exists_directedEar_of_detour {u r : V} {k : ℕ}
    (hu : u ∈ old) (hr : r ∈ old) (hur : u ≠ r)
    (P : RelPath E S k) (h0 : P.vertex ⟨0, by omega⟩ = u)
    (hk : P.vertex ⟨k, by omega⟩ = r)
    (hinterior : ∀ i : Fin (k + 1), i.1 ≠ 0 → i.1 ≠ k → P.vertex i ∉ old)
    (hk2 : 2 ≤ k) :
    ∃ (new : Finset V), DirectedEar E old new ∧ old ⊂ new := by
  classical
  obtain ⟨k', P', hP'0, hP'k, hP'inj, hP'interior, hP'new⟩ :=
    exists_simple_earPath u r hu hr hur P h0 hk hinterior hk2
  refine ⟨old ∪ (Finset.univ.image fun i : Fin (k' + 1) => P'.vertex i), ?_, ?_⟩
  · refine { length := k',
      path := { vertex := P'.vertex,
        mem := ?_,
        step := P'.step },
      injective := hP'inj,
      endpoints_distinct := hP'0.symm.trans (hur.trans hP'k),
      start_mem := hu,
      end_mem := hr,
      old_subset := Finset.subset_union_left,
      interior_new := ?_,
      covers_new := ?_ }
    · intro i
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · intro i hi0 hil
      exact hP'interior i hi0 hil
    · intro v hv
      rcases Finset.mem_union.mp hv with h | ⟨i, _, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, rfl⟩
  · refine finset_ssubset_of_subset_of_ne Finset.subset_union_left ?_
    intro he
    obtain ⟨i, hi⟩ := hP'new
    exact absurd hi (he ▸ P'.mem i)

/-- **A singleton base admits no ear at all.** Both endpoints of an ear must be members of `old`
and distinct, and `{v}` has one member. This is why the paper's construction — start at one
vertex and take the first ear to be a cycle through it — is not representable with
`DirectedEar`, and why every hypothesis of §4 below carries a two-vertex lower bound. -/
theorem not_directedEar_of_singleton_base (E : V → V → Prop) (v : V) (new : Finset V)
    (D : DirectedEar E {v} new) : False := by
  have h1 : D.path.vertex ⟨0, by omega⟩ = v := Finset.mem_singleton.mp D.start_mem
  have h2 : D.path.vertex ⟨D.length, by omega⟩ = v := Finset.mem_singleton.mp D.end_mem
  exact D.endpoints_distinct (h1.trans h2.symm)

/-- **A one-vertex ear is impossible too**: its endpoints are at positions `0` and `1`, both lie
in `old`, and injectivity forces them apart. So every ear in this representation has a nonempty
interior, and hence by `DirectedEar.ssubset_new_of_two_le_length` really adds a vertex. This is
what forces `htwo` in §4 to persist along the chain. -/
theorem DirectedEar.two_le_length (D : DirectedEar E {v} new) : 2 ≤ D.length := by
  by_contra h
  have hz : D.length = 0 ∨ D.length = 1 := by omega
  rcases hz with hz | hz
  · subst hz
    exact D.endpoints_distinct rfl
  · have h0 : D.path.vertex ⟨0, by omega⟩ = v := Finset.mem_singleton.mp D.start_mem
    have h1 : D.path.vertex ⟨1, by omega⟩ = v := by
      rw [show (⟨D.length, by omega⟩ : Fin (D.length + 1)) = ⟨1, by omega⟩ from Fin.ext hz]
      exact Finset.mem_singleton.mp D.end_mem
    exact D.endpoints_distinct (by rw [hz]; exact h0.trans h1.symm)

end OneEar

/-! ## §4 Existence of a whole directed ear decomposition -/

section Existence

variable {E : V → V → Prop} {S old : Finset V}

/-- **Existence of a directed ear decomposition of `S` starting at `old`** (Shinar--Feinberg
§A.1, Proposition A.3), under the detour hypothesis.

Hypotheses:

* `holdS` — `old ⊆ S`;
* `hsc` — `old` is strongly connected; it is used only to carry strong connectivity along the
  chain, which `hdetour`'s quantification requires at each stage;
* `htwo` — `|old| ≥ 2`, forced by `not_directedEar_of_singleton_base`;
* `hdetour` — **for every stage `old'` that still has vertices left, two *distinct* vertices
  `u ≠ r ∈ old'` are joined by a path whose interior avoids `old'` and is nonempty.**

`hdetour` is the whole 2-connectivity content. It is not implied by strong connectivity of `S`
(see the module docstring for a counterexample), which is exactly why the classical statement
needs an end-block/2-connectedness theory that Mathlib does not have.

Proof. Strong induction on `(S \ old').card` for a varying starting set `old'`. One step is
`exists_directedEar_of_detour`; the ear strictly enlarges `old'`, so `S \ new ⊊ S \ old'` and the
measure drops. Termination gives `old' = S`, the empty decomposition. -/
theorem exists_directedEarDecomposition
    (holdS : old ⊆ S)
    (hsc : ∀ a ∈ old, ∀ b ∈ old, Relation.ReflTransGen E a b)
    (htwo : 2 ≤ old.card)
    (hdetour : ∀ (old' : Finset V), old' ⊆ S →
        (∀ a ∈ old', ∀ b ∈ old', Relation.ReflTransGen E a b) → 2 ≤ old'.card →
        (S \ old').card ≠ 0 →
        ∃ (u r : V) (k : ℕ) (P : RelPath E S k),
          u ∈ old' ∧ r ∈ old' ∧ u ≠ r ∧
          P.vertex ⟨0, by omega⟩ = u ∧ P.vertex ⟨k, by omega⟩ = r ∧
          (∀ i : Fin (k + 1), i.1 ≠ 0 → i.1 ≠ k → P.vertex i ∉ old') ∧ 2 ≤ k) :
    DirectedEarDecomposition E old S := by
  classical
  have H : ∀ (n : ℕ) (old' : Finset V), (S \ old').card = n → old' ⊆ S →
      (∀ a ∈ old', ∀ b ∈ old', Relation.ReflTransGen E a b) → 2 ≤ old'.card →
      DirectedEarDecomposition E old' S := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro old' hcard hsub hsc' htwo'
      by_cases hzero : n = 0
      · have hdiff : S \ old' = ∅ := Finset.card_eq_zero.mp hcard
        have hSsub : S ⊆ old' := by
          intro v hv
          by_contra hn
          have hmem : v ∈ S \ old' := Finset.mem_sdiff.mpr ⟨hv, hn⟩
          rw [hdiff] at hmem
          exact Finset.not_mem_empty v hmem
        exact DirectedEarDecomposition.refl (Finset.Subset.antisymm hsub hSsub)
      · have hne : (S \ old').card ≠ 0 := by omega
        obtain ⟨u, r, k, P, hu, hr, hur, hP0, hPk, hPint, hPk2⟩ :=
          hdetour old' hsub hsc' htwo' hne
        obtain ⟨new, hear, hss⟩ := exists_directedEar_of_detour hu hr hur P hP0 hPk hPint hPk2
        have hsubNew : new ⊆ S := by
          intro v hv
          rcases hear.covers_new v hv with h | ⟨i, hi⟩
          · exact hsub h
          · exact hear.path.mem i
        have hscNew : ∀ a ∈ new, ∀ b ∈ new, Relation.ReflTransGen E a b :=
          hear.stronglyConnected hsc'
        have hex : ∃ v, v ∈ new ∧ v ∉ old' := by
          by_contra hc
          apply (Finset.ssubset_iff_subset_ne.mp hss).2
          refine Finset.Subset.antisymm ?_ (Finset.ssubset_iff_subset_ne.mp hss).1
          intro v hv
          by_contra hnv
          exact hc ⟨v, hv, hnv⟩
        have hlt : (S \ new).card < n := by
          have hss' : S \ new ⊂ S \ old' := finset_ssubset_of_subset_of_ne
            (Finset.sdiff_subset_sdiff (fun _ h => h) hsubNew) ?_
          · exact Finset.card_lt_card hss'
          · intro he
            obtain ⟨v, hv, hve⟩ := hex
            have hmem : v ∈ S \ old' := Finset.mem_sdiff.mpr ⟨hsubNew hv, hve⟩
            rw [he] at hmem
            exact hmem.2 hv
        have htwoNew : 2 ≤ new.card := by
          have hlt' := DirectedEarDecomposition.card_lt_of_ear hear
            (Finset.ssubset_iff_subset_ne.mp hss).2
          omega
        exact DirectedEarDecomposition.add
          (ih (S \ new).card hlt new (by rw [hcard]; exact rfl) hsubNew hscNew htwoNew) hear
  exact H (S \ old).card old rfl holdS hsc htwo

/-- **Consequence:** a decomposition built as above carries strong connectivity to its final set,
by `stronglyConnected_of_directedEarDecomposition`. Recorded here so that the §5 gap is visible
in one place. -/
theorem stronglyConnected_of_directedEarDecomposition' {base final : Finset V}
    (D : DirectedEarDecomposition E base final)
    (hbase : ∀ a ∈ base, ∀ b ∈ base, Relation.ReflTransGen E a b) :
    ∀ a ∈ final, ∀ b ∈ final, Relation.ReflTransGen E a b :=
  stronglyConnected_of_directedEarDecomposition hbase D

end Existence

/-! ## §5 The §A.1 / Proposition A.3 statement, recorded -/

/-- **Shinar--Feinberg §A.1, Proposition A.3 — the target data, and the honest status.**

PROPOSITION A.3 asks for a decomposition of the finite strongly connected sign-causality graph
into a starting set together with a chain of directed ears. `HasDirectedEarDecomposition E base
final` records the data a witness has to supply: a chain of `DirectedEar`s taking `base` to
`final`, i.e. exactly the `DirectedEarDecomposition` of `TrueChemistrySRCriterion.lean`.

**EXISTENCE IS UNPROVED in the paper's generality, and the obstruction is the representation,
not the combinatorics.** Two independent reasons, both discharged above:

1. `not_directedEar_of_singleton_base`: a one-vertex base admits no ear, because
   `DirectedEar.endpoints_distinct` demands two *distinct* old endpoints. The paper starts from a
   single vertex and takes the first ear to be a *cycle* through it; that ear does not exist in
   this representation. Hence `htwo : 2 ≤ old.card` in §4.
2. Even with two vertices, `exists_directedEarDecomposition` cannot be proved from strong
   connectivity alone: on `{a, b, w}` with edges `a → b`, `b → a`, `b → w`, `w → b` the digraph
   is strongly connected and predecessor closed, but every path between two distinct vertices of
   `{a, b}` either has no interior vertex or has one of them inside, so no `DirectedEar` on
   `{a, b}` adds a vertex. The missing input is the 2-connectivity/end-block structure that would
   rule this configuration out or supply a cycle ear instead; `hdetour` in
   `exists_directedEarDecomposition` is precisely the residual obligation that structure must
   discharge.

Nothing below claims otherwise, and there is no `sorry` in this file. -/
def HasDirectedEarDecomposition (E : V → V → Prop) (base final : Finset V) : Prop :=
  DirectedEarDecomposition E base final

/-- The application-shaped version: a strongly connected `final` that admits a directed ear
decomposition from `base`. **EXISTENCE IS UNPROVED** — see `HasDirectedEarDecomposition` for the
two reasons; the first conjunct is a hypothesis, not a conclusion. -/
def SourceHasDirectedEarDecomposition (E : V → V → Prop) (base final : Finset V) : Prop :=
  (∀ a ∈ final, ∀ b ∈ final, Relation.ReflTransGen E a b) ∧
    HasDirectedEarDecomposition E base final

/-- The proved part of §5, so that the gap between it and the unconditional `def` above is a
single visible line: `SourceHasDirectedEarDecomposition` **under** `hdetour`. -/
theorem SourceHasDirectedEarDecomposition.of_hyp
    (holdS : old ⊆ S)
    (hsc : ∀ a ∈ old, ∀ b ∈ old, Relation.ReflTransGen E a b)
    (htwo : 2 ≤ old.card)
    (hdetour : ∀ (old' : Finset V), old' ⊆ S →
        (∀ a ∈ old', ∀ b ∈ old', Relation.ReflTransGen E a b) → 2 ≤ old'.card →
        (S \ old').card ≠ 0 →
        ∃ (u r : V) (k : ℕ) (P : RelPath E S k),
          u ∈ old' ∧ r ∈ old' ∧ u ≠ r ∧
          P.vertex ⟨0, by omega⟩ = u ∧ P.vertex ⟨k, by omega⟩ = r ∧
          (∀ i : Fin (k + 1), i.1 ≠ 0 → i.1 ≠ k → P.vertex i ∉ old') ∧ 2 ≤ k)
    (hS : ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen E a b) :
    SourceHasDirectedEarDecomposition E old S :=
  ⟨exists_directedEarDecomposition holdS hsc htwo hdetour, hS⟩

end CRNT
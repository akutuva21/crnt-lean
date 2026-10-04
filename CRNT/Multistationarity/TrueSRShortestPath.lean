import CRNT.Multistationarity.TrueSRSpeciesPath

/-!
# Shortest species-to-species paths, and cutting them

The ear argument behind the true-SR criterion needs two ingredients that the tree does not
have yet, both about `TrueSRSSPath` rather than the raw `RelPath`:

* **Decomposition.**  A species-to-species path cut at an *even* interior position splits into
  two species-to-species paths — the prefix `x → z` and the suffix `z → y`.  Both are genuine
  `TrueSRSSPath`s, and the split is *clean*: no interior vertex and no edge is shared between
  the halves, so the two halves can be used independently in the glue bookkeeping.
  (`prefix`, `suffix`, `prefix_suffix_species_disjoint`, `prefix_suffix_reaction_disjoint`,
  `prefix_suffix_edge_disjoint`.)

* **Minimality.**  `ShortestSSPath` bundles a species-to-species path with its two endpoint
  species and a `Nat`-minimality clause, and `prefix_minimal` / `suffix_minimal` say **the
  halves of a shortest path are themselves shortest** — the workhorse for "cut the escape
  route here".

The two are then glued: `prefix_ssGluable_arc` and `suffix_ssGluable_arc` turn the two halves of
a shortest escape path into two `TrueSRSSPath.SSGluable` certificates against the corresponding
species-arcs of a cycle, which is exactly the input `ssGluable_chord_arcFwd` /
`ssGluable_chord_arcBwd` consume, and hence the input to `ssGlueCycle`.

Nothing here changes a hypothesis of anything downstream: this is machinery only.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {L M n : ℕ}

namespace TrueSRSSPath

/-! ### Cutting at an even interior position -/

/-- **The prefix of a species-to-species path, cut at an even position.**  Cutting at an even
position lands on a species vertex, so the prefix is again a species-to-species path. -/
def prefix (P : N.TrueSRSSPath L) (m : ℕ) (hm : m ≤ L) (hpos : 0 < m) (heven : m % 2 = 0) :
    N.TrueSRSSPath m := by
  have hML : m ≤ L := hm
  refine
    { length_pos := hpos
      edge := fun q => P.edge ⟨q.1, by have := q.isLt; omega⟩
      vertex := fun p => P.vertex ⟨p.1, by have := p.isLt; omega⟩
      connects := by
        intro q
        have hq := q.isLt
        simpa using (P.connects ⟨q.1, by omega⟩ : (P.edge ⟨q.1, _⟩).Connects
          (P.vertex ⟨q.1, _⟩) ((⟨q.1, _⟩ : Fin L).succ))
      edge_simple := by
        intro i j hij
        have hij' : (P.edge ⟨i.1, by omega⟩).SameIncidence (P.edge ⟨j.1, by omega⟩) := by
          simpa using hij
        have hz := P.edge_simple hij'
        exact Fin.ext (congrArg Fin.val hz)
      vertex_simple := by
        intro i j hij
        have hij' : P.vertex ⟨i.1, by omega⟩ = P.vertex ⟨j.1, by omega⟩ := by
          simpa using hij
        have hz := P.vertex_simple hij'
        exact Fin.ext (congrArg Fin.val hz)
      starts_at_species := by
        obtain ⟨x, hx⟩ := P.starts_at_species
        refine ⟨x, ?_⟩
        have h1 : P.vertex ⟨(0 : Fin (m + 1)).1, by omega⟩ = P.vertex ⟨0, by omega⟩ := by
          exact congrArg P.vertex (Fin.ext rfl)
        rw [h1]
        exact hx
      ends_at_species := by
        obtain ⟨x, hx⟩ := P.species_iff_even m hm heven
        refine ⟨x, ?_⟩
        have h1 : P.vertex ⟨(Fin.last m).1, by omega⟩ = P.vertex ⟨m, by omega⟩ := by
          exact congrArg P.vertex (Fin.ext rfl)
        rw [h1]
        exact hx }

/-- **The suffix of a species-to-species path, started at an even position.**  Since the start
position is even it carries a species vertex, and the suffix keeps the original terminal
species, so the suffix is again a species-to-species path. -/
def suffix (P : N.TrueSRSSPath L) (m : ℕ) (hm : m < L) (heven : m % 2 = 0) :
    N.TrueSRSSPath (L - m) := by
  have hML : m ≤ L := by omega
  have hback : m + (L - m) = L := Nat.add_sub_of_le hML
  refine
    { length_pos := by omega
      edge := fun q => P.edge ⟨m + q.1, by have := q.isLt; omega⟩
      vertex := fun p => P.vertex ⟨m + p.1, by have := p.isLt; rw [hback]; omega⟩
      connects := by
        intro q
        have hq := q.isLt
        have hlt : m + q.1 < L := by omega
        have hst := P.connects ⟨m + q.1, hlt⟩
        have e1 : (Fin.castSucc (⟨m + q.1, hlt⟩ : Fin L))
            = (⟨m + q.1, by omega⟩ : Fin (L + 1)) := Fin.ext rfl
        have e2 : ((⟨m + q.1, hlt⟩ : Fin L).succ)
            = (⟨m + q.1 + 1, by omega⟩ : Fin (L + 1)) := Fin.ext rfl
        rw [e1, e2] at hst
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hst
      edge_simple := by
        intro i j hij
        have hij' : (P.edge ⟨m + i.1, by omega⟩).SameIncidence
            (P.edge ⟨m + j.1, by omega⟩) := by
          simpa using hij
        have hz := P.edge_simple hij'
        have hv : m + i.1 = m + j.1 := congrArg Fin.val hz
        have hv' : i.1 = j.1 := by omega
        exact Fin.ext hv'
      vertex_simple := by
        intro i j hij
        have hij' : P.vertex ⟨m + i.1, by omega⟩ = P.vertex ⟨m + j.1, by omega⟩ := by
          simpa using hij
        have hz := P.vertex_simple hij'
        have hv : m + i.1 = m + j.1 := congrArg Fin.val hz
        have hv' : i.1 = j.1 := by omega
        exact Fin.ext hv'
      starts_at_species := by
        obtain ⟨x, hx⟩ := P.species_iff_even m (by omega) heven
        refine ⟨x, ?_⟩
        have h1 : P.vertex ⟨m + (0 : Fin ((L - m) + 1)).1, by omega⟩
            = P.vertex ⟨m, by omega⟩ := by
          exact congrArg P.vertex (Fin.ext (by omega))
        rw [h1]
        exact hx
      ends_at_species := by
        obtain ⟨x, hx⟩ := P.ends_at_species
        refine ⟨x, ?_⟩
        have h1 : P.vertex ⟨m + (Fin.last (L - m)).1, by omega⟩ = P.vertex ⟨L, by omega⟩ := by
          apply congrArg P.vertex
          apply Fin.ext
          omega
        rw [h1]
        exact hx }

@[simp] theorem prefix_vertex (P : N.TrueSRSSPath L) (m : ℕ) (hm : m ≤ L) (hpos : 0 < m)
    (heven : m % 2 = 0) (p : Fin (m + 1)) :
    (P.prefix m hm hpos heven).vertex p = P.vertex ⟨p.1, by have := p.isLt; omega⟩ := rfl

@[simp] theorem prefix_edge (P : N.TrueSRSSPath L) (m : ℕ) (hm : m ≤ L) (hpos : 0 < m)
    (heven : m % 2 = 0) (q : Fin m) :
    (P.prefix m hm hpos heven).edge q = P.edge ⟨q.1, by have := q.isLt; omega⟩ := rfl

@[simp] theorem suffix_vertex (P : N.TrueSRSSPath L) (m : ℕ) (hm : m < L) (heven : m % 2 = 0)
    (p : Fin (L - m + 1)) :
    (P.suffix m hm heven).vertex p
      = P.vertex ⟨m + p.1, by have := p.isLt; omega⟩ := rfl

@[simp] theorem suffix_edge (P : N.TrueSRSSPath L) (m : ℕ) (hm : m < L) (heven : m % 2 = 0)
    (q : Fin (L - m)) :
    (P.suffix m hm heven).edge q = P.edge ⟨m + q.1, by have := q.isLt; omega⟩ := rfl

/-- A cut at an even interior position produces two *nontrivial* species-to-species paths: the
prefix has length at least two and the suffix likewise, and both have even length. -/
theorem prefix_two_le_length (P : N.TrueSRSSPath L) (m : ℕ) (hm : m < L) (hpos : 0 < m)
    (heven : m % 2 = 0) : 2 ≤ m ∧ 2 ≤ L - m := by
  have h2 := (P.prefix m hm hpos heven).two_le_length
  have h3 := (P.suffix m hm heven).two_le_length
  exact ⟨h2, h3⟩

/-- The two halves of the split share no interior species vertex. -/
theorem prefix_suffix_species_disjoint (P : N.TrueSRSSPath L) (m : ℕ) (hm : m < L) (hpos : 0 < m)
    (heven : m % 2 = 0) (x : S) :
    ¬ ((P.prefix m hm hpos heven).InteriorSpecies x ∧ (P.suffix m hm heven).InteriorSpecies x) := by
  rintro ⟨⟨p, hp0, hpm, hpv⟩, ⟨q, hq0, hqm, hqv⟩⟩
  have hplt := p.isLt
  have hqlt := q.isLt
  have hvb : P.vertex ⟨p.1, by omega⟩ = P.vertex ⟨m + q.1, by omega⟩ := hpv.trans hqv.symm
  have hz : (⟨p.1, by omega⟩ : Fin (L + 1)) = ⟨m + q.1, by omega⟩ := P.vertex_simple hvb
  have hv := congrArg Fin.val hz
  have : p.1 < m := by omega
  omega

/-- The two halves of the split share no reaction vertex. -/
theorem prefix_suffix_reaction_disjoint (P : N.TrueSRSSPath L) (m : ℕ) (hm : m < L)
    (hpos : 0 < m) (heven : m % 2 = 0) (ρ : N.InternalTrueReaction) :
    ¬ ((P.prefix m hm hpos heven).InteriorReaction ρ ∧
        (P.suffix m hm heven).InteriorReaction ρ) := by
  rintro ⟨⟨p, hpv⟩, ⟨q, hqv⟩⟩
  have hplt := p.isLt
  have hqlt := q.isLt
  have hvb : P.vertex ⟨p.1, by omega⟩ = P.vertex ⟨m + q.1, by omega⟩ := hpv.trans hqv.symm
  have hz : (⟨p.1, by omega⟩ : Fin (L + 1)) = ⟨m + q.1, by omega⟩ := P.vertex_simple hvb
  have hv := congrArg Fin.val hz
  have : p.1 < m := by omega
  omega

/-- The two halves of the split share no edge. -/
theorem prefix_suffix_edge_disjoint (P : N.TrueSRSSPath L) (m : ℕ) (hm : m < L) (hpos : 0 < m)
    (heven : m % 2 = 0) {a : Fin m} {b : Fin (L - m)} :
    ¬ ((P.prefix m hm hpos heven).edge a).SameIncidence ((P.suffix m hm heven).edge b) := by
  intro hab
  have halt := a.isLt
  have hblt := b.isLt
  have hlt : m + b.1 < L := by omega
  have hab' : (P.edge ⟨a.1, by omega⟩).SameIncidence (P.edge ⟨m + b.1, hlt⟩) := by
    simpa using hab
  have hz := P.edge_simple hab'
  have hv := congrArg Fin.val hz
  have : a.1 < m := a.isLt
  omega

end TrueSRSSPath

/-! ### Shortest species-to-species paths -/

/-- **A shortest species-to-species path between two fixed species.**  `min_length` says the
length is at most that of *every* species-to-species path in the true-SR graph from `x` to
`y`. -/
structure ShortestSSPath (x y : S) where
  length : ℕ
  path : N.TrueSRSSPath length
  start_eq : path.vertex ⟨0, by omega⟩ = Sum.inl x
  end_eq : path.vertex ⟨length, by omega⟩ = Sum.inl y
  min_length : ∀ (M : ℕ) (Q : N.TrueSRSSPath M),
    Q.vertex ⟨0, by omega⟩ = Sum.inl x → Q.vertex ⟨M, by omega⟩ = Sum.inl y → length ≤ M

variable {x y : S}

/-- **Minimality is realised by `Nat.find`.**  Given *some* species-to-species path from `x` to
`y`, the shortest one exists and is `Nat`-minimal among all of them. -/
noncomputable def ShortestSSPath.of_path {P : N.TrueSRSSPath L}
    (hx : P.vertex ⟨0, by omega⟩ = Sum.inl x) (hy : P.vertex ⟨L, by omega⟩ = Sum.inl y) :
    ShortestSSPath x y := by
  classical
  have h2 := P.two_le_length
  let HasPath : ℕ → Prop := fun M =>
    ∃ Q : N.TrueSRSSPath M, Q.vertex ⟨0, by omega⟩ = Sum.inl x ∧
      Q.vertex ⟨M, by omega⟩ = Sum.inl y
  have hExists : ∃ M, HasPath M := ⟨L, P, hx, hy⟩
  have hk : HasPath (Nat.find hExists) := Nat.find_spec hExists
  obtain ⟨Q, hQ0, hQM⟩ := hk
  refine
    { length := Nat.find hExists, path := Q, start_eq := hQ0, end_eq := hQM,
      min_length := ?_ }
  intro M R hR0 hRM
  exact Nat.find_min' hExists ⟨R, hR0, hRM⟩

/-- A shortest species-to-species path exists exactly when some species-to-species path does. -/
theorem exists_shortestSSPath :
    (∃ P : ShortestSSPath x y) ↔
      ∃ (K : ℕ) (Q : N.TrueSRSSPath K),
        Q.vertex ⟨0, by omega⟩ = Sum.inl x ∧ Q.vertex ⟨K, by omega⟩ = Sum.inl y := by
  ⟨fun h => ⟨h.length, h.path, h.start_eq, h.end_eq⟩,
    fun h => obtain ⟨K, Q, hQ0, hQM⟩ := h; exact ⟨ShortestSSPath.of_path hQ0 hQM⟩⟩

namespace ShortestSSPath

variable {P : ShortestSSPath x y}

/-- A shortest species-to-species path has length at least two, hence an even length. -/
theorem two_le_length (P : ShortestSSPath x y) : 2 ≤ P.length := P.path.two_le_length

theorem even_length (P : ShortestSSPath x y) : Even P.length := P.path.even_length

theorem even_mod (P : ShortestSSPath x y) : P.length % 2 = 0 := P.path.even_mod

/-- **Every prefix of a shortest path is shortest.**  No species-to-species path from `x` to the
species at position `m` of `P` is shorter than `m` steps. -/
theorem prefix_minimal (P : ShortestSSPath x y) {m : ℕ} (hm : m ≤ P.length) (hpos : 0 < m)
    (heven : m % 2 = 0) {K : ℕ} (Q : N.TrueSRSSPath K)
    (hQ0 : Q.vertex ⟨0, by omega⟩ = Sum.inl x)
    (hQm : Q.vertex ⟨K, by omega⟩ = P.path.vertex ⟨m, by omega⟩) : m ≤ K :=
  P.min_length m (P.path.prefix m hm hpos heven) (by simpa using P.start_eq)
    (by simpa using (P.path.prefix_vertex m hm hpos heven))

/-- **Every suffix of a shortest path is shortest.**  No species-to-species path from the
species at position `m` of `P` to `y` is shorter than the remaining `P.length - m` steps. -/
theorem suffix_minimal (P : ShortestSSPath x y) {m : ℕ} (hm : m < P.length) (heven : m % 2 = 0)
    {K : ℕ} (Q : N.TrueSRSSPath K)
    (hQm : Q.vertex ⟨0, by omega⟩ = P.path.vertex ⟨m, by omega⟩)
    (hQK : Q.vertex ⟨K, by omega⟩ = Sum.inl y) : P.length - m ≤ K := by
  have hback : m + (P.length - m) = P.length := Nat.add_sub_of_le (by omega)
  have h := P.min_length (P.length - m) (P.path.suffix m hm heven) (by
    rw [P.path.suffix_vertex]; rfl) (by
    rw [P.path.suffix_vertex]
    exact P.end_eq)
  omega

/-- **No-shortcut lemma (prefix form).**  On a shortest species-to-species path, an interior
even position can never be reached from the start species in fewer steps than `P` takes.  In
particular, if a shorter species-to-species path `Q` from `x` reaches `P`'s vertex at position
`m`, then `Q`'s own cut there is itself a contradiction target. -/
theorem no_shorter_prefix (P : ShortestSSPath x y) {m : ℕ} (hm : m ≤ P.length) (hpos : 0 < m)
    (heven : m % 2 = 0) {K : ℕ} (Q : N.TrueSRSSPath K)
    (hQ0 : Q.vertex ⟨0, by omega⟩ = Sum.inl x)
    (hQm : Q.vertex ⟨K, by omega⟩ = P.path.vertex ⟨m, by omega⟩) (hK : K < m) : False := by
  have h := P.prefix_minimal hm hpos heven Q hQ0 hQm
  omega

/-- **No-shortcut lemma (suffix form).**  Likewise, from an interior even position of a shortest
path to the terminal species `y`, nothing shorter than the remaining tail exists. -/
theorem no_shorter_suffix (P : ShortestSSPath x y) {m : ℕ} (hm : m < P.length)
    (heven : m % 2 = 0) {K : ℕ} (Q : N.TrueSRSSPath K)
    (hQm : Q.vertex ⟨0, by omega⟩ = P.path.vertex ⟨m, by omega⟩)
    (hQK : Q.vertex ⟨K, by omega⟩ = Sum.inl y) (hK : K < P.length - m) : False := by
  have h := P.suffix_minimal hm heven Q hQm hQK
  omega

end ShortestSSPath

end CRNT.Network
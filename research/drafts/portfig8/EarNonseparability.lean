import CRNT.Graph.SourceBlocks
import CRNT.Multistationarity.TrueChemistrySRCriterion

/-!
# Internal nonseparability: restriction, directed ears, and cycles

Shinar--Feinberg Appendix A.1 propagates nonseparability along a directed ear
decomposition.  This file supplies the three propagation steps, phrased for the
restricted relation `CRNT.restrictRel` so that the walk universe of every
separation stays inside its vertex set (the paper's separations are statements of
the induced subgraph on the vertex set):

* `restrictRel` — the restricted relation; `IsDirectedCycleOn` — a directed cycle
  as a data-carrying witness on its vertex set;
* `isNonseparableOn_restrict_of_isNonseparableOn` — a sub-relation `F` of `E`
  whose every edge lands in `T × T` and which is nonseparable on `T` forces
  `restrictRel E T` itself to be nonseparable (every `F`-walk *is* a walk of the
  restriction, so walks lift along `F ⊆ restrictRel E T` with support unchanged);
* `directedEar_isNonseparableOn` — adjoining a directed ear preserves internal
  nonseparability (the induction step of Proposition A.3);
* `isNonseparableOn_of_directedEarDecomposition` — the induction itself;
* `isNonseparableOn_of_isDirectedCycleOn` — a directed cycle has no separator.

No `sorry`, no `native_decide`; all proofs are elementary finite-graph combinatorics.
-/

namespace CRNT

/-- `E` restricted to vertex pairs inside `T`: walks of `relationGraph (restrictRel E T)`
stay inside `T` by construction, which is the internal-walk notion ear theory needs. -/
def restrictRel {V : Type*} (E : V → V → Prop) (T : Finset V) : V → V → Prop :=
  fun u v => E u v ∧ u ∈ T ∧ v ∈ T

/-- A vertex set carrying a single directed cycle of `E`. -/
structure IsDirectedCycleOn {V : Type*} (E : V → V → Prop) (C : Finset V) where
  length : ℕ
  path : RelPath E C length
  closed : path.vertex ⟨0, by omega⟩ = path.vertex ⟨length, by omega⟩
  inj : Function.Injective fun i : Fin length => path.vertex (Fin.castSucc i)
  covers : ∀ v, v ∈ C → ∃ i : Fin (length + 1), path.vertex i = v

/-! ## Walk plumbing -/

/-- Adjacency of a pointwise stronger relation, as a standalone conversion. -/
private theorem adj_mono {V : Type*} {R R' : V → V → Prop}
    (hsub : ∀ u v, R u v → R' u v) {u v : V}
    (h : (relationGraph R).Adj u v) : (relationGraph R').Adj u v := by
  rcases h with ⟨hne, hdir⟩
  exact ⟨hne, Or.imp (hsub _ _) (hsub _ _) hdir⟩

/-- Both endpoints of a `restrictRel`-edge lie in the set. -/
private theorem adj_support {V : Type*} {E : V → V → Prop} {S : Finset V} {u v : V}
    (h : (relationGraph (restrictRel E S)).Adj u v) : u ∈ S ∧ v ∈ S := by
  rcases h with ⟨_, hdir⟩
  rcases hdir with huv | hvu
  · exact ⟨huv.2.1, huv.2.2⟩
  · exact ⟨hvu.2.2, hvu.2.1⟩

/-- Lift a walk along a pointwise stronger relation, keeping its support. -/
private theorem walk_mono {V : Type*} {R R' : V → V → Prop}
    (hsub : ∀ u v, R u v → R' u v) {a b : V}
    (W : SimpleGraph.Walk (relationGraph R) a b) :
    ∃ W' : SimpleGraph.Walk (relationGraph R') a b, W'.support = W.support := by
  induction W with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | cons hadj W ih =>
      obtain ⟨W', hW'⟩ := ih
      refine ⟨SimpleGraph.Walk.cons (adj_mono hsub hadj) W', ?_⟩
      simp only [SimpleGraph.Walk.support_cons, hW']

/-- Every vertex of a `restrictRel`-walk lies in the set once its source does: every
step carries both endpoints inside by construction. -/
private theorem support_subset_restrictRel {V : Type*} {E : V → V → Prop} {S : Finset V}
    {a b : V} (ha : a ∈ S)
    (W : SimpleGraph.Walk (relationGraph (restrictRel E S)) a b) :
    ∀ x ∈ W.support, x ∈ S := by
  induction W with
  | nil =>
      intro x hx
      simp only [SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rw [hx]
      exact ha
  | cons h t ih =>
      intro x hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact ha
      · exact ih (adj_support h).2 x hx

/-- A segment of a `RelPath` is a walk of the restriction on its vertex set; its
support reports which positions it visited. -/
private theorem exists_walkOn_segment {V : Type*} {E : V → V → Prop} {S : Finset V}
    {k : ℕ} (P : RelPath E S k)
    (hne : ∀ r (hr : r < k), P.vertex ⟨r, by omega⟩ ≠ P.vertex ⟨r + 1, by omega⟩)
    (m t : ℕ) (hm : m ≤ k) (hmt : m ≤ t) (ht : t ≤ k) :
    ∃ W : SimpleGraph.Walk (relationGraph (restrictRel E S))
        (P.vertex ⟨m, by omega⟩) (P.vertex ⟨t, by omega⟩),
      ∀ x ∈ W.support, ∃ i : Fin (k + 1), m ≤ i.1 ∧ i.1 ≤ t ∧ P.vertex i = x := by
  induction t generalizing m hm with
  | zero =>
      have hz : m = 0 := by omega
      subst hz
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro x hx
      simp only [SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rw [hx]
      exact ⟨⟨0, by omega⟩, by omega, by omega, rfl⟩
  | succ t ih =>
      by_cases hm' : m ≤ t
      · obtain ⟨W0, hW0⟩ := ih m hm hm' (by omega)
        have hstep : (relationGraph (restrictRel E S)).Adj
            (P.vertex ⟨t, by omega⟩) (P.vertex ⟨t + 1, by omega⟩) :=
          ⟨hne t (by omega), Or.inl ⟨P.step ⟨t, by omega⟩, P.mem ⟨t, by omega⟩,
            P.mem ⟨t + 1, by omega⟩⟩⟩
        refine ⟨W0.append (SimpleGraph.Walk.cons hstep SimpleGraph.Walk.nil), ?_⟩
        intro x hx
        simp only [SimpleGraph.Walk.mem_support_append_iff] at hx
        rcases hx with hx | hx
        · obtain ⟨i, hi1, hi2, hix⟩ := hW0 x hx
          exact ⟨i, hi1, by omega, hix⟩
        · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
            List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact ⟨⟨t, by omega⟩, hm', Nat.le_succ t, rfl⟩
          · exact ⟨⟨t + 1, by omega⟩, hmt, Nat.le_refl (t + 1), rfl⟩
      · have hm1 : m = t + 1 := by omega
        subst hm1
        refine ⟨SimpleGraph.Walk.nil, ?_⟩
        intro x hx
        simp only [SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rw [hx]
        exact ⟨⟨t + 1, by omega⟩, by omega, by omega, rfl⟩

/-! ## Restriction preserves internal nonseparability -/

/-- A sub-relation `F` of `E` whose edges all land in `T × T`, and which is
nonseparable on `T`, shows the `E`-restriction on `T` is nonseparable: every
`F`-walk is already a walk of `restrictRel E T`, so walks lift along
`F ⊆ restrictRel E T` keeping their support, in both directions the two
definitions need. -/
theorem isNonseparableOn_restrict_of_isNonseparableOn {V : Type*}
    {E F : V → V → Prop} {T : Finset V} (hsub : ∀ u v, F u v → restrictRel E T u v)
    (h : IsNonseparableOn F T) :
    IsNonseparableOn (restrictRel E T) T := by
  constructor
  · intro a ha b hb
    obtain ⟨W, hW⟩ := h.1 a ha b hb
    obtain ⟨W', heqW⟩ := walk_mono hsub W
    exact ⟨W', fun x hx => by rw [heqW] at hx; exact hW x hx⟩
  · intro v hv hsep
    obtain ⟨a, ha, b, hb, hav, hbv, _, hblk⟩ := hsep
    refine h.2 v hv ⟨a, ha, b, hb, hav, hbv, h.1 a ha b hb, ?_⟩
    intro W0
    obtain ⟨W', heqW⟩ := walk_mono hsub W0
    have h1 := hblk W'
    rw [heqW] at h1
    exact h1

/-! ## Directed ears preserve internal nonseparability -/

/-- Core of `directedEar_isNonseparableOn`, stated without a `DecidableEq`
hypothesis so that the induction through a decomposition can use it. -/
private theorem isNonseparableOn_add_ear {V : Type*} {E : V → V → Prop}
    {old new : Finset V} (D : DirectedEar E old new)
    (h : IsNonseparableOn (restrictRel E old) old) :
    IsNonseparableOn (restrictRel E new) new := by
  have hsub : ∀ u v, restrictRel E old u v → restrictRel E new u v :=
    fun u v hv => ⟨hv.1, D.old_subset hv.2.1, D.old_subset hv.2.2⟩
  have hne : ∀ r (hr : r < D.length),
      D.path.vertex ⟨r, by omega⟩ ≠ D.path.vertex ⟨r + 1, by omega⟩ := by
    intro r hr heq
    have hrr : r = r + 1 := congrArg Fin.val (D.injective heq)
    exact absurd hrr (by omega)
  -- connectedness on the enlarged set
  have hconn : ConnectedOn (restrictRel E new) new := by
    intro a ha b hb
    rcases D.covers_new a ha with haO | ⟨i, hi⟩ <;>
      rcases D.covers_new b hb with hbO | ⟨j, hj⟩
    · obtain ⟨W0, _hW0⟩ := h.1 a haO b hbO
      obtain ⟨W, _heqW⟩ := walk_mono hsub W0
      exact ⟨W, support_subset_restrictRel ha W⟩
    · obtain ⟨W0, _hW0⟩ := h.1 a haO _ D.start_mem
      obtain ⟨W1, _heqW⟩ := walk_mono hsub W0
      obtain ⟨W2, _hw2⟩ := exists_walkOn_segment D.path hne 0 j.1
        (by omega) (by omega) (by omega)
      exact ⟨(W1.append W2).copy rfl hj, support_subset_restrictRel ha _⟩
    · obtain ⟨W0, _hW0⟩ := h.1 _ D.start_mem b hbO
      obtain ⟨W1, _heqW⟩ := walk_mono hsub W0
      obtain ⟨W2, _hw2⟩ := exists_walkOn_segment D.path hne 0 i.1
        (by omega) (by omega) (by omega)
      exact ⟨(W2.reverse.append W1).copy hi rfl, support_subset_restrictRel ha _⟩
    · obtain ⟨W2, _hw2⟩ := exists_walkOn_segment D.path hne 0 i.1
        (by omega) (by omega) (by omega)
      obtain ⟨W3, _hw3⟩ := exists_walkOn_segment D.path hne 0 j.1
        (by omega) (by omega) (by omega)
      exact ⟨(W2.reverse.append W3).copy hi hj, support_subset_restrictRel ha _⟩
  refine ⟨hconn, ?_⟩
  intro v hv hs
  obtain ⟨a, ha, b, hb, hav, hbv, _, hblk⟩ := hs
  -- an avoiding walk immediately contradicts the blocking clause
  have havoid : ∀ W : SimpleGraph.Walk (relationGraph (restrictRel E new)) a b,
      (∀ z ∈ W.support, z ≠ v) → False :=
    fun W hW => hW v (hblk W) rfl
  -- both endpoints in `old`
  have caseBoth : a ∈ old → b ∈ old → False := by
    intro haO hbO
    rcases Classical.em (v ∈ old) with hvO | hvN
    · refine h.2 v hvO ⟨a, haO, b, hbO, hav, hbv, h.1 a haO b hbO, ?_⟩
      intro W0
      obtain ⟨W', heqW⟩ := walk_mono hsub W0
      have h1 := hblk W'
      rw [heqW] at h1
      exact h1
    · obtain ⟨W0, hW0⟩ := h.1 a haO b hbO
      obtain ⟨W', heqW⟩ := walk_mono hsub W0
      refine havoid W' ?_
      intro z hz
      rw [heqW] at hz
      intro hzv
      rw [hzv] at hz
      exact hvN (hW0 v hz)
  -- exactly one endpoint in `old`
  have caseOne : ∀ x y : V, x ∈ new → y ∈ new → x ∈ old → y ∉ old →
      x ≠ v → y ≠ v →
      (∀ W : SimpleGraph.Walk (relationGraph (restrictRel E new)) x y,
        v ∈ W.support) → False := by
    intro x y hx hy hxO yN xnev ynev hsep
    obtain ⟨k, hk⟩ : ∃ i : Fin (D.length + 1), D.path.vertex i = y := by
      rcases D.covers_new y hy with h | h
      · exact absurd h yN
      · exact h
    have hk0 : k.1 ≠ 0 := by
      intro h0
      apply yN
      rw [← hk]
      rw [show D.path.vertex k = D.path.vertex ⟨0, by omega⟩ from
        congrArg D.path.vertex (Fin.ext h0)]
      exact D.start_mem
    have hkL : k.1 ≠ D.length := by
      intro hL
      apply yN
      rw [← hk]
      rw [show D.path.vertex k = D.path.vertex ⟨D.length, by omega⟩ from
        congrArg D.path.vertex (Fin.ext hL)]
      exact D.end_mem
    have hk1 : 1 ≤ k.1 ∧ k.1 < D.length := by omega
    rcases Classical.em (v ∈ old) with hvO | hvN
    · -- `v` in `old`: separate `x` from an ear endpoint inside `old`
      rcases Classical.em (D.path.vertex ⟨0, by omega⟩ = v) with h0 | h0
      · -- the start equals `v`, so the finish differs; every `old`-walk passes `v`
        have hfin : D.path.vertex ⟨D.length, by omega⟩ ≠ v :=
          fun he => D.endpoints_distinct (h0.trans he.symm)
        refine h.2 v hvO ⟨x, hxO, D.path.vertex ⟨D.length, by omega⟩, D.end_mem,
          xnev, hfin, h.1 x hxO _ D.end_mem, ?_⟩
        intro W0
        by_contra hnv
        obtain ⟨W1, heq1⟩ := walk_mono hsub W0
        obtain ⟨W2, hw2⟩ := exists_walkOn_segment D.path hne k.1 D.length
          (by omega) (by omega) le_rfl
        have hblock : ∀ z ∈ (W1.append W2.reverse).support, z ≠ v := by
          intro z hz
          simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
          rcases hz with hz | hz
          · rw [heq1] at hz
            intro hzv
            rw [hzv] at hz
            exact hnv hz
          · rw [SimpleGraph.Walk.support_reverse] at hz
            rw [List.mem_reverse] at hz
            obtain ⟨q, hq1, hq2, hqz⟩ := hw2 z hz
            intro hzv
            have hq : D.path.vertex q = v := hqz.trans hzv
            by_cases hqL : q.1 = D.length
            · have hq' : D.path.vertex ⟨D.length, by omega⟩ = v :=
                (congrArg D.path.vertex (Fin.ext hqL.symm)).trans hq
              exact hfin hq'
            · have hint : D.path.vertex q ∉ old :=
                D.interior_new q (by omega) (by omega)
              have hvo : D.path.vertex q ∈ old := by rw [hq]; exact hvO
              exact absurd hvo hint
        have h1 := hsep ((W1.append W2.reverse).copy rfl hk)
        rw [SimpleGraph.Walk.support_copy] at h1
        exact hblock v h1 rfl
      · -- the start differs from `v`: pair `x` with the start
        refine h.2 v hvO ⟨x, hxO, D.path.vertex ⟨0, by omega⟩, D.start_mem, xnev, h0,
          h.1 x hxO _ D.start_mem, ?_⟩
        intro W0
        by_contra hnv
        obtain ⟨W1, heq1⟩ := walk_mono hsub W0
        obtain ⟨W2, hw2⟩ := exists_walkOn_segment D.path hne 0 k.1
          (by omega) (by omega) (by omega)
        have hblock : ∀ z ∈ (W1.append W2).support, z ≠ v := by
          intro z hz
          simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
          rcases hz with hz | hz
          · rw [heq1] at hz
            intro hzv
            rw [hzv] at hz
            exact hnv hz
          · obtain ⟨q, hq1, hq2, hqz⟩ := hw2 z hz
            intro hzv
            have hq : D.path.vertex q = v := hqz.trans hzv
            by_cases hq0 : q.1 = 0
            · have hq' : D.path.vertex ⟨0, by omega⟩ = v :=
                (congrArg D.path.vertex (Fin.ext hq0)).symm.trans hq
              exact absurd hq' h0
            · have hint : D.path.vertex q ∉ old :=
                D.interior_new q (by omega) (by omega)
              have hvo : D.path.vertex q ∈ old := by rw [hq]; exact hvO
              exact absurd hvo hint
        have h1 := hsep ((W1.append W2).copy rfl hk)
        rw [SimpleGraph.Walk.support_copy] at h1
        exact hblock v h1 rfl
    · -- `v` outside `old`: it sits at an interior path position; pick the
      -- ear route whose positions miss that index
      obtain ⟨j, hj⟩ : ∃ i : Fin (D.length + 1), D.path.vertex i = v := by
        rcases D.covers_new v hv with h | h
        · exact absurd h hvN
        · exact h
      have hj0 : j.1 ≠ 0 := by
        intro h0
        apply hvN
        rw [← hj]
        rw [show D.path.vertex j = D.path.vertex ⟨0, by omega⟩ from
          congrArg D.path.vertex (Fin.ext h0)]
        exact D.start_mem
      have hjL : j.1 ≠ D.length := by
        intro hL
        apply hvN
        rw [← hj]
        rw [show D.path.vertex j = D.path.vertex ⟨D.length, by omega⟩ from
          congrArg D.path.vertex (Fin.ext hL)]
        exact D.end_mem
      have hj1 : 1 ≤ j.1 ∧ j.1 < D.length := by omega
      have hvx : ∀ q : Fin (D.length + 1), D.path.vertex q = v → q.1 = j.1 :=
        fun q hq => congrArg Fin.val (D.injective (hq.trans hj.symm))
      by_cases hjk : j.1 < k.1
      · -- route over the finish endpoint: positions ≥ k.1 > j.1
        obtain ⟨W0, hW0⟩ := h.1 x hxO _ D.end_mem
        obtain ⟨W1, heq1⟩ := walk_mono hsub W0
        obtain ⟨W2, hw2⟩ := exists_walkOn_segment D.path hne k.1 D.length
          (by omega) (by omega) le_rfl
        have hblock : ∀ z ∈ (W1.append W2.reverse).support, z ≠ v := by
          intro z hz
          simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
          rcases hz with hz | hz
          · rw [heq1] at hz
            intro hzv
            rw [hzv] at hz
            exact hvN (hW0 v hz)
          · rw [SimpleGraph.Walk.support_reverse] at hz
            rw [List.mem_reverse] at hz
            obtain ⟨q, hq1, hq2, hqz⟩ := hw2 z hz
            intro hzv
            exact absurd (hvx q (hqz.trans hzv)) (by omega)
        have h1 := hsep ((W1.append W2.reverse).copy rfl hk)
        rw [SimpleGraph.Walk.support_copy] at h1
        exact hblock v h1 rfl
      · by_cases hkj : k.1 < j.1
        · -- route over the start endpoint: positions ≤ k.1 < j.1
          obtain ⟨W0, hW0⟩ := h.1 x hxO _ D.start_mem
          obtain ⟨W1, heq1⟩ := walk_mono hsub W0
          obtain ⟨W2, hw2⟩ := exists_walkOn_segment D.path hne 0 k.1
            (by omega) (by omega) (by omega)
          have hblock : ∀ z ∈ (W1.append W2).support, z ≠ v := by
            intro z hz
            simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
            rcases hz with hz | hz
            · rw [heq1] at hz
              intro hzv
              rw [hzv] at hz
              exact hvN (hW0 v hz)
            · obtain ⟨q, hq1, hq2, hqz⟩ := hw2 z hz
              intro hzv
              exact absurd (hvx q (hqz.trans hzv)) (by omega)
          have h1 := hsep ((W1.append W2).copy rfl hk)
          rw [SimpleGraph.Walk.support_copy] at h1
          exact hblock v h1 rfl
        · -- `v` would sit on `y` itself
          have hjk' : j.1 = k.1 := by omega
          have h : D.path.vertex j = D.path.vertex k :=
            congrArg D.path.vertex (Fin.ext hjk')
          exact ynev ((hj.symm.trans h).trans hk).symm
  -- neither endpoint in `old`
  have caseNone : a ∉ old → b ∉ old → False := by
    intro haN hbN
    obtain ⟨i, hi⟩ : ∃ q : Fin (D.length + 1), D.path.vertex q = a := by
      rcases D.covers_new a ha with h | h
      · exact absurd h haN
      · exact h
    obtain ⟨k, hk⟩ : ∃ q : Fin (D.length + 1), D.path.vertex q = b := by
      rcases D.covers_new b hb with h | h
      · exact absurd h hbN
      · exact h
    have hi0 : i.1 ≠ 0 := by
      intro h0
      apply haN
      rw [← hi]
      rw [show D.path.vertex i = D.path.vertex ⟨0, by omega⟩ from
        congrArg D.path.vertex (Fin.ext h0)]
      exact D.start_mem
    have hiL : i.1 ≠ D.length := by
      intro hL
      apply haN
      rw [← hi]
      rw [show D.path.vertex i = D.path.vertex ⟨D.length, by omega⟩ from
        congrArg D.path.vertex (Fin.ext hL)]
      exact D.end_mem
    have hi1 : 1 ≤ i.1 ∧ i.1 < D.length := by omega
    have hk0 : k.1 ≠ 0 := by
      intro h0
      apply hbN
      rw [← hk]
      rw [show D.path.vertex k = D.path.vertex ⟨0, by omega⟩ from
        congrArg D.path.vertex (Fin.ext h0)]
      exact D.start_mem
    have hkL : k.1 ≠ D.length := by
      intro hL
      apply hbN
      rw [← hk]
      rw [show D.path.vertex k = D.path.vertex ⟨D.length, by omega⟩ from
        congrArg D.path.vertex (Fin.ext hL)]
      exact D.end_mem
    have hk1 : 1 ≤ k.1 ∧ k.1 < D.length := by omega
    rcases Classical.em (v ∈ old) with hvO | hvN
    · -- `v` in `old`: a direct segment misses it (interior positions miss `old`)
      by_cases hik : i.1 ≤ k.1
      · obtain ⟨W2, hw2⟩ := exists_walkOn_segment D.path hne i.1 k.1
          (by omega) (by omega) (by omega)
        have hblock : ∀ z ∈ (W2.copy hi hk).support, z ≠ v := by
          intro z hz
          rw [SimpleGraph.Walk.support_copy] at hz
          obtain ⟨q, hq1, hq2, hqz⟩ := hw2 z hz
          intro hzv
          have hint : D.path.vertex q ∉ old :=
            D.interior_new q (by omega) (by omega)
          have hvo : D.path.vertex q ∈ old := by rw [hqz.trans hzv]; exact hvO
          exact absurd hvo hint
        exact hblock v (hblk (W2.copy hi hk)) rfl
      · obtain ⟨W2, hw2⟩ := exists_walkOn_segment D.path hne k.1 i.1
          (by omega) (by omega) (by omega)
        have hblock : ∀ z ∈ (W2.reverse.copy hi hk).support, z ≠ v := by
          intro z hz
          rw [SimpleGraph.Walk.support_copy] at hz
          rw [SimpleGraph.Walk.support_reverse] at hz
          rw [List.mem_reverse] at hz
          obtain ⟨q, hq1, hq2, hqz⟩ := hw2 z hz
          intro hzv
          have hint : D.path.vertex q ∉ old :=
            D.interior_new q (by omega) (by omega)
          have hvo : D.path.vertex q ∈ old := by rw [hqz.trans hzv]; exact hvO
          exact absurd hvo hint
        exact hblock v (hblk (W2.reverse.copy hi hk)) rfl
    · -- `v` outside `old`: it sits at an interior path position
      obtain ⟨j, hj⟩ : ∃ q : Fin (D.length + 1), D.path.vertex q = v := by
        rcases D.covers_new v hv with h | h
        · exact absurd h hvN
        · exact h
      have hj0 : j.1 ≠ 0 := by
        intro h0
        apply hvN
        rw [← hj]
        rw [show D.path.vertex j = D.path.vertex ⟨0, by omega⟩ from
          congrArg D.path.vertex (Fin.ext h0)]
        exact D.start_mem
      have hjL : j.1 ≠ D.length := by
        intro hL
        apply hvN
        rw [← hj]
        rw [show D.path.vertex j = D.path.vertex ⟨D.length, by omega⟩ from
          congrArg D.path.vertex (Fin.ext hL)]
        exact D.end_mem
      have hj1 : 1 ≤ j.1 ∧ j.1 < D.length := by omega
      have hvx : ∀ q : Fin (D.length + 1), D.path.vertex q = v → q.1 = j.1 :=
        fun q hq => congrArg Fin.val (D.injective (hq.trans hj.symm))
      have hij : i.1 ≠ j.1 := by
        intro hh
        apply hav
        rw [← hi, ← hj]
        exact congrArg D.path.vertex (Fin.ext hh)
      have hjk2 : j.1 ≠ k.1 := by
        intro hh
        apply hbv
        rw [← hj, ← hk]
        exact congrArg D.path.vertex (Fin.ext hh.symm)
      by_cases hik : i.1 ≤ k.1
      · by_cases hjl : i.1 < j.1 ∧ j.1 < k.1
        · -- detour through `old` between the interior positions
          obtain ⟨W1, hw1⟩ := exists_walkOn_segment D.path hne 0 i.1
            (by omega) (by omega) (by omega)
          obtain ⟨W2, hW2⟩ := h.1 _ D.start_mem _ D.end_mem
          obtain ⟨W2l, heq2⟩ := walk_mono hsub W2
          obtain ⟨W3, hw3⟩ := exists_walkOn_segment D.path hne k.1 D.length
            (by omega) (by omega) le_rfl
          have hblock : ∀ z ∈
              ((W1.reverse.append W2l).append W3.reverse).copy hi hk |>.support,
              z ≠ v := by
            intro z hz
            rw [SimpleGraph.Walk.support_copy] at hz
            simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
            rcases hz with hz | hz
            · rcases hz with hz | hz
              · rw [SimpleGraph.Walk.support_reverse] at hz
                rw [List.mem_reverse] at hz
                obtain ⟨q, hq1, hq2, hqz⟩ := hw1 z hz
                intro hzv
                exact absurd (hvx q (hqz.trans hzv)) (by omega)
              · rw [heq2] at hz
                intro hzv
                apply hvN
                rw [← hzv]
                exact hW2 z hz
            · rw [SimpleGraph.Walk.support_reverse] at hz
              rw [List.mem_reverse] at hz
              obtain ⟨q, hq1, hq2, hqz⟩ := hw3 z hz
              intro hzv
              exact absurd (hvx q (hqz.trans hzv)) (by omega)
          exact hblock v
            (hblk (((W1.reverse.append W2l).append W3.reverse).copy hi hk)) rfl
        · -- the direct segment misses `v`
          obtain ⟨W2, hw2⟩ := exists_walkOn_segment D.path hne i.1 k.1
            (by omega) (by omega) (by omega)
          have hblock : ∀ z ∈ (W2.copy hi hk).support, z ≠ v := by
            intro z hz
            rw [SimpleGraph.Walk.support_copy] at hz
            obtain ⟨q, hq1, hq2, hqz⟩ := hw2 z hz
            intro hzv
            exact absurd (hvx q (hqz.trans hzv)) (by omega)
          exact hblock v (hblk (W2.copy hi hk)) rfl
      · by_cases hjl : k.1 < j.1 ∧ j.1 < i.1
        · -- detour through `old` the other way round
          obtain ⟨W1, hw1⟩ := exists_walkOn_segment D.path hne i.1 D.length
            (by omega) (by omega) le_rfl
          obtain ⟨W2, hW2⟩ := h.1 _ D.end_mem _ D.start_mem
          obtain ⟨W2l, heq2⟩ := walk_mono hsub W2
          obtain ⟨W3, hw3⟩ := exists_walkOn_segment D.path hne 0 k.1
            (by omega) (by omega) (by omega)
          have hblock : ∀ z ∈ ((W1.append W2l).append W3).copy hi hk |>.support,
              z ≠ v := by
            intro z hz
            rw [SimpleGraph.Walk.support_copy] at hz
            simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
            rcases hz with hz | hz
            · rcases hz with hz | hz
              · obtain ⟨q, hq1, hq2, hqz⟩ := hw1 z hz
                intro hzv
                exact absurd (hvx q (hqz.trans hzv)) (by omega)
              · rw [heq2] at hz
                intro hzv
                apply hvN
                rw [← hzv]
                exact hW2 z hz
            · obtain ⟨q, hq1, hq2, hqz⟩ := hw3 z hz
              intro hzv
              exact absurd (hvx q (hqz.trans hzv)) (by omega)
          exact hblock v
            (hblk (((W1.append W2l).append W3).copy hi hk)) rfl
        · -- the reversed direct segment misses `v`
          obtain ⟨W2, hw2⟩ := exists_walkOn_segment D.path hne k.1 i.1
            (by omega) (by omega) (by omega)
          have hblock : ∀ z ∈ (W2.reverse.copy hi hk).support, z ≠ v := by
            intro z hz
            rw [SimpleGraph.Walk.support_copy] at hz
            rw [SimpleGraph.Walk.support_reverse] at hz
            rw [List.mem_reverse] at hz
            obtain ⟨q, hq1, hq2, hqz⟩ := hw2 z hz
            intro hzv
            exact absurd (hvx q (hqz.trans hzv)) (by omega)
          exact hblock v (hblk (W2.reverse.copy hi hk)) rfl
  rcases Classical.em (a ∈ old) with haO | haN
  · rcases Classical.em (b ∈ old) with hbO | hbN
    · exact caseBoth haO hbO
    · exact caseOne a b ha hb haO hbN hav hbv hblk
  · rcases Classical.em (b ∈ old) with hbO | hbN
    · exact caseOne b a hb ha hbO haN hbv hav (fun W => by
        have h1 := hblk W.reverse
        rw [SimpleGraph.Walk.support_reverse] at h1
        rwa [List.mem_reverse] at h1)
    · exact caseNone haN hbN

/-- Adjoining a directed ear preserves internal nonseparability. -/
theorem directedEar_isNonseparableOn {V : Type*} [DecidableEq V] {E : V → V → Prop}
    {old new : Finset V} (D : DirectedEar E old new)
    (h : IsNonseparableOn (restrictRel E old) old) :
    IsNonseparableOn (restrictRel E new) new :=
  isNonseparableOn_add_ear D h

/-- Nonseparability propagates through every stage of a directed-ear decomposition. -/
theorem isNonseparableOn_of_directedEarDecomposition {V : Type*} {E : V → V → Prop}
    {base final : Finset V} (hbase : IsNonseparableOn (restrictRel E base) base)
    (D : DirectedEarDecomposition E base final) :
    IsNonseparableOn (restrictRel E final) final := by
  induction D with
  | refl => exact hbase
  | @add old new previous ear ih => exact isNonseparableOn_add_ear ear ih

/-! ## Directed cycles are nonseparable -/

/-- A directed cycle has no internal separator: for a putative separator `v` and a
pair `a ≠ v, b ≠ v`, walk along the cycle from `a` to `b` the way that misses `v`. -/
theorem isNonseparableOn_of_isDirectedCycleOn {V : Type*} {E : V → V → Prop}
    {C : Finset V} (h : IsDirectedCycleOn E C) :
    IsNonseparableOn (restrictRel E C) C := by
  obtain ⟨n, P, hclosed, hinj, hcovers⟩ := h
  by_cases hn : n ≤ 1
  · -- at most one vertex: no two witnesses exist to separate
    have hsingle : ∀ v ∈ C, v = P.vertex ⟨0, by omega⟩ := by
      intro v hv
      obtain ⟨q, hq⟩ := hcovers v hv
      by_cases hqn : q.1 = n
      · have hqn0 : P.vertex q = P.vertex ⟨0, by omega⟩ :=
          (congrArg P.vertex (Fin.ext hqn)).trans hclosed.symm
        rw [← hq, hqn0]
      · have hq0 : q.1 = 0 := by omega
        rw [← hq]
        exact congrArg P.vertex (Fin.ext hq0)
    constructor
    · intro a ha b hb
      have ha0 := hsingle a ha
      have hb0 := hsingle b hb
      refine ⟨SimpleGraph.Walk.nil.copy rfl (ha0.trans hb0.symm), ?_⟩
      intro x hx
      rw [SimpleGraph.Walk.support_copy] at hx
      simp only [SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rw [hx]
      exact ha
    · intro v hv hsep
      obtain ⟨a, ha, b, hb, hav, hbv, _, _⟩ := hsep
      exact hav ((hsingle a ha).trans (hsingle v hv).symm)
  · have hn2 : 2 ≤ n := by omega
    have hne : ∀ r (hr : r < n),
        P.vertex ⟨r, by omega⟩ ≠ P.vertex ⟨r + 1, by omega⟩ := by
      intro r hr heq
      by_cases hlt : r + 1 < n
      · have h2 : (⟨r, hr⟩ : Fin n) = ⟨r + 1, hlt⟩ :=
          hinj (a₁ := ⟨r, hr⟩) (a₂ := ⟨r + 1, hlt⟩)
            (show P.vertex (Fin.castSucc (⟨r, hr⟩ : Fin n)) =
              P.vertex (Fin.castSucc (⟨r + 1, hlt⟩ : Fin n)) from heq)
        have hrr : r = r + 1 := congrArg Fin.val h2
        exact absurd hrr (by omega)
      · have hrn : r + 1 = n := by omega
        have hrv : P.vertex ⟨r, by omega⟩ = P.vertex ⟨0, by omega⟩ := by
          rw [heq]
          rw [show P.vertex ⟨r + 1, by omega⟩ = P.vertex ⟨n, by omega⟩ from
            congrArg P.vertex (show (⟨r + 1, by omega⟩ : Fin (n + 1)) =
              ⟨n, by omega⟩ from Fin.ext hrn)]
          exact hclosed.symm
        have h2 : (⟨0, by omega⟩ : Fin n) = ⟨r, hr⟩ :=
          hinj (a₁ := ⟨0, by omega⟩) (a₂ := ⟨r, hr⟩)
            (show P.vertex (Fin.castSucc (⟨0, by omega⟩ : Fin n)) =
              P.vertex (Fin.castSucc (⟨r, hr⟩ : Fin n)) from hrv.symm)
        have h0r : 0 = r := congrArg Fin.val h2
        exact absurd h0r.symm (by omega)
    have hconn : ConnectedOn (restrictRel E C) C := by
      intro a ha b hb
      obtain ⟨q1, hq1⟩ := hcovers a ha
      obtain ⟨q2, hq2⟩ := hcovers b hb
      by_cases hij : q1.1 ≤ q2.1
      · obtain ⟨W, hw⟩ := exists_walkOn_segment P hne q1.1 q2.1
          (by omega) (by omega) (by omega)
        refine ⟨W.copy hq1 hq2, ?_⟩
        intro x hx
        rw [SimpleGraph.Walk.support_copy] at hx
        obtain ⟨t, -, -, htx⟩ := hw x hx
        rw [← htx]
        exact P.mem t
      · obtain ⟨W1, hw1⟩ := exists_walkOn_segment P hne q1.1 n
          (by omega) (by omega) le_rfl
        obtain ⟨W2, hw2⟩ := exists_walkOn_segment P hne 0 q2.1
          (by omega) (by omega) (by omega)
        refine ⟨(W1.append (W2.copy hclosed rfl)).copy hq1 hq2, ?_⟩
        intro x hx
        rw [SimpleGraph.Walk.support_copy] at hx
        simp only [SimpleGraph.Walk.mem_support_append_iff] at hx
        rcases hx with hx | hx
        · obtain ⟨t, -, -, htx⟩ := hw1 x hx
          rw [← htx]
          exact P.mem t
        · rw [SimpleGraph.Walk.support_copy] at hx
          obtain ⟨t, -, -, htx⟩ := hw2 x hx
          rw [← htx]
          exact P.mem t
    refine ⟨hconn, ?_⟩
    intro v hv hsep
    obtain ⟨a, ha, b, hb, hav, hbv, _, hblk⟩ := hsep
    obtain ⟨q1, hq1⟩ := hcovers a ha
    obtain ⟨q2, hq2⟩ := hcovers b hb
    obtain ⟨q0, hq0⟩ := hcovers v hv
    -- a position of `v` strictly below the wrap
    obtain ⟨q3, hq3l, hq3⟩ : ∃ r : Fin (n + 1), r.1 < n ∧ P.vertex r = v := by
      by_cases hq : q0.1 = n
      · have h0n : 0 < n := by omega
        have hnq : P.vertex ⟨n, by omega⟩ = P.vertex q0 :=
          congrArg P.vertex (show (⟨n, by omega⟩ : Fin (n + 1)) = q0 from
            Fin.ext hq.symm)
        exact ⟨⟨0, by omega⟩, h0n, (hclosed.trans hnq).trans hq0⟩
      · exact ⟨q0, by omega, hq0⟩
    have h13 : q1.1 ≠ q3.1 := by
      intro hh
      apply hav
      rw [← hq1, ← hq3]
      exact congrArg P.vertex (Fin.ext hh)
    have h23 : q2.1 ≠ q3.1 := by
      intro hh
      apply hbv
      rw [← hq2, ← hq3]
      exact congrArg P.vertex (Fin.ext hh)
    have h1wrap : q1.1 = n → q3.1 ≠ 0 := by
      intro h1n h30
      apply hav
      rw [← hq1, ← hq3]
      have hq10 : P.vertex q1 = P.vertex ⟨0, by omega⟩ :=
        (congrArg P.vertex (Fin.ext h1n)).trans hclosed.symm
      have hq30 : P.vertex q3 = P.vertex ⟨0, by omega⟩ := by
        congr 1
        exact Fin.ext h30
      exact hq10.trans hq30.symm
    have h2wrap : q2.1 = n → q3.1 ≠ 0 := by
      intro h2n h30
      apply hbv
      rw [← hq2, ← hq3]
      have hq20 : P.vertex q2 = P.vertex ⟨0, by omega⟩ :=
        (congrArg P.vertex (Fin.ext h2n)).trans hclosed.symm
      have hq30 : P.vertex q3 = P.vertex ⟨0, by omega⟩ := by
        congr 1
        exact Fin.ext h30
      exact hq20.trans hq30.symm
    -- the position of `v` on the cycle, up to the wrap-around
    have hvp : ∀ t : Fin (n + 1), P.vertex t = v →
        t.1 = q3.1 ∨ (t.1 = n ∧ q3.1 = 0) := by
      intro t htv
      by_cases htL : t.1 = n
      · right
        refine ⟨htL, ?_⟩
        have h0v : P.vertex ⟨0, by omega⟩ = P.vertex q3 :=
          hclosed.trans
            ((congrArg P.vertex (Fin.ext htL)).symm.trans (htv.trans hq3.symm))
        have h0 : (⟨0, by omega⟩ : Fin n) = ⟨q3.1, hq3l⟩ :=
          hinj (a₁ := ⟨0, by omega⟩) (a₂ := ⟨q3.1, hq3l⟩)
            (show P.vertex (Fin.castSucc (⟨0, by omega⟩ : Fin n)) =
              P.vertex (Fin.castSucc (⟨q3.1, hq3l⟩ : Fin n)) from h0v)
        exact (congrArg Fin.val h0).symm
      · left
        have ht : t.1 < n := by omega
        have h2 : (⟨t.1, ht⟩ : Fin n) = ⟨q3.1, hq3l⟩ :=
          hinj (a₁ := ⟨t.1, ht⟩) (a₂ := ⟨q3.1, hq3l⟩)
            (show P.vertex (Fin.castSucc (⟨t.1, ht⟩ : Fin n)) =
              P.vertex (Fin.castSucc (⟨q3.1, hq3l⟩ : Fin n)) from htv.trans hq3.symm)
        have h8 : Fin.val (⟨t.1, ht⟩ : Fin n) = Fin.val ⟨q3.1, hq3l⟩ :=
          congrArg Fin.val h2
        exact h8
    by_cases hij : q1.1 ≤ q2.1
    · by_cases hF : q1.1 ≤ q3.1 ∧ q3.1 ≤ q2.1
      · -- walking forward contains `v`; the wrapping backward arc avoids it
        obtain ⟨W1, hw1⟩ := exists_walkOn_segment P hne 0 q1.1
          (by omega) (by omega) (by omega)
        obtain ⟨W2, hw2⟩ := exists_walkOn_segment P hne q2.1 n
          (by omega) (by omega) le_rfl
        have hblock : ∀ z ∈
            ((W1.reverse.append (W2.reverse.copy hclosed.symm rfl)).copy hq1 hq2).support,
            z ≠ v := by
          intro z hz
          rw [SimpleGraph.Walk.support_copy] at hz
          simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
          rcases hz with hz | hz
          · rw [SimpleGraph.Walk.support_reverse] at hz
            rw [List.mem_reverse] at hz
            obtain ⟨t, ht1, ht2, htz⟩ := hw1 z hz
            intro hzv
            exact absurd (hvp t (htz.trans hzv)) (by omega)
          · rw [SimpleGraph.Walk.support_copy] at hz
            rw [SimpleGraph.Walk.support_reverse] at hz
            rw [List.mem_reverse] at hz
            obtain ⟨t, ht1, ht2, htz⟩ := hw2 z hz
            intro hzv
            exact absurd (hvp t (htz.trans hzv)) (by omega)
        exact hblock v
          (hblk ((W1.reverse.append (W2.reverse.copy hclosed.symm rfl)).copy hq1 hq2))
          rfl
      · -- the forward arc misses `v`
        obtain ⟨W, hw⟩ := exists_walkOn_segment P hne q1.1 q2.1
          (by omega) (by omega) (by omega)
        have hblock : ∀ z ∈ (W.copy hq1 hq2).support, z ≠ v := by
          intro z hz
          rw [SimpleGraph.Walk.support_copy] at hz
          obtain ⟨t, ht1, ht2, htz⟩ := hw z hz
          intro hzv
          exact absurd (hvp t (htz.trans hzv)) (by omega)
        exact hblock v (hblk (W.copy hq1 hq2)) rfl
    · by_cases hF : q3.1 ≥ q1.1 ∨ q3.1 ≤ q2.1
      · -- the wrapping forward arc contains `v`; the direct backward arc avoids it
        obtain ⟨W, hw⟩ := exists_walkOn_segment P hne q2.1 q1.1
          (by omega) (by omega) (by omega)
        have hblock : ∀ z ∈ (W.reverse.copy hq1 hq2).support, z ≠ v := by
          intro z hz
          rw [SimpleGraph.Walk.support_copy] at hz
          rw [SimpleGraph.Walk.support_reverse] at hz
          rw [List.mem_reverse] at hz
          obtain ⟨t, ht1, ht2, htz⟩ := hw z hz
          intro hzv
          exact absurd (hvp t (htz.trans hzv)) (by omega)
        exact hblock v (hblk (W.reverse.copy hq1 hq2)) rfl
      · -- the wrapping forward arc misses `v`
        obtain ⟨W1, hw1⟩ := exists_walkOn_segment P hne q1.1 n
          (by omega) (by omega) le_rfl
        obtain ⟨W2, hw2⟩ := exists_walkOn_segment P hne 0 q2.1
          (by omega) (by omega) (by omega)
        have hblock : ∀ z ∈ ((W1.append (W2.copy hclosed rfl)).copy hq1 hq2).support,
            z ≠ v := by
          intro z hz
          rw [SimpleGraph.Walk.support_copy] at hz
          simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
          rcases hz with hz | hz
          · obtain ⟨t, ht1, ht2, htz⟩ := hw1 z hz
            intro hzv
            exact absurd (hvp t (htz.trans hzv)) (by omega)
          · rw [SimpleGraph.Walk.support_copy] at hz
            obtain ⟨t, ht1, ht2, htz⟩ := hw2 z hz
            intro hzv
            exact absurd (hvp t (htz.trans hzv)) (by omega)
        exact hblock v (hblk ((W1.append (W2.copy hclosed rfl)).copy hq1 hq2)) rfl

end CRNT

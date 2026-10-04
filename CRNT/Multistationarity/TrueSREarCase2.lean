import CRNT.Multistationarity.TrueSRParityRR
import CRNT.Multistationarity.TrueSRPath
import CRNT.Multistationarity.TrueSRSSGlueCPairs

/-!
# Case 2 of Lemma A.6 (ported core): sign-directed cycles, the two-component S-to-R
intersection certificate, and the two criterion-discharge lemmas

Shinar--Feinberg (arXiv:1203.6560, Appendix A.3) rule out, at every stage `Gᵢ` of the directed
ear decomposition of a sign-causality source block, an ear joining two vertices of the stage
cycle.  Case 1 (an ear from a stage species to a stage reaction) is handled elsewhere.  This
file carries **Case 2**: the ear `Pᵢ` joins two distinct stage species `S*` (where it leaves the
cycle) and `S**` (where it re-enters).

This module is a **port** of the four declarations that the Case-2 argument actually consumes,
taken from the unmerged branch `backup-fig8` (commit `637a970`, `CRNT/Multistationarity/
TrueSREarCase2.lean`).  That branch was reset to `ef8048c` and never merged, and its other
content depends on the also-unmerged side branches `sr-blocks` (`84e49f2`) and `sr-route-ear`
(`9285de1`), so it could not be cherry-picked.  What is ported here is exactly the part that is
*reproducible against the current tree*:

1. `TrueSRCycle.SignDirected` and `TrueSRCycle.even_of_signDirected` — the "directed cycle" package
   (Shinar--Feinberg Lemma 5.4).  The sign-change counting argument
   (`cyclic_sign_changes_even`) is re-proved here because the in-tree copy at
   `TrueChemistrySRCriterion.lean:6885` is `private`.
2. `TrueSRCycle.sToRIntersectionOfTwoPaths` — the `componentCount = 2` witness for
   `TrueSRCycle.SToRIntersection`, needed because four of the six arrangements of Fig. 8 leave
   *two* common components and `no_shared_path_of_trueSRCriterion` cannot express a
   disconnected common subgraph.
3. `lemmaA6_case2_twoComponents` — the discharge for the four two-component arrangements.
4. `lemmaA6_case2_oneComponent` — the discharge for the two alternating orders, whose common
   subgraph is a single S-to-R path.

**What is *not* here, and why.**  The five per-arrangement entry points
(`lemmaA6_case2_arrangement1`, `..._arrangement2`, `..._interleaved`, `..._arrangement4`,
`..._arrangement6`) and the support lemmas they need (`fresh_rr_ss`,
`ssGlueCycle_even_of_partner`, `TrueSRPathRR.rrGluedCycle_containsEdge_iff`,
`TrueSRSSPath.ssGlueCycle_containsEdge_iff`, `ssGlueCycle_even_of_partner`) are *not* ported:
each is a `False`-producing **consumer** of a directed ear decomposition that the current tree
does not build.  Concretely, all five require a `N.TrueSRPathRR` ear, and there is **no
constructor for `TrueSRPathRR` anywhere in this repository** — it is a structure whose fields
(`first`, `first_species`, `first_ne_tail_edge`, `first_ne_tail_vertex`) are never discharged
outside `TrueSRParityRR.lean` itself, so no aggregate `RelPath` and no `TrueSRPath` can be
turned into one.  They also require `SignDirected σ` on glued cycles, `RRGluable`/`SSGluable`
gluing data, and the arrangement identity `harr`; none of those is derivable above the frontier
branch of `stronglyConcordant_fullyOpen_of_trueSRCriterion`.  See
`research/routes/a6-case2-landing.md`.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

open TrueSRPath TrueSRSSPath TrueSRPathRR TrueSREdge

/-- `1 ≠ -1` in `ℝ`, spelled out rather than taken from a library lemma whose instance
bundle this file does not otherwise need. -/
private theorem one_ne_neg_one_real : (1 : ℝ) ≠ -1 := by
  have h1 : (0 : ℝ) < 1 := by norm_num
  have h2 : (-1 : ℝ) < 0 := by norm_num
  intro hz
  exact absurd (h1.trans (by rw [hz]; exact h2)) (by norm_num)

private theorem two_ne_neg_two_real : (2 : ℝ) ≠ -2 := by
  have h1 : (0 : ℝ) < 2 := by norm_num
  have h2 : (-2 : ℝ) < 0 := by norm_num
  intro hz
  exact absurd (h1.trans (by rw [hz]; exact h2)) (by norm_num)

private theorem neg_one_ne_one_real : (-1 : ℝ) ≠ 1 := fun hz => one_ne_neg_one_real hz.symm


/-! ### Sign changes around a cycle

Shinar--Feinberg Lemma 5.4: a cycle that is a union of causal units has an even number of
c-pairs, because c-pairs are exactly the sign changes of a nonvanishing species sign pattern
around the cycle, and a closed loop has an even number of sign changes.  The two clauses are
bundled in `TrueSRCycle.SignDirected` below. -/

private theorem prod_pm_one_eq_neg_one_pow_card_neg
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hpm : ∀ i ∈ s, f i = 1 ∨ f i = -1) :
    ∏ i ∈ s, f i = (-1 : ℝ) ^ (s.filter (fun i => f i = -1)).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hfa := hpm a (by simp)
      have hs : ∀ i ∈ s, f i = 1 ∨ f i = -1 := fun i hi => hpm i (by simp [hi])
      rw [ih hs]
      rcases hfa with h1 | hn
      · have hfilter :
            (insert a s).filter (fun i => f i = -1) = s.filter (fun i => f i = -1) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · intro h
            rcases h.1 with hi | hi
            · exfalso
              rw [hi, h1] at h
              exact absurd h.2 one_ne_neg_one_real
            · exact ⟨hi, h.2⟩
          · rintro ⟨hi, h⟩
            exact ⟨Or.inr hi, h⟩
        rw [h1, hfilter, one_mul]
      · simp [Finset.filter_insert, hn, ha, pow_succ, mul_comm]

private theorem even_card_neg_of_prod_one
    {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hpm : ∀ i, f i = 1 ∨ f i = -1)
    (hprod : ∏ i, f i = 1) :
    Even ((Finset.univ.filter (fun i => f i = -1)).card) := by
  classical
  have h := prod_pm_one_eq_neg_one_pow_card_neg Finset.univ f (by simpa using hpm)
  rw [hprod] at h
  have hne : (-1 : ℝ) ≠ 1 := neg_one_ne_one_real
  exact (neg_one_pow_eq_one_iff_even hne).mp h.symm

private theorem cyclic_sign_changes_even {n : ℕ} [NeZero n] (a : Fin n → ℝ)
    (hne : ∀ i, a i ≠ 0) :
    Even ((Finset.univ.filter (fun i => a i * a (finRotate n i) < 0)).card) := by
  classical
  let g : Fin n → ℝ := fun i => if 0 < a i then 1 else -1
  let f : Fin n → ℝ := fun i => g i * g (finRotate n i)
  have hg : ∀ i, g i = 1 ∨ g i = -1 := by
    intro i
    simp only [g]
    split <;> simp
  have hf : ∀ i, f i = 1 ∨ f i = -1 := by
    intro i
    rcases hg i with hi | hi <;> rcases hg (finRotate n i) with hj | hj
    · left; change g i * g (finRotate n i) = 1; rw [hi, hj]; norm_num
    · right; change g i * g (finRotate n i) = -1; rw [hi, hj]; norm_num
    · right; change g i * g (finRotate n i) = -1; rw [hi, hj]; norm_num
    · left; change g i * g (finRotate n i) = 1; rw [hi, hj]; norm_num
  have hrot : (∏ i, g (finRotate n i)) = ∏ i, g i := Equiv.prod_comp _ _
  have hprodg : (∏ i, g i) = 1 ∨ (∏ i, g i) = -1 := by
    have hp := prod_pm_one_eq_neg_one_pow_card_neg Finset.univ g (by simpa using hg)
    rw [hp]
    rcases Nat.even_or_odd ((Finset.univ.filter (fun i => g i = -1)).card) with he | ho
    · left; simp [Even.neg_one_pow he]
    · right; simpa using Odd.neg_one_pow ho
  have hprod : ∏ i, f i = 1 := by
    rw [show (∏ i, f i) = (∏ i, g i) * (∏ i, g (finRotate n i)) by
      simp [f, Finset.prod_mul_distrib], hrot]
    rcases hprodg with h | h <;> rw [h] <;> norm_num
  have he := even_card_neg_of_prod_one f hf hprod
  have hfilter : (Finset.univ.filter (fun i => f i = -1)) =
      Finset.univ.filter (fun i => a i * a (finRotate n i) < 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hai := hne i
    have haj := hne (finRotate n i)
    rcases lt_or_gt_of_ne hai with hi | hi <;> rcases lt_or_gt_of_ne haj with hj | hj
    · have hgi : g i = -1 := if_neg (not_lt.mpr hi.le)
      have hgj : g (finRotate n i) = -1 := if_neg (not_lt.mpr hj.le)
      have hp : 0 < a i * a (finRotate n i) := mul_pos_of_neg_of_neg hi hj
      change (g i * g (finRotate n i) = -1 ↔ a i * a (finRotate n i) < 0)
      rw [hgi, hgj]
      constructor
      · intro hcontra
        rw [show ((-1 : ℝ) * (-1 : ℝ)) = (1 : ℝ) by norm_num] at hcontra
        exact absurd hcontra one_ne_neg_one_real
      · intro h
        exact absurd h (not_lt.mpr hp.le)
    · have hgi : g i = -1 := if_neg (not_lt.mpr hi.le)
      have hgj : g (finRotate n i) = 1 := if_pos hj
      have hp : a i * a (finRotate n i) < 0 := mul_neg_of_neg_of_pos hi hj
      change (g i * g (finRotate n i) = -1 ↔ a i * a (finRotate n i) < 0)
      rw [hgi, hgj]
      constructor
      · intro _
        exact hp
      · intro _
        rw [mul_one]
    · have hgi : g i = 1 := if_pos hi
      have hgj : g (finRotate n i) = -1 := if_neg (not_lt.mpr hj.le)
      have hp : a i * a (finRotate n i) < 0 := mul_neg_of_pos_of_neg hi hj
      change (g i * g (finRotate n i) = -1 ↔ a i * a (finRotate n i) < 0)
      rw [hgi, hgj]
      constructor
      · intro _
        exact hp
      · intro _
        rw [one_mul]
    · have hgi : g i = 1 := if_pos hi
      have hgj : g (finRotate n i) = 1 := if_pos hj
      have hp : 0 < a i * a (finRotate n i) := mul_pos hi hj
      change (g i * g (finRotate n i) = -1 ↔ a i * a (finRotate n i) < 0)
      rw [hgi, hgj, one_mul]
      constructor
      · intro hcontra
        exact absurd hcontra one_ne_neg_one_real
      · intro h
        exact absurd h (not_lt.mpr hp.le)
  rwa [hfilter] at he

/-- A sign pattern σ that is nonvanishing on the cycle's species and whose sign changes are
exactly the cycle's c-pairs — the hypothesis under which a *directed* cycle is even. -/
def TrueSRCycle.SignDirected {n : ℕ} (C : N.TrueSRCycle n) (σ : S → ℝ) : Prop :=
  (∀ i, σ (C.species i) ≠ 0) ∧
    (∀ i, C.isCPair i ↔ σ (C.species i) * σ (C.species (finRotate n i)) < 0)

/-- **A sign-directed cycle is even** (Shinar--Feinberg Lemma 5.4). -/
theorem TrueSRCycle.even_of_signDirected {n : ℕ} (C : N.TrueSRCycle n) {σ : S → ℝ}
    (h : C.SignDirected σ) : C.Even := by
  classical
  let a : Fin n → ℝ := fun i => σ (C.species i)
  haveI : NeZero n := ⟨by have := C.nontrivial; omega⟩
  have hEven := cyclic_sign_changes_even a h.1
  rw [TrueSRCycle.Even, TrueSRCycle.numCPairs]
  rw [show (Finset.univ.filter C.isCPair) =
      Finset.univ.filter (fun i => a i * a (finRotate n i) < 0) by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, a]
    exact h.2 i]
  exact hEven

/-! ### Edge sets of paths

The presentation order of a path never matters to `SameIncidence`-based statements; these are
the predicates the arrangement data are phrased in. -/

/-- The edge set of a species-to-reaction path, as an edge predicate. -/
def TrueSRPath.HasEdge {L : ℕ} (P : N.TrueSRPath L) (e : N.TrueSREdge) : Prop :=
  ∃ k : Fin L, e.SameIncidence (P.edge k)

/-- The edge set of a species-to-species path, as an edge predicate. -/
def TrueSRSSPath.HasEdge {L : ℕ} (P : N.TrueSRSSPath L) (e : N.TrueSREdge) : Prop :=
  ∃ k : Fin L, e.SameIncidence (P.edge k)

/-- The edge set of a reaction-to-reaction path, as an edge predicate. -/
def TrueSRPathRR.HasEdge {j : ℕ} (A : N.TrueSRPathRR j) (e : N.TrueSREdge) : Prop :=
  ∃ k : Fin (2 * j + 2), e.SameIncidence (A.edgeAt k)

/-! ### A two-component S-to-R intersection certificate

`TrueSRSingleSharedEdge.sToRIntersectionOfPath` builds the `componentCount = 1` witness from a
single common S-to-R path.  Four of the six arrangements of Fig. 8 leave *two* common
components, and `TrueSRCycle.SToRIntersection` allows a disconnected common subgraph as long as
every component is a simple S-to-R path, the components are pairwise vertex-separated, and all
common edges are covered.  This is that builder for two components. -/

/-- Two common S-to-R paths, vertex-separated from each other and together covering every
common edge, witness `C.SToRIntersection D`. -/
noncomputable def TrueSRCycle.sToRIntersectionOfTwoPaths {m n L₁ L₂ : ℕ}
    (C : N.TrueSRCycle m) (D : N.TrueSRCycle n)
    (c₁ : N.TrueSRPath L₁) (c₂ : N.TrueSRPath L₂)
    (h₁C : ∀ i, C.ContainsEdge (c₁.edge i)) (h₁D : ∀ i, D.ContainsEdge (c₁.edge i))
    (h₂C : ∀ i, C.ContainsEdge (c₂.edge i)) (h₂D : ∀ i, D.ContainsEdge (c₂.edge i))
    (hcov : ∀ f : N.TrueSREdge, C.ContainsEdge f → D.ContainsEdge f →
      c₁.HasEdge f ∨ c₂.HasEdge f)
    (hsep : ∀ i j, ¬ (c₁.edge i).ShareVertex (c₂.edge j)) :
    C.SToRIntersection D := by
  let len : Fin 2 → ℕ := fun c => if c = 0 then L₁ else L₂
  let edg : ∀ c : Fin 2, Fin (len c) → N.TrueSREdge := fun c i =>
    if h : c = 0 then c₁.edge ⟨i.1, by
        have hi : i.1 < (if c = 0 then L₁ else L₂) := i.isLt
        rw [if_pos h] at hi
        exact hi⟩
    else c₂.edge ⟨i.1, by
        have hi : i.1 < (if c = 0 then L₁ else L₂) := i.isLt
        rw [if_neg h] at hi
        exact hi⟩
  let vtx : ∀ c : Fin 2, Fin (len c + 1) → N.TrueSRVertex := fun c i =>
    if h : c = 0 then c₁.vertex ⟨i.1, by
        have hi : i.1 < (if c = 0 then L₁ else L₂) + 1 := i.isLt
        rw [if_pos h] at hi
        exact hi⟩
    else c₂.vertex ⟨i.1, by
        have hi : i.1 < (if c = 0 then L₁ else L₂) + 1 := i.isLt
        rw [if_neg h] at hi
        exact hi⟩
  have hcases : ∀ c : Fin 2, c.1 = 0 ∨ c.1 = 1 := by
    intro c
    have := c.isLt
    omega
  have hlenpos : ∀ c, 0 < len c := by
    intro c
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      show 0 < (if (0 : Fin 2) = 0 then L₁ else L₂)
      rw [if_pos rfl]
      exact c₁.length_pos
    · have hc : c = 1 := Fin.ext h
      subst hc
      show 0 < (if (1 : Fin 2) = 0 then L₁ else L₂)
      rw [if_neg (by decide)]
      exact c₂.length_pos
  refine
    { componentCount := 2
      componentCount_pos := Nat.zero_lt_two
      componentLength := len
      componentLength_pos := hlenpos
      edge := edg
      vertex := vtx
      edge_on_C := ?_
      edge_on_D := ?_
      connects := ?_
      edge_simple := ?_
      vertex_simple := ?_
      starts_at_species := ?_
      ends_at_reaction := ?_
      covers_common := ?_
      components_separated := ?_ }
  · intro c i
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      exact h₁C i
    · have hc : c = 1 := Fin.ext h
      subst hc
      exact h₂C i
  · intro c i
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      exact h₁D i
    · have hc : c = 1 := Fin.ext h
      subst hc
      exact h₂D i
  · intro c i
    show (edg c i).Connects (vtx c (Fin.castSucc i)) (vtx c i.succ)
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      exact c₁.connects i
    · have hc : c = 1 := Fin.ext h
      subst hc
      exact c₂.connects i
  · intro c i j hsame
    rcases hcases c with hc | hc
    · have hcc : c = 0 := Fin.ext hc
      subst hcc
      exact c₁.edge_simple hsame
    · have hcc : c = 1 := Fin.ext hc
      subst hcc
      exact c₂.edge_simple hsame
  · intro c
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      exact c₁.vertex_simple
    · have hc : c = 1 := Fin.ext h
      subst hc
      exact c₂.vertex_simple
  · intro c
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      exact c₁.starts_at_species
    · have hc : c = 1 := Fin.ext h
      subst hc
      exact c₂.starts_at_species
  · intro c
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      exact c₁.ends_at_reaction
    · have hc : c = 1 := Fin.ext h
      subst hc
      exact c₂.ends_at_reaction
  · intro f hfC hfD
    rcases hcov f hfC hfD with h | h
    · obtain ⟨i, hi⟩ := h
      exact ⟨0, i, hi⟩
    · obtain ⟨i, hi⟩ := h
      exact ⟨1, i, hi⟩
  · intro c d hcd
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      rcases hcases d with h' | h'
      · have hd : d = 0 := Fin.ext h'
        subst hd
        intro i j
        exact absurd rfl hcd
      · have hd : d = 1 := Fin.ext h'
        subst hd
        intro i j
        exact hsep i j
    · have hc : c = 1 := Fin.ext h
      subst hc
      rcases hcases d with h' | h'
      · have hd : d = 0 := Fin.ext h'
        subst hd
        intro i j hv
        apply hsep j i
        rcases hv with hv | hv
        · exact Or.inl hv.symm
        · exact Or.inr hv.symm
      · have hd : d = 1 := Fin.ext h'
        subst hd
        intro i j
        exact absurd rfl hcd

/-! ### The criterion discharge

Both core theorems below take the two extracted cycles, their evenness, the *decomposition* of
each cycle into "the ear plus the closing arc" (as edge predicates `CE`/`QE` for `X = C ∪ q`,
`PE`/`VE` for `Y = P ∪ v`), the freshness of the ears against each other and against the
closing arc, and the arrangement datum `harr` (the two closing arcs meet exactly in the listed
S-to-R component paths).  From these they derive `hcov` and contradict `hSR`. -/

/-- **Core of Lemma A.6 Case 2, two-component form.**  See `lemmaA6_case2_oneComponent` for
the single-component variant. -/
theorem lemmaA6_case2_twoComponents (N : Network S) (hSR : N.TrueSRStrongCriterion)
    {m n L₁ L₂ : ℕ} (X : N.TrueSRCycle m) (Y : N.TrueSRCycle n)
    (c₁ : N.TrueSRPath L₁) (c₂ : N.TrueSRPath L₂)
    (CE QE PE VE : N.TrueSREdge → Prop)
    (hXE : X.Even) (hYE : Y.Even)
    (hdecX : ∀ e, X.ContainsEdge e ↔ (CE e ∨ QE e))
    (hdecY : ∀ e, Y.ContainsEdge e ↔ (PE e ∨ VE e))
    (hCP : ∀ e, ¬ (CE e ∧ PE e))
    (hCV : ∀ e, ¬ (CE e ∧ VE e))
    (hQP : ∀ e, ¬ (QE e ∧ PE e))
    (harr : ∀ e, QE e ∧ VE e ↔ (c₁.HasEdge e ∨ c₂.HasEdge e))
    (hsep : ∀ i j, ¬ (c₁.edge i).ShareVertex (c₂.edge j)) :
    False := by
  have hcov : ∀ f, X.ContainsEdge f → Y.ContainsEdge f →
      (c₁.HasEdge f ∨ c₂.HasEdge f) := by
    intro f hfX hfY
    rcases (hdecX f).1 hfX with hCE | hQE
    · rcases (hdecY f).1 hfY with hPE | hVE
      · exact absurd ⟨hCE, hPE⟩ (hCP f)
      · exact absurd ⟨hCE, hVE⟩ (hCV f)
    · rcases (hdecY f).1 hfY with hPE | hVE
      · exact absurd ⟨hQE, hPE⟩ (hQP f)
      · exact (harr f).1 ⟨hQE, hVE⟩
  refine hSR.2 X Y hXE hYE ⟨?_⟩
  exact TrueSRCycle.sToRIntersectionOfTwoPaths X Y c₁ c₂
    (fun i => (hdecX (c₁.edge i)).2 (Or.inr ((harr (c₁.edge i)).2
      (Or.inl ⟨i, TrueSREdge.SameIncidence.refl _⟩)).1))
    (fun i => (hdecY (c₁.edge i)).2 (Or.inr ((harr (c₁.edge i)).2
      (Or.inl ⟨i, TrueSREdge.SameIncidence.refl _⟩)).2))
    (fun i => (hdecX (c₂.edge i)).2 (Or.inr ((harr (c₂.edge i)).2
      (Or.inr ⟨i, TrueSREdge.SameIncidence.refl _⟩)).1))
    (fun i => (hdecY (c₂.edge i)).2 (Or.inr ((harr (c₂.edge i)).2
      (Or.inr ⟨i, TrueSREdge.SameIncidence.refl _⟩)).2))
    hcov hsep

/-- **Core of Lemma A.6 Case 2, single-component form.**  The variant used when the two
closing arcs meet in one S-to-R path (the alternating orders of Fig. 8), discharged through
`no_shared_path_of_trueSRCriterion`. -/
theorem lemmaA6_case2_oneComponent (N : Network S) (hSR : N.TrueSRStrongCriterion)
    {m n L : ℕ} (X : N.TrueSRCycle m) (Y : N.TrueSRCycle n) (c₁ : N.TrueSRPath L)
    (CE QE PE VE : N.TrueSREdge → Prop)
    (hXE : X.Even) (hYE : Y.Even)
    (hdecX : ∀ e, X.ContainsEdge e ↔ (CE e ∨ QE e))
    (hdecY : ∀ e, Y.ContainsEdge e ↔ (PE e ∨ VE e))
    (hCP : ∀ e, ¬ (CE e ∧ PE e))
    (hCV : ∀ e, ¬ (CE e ∧ VE e))
    (hQP : ∀ e, ¬ (QE e ∧ PE e))
    (harr : ∀ e, QE e ∧ VE e ↔ c₁.HasEdge e) :
    False := by
  have hcov : ∀ f, X.ContainsEdge f → Y.ContainsEdge f →
      ∃ i, f.SameIncidence (c₁.edge i) := by
    intro f hfX hfY
    rcases (hdecX f).1 hfX with hCE | hQE
    · rcases (hdecY f).1 hfY with hPE | hVE
      · exact absurd ⟨hCE, hPE⟩ (hCP f)
      · exact absurd ⟨hCE, hVE⟩ (hCV f)
    · rcases (hdecY f).1 hfY with hPE | hVE
      · exact absurd ⟨hQE, hPE⟩ (hQP f)
      · exact (harr f).1 ⟨hQE, hVE⟩
  exact no_shared_path_of_trueSRCriterion N hSR X Y hXE hYE c₁
    (fun i => (hdecX (c₁.edge i)).2 (Or.inr ((harr (c₁.edge i)).2
      (⟨i, TrueSREdge.SameIncidence.refl _⟩ : c₁.HasEdge (c₁.edge i))).1))
    (fun i => (hdecY (c₁.edge i)).2 (Or.inr ((harr (c₁.edge i)).2
      (⟨i, TrueSREdge.SameIncidence.refl _⟩ : c₁.HasEdge (c₁.edge i))).2))
    hcov

end CRNT.Network
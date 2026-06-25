import CRNT.Analysis.SpernerNHandshake
import CRNT.Analysis.SpernerNFacetCount
import CRNT.Analysis.SpernerNDoor

/-!
# Interior door facets always have a neighbour

The geometric crux of the n-dimensional Sperner handshake. An interior-chain door incidence — a door
facet dropping vertex `m` with `0 < m < n+1` — is always *flip valid*: the adjacent-transposition flip
stays inside the nonnegative orthant, so the facet genuinely borders a second cell.

The proof is by contradiction. If the flip were invalid, the only coordinate that can go negative is
`a := (σ m).succ`, and invalidity forces `(v_{m-1})_a = 0`. A coordinate-count argument then shows that
coordinate `a` vanishes on *every* vertex of the facet (it equals `1` only at the dropped vertex `m`),
so the whole door facet lies on the coordinate face `{x_a = 0}`. But `a ≠ last` (it is a `castSucc`),
contradicting `door_face_eq_last`: a door facet on a coordinate face lies on the face opposite the top
color. Hence the flip is valid.

Depends on: `CRNT.Analysis.SpernerNHandshake`, `CRNT.Analysis.SpernerNFacetCount`,
`CRNT.Analysis.SpernerNDoor`.
-/

namespace CRNT.Analysis.SpernerN

open scoped BigOperators
open Finset

variable {n N : ℕ}

/-- **The flip offset at the dropped vertex.** The flip swaps permutation positions `m-1` and `m`;
only the dropped vertex `m` changes, and its offset is the original offset with the step `σ(m-1)`
replaced by the step `σ(m)`. -/
theorem voff_flipPerm_self (σ : Equiv.Perm (Fin n)) (m : Fin (n + 1)) (hm0 : 0 < (m : ℕ))
    (hmn : (m : ℕ) < n) (i : Fin (n + 1)) :
    voff (flipPerm σ m hm0 hmn) m i
      = voff σ m i - root (σ ⟨(m : ℕ) - 1, by omega⟩) i + root (σ ⟨(m : ℕ), hmn⟩) i := by
  classical
  set A : Fin n := ⟨(m : ℕ) - 1, by omega⟩ with hAdef
  set B : Fin n := ⟨(m : ℕ), hmn⟩ with hBdef
  set F : Finset (Fin n) := Finset.univ.filter (fun l : Fin n => (l : ℕ) < (m : ℕ)) with hFdef
  have key : voff (flipPerm σ m hm0 hmn) m i
      = ∑ l ∈ F, root (σ (Equiv.swap A B l)) i := by
    simp only [voff, flipPerm, Equiv.Perm.mul_apply, hFdef, hAdef, hBdef]
  rw [key]
  have hAmem : A ∈ F := by
    simp only [hFdef, hAdef, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  rw [← Finset.add_sum_erase _ _ hAmem, Equiv.swap_apply_left]
  have herase : ∑ l ∈ F.erase A, root (σ (Equiv.swap A B l)) i
      = ∑ l ∈ F.erase A, root (σ l) i := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mem_erase] at hl
    have hlA : l ≠ A := hl.1
    have hlval : (l : ℕ) < (m : ℕ) := by
      have := hl.2; rw [hFdef, Finset.mem_filter] at this; exact this.2
    have hlB : l ≠ B := by rw [hBdef]; intro h; rw [h] at hlval; simp at hlval
    rw [Equiv.swap_apply_of_ne_of_ne hlA hlB]
  rw [herase]
  have hvoff : voff σ m i = root (σ A) i + ∑ l ∈ F.erase A, root (σ l) i := by
    rw [voff, ← hFdef]; exact (Finset.add_sum_erase _ _ hAmem).symm
  rw [hvoff]; ring

/-- **G1 — interior door facets are flip valid.** A door incidence `(c, m)` with `0 < m < n+1` always
satisfies the flip-validity condition: the door's color structure forbids the facet from lying on a
coordinate face other than `x_last = 0`, so the flipped vertex stays in the orthant. -/
theorem flipValid_of_doorFacet (col : SpernerColoring (n + 1) N) (c : Cell (n + 1) N)
    (m : Fin (n + 2)) (h0 : 0 < (m : ℕ)) (hn : (m : ℕ) < n + 1)
    (hdoor : IsDoorFacet col c m) :
    FlipValid c m h0 hn := by
  classical
  set σ := c.perm with hσ
  set M : ℕ := (m : ℕ) with hM
  -- the two permutation positions and the candidate negative coordinate
  set A : Fin (n + 1) := ⟨M - 1, by omega⟩ with hAdef
  set B : Fin (n + 1) := ⟨M, hn⟩ with hBdef
  set a : Fin (n + 2) := (σ B).succ with hadef
  -- vertex indices m-1 and m+1
  have hm_eq : m = A.succ := by apply Fin.ext; simp [hAdef]; omega
  set mm1 : Fin (n + 2) := A.castSucc with hmm1def
  have hBcast : B.castSucc = m := by
    apply Fin.ext
    have hb : (B.castSucc : ℕ) = M := by rw [Fin.val_castSucc]
    omega
  set mp1 : Fin (n + 2) := B.succ with hmp1def
  have eA : (⟨(m : ℕ) - 1, by omega⟩ : Fin (n + 1)) = A := rfl
  have eB : (⟨(m : ℕ), hn⟩ : Fin (n + 1)) = B := rfl
  -- the flipped vertex value, as g i
  have hg : ∀ i, (c.base i : ℤ) + voff (flipPerm σ m h0 hn) m i
      = ((c.vertex mm1).1 i : ℤ) + root (σ B) i := by
    intro i
    rw [voff_flipPerm_self σ m h0 hn i, eA, eB]
    -- voff σ m i - voff σ mm1 i = root (σ A) i, via voff_step at A
    have hstepA : voff σ m i - voff σ mm1 i = root (σ A) i := by
      have := voff_step σ A i
      rw [← hm_eq] at this; rw [← hmm1def] at this; linarith [this]
    have hvm : ((c.vertex m).1 i : ℤ) = (c.base i : ℤ) + voff σ m i := c.vertex_val m i
    have hvmm1 : ((c.vertex mm1).1 i : ℤ) = (c.base i : ℤ) + voff σ mm1 i := c.vertex_val mm1 i
    linarith [hstepA, hvm, hvmm1]
  -- suppose not flip valid
  by_contra hnv
  rw [FlipValid] at hnv
  simp only [not_forall, not_le] at hnv
  obtain ⟨i0, hi0⟩ := hnv
  rw [hg i0] at hi0
  -- the only coordinate that can be negative is a
  have hroot_le : root (σ B) i0 ≥ -1 := by rw [root]; split_ifs <;> omega
  have hvmm1_nn : (0 : ℤ) ≤ ((c.vertex mm1).1 i0 : ℤ) := Int.natCast_nonneg _
  have hi0a : i0 = a := by
    by_contra hne
    have hnsucc : ¬ i0 = (σ B).succ := by rw [← hadef]; exact hne
    have hrz : root (σ B) i0 = 0 ∨ root (σ B) i0 = 1 := by
      rw [root]
      by_cases h1 : i0 = (σ B).castSucc
      · right; rw [if_pos h1, if_neg hnsucc]; ring
      · left; rw [if_neg h1, if_neg hnsucc]; ring
    rcases hrz with hr | hr <;> rw [hr] at hi0 <;> omega
  subst hi0a
  -- so (v_{mm1})_a = 0  and root (σ B) a = -1
  have hrootBa : root (σ B) a = -1 := by
    have hcast : ¬ (a = (σ B).castSucc) := by
      rw [hadef]; intro h
      have := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at this; omega
    rw [root, if_neg hcast, if_pos hadef]; ring
  have hva0 : ((c.vertex mm1).1 a : ℤ) = 0 := by
    have := hi0; rw [hrootBa] at this; omega
  -- step relations at A and B to pin root (σ A) a = 1
  have hvalmp1 : (0 : ℤ) ≤ ((c.vertex mp1).1 a : ℤ) := Int.natCast_nonneg _
  have hstepB : ((c.vertex mp1).1 a : ℤ) - ((c.vertex m).1 a : ℤ) = root (σ B) a := by
    have := voff_step σ B a
    rw [← hmp1def, hBcast] at this
    have h1 : ((c.vertex mp1).1 a : ℤ) = (c.base a : ℤ) + voff σ mp1 a := c.vertex_val mp1 a
    have h2 : ((c.vertex m).1 a : ℤ) = (c.base a : ℤ) + voff σ m a := c.vertex_val m a
    linarith [this, h1, h2]
  have hvm_ge1 : (1 : ℤ) ≤ ((c.vertex m).1 a : ℤ) := by
    rw [hrootBa] at hstepB; linarith [hvalmp1, hstepB]
  have hstepA2 : ((c.vertex m).1 a : ℤ) - ((c.vertex mm1).1 a : ℤ) = root (σ A) a := by
    have := voff_step σ A a
    rw [← hm_eq, ← hmm1def] at this
    have h1 : ((c.vertex m).1 a : ℤ) = (c.base a : ℤ) + voff σ m a := c.vertex_val m a
    have h2 : ((c.vertex mm1).1 a : ℤ) = (c.base a : ℤ) + voff σ mm1 a := c.vertex_val mm1 a
    linarith [this, h1, h2]
  have hrootAa : root (σ A) a = 1 := by
    have hle : root (σ A) a ≤ 1 := by rw [root]; split_ifs <;> omega
    have hva : ((c.vertex m).1 a : ℤ) = root (σ A) a := by rw [hva0] at hstepA2; linarith [hstepA2]
    omega
  -- from root (σ A) a = 1 :  a = (σ A).castSucc, hence a.val = (σ A).val ≤ n, so a ≠ last
  have haA : a = (σ A).castSucc := by
    by_contra h
    rw [root, if_neg h] at hrootAa
    split_ifs at hrootAa <;> omega
  have ha_val : (a : ℕ) = (σ A : ℕ) := by rw [haA, Fin.val_castSucc]
  have ha_ne_last : a ≠ Fin.last (n + 1) := by
    intro h
    have : (a : ℕ) = n + 1 := by rw [h, Fin.val_last]
    have hlt : (σ A : ℕ) < n + 1 := (σ A).isLt
    omega
  -- the per-position root formula along coordinate a
  have hrootl : ∀ l : Fin (n + 1),
      root (σ l) a = (if l = A then (1 : ℤ) else 0) - (if l = B then (1 : ℤ) else 0) := by
    intro l
    have hc : (a = (σ l).castSucc) ↔ l = A := by
      constructor
      · intro h
        exact σ.injective (Fin.castSucc_injective _ (by rw [← h, ← haA]))
      · intro h; rw [h, ← haA]
    have hs : (a = (σ l).succ) ↔ l = B := by
      constructor
      · intro h
        exact σ.injective (Fin.succ_injective _ (by rw [← h, hadef]))
      · intro h; rw [h, hadef]
    rw [root]
    congr 1
    · exact if_congr hc rfl rfl
    · exact if_congr hs rfl rfl
  -- the closed form for voff along a
  have hAval : (A : ℕ) = M - 1 := rfl
  have hBval : (B : ℕ) = M := rfl
  have hvoffa : ∀ k : Fin (n + 2),
      voff σ k a = (if M - 1 < (k : ℕ) then (1 : ℤ) else 0) - (if M < (k : ℕ) then (1 : ℤ) else 0) := by
    intro k
    rw [voff, Finset.sum_congr rfl (fun l _ => hrootl l), Finset.sum_sub_distrib,
      Finset.sum_ite_eq' (Finset.univ.filter (fun l : Fin (n + 1) => (l : ℕ) < (k : ℕ))) A (fun _ => (1 : ℤ)),
      Finset.sum_ite_eq' (Finset.univ.filter (fun l : Fin (n + 1) => (l : ℕ) < (k : ℕ))) B (fun _ => (1 : ℤ))]
    have hAm : (A ∈ Finset.univ.filter (fun l : Fin (n + 1) => (l : ℕ) < (k : ℕ))) ↔ M - 1 < (k : ℕ) := by
      rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and, hAval]
    have hBm : (B ∈ Finset.univ.filter (fun l : Fin (n + 1) => (l : ℕ) < (k : ℕ))) ↔ M < (k : ℕ) := by
      rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and, hBval]
    rw [if_congr hAm rfl rfl, if_congr hBm rfl rfl]
  -- base coordinate a is 0
  have hmm1val : (mm1 : ℕ) = M - 1 := by rw [hmm1def, Fin.val_castSucc, hAval]
  have hba0 : (c.base a : ℤ) = 0 := by
    have h1 : ((c.vertex mm1).1 a : ℤ) = (c.base a : ℤ) + voff σ mm1 a := c.vertex_val mm1 a
    rw [hvoffa mm1, hmm1val, hva0,
      if_neg (by omega : ¬ M - 1 < M - 1), if_neg (by omega : ¬ M < M - 1)] at h1
    linarith [h1]
  -- coordinate a vanishes on every facet vertex
  have hface : ∀ p ∈ facetVerts c m, p.1 a = 0 := by
    intro p hp
    rw [facetVerts, Finset.mem_image] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [Finset.mem_erase] at hk
    have hkne : k ≠ m := hk.1
    have hkval : (k : ℕ) ≠ M := fun h => hkne (Fin.ext (by rw [hM] at h; exact h))
    have hcoord : ((c.vertex k).1 a : ℤ) = 0 := by
      have h1 : ((c.vertex k).1 a : ℤ) = (c.base a : ℤ) + voff σ k a := c.vertex_val k a
      rw [hvoffa k, hba0] at h1
      have hkv : (k : ℕ) < M ∨ M < (k : ℕ) := by omega
      rcases hkv with hlt | hgt
      · simp only [if_neg (by omega : ¬ M - 1 < (k : ℕ)), if_neg (by omega : ¬ M < (k : ℕ))] at h1
        linarith [h1]
      · simp only [if_pos (by omega : M - 1 < (k : ℕ)), if_pos hgt] at h1
        linarith [h1]
    have : ((c.vertex k).1 a : ℤ) = ((0 : ℕ) : ℤ) := by rw [hcoord]; simp
    exact_mod_cast this
  -- contradiction with door_face_eq_last
  have hlast : a = Fin.last (n + 1) := door_face_eq_last c m col a hdoor hface
  exact ha_ne_last hlast

end CRNT.Analysis.SpernerN

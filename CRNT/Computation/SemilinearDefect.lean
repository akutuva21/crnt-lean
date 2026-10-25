import CRNT.Computation.Semilinear
import CRNT.Computation.StableComputation
import Mathlib.Data.Nat.Prime.Basic

/-!
# The two ways the repository's `Semilinear` misses the Chen–Doty–Soloveichik class

Leaf **C2** of `docs/field-map.md` records as open "the full Chen–Doty–Soloveichik theorem
(every semilinear function is stably computable, and every stably computable function is
semilinear)" for the predicate `CRNT.Computation.Semilinear`.  This module shows that neither
direction can hold for that predicate, nor for its natural repair, so the target has to be
restated with Presburger-semilinear functions (linear inequalities *and congruences*).

## 1. `Semilinear` is too weak: it accepts every finitely-valued function

`Semilinear f` asks for a finite list of pairs (region, affine map) such that every point lies in
*some* region on which `f` equals the paired affine map **at that point**.  The regions may
overlap, and `f` is not required to agree with an affine map on a whole region.  Hence every
function whose values lie, pointwise, in a fixed finite list of constants is `Semilinear`
(`semilinear_of_finite_values`), for instance the indicator of the primes
(`semilinear_prime_indicator`).  Under the classical theorem (stably decidable predicates are
semilinear sets, Angluin–Aspnes–Eisenstat 2007), the prime indicator is not stably computable, so
"every `Semilinear` function is stably computable" is false.

## 2. The repair without congruences is too strong: parity

The natural repair, `SemilinearStrict` (each affine map agrees with `f` on its whole region, and
the regions cover `ℕ^d`), excludes the parity function `n ↦ n % 2`: every region of `ℕ` cut out
by linear inequalities is eventually constant in membership (`LinFormula.eventually_const`), so a
strictly semilinear function of one variable is eventually affine, and parity is not
(`not_semilinearStrict_parity`).  But parity is stably computable, by `X → Y`, `2Y → ∅`
(`parityCRN_stablyComputes`).  So "every stably computable function is `SemilinearStrict`" is also
false (`parity_counterexample`).

Both failures disappear for Presburger-semilinear functions, whose regions may also use
congruences `a · x ≡ b (mod m)`; that is the class of the Chen–Doty–Soloveichik theorem.
-/

namespace CRNT

namespace Computation

/-! ## 1. Finitely-valued functions are `Semilinear` -/

/-- The always-true linear formula `0 · x ≤ 0`. -/
def LinFormula.tt (d : ℕ) : LinFormula d := .le (fun _ => 0) 0

theorem LinFormula.tt_satisfied {d : ℕ} (x : Fin d → ℕ) : (LinFormula.tt d).Satisfied x := by
  simp [LinFormula.tt, LinFormula.Satisfied]

/-- The constant affine map `c`. -/
def Affine.constMap (d : ℕ) (c : ℕ) : Affine d := ⟨c, fun _ => 0⟩

theorem Affine.constMap_eval {d : ℕ} (c : ℕ) (x : Fin d → ℕ) : (Affine.constMap d c).eval x = c := by
  simp [Affine.constMap, Affine.eval]

/-- **Every function with values in a finite list is `Semilinear`.** -/
theorem semilinear_of_finite_values {d : ℕ} (f : (Fin d → ℕ) → ℕ) (vals : List ℕ)
    (h : ∀ x, f x ∈ vals) : Semilinear f := by
  refine ⟨vals.map (fun c => (LinFormula.tt d, Affine.constMap d c)), fun x => ?_⟩
  refine ⟨(LinFormula.tt d, Affine.constMap d (f x)), List.mem_map.mpr ⟨f x, h x, rfl⟩,
    LinFormula.tt_satisfied x, ?_⟩
  rw [Affine.constMap_eval]

/-- **Every `{0, 1}`-valued function is `Semilinear`**, whatever the underlying set. -/
theorem semilinear_indicator {d : ℕ} (P : (Fin d → ℕ) → Prop) [DecidablePred P] :
    Semilinear (fun x => if P x then 1 else 0) :=
  semilinear_of_finite_values _ [0, 1] (fun x => by split_ifs <;> simp)

/-- **The indicator of the primes is `Semilinear`.** -/
theorem semilinear_prime_indicator :
    Semilinear (fun v : Fin 1 → ℕ => if Nat.Prime (v 0) then 1 else 0) :=
  semilinear_indicator (fun v : Fin 1 → ℕ => Nat.Prime (v 0))

/-! ## 2. The strict repair and the parity function -/

/-- **Strictly semilinear**: finitely many (region, affine map) pairs, the regions cover `ℕ^d`,
and `f` agrees with each affine map on the *whole* of its region. -/
def SemilinearStrict {d : ℕ} (f : (Fin d → ℕ) → ℕ) : Prop :=
  ∃ pieces : List (LinFormula d × Affine d),
    (∀ x, ∃ p ∈ pieces, p.1.Satisfied x) ∧ ∀ p ∈ pieces, ∀ x, p.1.Satisfied x → f x = p.2.eval x

theorem SemilinearStrict.semilinear {d : ℕ} {f : (Fin d → ℕ) → ℕ} (h : SemilinearStrict f) :
    Semilinear f := by
  obtain ⟨pieces, hcov, hagree⟩ := h
  refine ⟨pieces, fun x => ?_⟩
  obtain ⟨p, hp, hsat⟩ := hcov x
  exact ⟨p, hp, hsat, hagree p hp x hsat⟩

/-- The point `n` of `ℕ¹`. -/
def pt1 (n : ℕ) : Fin 1 → ℕ := fun _ => n

theorem dotZ_pt1 (a : Fin 1 → ℤ) (n : ℕ) : dotZ a (pt1 n) = a 0 * (n : ℤ) := by
  simp [dotZ, pt1]

theorem eval_pt1 (A : Affine 1) (n : ℕ) : A.eval (pt1 n) = A.const + A.coeff 0 * n := by
  simp [Affine.eval, pt1]

/-- An inequality `a n ≤ b` is eventually constant in `n`. -/
theorem le_eventually_const (a b : ℤ) :
    ∃ N : ℕ, ∃ q : Prop, ∀ n : ℕ, N ≤ n → (a * (n : ℤ) ≤ b ↔ q) := by
  refine ⟨b.natAbs + 1, ?_⟩
  have hb1 : b ≤ (b.natAbs : ℤ) := by first | exact Int.le_natAbs | omega
  have hb2 : -(b.natAbs : ℤ) ≤ b := by
    first
      | omega
      | (have h := Int.le_natAbs (a := -b); rw [Int.natAbs_neg] at h; linarith)
  rcases lt_trichotomy a 0 with ha | ha | ha
  · refine ⟨True, fun n hn => ?_⟩
    have hn' : (b.natAbs : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
    have ha1 : a ≤ -1 := by omega
    have h1 : a * (n : ℤ) ≤ -1 * (n : ℤ) :=
      mul_le_mul_of_nonneg_right ha1 (by positivity)
    simp only [iff_true]
    linarith
  · refine ⟨0 ≤ b, fun n _ => ?_⟩
    rw [ha, zero_mul]
  · refine ⟨False, fun n hn => ?_⟩
    have hn' : (b.natAbs : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
    have ha1 : 1 ≤ a := by omega
    have h1 : 1 * (n : ℤ) ≤ a * (n : ℤ) :=
      mul_le_mul_of_nonneg_right ha1 (by positivity)
    simp only [iff_false, not_le]
    linarith

/-- An inequality `b ≤ a n` is eventually constant in `n`. -/
theorem ge_eventually_const (a b : ℤ) :
    ∃ N : ℕ, ∃ q : Prop, ∀ n : ℕ, N ≤ n → (b ≤ a * (n : ℤ) ↔ q) := by
  obtain ⟨N, q, h⟩ := le_eventually_const (-a) (-b)
  refine ⟨N, q, fun n hn => ?_⟩
  rw [← h n hn]
  constructor <;> intro h' <;> linarith

/-- **Regions of `ℕ` cut out by linear inequalities are eventually constant in membership.** -/
theorem LinFormula.eventually_const (φ : LinFormula 1) :
    ∃ N : ℕ, ∃ q : Prop, ∀ n : ℕ, N ≤ n → (φ.Satisfied (pt1 n) ↔ q) := by
  induction φ with
  | le a b =>
      obtain ⟨N, q, h⟩ := le_eventually_const (a 0) b
      exact ⟨N, q, fun n hn => by simp only [LinFormula.Satisfied, dotZ_pt1]; exact h n hn⟩
  | ge a b =>
      obtain ⟨N, q, h⟩ := ge_eventually_const (a 0) b
      exact ⟨N, q, fun n hn => by simp only [LinFormula.Satisfied, dotZ_pt1]; exact h n hn⟩
  | not φ ih =>
      obtain ⟨N, q, h⟩ := ih
      exact ⟨N, ¬ q, fun n hn => by simp only [LinFormula.Satisfied]; exact not_congr (h n hn)⟩
  | and φ ψ ih₁ ih₂ =>
      obtain ⟨N₁, q₁, h₁⟩ := ih₁
      obtain ⟨N₂, q₂, h₂⟩ := ih₂
      exact ⟨max N₁ N₂, q₁ ∧ q₂, fun n hn => by
        simp only [LinFormula.Satisfied]
        exact and_congr (h₁ n ((max_le_iff.mp hn).1)) (h₂ n ((max_le_iff.mp hn).2))⟩
  | or φ ψ ih₁ ih₂ =>
      obtain ⟨N₁, q₁, h₁⟩ := ih₁
      obtain ⟨N₂, q₂, h₂⟩ := ih₂
      exact ⟨max N₁ N₂, q₁ ∨ q₂, fun n hn => by
        simp only [LinFormula.Satisfied]
        exact or_congr (h₁ n ((max_le_iff.mp hn).1)) (h₂ n ((max_le_iff.mp hn).2))⟩

/-- A common threshold for finitely many formulas. -/
theorem list_eventually_const (pieces : List (LinFormula 1 × Affine 1)) :
    ∃ N : ℕ, ∀ p ∈ pieces, ∃ q : Prop, ∀ n : ℕ, N ≤ n → (p.1.Satisfied (pt1 n) ↔ q) := by
  induction pieces with
  | nil => exact ⟨0, fun p hp => by simp at hp⟩
  | cons a t ih =>
      obtain ⟨N₁, h₁⟩ := ih
      obtain ⟨N₀, q₀, h₀⟩ := LinFormula.eventually_const a.1
      refine ⟨max N₀ N₁, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hpt
      · exact ⟨q₀, fun n hn => h₀ n ((max_le_iff.mp hn).1)⟩
      · obtain ⟨q, hq⟩ := h₁ p hpt
        exact ⟨q, fun n hn => hq n ((max_le_iff.mp hn).2)⟩

/-- **Parity is not strictly semilinear.** -/
theorem not_semilinearStrict_parity : ¬ SemilinearStrict (fun v : Fin 1 → ℕ => v 0 % 2) := by
  rintro ⟨pieces, hcov, hagree⟩
  obtain ⟨N, hN⟩ := list_eventually_const pieces
  obtain ⟨M, hM⟩ : ∃ M, M = N + 1 := ⟨_, rfl⟩
  obtain ⟨p, hp, hsat⟩ := hcov (pt1 (2 * M))
  obtain ⟨q, hq⟩ := hN p hp
  have hqtrue : q := (hq (2 * M) (by omega)).mp hsat
  have hsat' : p.1.Satisfied (pt1 (2 * M + 1)) := (hq (2 * M + 1) (by omega)).mpr hqtrue
  have e0 : (2 * M) % 2 = p.2.const + p.2.coeff 0 * (2 * M) := by
    have h := hagree p hp (pt1 (2 * M)) hsat
    rw [eval_pt1] at h
    exact h
  have e1 : (2 * M + 1) % 2 = p.2.const + p.2.coeff 0 * (2 * M + 1) := by
    have h := hagree p hp (pt1 (2 * M + 1)) hsat'
    rw [eval_pt1] at h
    exact h
  -- `0 = c + e (2M)` forces `c = 0` and `e = 0`, and then `1 = c + e (2M + 1) = 0`.
  have hc : p.2.const = 0 := by omega
  have hprod : p.2.coeff 0 * (2 * M) = 0 := by omega
  have he : p.2.coeff 0 = 0 := by
    rcases Nat.mul_eq_zero.mp hprod with h | h
    · exact h
    · omega
  rw [hc, he, zero_mul] at e1
  omega

/-- **The parity network** `X → Y`, `2Y → ∅` (species `0 = X`, `1 = Y`). -/
def parityCRN : Network (Fin 2) :=
  finNetwork (fun i : Fin 2 => if i = 0 then ⟨![1, 0], ![0, 1]⟩ else ⟨![0, 2], ![0, 0]⟩)

/-- **The parity network stably computes `n % 2`.**  Every step lowers `2·#X + #Y`, the parity of
`#X + #Y` is invariant, and a terminal configuration has no `X` and at most one `Y`. -/
theorem parityCRN_stablyComputes : StablyComputes parityCRN init₁ 1 (fun n => n % 2) := by
  refine stablyComputes_of_terminating _ _ _ _ (fun c => 2 * c 0 + c 1) ?_ ?_
  · rintro c c' ⟨r, hr, rfl⟩
    have h0 := hr 0
    have h1 := hr 1
    fin_cases r <;> simp_all [parityCRN, finNetwork, fire] <;> omega
  · intro n c hc hterm
    have inv := reach_invariant parityCRN (fun c => (c 0 + c 1) % 2 = n % 2) (by
        rintro c c' ⟨r, hr, rfl⟩ h
        have h0 := hr 0
        have h1 := hr 1
        fin_cases r <;> simp_all [parityCRN, finNetwork, fire] <;> omega) hc (by simp [init₁])
    have ht0 := hterm ((0 : Fin 2) : parityCRN.R)
    have ht1 := hterm ((1 : Fin 2) : parityCRN.R)
    simp only [Applicable, parityCRN, finNetwork, not_forall, not_le] at ht0 ht1
    obtain ⟨s, hs⟩ := ht0
    obtain ⟨s', hs'⟩ := ht1
    show c 1 = n % 2
    fin_cases s <;> fin_cases s' <;> simp at hs hs' <;> omega

/-- **A stably computable function that is not strictly semilinear.**  Together with
`semilinear_prime_indicator`, this shows that the Chen–Doty–Soloveichik characterization holds
neither for `Semilinear` nor for `SemilinearStrict`; it needs congruences. -/
theorem parity_counterexample :
    StablyComputes parityCRN init₁ 1 (fun n => n % 2) ∧
      ¬ SemilinearStrict (fun v : Fin 1 → ℕ => v 0 % 2) :=
  ⟨parityCRN_stablyComputes, not_semilinearStrict_parity⟩

/-! ## 3. Every modulus: `n mod m` -/

/-- **The modulus network** `X → Y`, `m Y → ∅` (species `0 = X`, `1 = Y`). -/
def modCRN (m : ℕ) : Network (Fin 2) :=
  finNetwork (fun i : Fin 2 => if i = 0 then ⟨![1, 0], ![0, 1]⟩ else ⟨![0, m], ![0, 0]⟩)

theorem modCRN_fire0 (m : ℕ) (c : Config (Fin 2)) :
    fire (modCRN m) (0 : Fin 2) c = ![c 0 - 1, c 1 + 1] := by
  funext i; fin_cases i <;> simp [fire, modCRN, finNetwork]

theorem modCRN_fire1 (m : ℕ) (c : Config (Fin 2)) :
    fire (modCRN m) (1 : Fin 2) c = ![c 0, c 1 - m] := by
  funext i; fin_cases i <;> simp [fire, modCRN, finNetwork]

theorem modCRN_app0 (m : ℕ) (c : Config (Fin 2)) (h : Applicable (modCRN m) (0 : Fin 2) c) :
    1 ≤ c 0 := by
  have := h 0; simpa [modCRN, finNetwork] using this

theorem modCRN_app1 (m : ℕ) (c : Config (Fin 2)) (h : Applicable (modCRN m) (1 : Fin 2) c) :
    m ≤ c 1 := by
  have := h 1; simpa [modCRN, finNetwork] using this

/-- The potential `2 #X + #Y` decreases along every step (for `m ≥ 1`). -/
theorem modCRN_step_lt (m : ℕ) (hm : 1 ≤ m) (c c' : Config (Fin 2))
    (h : Step (modCRN m) c c') : 2 * c' 0 + c' 1 < 2 * c 0 + c 1 := by
  obtain ⟨r, hr, rfl⟩ := h
  fin_cases r
  · have h0 := modCRN_app0 m c hr
    show 2 * fire (modCRN m) (0 : Fin 2) c 0 + fire (modCRN m) (0 : Fin 2) c 1 < 2 * c 0 + c 1
    rw [modCRN_fire0]; simp; omega
  · have h1 := modCRN_app1 m c hr
    show 2 * fire (modCRN m) (1 : Fin 2) c 0 + fire (modCRN m) (1 : Fin 2) c 1 < 2 * c 0 + c 1
    rw [modCRN_fire1]; simp; omega

/-- The residue of `#X + #Y` modulo `m` is invariant. -/
theorem modCRN_step_inv (m n : ℕ) (c c' : Config (Fin 2)) (h : Step (modCRN m) c c')
    (hc : (c 0 + c 1) % m = n % m) : (c' 0 + c' 1) % m = n % m := by
  obtain ⟨r, hr, rfl⟩ := h
  fin_cases r
  · have h0 := modCRN_app0 m c hr
    show (fire (modCRN m) (0 : Fin 2) c 0 + fire (modCRN m) (0 : Fin 2) c 1) % m = n % m
    rw [modCRN_fire0]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [show c 0 - 1 + (c 1 + 1) = c 0 + c 1 by omega]
    exact hc
  · have h1 := modCRN_app1 m c hr
    show (fire (modCRN m) (1 : Fin 2) c 0 + fire (modCRN m) (1 : Fin 2) c 1) % m = n % m
    rw [modCRN_fire1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h1
    rw [hk, Nat.add_sub_cancel_left]
    rw [hk, show c 0 + (m + k) = c 0 + k + m by ring, Nat.add_mod_right] at hc
    exact hc

/-- **The modulus network stably computes `n mod m`** for every `m ≥ 1`. -/
theorem modCRN_stablyComputes (m : ℕ) (hm : 1 ≤ m) :
    StablyComputes (modCRN m) init₁ 1 (fun n => n % m) := by
  refine stablyComputes_of_terminating _ _ _ _ (fun c => 2 * c 0 + c 1)
    (fun c c' h => modCRN_step_lt m hm c c' h) ?_
  intro n c hc hterm
  have inv := reach_invariant (modCRN m) (fun c => (c 0 + c 1) % m = n % m)
    (fun c c' h hP => modCRN_step_inv m n c c' h hP) hc (by simp [init₁])
  have ht0 := hterm ((0 : Fin 2) : (modCRN m).R)
  have ht1 := hterm ((1 : Fin 2) : (modCRN m).R)
  have hc0 : c 0 = 0 := by
    by_contra hne
    exact ht0 fun s => by
      fin_cases s <;> simp [modCRN, finNetwork] <;> omega
  have hc1 : c 1 < m := by
    by_contra hge
    exact ht1 fun s => by
      fin_cases s <;> simp [modCRN, finNetwork] <;> omega
  show c 1 = n % m
  rw [hc0, zero_add, Nat.mod_eq_of_lt hc1] at inv
  exact inv

/-- **`n mod m` is not strictly semilinear** for `m ≥ 2`. -/
theorem not_semilinearStrict_mod (m : ℕ) (hm : 2 ≤ m) :
    ¬ SemilinearStrict (fun v : Fin 1 → ℕ => v 0 % m) := by
  rintro ⟨pieces, hcov, hagree⟩
  obtain ⟨N, hN⟩ := list_eventually_const pieces
  obtain ⟨M, hM⟩ : ∃ M, M = N + 1 := ⟨_, rfl⟩
  have hmM : N ≤ m * M := by
    have : M ≤ m * M := Nat.le_mul_of_pos_left M (by omega)
    omega
  obtain ⟨p, hp, hsat⟩ := hcov (pt1 (m * M))
  obtain ⟨q, hq⟩ := hN p hp
  have hqtrue : q := (hq (m * M) hmM).mp hsat
  have hsat' : p.1.Satisfied (pt1 (m * M + 1)) := (hq (m * M + 1) (by omega)).mpr hqtrue
  have e0 : (m * M) % m = p.2.const + p.2.coeff 0 * (m * M) := by
    have h := hagree p hp (pt1 (m * M)) hsat
    rw [eval_pt1] at h
    exact h
  have e1 : (m * M + 1) % m = p.2.const + p.2.coeff 0 * (m * M + 1) := by
    have h := hagree p hp (pt1 (m * M + 1)) hsat'
    rw [eval_pt1] at h
    exact h
  have h0m : (m * M) % m = 0 := Nat.mul_mod_right m M
  have h1m : (m * M + 1) % m = 1 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [h0m] at e0
  rw [h1m] at e1
  have hc : p.2.const = 0 := by omega
  have hprod : p.2.coeff 0 * (m * M) = 0 := by omega
  have he : p.2.coeff 0 = 0 := by
    rcases Nat.mul_eq_zero.mp hprod with h | h
    · exact h
    · rcases Nat.mul_eq_zero.mp h with h' | h' <;> omega
  rw [hc, he, zero_mul] at e1
  omega

end Computation

end CRNT

#print axioms CRNT.Computation.semilinear_prime_indicator
#print axioms CRNT.Computation.not_semilinearStrict_parity
#print axioms CRNT.Computation.parityCRN_stablyComputes
#print axioms CRNT.Computation.parity_counterexample
#print axioms CRNT.Computation.modCRN_stablyComputes
#print axioms CRNT.Computation.not_semilinearStrict_mod

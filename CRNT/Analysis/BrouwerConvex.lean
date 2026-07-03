import CRNT.Analysis.SpernerBrouwerN

/-!
# Brouwer on the cube and the Poincaré–Miranda theorem

Two analytic corollaries of the `n`-dimensional Brouwer fixed-point theorem
`SpernerN.brouwer_stdSimplex_fin`:

* `brouwer_cube` — every continuous self-map of the unit cube `Set.Icc 0 1 ⊆ Fin n → ℝ` has a fixed
  point. Proved by transporting Brouwer from the standard simplex: the affine map
  `cornerOfSimplex y = (n · y_{castSucc i})ᵢ` carries `stdSimplex ℝ (Fin (n+1))` onto the *corner
  simplex* `{x ≥ 0, ∑ ≤ n}`, which contains the cube, with one-sided inverse `simplexOfCorner`.
  Composing with the coordinatewise clamp into `[0,1]` gives a self-map of the simplex whose Brouwer
  fixed point lands, by the clamp, inside the cube and is fixed by the original map.
* `poincare_miranda` — a continuous map `f` on the cube whose `i`-th component is `≤ 0` on the face
  `xᵢ = 0` and `≥ 0` on the face `xᵢ = 1` has a zero. Proved from `brouwer_cube` applied to
  `x ↦ clamp (x - f x)`: a fixed point forces, coordinatewise, `f x i = 0`, the boundary sign
  conditions ruling out the clamped (face) alternatives.

Depends on: `CRNT.Analysis.SpernerBrouwerN`.
-/

namespace CRNT.Analysis

open Set Finset
open scoped BigOperators

namespace BrouwerCube

variable {n : ℕ}

/-! ### The coordinatewise clamp into `[0,1]` -/

/-- Coordinatewise clamp of a point into the unit cube `[0,1]`. -/
def clamp (x : Fin n → ℝ) : Fin n → ℝ := fun i => max 0 (min 1 (x i))

theorem clamp_mem (x : Fin n → ℝ) : clamp x ∈ Icc (0 : Fin n → ℝ) 1 := by
  rw [Set.mem_Icc]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · simp only [clamp, Pi.zero_apply]; exact le_max_left _ _
  · simp only [clamp, Pi.one_apply]
    exact max_le zero_le_one (min_le_left 1 (x i))

theorem clamp_eq_self {x : Fin n → ℝ} (hx : x ∈ Icc (0 : Fin n → ℝ) 1) : clamp x = x := by
  rw [Set.mem_Icc] at hx
  funext i
  have h0 : 0 ≤ x i := hx.1 i
  have h1 : x i ≤ 1 := hx.2 i
  simp only [clamp]
  rw [min_eq_right h1, max_eq_right h0]

theorem continuous_clamp : Continuous (clamp : (Fin n → ℝ) → (Fin n → ℝ)) :=
  continuous_pi fun i => continuous_const.max (continuous_const.min (continuous_apply i))

/-! ### The affine correspondence with the corner simplex -/

/-- The affine surjection from the standard simplex onto the corner simplex `{x ≥ 0, ∑ ≤ n}`:
scale by `n` and drop the last barycentric coordinate. -/
def cornerOfSimplex (n : ℕ) (y : Fin (n + 1) → ℝ) : Fin n → ℝ := fun i => (n : ℝ) * y i.castSucc

/-- The one-sided inverse: divide by `n` and append the slack coordinate `1 - ∑ xᵢ/n`. -/
noncomputable def simplexOfCorner (n : ℕ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (fun i => x i / (n : ℝ)) (1 - ∑ i, x i / (n : ℝ))

theorem continuous_cornerOfSimplex : Continuous (cornerOfSimplex n) :=
  continuous_pi fun _ => continuous_const.mul (continuous_apply _)

theorem continuous_simplexOfCorner : Continuous (simplexOfCorner n) :=
  Continuous.finSnoc
    (continuous_pi fun i => (continuous_apply i).div_const _)
    (continuous_const.sub (continuous_finsetSum _ fun i _ => (continuous_apply i).div_const _))

/-- `cornerOfSimplex` is a left inverse of `simplexOfCorner` (when `n ≠ 0`). -/
theorem cornerOfSimplex_simplexOfCorner (hn : (n : ℝ) ≠ 0) (x : Fin n → ℝ) :
    cornerOfSimplex n (simplexOfCorner n x) = x := by
  funext i
  simp only [cornerOfSimplex, simplexOfCorner, Fin.snoc_castSucc]
  field_simp

/-- `simplexOfCorner` maps the cube into the standard simplex. -/
theorem simplexOfCorner_mem {x : Fin n → ℝ} (hx : x ∈ Icc (0 : Fin n → ℝ) 1) :
    simplexOfCorner n x ∈ stdSimplex ℝ (Fin (n + 1)) := by
  rw [Set.mem_Icc] at hx
  have hsum_le : ∑ i, x i / (n : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hncast : (0 : ℝ) < n := by exact_mod_cast hn
      have hne : (n : ℝ) ≠ 0 := ne_of_gt hncast
      calc ∑ i, x i / (n : ℝ) ≤ ∑ _i : Fin n, (1 : ℝ) / (n : ℝ) :=
            Finset.sum_le_sum fun i _ => by gcongr; exact hx.2 i
        _ = 1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
              div_self hne]
  refine ⟨fun j => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [simplexOfCorner, Fin.snoc_last]
      linarith [hsum_le]
    · simp only [simplexOfCorner, Fin.snoc_castSucc]
      exact div_nonneg (hx.1 i) (Nat.cast_nonneg n)
  · simp only [simplexOfCorner]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring

end BrouwerCube

open BrouwerCube

/-! ### Brouwer on the cube -/

/-- **Brouwer on the unit cube.** Every continuous self-map of `Set.Icc 0 1 ⊆ Fin n → ℝ` has a fixed
point. -/
theorem brouwer_cube {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf : ContinuousOn f (Icc 0 1)) (hmaps : MapsTo f (Icc (0 : Fin n → ℝ) 1) (Icc 0 1)) :
    ∃ x ∈ Icc (0 : Fin n → ℝ) 1, f x = x := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- dimension zero: the cube is a single point and `Fin 0 → ℝ` is a subsingleton
    subst hn0
    exact ⟨0, by simp [Set.mem_Icc], Subsingleton.elim _ _⟩
  · have hncast : (n : ℝ) ≠ 0 := by positivity
    -- `f ∘ clamp` is continuous everywhere (clamp lands in the cube)
    have hfc_cont : Continuous (fun z => f (clamp z)) :=
      hf.comp_continuous continuous_clamp clamp_mem
    -- the induced self-map of the simplex
    have hg_maps : ∀ y : ↥(stdSimplex ℝ (Fin (n + 1))),
        simplexOfCorner n (f (clamp (cornerOfSimplex n y.1))) ∈ stdSimplex ℝ (Fin (n + 1)) :=
      fun y => simplexOfCorner_mem (hmaps (clamp_mem (cornerOfSimplex n y.1)))
    set g : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1))) :=
      fun y => ⟨simplexOfCorner n (f (clamp (cornerOfSimplex n y.1))), hg_maps y⟩ with hg
    have hg_cont : Continuous g := by
      apply Continuous.subtype_mk
      exact continuous_simplexOfCorner.comp
        (hfc_cont.comp (continuous_cornerOfSimplex.comp continuous_subtype_val))
    obtain ⟨y, hy⟩ := SpernerN.brouwer_stdSimplex_fin n g hg_cont
    have hyval : simplexOfCorner n (f (clamp (cornerOfSimplex n y.1))) = y.1 :=
      congrArg Subtype.val hy
    have hkey : f (clamp (cornerOfSimplex n y.1)) = cornerOfSimplex n y.1 := by
      have h := cornerOfSimplex_simplexOfCorner hncast (f (clamp (cornerOfSimplex n y.1)))
      rw [hyval] at h
      exact h.symm
    have hx0mem : cornerOfSimplex n y.1 ∈ Icc (0 : Fin n → ℝ) 1 := by
      rw [← hkey]; exact hmaps (clamp_mem _)
    have hclampeq : clamp (cornerOfSimplex n y.1) = cornerOfSimplex n y.1 := clamp_eq_self hx0mem
    refine ⟨cornerOfSimplex n y.1, hx0mem, ?_⟩
    rw [hclampeq] at hkey
    exact hkey

/-! ### Poincaré–Miranda -/

/-- **The Poincaré–Miranda theorem.** A continuous map `f` on the unit cube whose `i`-th component is
nonpositive on the face `xᵢ = 0` and nonnegative on the face `xᵢ = 1`, for every `i`, has a zero in
the cube. -/
theorem poincare_miranda {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf : ContinuousOn f (Icc 0 1))
    (hlo : ∀ x ∈ Icc (0 : Fin n → ℝ) 1, ∀ i, x i = 0 → f x i ≤ 0)
    (hhi : ∀ x ∈ Icc (0 : Fin n → ℝ) 1, ∀ i, x i = 1 → 0 ≤ f x i) :
    ∃ x ∈ Icc (0 : Fin n → ℝ) 1, f x = 0 := by
  -- the clamped displacement map `g x = clamp (x - f x)` is a continuous self-map of the cube
  set g : (Fin n → ℝ) → (Fin n → ℝ) := fun x => clamp (x - f x) with hg
  have hg_cont : ContinuousOn g (Icc 0 1) :=
    continuous_clamp.comp_continuousOn (continuousOn_id.sub hf)
  have hg_maps : MapsTo g (Icc (0 : Fin n → ℝ) 1) (Icc 0 1) := fun x _ => clamp_mem _
  obtain ⟨x, hxmem, hfix⟩ := brouwer_cube g hg_cont hg_maps
  refine ⟨x, hxmem, ?_⟩
  rw [Set.mem_Icc] at hxmem
  funext i
  -- the fixed-point identity at coordinate `i`: `clamp (x i - f x i) = x i`
  have hi : max 0 (min 1 (x i - f x i)) = x i := by
    have h := congrFun hfix i
    simpa [hg, clamp, Pi.sub_apply] using h
  have h0 : 0 ≤ x i := hxmem.1 i
  have h1 : x i ≤ 1 := hxmem.2 i
  simp only [Pi.zero_apply]
  -- rule out the two clamped (boundary) cases using the sign conditions
  rcases lt_or_ge (x i - f x i) 0 with hneg | hpos
  · -- clamp pins to `0`, forcing `x i = 0`; then `hlo` gives `f x i ≤ 0`, contradicting `f x i > 0`
    rw [min_eq_right (by linarith : x i - f x i ≤ 1), max_eq_left (le_of_lt hneg)] at hi
    have hxi0 : x i = 0 := hi.symm
    have hflo : f x i ≤ 0 := hlo x (Set.mem_Icc.mpr ⟨hxmem.1, hxmem.2⟩) i hxi0
    rw [hxi0] at hneg
    linarith
  · rcases lt_or_ge (x i - f x i) 1 with hlt | hge
    · -- interior case: `clamp` is the identity, so `x i - f x i = x i`, giving `f x i = 0`
      rw [min_eq_right (le_of_lt hlt), max_eq_right hpos] at hi
      linarith
    · -- clamp pins to `1`, forcing `x i = 1`; `hhi` gives `0 ≤ f x i`, and `x i - f x i ≥ 1` gives
      -- `f x i ≤ 0`, so `f x i = 0`
      rw [min_eq_left hge, max_eq_right zero_le_one] at hi
      have hxi1 : x i = 1 := hi.symm
      have hfhi : 0 ≤ f x i := hhi x (Set.mem_Icc.mpr ⟨hxmem.1, hxmem.2⟩) i hxi1
      rw [hxi1] at hge
      linarith

end CRNT.Analysis

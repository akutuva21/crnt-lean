import CRNT.Design.AntitheticFoster
import CRNT.Stochastic.ExpSqrtDrift

/-!
# Geometric ergodicity of the antithetic closed loop

This module proves the item that leaf **C3** of `docs/field-map.md` records as open:

> "what remains is the geometric ergodicity of that network, which the obstruction shows needs a
> genuinely new Lyapunov function."

The antithetic integral controller closed around a production–degradation plant
(`CRNT.Antithetic.closedLoop`, species `Z₁, Z₂, X`, reactions `∅ → Z₁`, `Z₁ + Z₂ → ∅`,
`Z₁ → Z₁ + X`, `X → ∅`, `X → X + Z₂`) is **geometrically ergodic for every choice of positive
rate constants** (`CRNT.Antithetic.Geometric.closedLoop_geometric_ergodic`).

## Why the earlier candidates fail and what replaces them

The repository's piecewise quadratic Lyapunov function `lyap` has the Foster drift
`Q lyap ≤ −fLyap + cK` (`CRNT.Antithetic.drift_lyap_le`) with
`fLyap = ε (x² + |q| + (q⁺)² + x |q| + z₁ z₂ (z₁ + z₂ − 1))`, `q = z₁ − z₂`.  On the line
`z₁ = 0` the dissipation is only *linear* in `z₂` while `lyap` is *quadratic*, so no constant
`c > 0` gives `Q lyap ≤ −c lyap + K` (`CRNT.Antithetic.lyap_no_exponential_drift`), and every
function affine in `z₂` above the diagonal fails as well
(`CRNT.Antithetic.wLyapSlope_no_exponential_drift`).  Dynamically: on `z₁ = 0` the charge `q` can
only increase through the reference reaction `∅ → Z₁` at the constant rate `μ`, so the return time
from `q = −m` is of order `m`, and a geometric drift certificate must grow *exponentially* in `m`.

The new Lyapunov function is the exponential–square-root tilt

`W = exp (a √(1 + lyap))`,

for a small `a > 0`.  The general transfer theorem `CRNT.JumpSystem.exists_expSqrt_drift` needs
three facts about `lyap`, all proved here:

1. **jumps of order `√lyap`** (`jump_sq_le`): every enabled reaction changes `lyap` by at most
   `cD (1 + |q| + x + min(z₁, z₂))`, and `lyap ≥ c₀ (q² + x² + min(z₁, z₂)²)`
   (`CRNT.Antithetic.lyap_ge`), so the change is at most `cL √(1 + lyap)`;
2. **absolute flux controlled by the dissipation** (`sum_rate_abs_inc_le`):
   `∑ᵣ λᵣ |Δᵣ lyap| ≤ cM (fLyap + 1)`, reaction by reaction against the terms of `fLyap`;
3. **dissipation dominating `√lyap`** (`coer_le`): `lyap ≤ cMax (fLyap/ε + 1)²`.

On the line `z₁ = 0`, `√lyap` is linear in `z₂`, so the linear dissipation suffices: the
square root converts the quadratic-versus-linear mismatch into a linear-versus-linear one, and
the exponential converts the resulting constant negative drift of `√lyap` into a geometric drift
of `W`.
-/

namespace CRNT
namespace Antithetic
namespace Geometric

open Network

variable (κ : closedLoop.RateConstants)

/-! ## Constants -/

/-- The jump constant: every enabled reaction changes `lyap` by at most
`cD (1 + |q| + x + min(z₁, z₂))`. -/
noncomputable def cD : ℝ := 2 * cA κ + 2 * cb κ + cc κ + 2 * cd κ

/-- The coercivity constant of `lyap` (as in `CRNT.Antithetic.lyap_finite`). -/
noncomputable def c₀ : ℝ := min (min (cB κ / 4) (32 / 3 * θ κ ^ 2)) (cd κ)

/-- The square-root jump constant. -/
noncomputable def cL : ℝ := 2 * cD κ * (1 + 1 / c₀ κ)

/-- The raw absolute-flux constant (against `1 + fLyap / ε`). -/
noncomputable def cMraw : ℝ :=
  3 * μ κ * cD κ + η κ * cd κ + kk κ * (3 * cb κ + cc κ) + γ κ * (3 * cb κ + cc κ) +
    θ κ * (3 * cA κ + cc κ + cd κ)

/-- The absolute-flux constant (against `fLyap + 1`). -/
noncomputable def cM : ℝ := cMraw κ * (1 + 1 / cε κ)

/-- The sum of the coefficients of `lyap`. -/
noncomputable def cMax : ℝ := cA κ + cb κ + cc κ + cd κ

/-- The square-root dissipation constant. -/
noncomputable def cεs : ℝ := cε κ / (1 + cMax κ)

/-- All rate-derived coefficients are positive. -/
theorem coeffs_pos :
    0 < cA κ ∧ 0 < cB κ ∧ 0 < cb κ ∧ 0 < cc κ ∧ 0 < cd κ := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  refine ⟨cA_pos κ, ?_, ?_, ?_, ?_⟩
  · unfold cB; positivity
  · unfold cb; positivity
  · unfold cc; positivity
  · unfold cd; positivity

theorem cD_pos : 0 < cD κ := by
  obtain ⟨hA, -, hb, hcc, hd⟩ := coeffs_pos κ
  unfold cD; positivity

theorem c₀_pos : 0 < c₀ κ := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  obtain ⟨-, hB, -, -, hd⟩ := coeffs_pos κ
  unfold c₀
  exact lt_min (lt_min (by positivity) (by positivity)) hd

theorem cL_nonneg : 0 ≤ cL κ := by
  have := cD_pos κ; have := c₀_pos κ
  unfold cL; positivity

theorem cMraw_nonneg : 0 ≤ cMraw κ := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  obtain ⟨hA, -, hb, hcc, hd⟩ := coeffs_pos κ
  have := cD_pos κ
  unfold cMraw; positivity

theorem cM_nonneg : 0 ≤ cM κ := by
  have := cMraw_nonneg κ; have := cε_pos κ
  unfold cM; positivity

theorem cMax_pos : 0 < cMax κ := by
  obtain ⟨hA, -, hb, hcc, hd⟩ := coeffs_pos κ
  unfold cMax; positivity

theorem cεs_pos : 0 < cεs κ := by
  have := cε_pos κ; have := cMax_pos κ
  unfold cεs; positivity

/-! ## The increments of `lyap` -/

theorem inc0 (n : Fin 3 → ℕ) :
    lyap κ (closedLoop.jumpNextCount n (0 : Fin 5)) - lyap κ n =
      (phi κ (n 0 + 1) (n 1) - phi κ (n 0) (n 1)) - cc κ * (n 2 : ℝ) + cd κ * (n 1 : ℝ) := by
  obtain ⟨a, b, c⟩ := next0 n
  unfold lyap; rw [a, b, c]; push_cast; ring

theorem inc1 (n : Fin 3 → ℕ) (h0 : 0 < n 0) (h1 : 0 < n 1) :
    lyap κ (closedLoop.jumpNextCount n (1 : Fin 5)) - lyap κ n =
      cd κ * (1 - (n 0 : ℝ) - (n 1 : ℝ)) := by
  obtain ⟨a, b, c⟩ := next1 n
  unfold lyap; rw [a, b, c]
  have hphi : phi κ (n 0 - 1) (n 1 - 1) = phi κ (n 0) (n 1) := by
    unfold phi
    have hiff : n 1 - 1 ≤ n 0 - 1 ↔ n 1 ≤ n 0 := by omega
    rw [Nat.cast_sub h0, Nat.cast_sub h1]
    simp only [hiff]
    split_ifs <;> ring
  rw [hphi, Nat.cast_sub h0, Nat.cast_sub h1]; push_cast; ring

theorem inc2 (n : Fin 3 → ℕ) (h0 : 0 < n 0) :
    lyap κ (closedLoop.jumpNextCount n (2 : Fin 5)) - lyap κ n =
      cb κ * (2 * (n 2 : ℝ) + 1) - cc κ * ((n 0 : ℝ) - n 1) := by
  obtain ⟨a, b, c⟩ := next2 n
  have ha : n 0 - 1 + 1 = n 0 := by omega
  unfold lyap; rw [a, b, c, ha]; push_cast; ring

theorem inc3 (n : Fin 3 → ℕ) (h2 : 0 < n 2) :
    lyap κ (closedLoop.jumpNextCount n (3 : Fin 5)) - lyap κ n =
      cb κ * (1 - 2 * (n 2 : ℝ)) + cc κ * ((n 0 : ℝ) - n 1) := by
  obtain ⟨a, b, c⟩ := next3 n
  unfold lyap; rw [a, b, c, Nat.cast_sub h2]; push_cast; ring

theorem inc4 (n : Fin 3 → ℕ) (h2 : 0 < n 2) :
    lyap κ (closedLoop.jumpNextCount n (4 : Fin 5)) - lyap κ n =
      (phi κ (n 0) (n 1 + 1) - phi κ (n 0) (n 1)) + cc κ * (n 2 : ℝ) + cd κ * (n 0 : ℝ) := by
  obtain ⟨a, b, c⟩ := next4 n
  have hc : n 2 - 1 + 1 = n 2 := by omega
  unfold lyap; rw [a, b, c, hc]; push_cast; ring

/-! ## Elementary bounds -/

theorem abs_phi_succ_left_le (z1 z2 : ℕ) :
    |phi κ (z1 + 1) z2 - phi κ z1 z2| ≤ cA κ * (2 * |(z1 : ℝ) - z2| + 1) := by
  rw [phi_succ_left, abs_mul]
  obtain ⟨hA, hB, -, -, -⟩ := coeffs_pos κ
  have hBA := cB_le_cA κ
  have hc : |(if z2 ≤ z1 then cA κ else cB κ)| ≤ cA κ := by
    split_ifs
    · exact (abs_of_pos hA).le
    · rw [abs_of_pos hB]; exact hBA
  have hq : |2 * ((z1 : ℝ) - z2) + 1| ≤ 2 * |(z1 : ℝ) - z2| + 1 := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le ((z1 : ℝ) - z2)]
    · linarith [le_abs_self ((z1 : ℝ) - z2)]
  exact mul_le_mul hc hq (abs_nonneg _) hA.le

theorem abs_phi_succ_right_le (z1 z2 : ℕ) :
    |phi κ z1 (z2 + 1) - phi κ z1 z2| ≤ cA κ * (2 * |(z1 : ℝ) - z2| + 1) := by
  rw [phi_succ_right, abs_mul]
  obtain ⟨hA, hB, -, -, -⟩ := coeffs_pos κ
  have hBA := cB_le_cA κ
  have hc : |(if z2 + 1 ≤ z1 then cA κ else cB κ)| ≤ cA κ := by
    split_ifs
    · exact (abs_of_pos hA).le
    · rw [abs_of_pos hB]; exact hBA
  have hq : |1 - 2 * ((z1 : ℝ) - z2)| ≤ 2 * |(z1 : ℝ) - z2| + 1 := by
    rw [abs_le]
    constructor
    · linarith [le_abs_self ((z1 : ℝ) - z2)]
    · linarith [neg_abs_le ((z1 : ℝ) - z2)]
  exact mul_le_mul hc hq (abs_nonneg _) hA.le

/-- The square of the minimum is at most the product. -/
theorem min_sq_le_prod (z1 z2 : ℕ) :
    ((min z1 z2 : ℕ) : ℝ) ^ 2 ≤ (z1 : ℝ) * z2 := by
  have h1 : ((min z1 z2 : ℕ) : ℝ) ≤ z1 := by exact_mod_cast min_le_left _ _
  have h2 : ((min z1 z2 : ℕ) : ℝ) ≤ z2 := by exact_mod_cast min_le_right _ _
  have h0 : (0 : ℝ) ≤ ((min z1 z2 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [sq]; exact mul_le_mul h1 h2 h0 (Nat.cast_nonneg _)

/-- The bounds of the terms of `fRaw` used below. -/
theorem fRaw_bounds (n : Fin 3 → ℕ) :
    0 ≤ fRaw n ∧ |(n 0 : ℝ) - n 1| ≤ fRaw n ∧ (n 2 : ℝ) ^ 2 ≤ fRaw n ∧ (n 2 : ℝ) ≤ fRaw n ∧
      (n 2 : ℝ) * |(n 0 : ℝ) - n 1| ≤ fRaw n ∧
      (n 0 : ℝ) * (n 1 : ℝ) ≤ fRaw n ∧
      ((min (n 0) (n 1) : ℕ) : ℝ) ≤ fRaw n ∧ (n 0 : ℝ) ≤ fRaw n ∧
      (n 0 : ℝ) * |(n 0 : ℝ) - n 1| ≤ fRaw n ∧ (n 2 : ℝ) * (n 0 : ℝ) ≤ fRaw n := by
  have hF0 := fRaw_nonneg n
  have hP := annih_nonneg (n 0) (n 1)
  have hsq : 0 ≤ (max ((n 0 : ℝ) - n 1) 0) ^ 2 := sq_nonneg _
  have hxq : 0 ≤ (n 2 : ℝ) * |(n 0 : ℝ) - n 1| := by positivity
  have hx2 : 0 ≤ (n 2 : ℝ) ^ 2 := sq_nonneg _
  have hqa := abs_nonneg ((n 0 : ℝ) - n 1)
  have hfq : |(n 0 : ℝ) - n 1| ≤ fRaw n := by unfold fRaw; linarith
  have hfx2 : (n 2 : ℝ) ^ 2 ≤ fRaw n := by unfold fRaw; linarith
  have hfx : (n 2 : ℝ) ≤ fRaw n := (cast_le_sq (n 2)).trans hfx2
  have hfxq : (n 2 : ℝ) * |(n 0 : ℝ) - n 1| ≤ fRaw n := by unfold fRaw; linarith
  have hfP : (n 0 : ℝ) * (n 1 : ℝ) * ((n 0 : ℝ) + n 1 - 1) ≤ fRaw n := by unfold fRaw; linarith
  have hfprod : (n 0 : ℝ) * (n 1 : ℝ) ≤ fRaw n := (prod_le_annih (n 0) (n 1)).trans hfP
  have hfm : ((min (n 0) (n 1) : ℕ) : ℝ) ≤ fRaw n :=
    ((cast_le_cube _).trans (min_cube_le (n 0) (n 1))).trans hfP
  have hfqP : |(n 0 : ℝ) - n 1| + (n 0 : ℝ) * (n 1 : ℝ) * ((n 0 : ℝ) + n 1 - 1) ≤ fRaw n := by
    unfold fRaw; linarith
  have hfz1 : (n 0 : ℝ) ≤ fRaw n := (z_le (n 0) (n 1)).trans hfqP
  have hfz : (max ((n 0 : ℝ) - n 1) 0) ^ 2 + (n 0 : ℝ) * (n 1 : ℝ) * ((n 0 : ℝ) + n 1 - 1) ≤
      fRaw n := by unfold fRaw; linarith
  have hfz1q : (n 0 : ℝ) * |(n 0 : ℝ) - n 1| ≤ fRaw n := (z1_abs_le (n 0) (n 1)).trans hfz
  -- `x z₁ ≤ x (m + |q|) ≤ x² + m² + x |q| ≤ x² + P + x |q| ≤ fRaw`
  have hxz1 : (n 2 : ℝ) * (n 0 : ℝ) ≤ fRaw n := by
    obtain ⟨c1, -⟩ := coord_le_min_add (n 0) (n 1)
    have hx0 : (0 : ℝ) ≤ n 2 := Nat.cast_nonneg _
    have hm0 : (0 : ℝ) ≤ ((min (n 0) (n 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have e1 : (n 2 : ℝ) * (n 0 : ℝ) ≤
        (n 2 : ℝ) * ((min (n 0) (n 1) : ℕ) : ℝ) + (n 2 : ℝ) * |(n 0 : ℝ) - n 1| := by
      have := mul_le_mul_of_nonneg_left c1 hx0
      linarith
    have e2 : (n 2 : ℝ) * ((min (n 0) (n 1) : ℕ) : ℝ) ≤
        (n 2 : ℝ) ^ 2 + ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((n 2 : ℝ) - ((min (n 0) (n 1) : ℕ) : ℝ)), sq_nonneg (n 2 : ℝ),
        sq_nonneg ((min (n 0) (n 1) : ℕ) : ℝ)]
    have e3 := min_sq_le_prod (n 0) (n 1)
    have e4 := prod_le_annih (n 0) (n 1)
    unfold fRaw; linarith
  exact ⟨hF0, hfq, hfx2, hfx, hfxq, hfprod, hfm, hfz1, hfz1q, hxz1⟩

/-! ## 1. Jumps of order `√lyap` -/

theorem jb0 (n : Fin 3 → ℕ) :
    |lyap κ (closedLoop.jumpNextCount n (0 : Fin 5)) - lyap κ n| ≤
      cD κ * (1 + |(n 0 : ℝ) - n 1| + (n 2 : ℝ) + ((min (n 0) (n 1) : ℕ) : ℝ)) := by
  obtain ⟨hA, -, hb, hcc, hd⟩ := coeffs_pos κ
  rw [inc0]
  have hφ := abs_phi_succ_left_le κ (n 0) (n 1)
  have hx0 : (0 : ℝ) ≤ n 2 := Nat.cast_nonneg _
  have hz2 : (0 : ℝ) ≤ n 1 := Nat.cast_nonneg _
  have hq0 := abs_nonneg ((n 0 : ℝ) - n 1)
  have hm0 : (0 : ℝ) ≤ ((min (n 0) (n 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨-, c2⟩ := coord_le_min_add (n 0) (n 1)
  have hB : 0 ≤ cc κ * (n 2 : ℝ) := by positivity
  have hC : 0 ≤ cd κ * (n 1 : ℝ) := by positivity
  have htri : |phi κ (n 0 + 1) (n 1) - phi κ (n 0) (n 1) - cc κ * (n 2 : ℝ) + cd κ * (n 1 : ℝ)| ≤
      |phi κ (n 0 + 1) (n 1) - phi κ (n 0) (n 1)| + cc κ * (n 2 : ℝ) + cd κ * (n 1 : ℝ) := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (phi κ (n 0 + 1) (n 1) - phi κ (n 0) (n 1))]
    · linarith [le_abs_self (phi κ (n 0 + 1) (n 1) - phi κ (n 0) (n 1))]
  have e0 : cA κ ≤ cD κ := by unfold cD; linarith
  have e1 : (2 * cA κ + cd κ) * |(n 0 : ℝ) - n 1| ≤ cD κ * |(n 0 : ℝ) - n 1| :=
    mul_le_mul_of_nonneg_right (by unfold cD; linarith) hq0
  have e2 : cc κ * (n 2 : ℝ) ≤ cD κ * (n 2 : ℝ) :=
    mul_le_mul_of_nonneg_right (by unfold cD; linarith) hx0
  have e3 : cd κ * ((min (n 0) (n 1) : ℕ) : ℝ) ≤ cD κ * ((min (n 0) (n 1) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right (by unfold cD; linarith) hm0
  have e4 : cd κ * (n 1 : ℝ) ≤ cd κ * (((min (n 0) (n 1) : ℕ) : ℝ) + |(n 0 : ℝ) - n 1|) :=
    mul_le_mul_of_nonneg_left c2 hd.le
  linarith [htri, hφ, e0, e1, e2, e3, e4]

theorem jb1 (n : Fin 3 → ℕ) (h0 : 0 < n 0) (h1 : 0 < n 1) :
    |lyap κ (closedLoop.jumpNextCount n (1 : Fin 5)) - lyap κ n| ≤
      cD κ * (1 + |(n 0 : ℝ) - n 1| + (n 2 : ℝ) + ((min (n 0) (n 1) : ℕ) : ℝ)) := by
  obtain ⟨hA, -, hb, hcc, hd⟩ := coeffs_pos κ
  rw [inc1 κ n h0 h1]
  have hz1 : (1 : ℝ) ≤ n 0 := by exact_mod_cast h0
  have hz2 : (1 : ℝ) ≤ n 1 := by exact_mod_cast h1
  have hx0 : (0 : ℝ) ≤ n 2 := Nat.cast_nonneg _
  have hq0 := abs_nonneg ((n 0 : ℝ) - n 1)
  have hm0 : (0 : ℝ) ≤ ((min (n 0) (n 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨c1, c2⟩ := coord_le_min_add (n 0) (n 1)
  rw [abs_mul, abs_of_pos hd, abs_of_nonpos (by linarith)]
  have e1 : 2 * cd κ * |(n 0 : ℝ) - n 1| ≤ cD κ * |(n 0 : ℝ) - n 1| :=
    mul_le_mul_of_nonneg_right (by unfold cD; linarith) hq0
  have e2 : 2 * cd κ * ((min (n 0) (n 1) : ℕ) : ℝ) ≤ cD κ * ((min (n 0) (n 1) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right (by unfold cD; linarith) hm0
  have e3 : cd κ * ((n 0 : ℝ) + n 1) ≤
      cd κ * (2 * ((min (n 0) (n 1) : ℕ) : ℝ) + 2 * |(n 0 : ℝ) - n 1|) :=
    mul_le_mul_of_nonneg_left (by linarith) hd.le
  have e4 : 0 ≤ cD κ * (1 + (n 2 : ℝ)) := by have := cD_pos κ; positivity
  linarith [e1, e2, e3, e4]

theorem jb2 (n : Fin 3 → ℕ) (h0 : 0 < n 0) :
    |lyap κ (closedLoop.jumpNextCount n (2 : Fin 5)) - lyap κ n| ≤
      cD κ * (1 + |(n 0 : ℝ) - n 1| + (n 2 : ℝ) + ((min (n 0) (n 1) : ℕ) : ℝ)) := by
  obtain ⟨hA, -, hb, hcc, hd⟩ := coeffs_pos κ
  rw [inc2 κ n h0]
  have hx0 : (0 : ℝ) ≤ n 2 := Nat.cast_nonneg _
  have hq0 := abs_nonneg ((n 0 : ℝ) - n 1)
  have hm0 : (0 : ℝ) ≤ ((min (n 0) (n 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcq1 : cc κ * ((n 0 : ℝ) - n 1) ≤ cc κ * |(n 0 : ℝ) - n 1| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hcc.le
  have hcq2 : -(cc κ * |(n 0 : ℝ) - n 1|) ≤ cc κ * ((n 0 : ℝ) - n 1) := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le ((n 0 : ℝ) - n 1)) hcc.le
    linarith
  have hb0 : 0 ≤ cb κ * (2 * (n 2 : ℝ) + 1) := by positivity
  have htri : |cb κ * (2 * (n 2 : ℝ) + 1) - cc κ * ((n 0 : ℝ) - n 1)| ≤
      cb κ * (2 * (n 2 : ℝ) + 1) + cc κ * |(n 0 : ℝ) - n 1| := by
    rw [abs_le]; constructor <;> linarith
  have e0 : cb κ ≤ cD κ := by unfold cD; linarith
  have e1 : cc κ * |(n 0 : ℝ) - n 1| ≤ cD κ * |(n 0 : ℝ) - n 1| :=
    mul_le_mul_of_nonneg_right (by unfold cD; linarith) hq0
  have e2 : 2 * cb κ * (n 2 : ℝ) ≤ cD κ * (n 2 : ℝ) :=
    mul_le_mul_of_nonneg_right (by unfold cD; linarith) hx0
  have e3 : 0 ≤ cD κ * ((min (n 0) (n 1) : ℕ) : ℝ) := by have := cD_pos κ; positivity
  linarith [htri, e0, e1, e2, e3]

theorem jb3 (n : Fin 3 → ℕ) (h2 : 0 < n 2) :
    |lyap κ (closedLoop.jumpNextCount n (3 : Fin 5)) - lyap κ n| ≤
      cD κ * (1 + |(n 0 : ℝ) - n 1| + (n 2 : ℝ) + ((min (n 0) (n 1) : ℕ) : ℝ)) := by
  obtain ⟨hA, -, hb, hcc, hd⟩ := coeffs_pos κ
  rw [inc3 κ n h2]
  have hx0 : (0 : ℝ) ≤ n 2 := Nat.cast_nonneg _
  have hq0 := abs_nonneg ((n 0 : ℝ) - n 1)
  have hm0 : (0 : ℝ) ≤ ((min (n 0) (n 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcq1 : cc κ * ((n 0 : ℝ) - n 1) ≤ cc κ * |(n 0 : ℝ) - n 1| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hcc.le
  have hcq2 : -(cc κ * |(n 0 : ℝ) - n 1|) ≤ cc κ * ((n 0 : ℝ) - n 1) := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le ((n 0 : ℝ) - n 1)) hcc.le
    linarith
  have hbx : 0 ≤ cb κ * (n 2 : ℝ) := by positivity
  have htri : |cb κ * (1 - 2 * (n 2 : ℝ)) + cc κ * ((n 0 : ℝ) - n 1)| ≤
      cb κ * (2 * (n 2 : ℝ) + 1) + cc κ * |(n 0 : ℝ) - n 1| := by
    rw [abs_le]; constructor <;> linarith
  have e0 : cb κ ≤ cD κ := by unfold cD; linarith
  have e1 : cc κ * |(n 0 : ℝ) - n 1| ≤ cD κ * |(n 0 : ℝ) - n 1| :=
    mul_le_mul_of_nonneg_right (by unfold cD; linarith) hq0
  have e2 : 2 * cb κ * (n 2 : ℝ) ≤ cD κ * (n 2 : ℝ) :=
    mul_le_mul_of_nonneg_right (by unfold cD; linarith) hx0
  have e3 : 0 ≤ cD κ * ((min (n 0) (n 1) : ℕ) : ℝ) := by have := cD_pos κ; positivity
  linarith [htri, e0, e1, e2, e3]

theorem jb4 (n : Fin 3 → ℕ) (h2 : 0 < n 2) :
    |lyap κ (closedLoop.jumpNextCount n (4 : Fin 5)) - lyap κ n| ≤
      cD κ * (1 + |(n 0 : ℝ) - n 1| + (n 2 : ℝ) + ((min (n 0) (n 1) : ℕ) : ℝ)) := by
  obtain ⟨hA, -, hb, hcc, hd⟩ := coeffs_pos κ
  rw [inc4 κ n h2]
  have hφ := abs_phi_succ_right_le κ (n 0) (n 1)
  have hx0 : (0 : ℝ) ≤ n 2 := Nat.cast_nonneg _
  have hz1 : (0 : ℝ) ≤ n 0 := Nat.cast_nonneg _
  have hq0 := abs_nonneg ((n 0 : ℝ) - n 1)
  have hm0 : (0 : ℝ) ≤ ((min (n 0) (n 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨c1, -⟩ := coord_le_min_add (n 0) (n 1)
  have hB : 0 ≤ cc κ * (n 2 : ℝ) := by positivity
  have hC : 0 ≤ cd κ * (n 0 : ℝ) := by positivity
  have htri : |phi κ (n 0) (n 1 + 1) - phi κ (n 0) (n 1) + cc κ * (n 2 : ℝ) + cd κ * (n 0 : ℝ)| ≤
      |phi κ (n 0) (n 1 + 1) - phi κ (n 0) (n 1)| + cc κ * (n 2 : ℝ) + cd κ * (n 0 : ℝ) := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (phi κ (n 0) (n 1 + 1) - phi κ (n 0) (n 1))]
    · linarith [le_abs_self (phi κ (n 0) (n 1 + 1) - phi κ (n 0) (n 1))]
  have e0 : cA κ ≤ cD κ := by unfold cD; linarith
  have e1 : (2 * cA κ + cd κ) * |(n 0 : ℝ) - n 1| ≤ cD κ * |(n 0 : ℝ) - n 1| :=
    mul_le_mul_of_nonneg_right (by unfold cD; linarith) hq0
  have e2 : cc κ * (n 2 : ℝ) ≤ cD κ * (n 2 : ℝ) :=
    mul_le_mul_of_nonneg_right (by unfold cD; linarith) hx0
  have e3 : cd κ * ((min (n 0) (n 1) : ℕ) : ℝ) ≤ cD κ * ((min (n 0) (n 1) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right (by unfold cD; linarith) hm0
  have e4 : cd κ * (n 0 : ℝ) ≤ cd κ * (((min (n 0) (n 1) : ℕ) : ℝ) + |(n 0 : ℝ) - n 1|) :=
    mul_le_mul_of_nonneg_left c1 hd.le
  linarith [htri, hφ, e0, e1, e2, e3, e4]

/-- Enabledness of the annihilation. -/
theorem en1 (n : Fin 3 → ℕ) (hr : 0 < closedLoop.stochasticMassActionRate κ n (1 : Fin 5)) :
    0 < n 0 ∧ 0 < n 1 := by
  rw [(rate_eq κ n).2.1] at hr
  refine ⟨Nat.pos_of_ne_zero fun h => ?_, Nat.pos_of_ne_zero fun h => ?_⟩ <;> simp [h] at hr

/-- Enabledness of the actuation. -/
theorem en2 (n : Fin 3 → ℕ) (hr : 0 < closedLoop.stochasticMassActionRate κ n (2 : Fin 5)) :
    0 < n 0 := by
  rw [(rate_eq κ n).2.2.1] at hr
  exact Nat.pos_of_ne_zero fun h => by simp [h] at hr

/-- Enabledness of the degradation. -/
theorem en3 (n : Fin 3 → ℕ) (hr : 0 < closedLoop.stochasticMassActionRate κ n (3 : Fin 5)) :
    0 < n 2 := by
  rw [(rate_eq κ n).2.2.2.1] at hr
  exact Nat.pos_of_ne_zero fun h => by simp [h] at hr

/-- Enabledness of the sensing. -/
theorem en4 (n : Fin 3 → ℕ) (hr : 0 < closedLoop.stochasticMassActionRate κ n (4 : Fin 5)) :
    0 < n 2 := by
  rw [(rate_eq κ n).2.2.2.2] at hr
  exact Nat.pos_of_ne_zero fun h => by simp [h] at hr

/-- **Every enabled reaction changes `lyap` by at most `cD (1 + |q| + x + min(z₁, z₂))`.** -/
theorem inc_abs_le (n : Fin 3 → ℕ) (r : Fin 5)
    (hr : 0 < closedLoop.stochasticMassActionRate κ n r) :
    |lyap κ (closedLoop.jumpNextCount n r) - lyap κ n| ≤
      cD κ * (1 + |(n 0 : ℝ) - n 1| + (n 2 : ℝ) + ((min (n 0) (n 1) : ℕ) : ℝ)) := by
  fin_cases r
  · exact jb0 κ n
  · exact jb1 κ n (en1 κ n hr).1 (en1 κ n hr).2
  · exact jb2 κ n (en2 κ n hr)
  · exact jb3 κ n (en3 κ n hr)
  · exact jb4 κ n (en4 κ n hr)

/-- The coercivity of `lyap` in the form used below. -/
theorem lyap_ge_c₀ (n : Fin 3 → ℕ) :
    c₀ κ * (((n 0 : ℝ) - n 1) ^ 2 + (n 2 : ℝ) ^ 2 + ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2) ≤
      lyap κ n := by
  have h := lyap_ge κ n
  have a1 : c₀ κ * ((n 0 : ℝ) - n 1) ^ 2 ≤ cB κ / 4 * ((n 0 : ℝ) - n 1) ^ 2 :=
    mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (sq_nonneg _)
  have a2 : c₀ κ * (n 2 : ℝ) ^ 2 ≤ 32 / 3 * θ κ ^ 2 * (n 2 : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) (sq_nonneg _)
  have a3 : c₀ κ * ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2 ≤ cd κ * ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
  linarith [a1, a2, a3, h]

/-- **The jumps of `lyap` are of order `√lyap`**, in squared form:
`(Δᵣ lyap)² ≤ cL² (1 + lyap)` for every enabled reaction. -/
theorem jump_sq_le (n : Fin 3 → ℕ) (r : Fin 5)
    (hr : 0 < closedLoop.stochasticMassActionRate κ n r) :
    (lyap κ (closedLoop.jumpNextCount n r) - lyap κ n) ^ 2 ≤ cL κ ^ 2 * (1 + lyap κ n) := by
  have hD := cD_pos κ
  have hc0 := c₀_pos κ
  have hlyap := lyap_nonneg κ n
  have h := inc_abs_le κ n r hr
  have hq0 := abs_nonneg ((n 0 : ℝ) - n 1)
  have hx0 : (0 : ℝ) ≤ n 2 := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ ((min (n 0) (n 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 1 + |(n 0 : ℝ) - n 1| + (n 2 : ℝ) + ((min (n 0) (n 1) : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  rw [← hσ] at h
  have hσ0 : 0 ≤ σ := by rw [hσ]; positivity
  -- `δ² ≤ (cD σ)²`
  have h1 : (lyap κ (closedLoop.jumpNextCount n r) - lyap κ n) ^ 2 ≤ (cD κ * σ) ^ 2 := by
    have h' := pow_le_pow_left₀ (abs_nonneg _) h 2
    rwa [sq_abs] at h'
  -- `σ² ≤ 4 (1 + q² + x² + m²)`
  have h2 : σ ^ 2 ≤ 4 * (1 + (((n 0 : ℝ) - n 1) ^ 2 + (n 2 : ℝ) ^ 2 +
      ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2)) := by
    rw [hσ]
    have hsa : |(n 0 : ℝ) - n 1| ^ 2 = ((n 0 : ℝ) - n 1) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (1 - |(n 0 : ℝ) - n 1|), sq_nonneg (1 - (n 2 : ℝ)),
      sq_nonneg (1 - ((min (n 0) (n 1) : ℕ) : ℝ)),
      sq_nonneg (|(n 0 : ℝ) - n 1| - (n 2 : ℝ)),
      sq_nonneg (|(n 0 : ℝ) - n 1| - ((min (n 0) (n 1) : ℕ) : ℝ)),
      sq_nonneg ((n 2 : ℝ) - ((min (n 0) (n 1) : ℕ) : ℝ))]
  -- `q² + x² + m² ≤ lyap / c₀`
  have h3 : ((n 0 : ℝ) - n 1) ^ 2 + (n 2 : ℝ) ^ 2 + ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2 ≤
      1 / c₀ κ * lyap κ n := by
    have hg := lyap_ge_c₀ κ n
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc0]
    linarith
  -- `σ² ≤ 4 (1 + 1/c₀) (1 + lyap)`
  have h4 : σ ^ 2 ≤ 4 * (1 + 1 / c₀ κ) * (1 + lyap κ n) := by
    have hi : 0 ≤ 1 / c₀ κ := by positivity
    have : 1 + 1 / c₀ κ * lyap κ n ≤ (1 + 1 / c₀ κ) * (1 + lyap κ n) := by linarith
    linarith
  -- `cL² ≥ 4 cD² (1 + 1/c₀)`
  have h5 : 4 * cD κ ^ 2 * (1 + 1 / c₀ κ) ≤ cL κ ^ 2 := by
    have hi : 0 ≤ 1 / c₀ κ := by positivity
    unfold cL
    have : (1 + 1 / c₀ κ) ≤ (1 + 1 / c₀ κ) ^ 2 := by nlinarith
    have hD2 : 0 ≤ 4 * cD κ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hD2]
  have h6 : (cD κ * σ) ^ 2 ≤ cD κ ^ 2 * (4 * (1 + 1 / c₀ κ) * (1 + lyap κ n)) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
  have h7 : cD κ ^ 2 * (4 * (1 + 1 / c₀ κ) * (1 + lyap κ n)) ≤ cL κ ^ 2 * (1 + lyap κ n) := by
    have : cD κ ^ 2 * (4 * (1 + 1 / c₀ κ) * (1 + lyap κ n)) =
        (4 * cD κ ^ 2 * (1 + 1 / c₀ κ)) * (1 + lyap κ n) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h5 (by linarith)
  linarith

/-! ## 2. The absolute flux is controlled by the dissipation -/

/-- **The absolute flux of `lyap` is at most `cM (fLyap + 1)`.** -/
theorem sum_rate_abs_inc_le (n : Fin 3 → ℕ) :
    ∑ r, (closedLoop.jumpSystem κ).rate r n *
        |lyap κ ((closedLoop.jumpSystem κ).next r n) - lyap κ n| ≤ cM κ * (fLyap κ n + 1) := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  obtain ⟨hA, -, hb, hcc, hd⟩ := coeffs_pos κ
  have hD := cD_pos κ
  obtain ⟨r0, r1, r2, r3, r4⟩ := rate_eq κ n
  obtain ⟨hF0, hqF, hx2F, hxF, hxqF, hprodF, hmF, hz1F, hz1qF, hxz1F⟩ := fRaw_bounds n
  have hq0 := abs_nonneg ((n 0 : ℝ) - n 1)
  have hx0 : (0 : ℝ) ≤ n 2 := Nat.cast_nonneg _
  have hz10 : (0 : ℝ) ≤ n 0 := Nat.cast_nonneg _
  show ∑ r : closedLoop.R, closedLoop.stochasticMassActionRate κ n r *
      |lyap κ (closedLoop.jumpNextCount n r) - lyap κ n| ≤ _
  change ∑ r : Fin 5, _ ≤ _
  rw [Fin.sum_univ_five]
  -- reference
  have b0 : closedLoop.stochasticMassActionRate κ n (0 : Fin 5) *
      |lyap κ (closedLoop.jumpNextCount n (0 : Fin 5)) - lyap κ n| ≤
      3 * μ κ * cD κ * (1 + fRaw n) := by
    have h := jb0 κ n
    have hσ : 1 + |(n 0 : ℝ) - n 1| + (n 2 : ℝ) + ((min (n 0) (n 1) : ℕ) : ℝ) ≤
        3 * (1 + fRaw n) := by linarith
    rw [r0]
    calc μ κ * |lyap κ (closedLoop.jumpNextCount n (0 : Fin 5)) - lyap κ n|
        ≤ μ κ * (cD κ * (3 * (1 + fRaw n))) := by
          refine mul_le_mul_of_nonneg_left ?_ hμ.le
          exact h.trans (mul_le_mul_of_nonneg_left hσ hD.le)
      _ = 3 * μ κ * cD κ * (1 + fRaw n) := by ring
  -- annihilation
  have b1 : closedLoop.stochasticMassActionRate κ n (1 : Fin 5) *
      |lyap κ (closedLoop.jumpNextCount n (1 : Fin 5)) - lyap κ n| ≤
      η κ * cd κ * (1 + fRaw n) := by
    have hc : 0 ≤ η κ * cd κ * (1 + fRaw n) := mul_nonneg (by positivity) (by linarith)
    rcases Nat.eq_zero_or_pos (n 0) with h0 | h0
    · have : closedLoop.stochasticMassActionRate κ n (1 : Fin 5) = 0 := by rw [r1, h0]; simp
      rw [this, zero_mul]; exact hc
    rcases Nat.eq_zero_or_pos (n 1) with h1 | h1
    · have : closedLoop.stochasticMassActionRate κ n (1 : Fin 5) = 0 := by rw [r1, h1]; simp
      rw [this, zero_mul]; exact hc
    have hz1 : (1 : ℝ) ≤ n 0 := by exact_mod_cast h0
    have hz2 : (1 : ℝ) ≤ n 1 := by exact_mod_cast h1
    have hfP : (n 0 : ℝ) * (n 1 : ℝ) * ((n 0 : ℝ) + n 1 - 1) ≤ fRaw n := by
      unfold fRaw
      have := sq_nonneg (max ((n 0 : ℝ) - n 1) 0)
      have : 0 ≤ (n 2 : ℝ) * |(n 0 : ℝ) - n 1| := by positivity
      have := sq_nonneg (n 2 : ℝ)
      linarith
    rw [r1, inc1 κ n h0 h1, abs_mul, abs_of_pos hd, abs_of_nonpos (by linarith)]
    have e : η κ * (n 0 : ℝ) * (n 1 : ℝ) * (cd κ * -(1 - (n 0 : ℝ) - (n 1 : ℝ))) =
        η κ * cd κ * ((n 0 : ℝ) * (n 1 : ℝ) * ((n 0 : ℝ) + n 1 - 1)) := by ring
    rw [e]
    have hηd : 0 ≤ η κ * cd κ := by positivity
    calc η κ * cd κ * ((n 0 : ℝ) * (n 1 : ℝ) * ((n 0 : ℝ) + n 1 - 1))
        ≤ η κ * cd κ * fRaw n := mul_le_mul_of_nonneg_left hfP hηd
      _ ≤ η κ * cd κ * (1 + fRaw n) := mul_le_mul_of_nonneg_left (by linarith) hηd
  -- actuation
  have b2 : closedLoop.stochasticMassActionRate κ n (2 : Fin 5) *
      |lyap κ (closedLoop.jumpNextCount n (2 : Fin 5)) - lyap κ n| ≤
      kk κ * (3 * cb κ + cc κ) * (1 + fRaw n) := by
    have hc : 0 ≤ kk κ * (3 * cb κ + cc κ) * (1 + fRaw n) :=
      mul_nonneg (by positivity) (by linarith)
    rcases Nat.eq_zero_or_pos (n 0) with h0 | h0
    · have : closedLoop.stochasticMassActionRate κ n (2 : Fin 5) = 0 := by rw [r2, h0]; simp
      rw [this, zero_mul]; exact hc
    rw [r2, inc2 κ n h0]
    have hcq1 : cc κ * ((n 0 : ℝ) - n 1) ≤ cc κ * |(n 0 : ℝ) - n 1| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hcc.le
    have hcq2 : -(cc κ * |(n 0 : ℝ) - n 1|) ≤ cc κ * ((n 0 : ℝ) - n 1) := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le ((n 0 : ℝ) - n 1)) hcc.le
      linarith
    have hb0 : 0 ≤ cb κ * (2 * (n 2 : ℝ) + 1) := by positivity
    have htri : |cb κ * (2 * (n 2 : ℝ) + 1) - cc κ * ((n 0 : ℝ) - n 1)| ≤
        cb κ * (2 * (n 2 : ℝ) + 1) + cc κ * |(n 0 : ℝ) - n 1| := by
      rw [abs_le]; constructor <;> linarith
    have hkz : 0 ≤ kk κ * (n 0 : ℝ) := by positivity
    have p1 : cb κ * ((n 2 : ℝ) * (n 0 : ℝ)) ≤ cb κ * fRaw n :=
      mul_le_mul_of_nonneg_left hxz1F hb.le
    have p2 : cb κ * (n 0 : ℝ) ≤ cb κ * fRaw n := mul_le_mul_of_nonneg_left hz1F hb.le
    have p3 : cc κ * ((n 0 : ℝ) * |(n 0 : ℝ) - n 1|) ≤ cc κ * fRaw n :=
      mul_le_mul_of_nonneg_left hz1qF hcc.le
    have p4 : (3 * cb κ + cc κ) * fRaw n ≤ (3 * cb κ + cc κ) * (1 + fRaw n) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have inner : (n 0 : ℝ) * (cb κ * (2 * (n 2 : ℝ) + 1) + cc κ * |(n 0 : ℝ) - n 1|) ≤
        (3 * cb κ + cc κ) * (1 + fRaw n) := by linarith [p1, p2, p3, p4]
    calc kk κ * (n 0 : ℝ) * |cb κ * (2 * (n 2 : ℝ) + 1) - cc κ * ((n 0 : ℝ) - n 1)|
        ≤ kk κ * (n 0 : ℝ) * (cb κ * (2 * (n 2 : ℝ) + 1) + cc κ * |(n 0 : ℝ) - n 1|) :=
          mul_le_mul_of_nonneg_left htri hkz
      _ = kk κ * ((n 0 : ℝ) * (cb κ * (2 * (n 2 : ℝ) + 1) + cc κ * |(n 0 : ℝ) - n 1|)) := by
          ring
      _ ≤ kk κ * ((3 * cb κ + cc κ) * (1 + fRaw n)) := mul_le_mul_of_nonneg_left inner hk.le
      _ = kk κ * (3 * cb κ + cc κ) * (1 + fRaw n) := by ring
  -- degradation
  have b3 : closedLoop.stochasticMassActionRate κ n (3 : Fin 5) *
      |lyap κ (closedLoop.jumpNextCount n (3 : Fin 5)) - lyap κ n| ≤
      γ κ * (3 * cb κ + cc κ) * (1 + fRaw n) := by
    have hc : 0 ≤ γ κ * (3 * cb κ + cc κ) * (1 + fRaw n) :=
      mul_nonneg (by positivity) (by linarith)
    rcases Nat.eq_zero_or_pos (n 2) with h2 | h2
    · have : closedLoop.stochasticMassActionRate κ n (3 : Fin 5) = 0 := by rw [r3, h2]; simp
      rw [this, zero_mul]; exact hc
    rw [r3, inc3 κ n h2]
    have hcq1 : cc κ * ((n 0 : ℝ) - n 1) ≤ cc κ * |(n 0 : ℝ) - n 1| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hcc.le
    have hcq2 : -(cc κ * |(n 0 : ℝ) - n 1|) ≤ cc κ * ((n 0 : ℝ) - n 1) := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le ((n 0 : ℝ) - n 1)) hcc.le
      linarith
    have hbx : 0 ≤ cb κ * (n 2 : ℝ) := by positivity
    have htri : |cb κ * (1 - 2 * (n 2 : ℝ)) + cc κ * ((n 0 : ℝ) - n 1)| ≤
        cb κ * (2 * (n 2 : ℝ) + 1) + cc κ * |(n 0 : ℝ) - n 1| := by
      rw [abs_le]; constructor <;> linarith
    have hgx : 0 ≤ γ κ * (n 2 : ℝ) := by positivity
    have p1 : cb κ * (n 2 : ℝ) ^ 2 ≤ cb κ * fRaw n := mul_le_mul_of_nonneg_left hx2F hb.le
    have p2 : cb κ * (n 2 : ℝ) ≤ cb κ * fRaw n := mul_le_mul_of_nonneg_left hxF hb.le
    have p3 : cc κ * ((n 2 : ℝ) * |(n 0 : ℝ) - n 1|) ≤ cc κ * fRaw n :=
      mul_le_mul_of_nonneg_left hxqF hcc.le
    have p4 : (3 * cb κ + cc κ) * fRaw n ≤ (3 * cb κ + cc κ) * (1 + fRaw n) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have inner : (n 2 : ℝ) * (cb κ * (2 * (n 2 : ℝ) + 1) + cc κ * |(n 0 : ℝ) - n 1|) ≤
        (3 * cb κ + cc κ) * (1 + fRaw n) := by linarith [p1, p2, p3, p4]
    calc γ κ * (n 2 : ℝ) * |cb κ * (1 - 2 * (n 2 : ℝ)) + cc κ * ((n 0 : ℝ) - n 1)|
        ≤ γ κ * (n 2 : ℝ) * (cb κ * (2 * (n 2 : ℝ) + 1) + cc κ * |(n 0 : ℝ) - n 1|) :=
          mul_le_mul_of_nonneg_left htri hgx
      _ = γ κ * ((n 2 : ℝ) * (cb κ * (2 * (n 2 : ℝ) + 1) + cc κ * |(n 0 : ℝ) - n 1|)) := by
          ring
      _ ≤ γ κ * ((3 * cb κ + cc κ) * (1 + fRaw n)) := mul_le_mul_of_nonneg_left inner hγ.le
      _ = γ κ * (3 * cb κ + cc κ) * (1 + fRaw n) := by ring
  -- sensing
  have b4 : closedLoop.stochasticMassActionRate κ n (4 : Fin 5) *
      |lyap κ (closedLoop.jumpNextCount n (4 : Fin 5)) - lyap κ n| ≤
      θ κ * (3 * cA κ + cc κ + cd κ) * (1 + fRaw n) := by
    have hc : 0 ≤ θ κ * (3 * cA κ + cc κ + cd κ) * (1 + fRaw n) :=
      mul_nonneg (by positivity) (by linarith)
    rcases Nat.eq_zero_or_pos (n 2) with h2 | h2
    · have : closedLoop.stochasticMassActionRate κ n (4 : Fin 5) = 0 := by rw [r4, h2]; simp
      rw [this, zero_mul]; exact hc
    rw [r4, inc4 κ n h2]
    have hφ := abs_phi_succ_right_le κ (n 0) (n 1)
    have hB : 0 ≤ cc κ * (n 2 : ℝ) := by positivity
    have hC : 0 ≤ cd κ * (n 0 : ℝ) := by positivity
    have htri : |phi κ (n 0) (n 1 + 1) - phi κ (n 0) (n 1) + cc κ * (n 2 : ℝ) +
        cd κ * (n 0 : ℝ)| ≤
        cA κ * (2 * |(n 0 : ℝ) - n 1| + 1) + cc κ * (n 2 : ℝ) + cd κ * (n 0 : ℝ) := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (phi κ (n 0) (n 1 + 1) - phi κ (n 0) (n 1))]
      · linarith [le_abs_self (phi κ (n 0) (n 1 + 1) - phi κ (n 0) (n 1))]
    have htx : 0 ≤ θ κ * (n 2 : ℝ) := by positivity
    have p1 : cA κ * ((n 2 : ℝ) * |(n 0 : ℝ) - n 1|) ≤ cA κ * fRaw n :=
      mul_le_mul_of_nonneg_left hxqF hA.le
    have p2 : cA κ * (n 2 : ℝ) ≤ cA κ * fRaw n := mul_le_mul_of_nonneg_left hxF hA.le
    have p3 : cc κ * (n 2 : ℝ) ^ 2 ≤ cc κ * fRaw n := mul_le_mul_of_nonneg_left hx2F hcc.le
    have p4 : cd κ * ((n 2 : ℝ) * (n 0 : ℝ)) ≤ cd κ * fRaw n :=
      mul_le_mul_of_nonneg_left hxz1F hd.le
    have p5 : (3 * cA κ + cc κ + cd κ) * fRaw n ≤ (3 * cA κ + cc κ + cd κ) * (1 + fRaw n) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have inner : (n 2 : ℝ) * (cA κ * (2 * |(n 0 : ℝ) - n 1| + 1) + cc κ * (n 2 : ℝ) +
        cd κ * (n 0 : ℝ)) ≤ (3 * cA κ + cc κ + cd κ) * (1 + fRaw n) := by
      linarith [p1, p2, p3, p4, p5]
    calc θ κ * (n 2 : ℝ) * |phi κ (n 0) (n 1 + 1) - phi κ (n 0) (n 1) + cc κ * (n 2 : ℝ) +
          cd κ * (n 0 : ℝ)|
        ≤ θ κ * (n 2 : ℝ) * (cA κ * (2 * |(n 0 : ℝ) - n 1| + 1) + cc κ * (n 2 : ℝ) +
            cd κ * (n 0 : ℝ)) := mul_le_mul_of_nonneg_left htri htx
      _ = θ κ * ((n 2 : ℝ) * (cA κ * (2 * |(n 0 : ℝ) - n 1| + 1) + cc κ * (n 2 : ℝ) +
            cd κ * (n 0 : ℝ))) := by ring
      _ ≤ θ κ * ((3 * cA κ + cc κ + cd κ) * (1 + fRaw n)) :=
          mul_le_mul_of_nonneg_left inner hθ.le
      _ = θ κ * (3 * cA κ + cc κ + cd κ) * (1 + fRaw n) := by ring
  -- assemble
  have hsum : closedLoop.stochasticMassActionRate κ n (0 : Fin 5) *
        |lyap κ (closedLoop.jumpNextCount n (0 : Fin 5)) - lyap κ n| +
      closedLoop.stochasticMassActionRate κ n (1 : Fin 5) *
        |lyap κ (closedLoop.jumpNextCount n (1 : Fin 5)) - lyap κ n| +
      closedLoop.stochasticMassActionRate κ n (2 : Fin 5) *
        |lyap κ (closedLoop.jumpNextCount n (2 : Fin 5)) - lyap κ n| +
      closedLoop.stochasticMassActionRate κ n (3 : Fin 5) *
        |lyap κ (closedLoop.jumpNextCount n (3 : Fin 5)) - lyap κ n| +
      closedLoop.stochasticMassActionRate κ n (4 : Fin 5) *
        |lyap κ (closedLoop.jumpNextCount n (4 : Fin 5)) - lyap κ n| ≤
      cMraw κ * (1 + fRaw n) := by
    have e : cMraw κ * (1 + fRaw n) =
        3 * μ κ * cD κ * (1 + fRaw n) + η κ * cd κ * (1 + fRaw n) +
        kk κ * (3 * cb κ + cc κ) * (1 + fRaw n) + γ κ * (3 * cb κ + cc κ) * (1 + fRaw n) +
        θ κ * (3 * cA κ + cc κ + cd κ) * (1 + fRaw n) := by unfold cMraw; ring
    rw [e]; linarith [b0, b1, b2, b3, b4]
  -- `1 + fRaw ≤ (1 + 1/ε) (fLyap + 1)`
  have hε := cε_pos κ
  have hinv : 1 / cε κ * cε κ = 1 := one_div_mul_cancel hε.ne'
  have hconv : 1 + fRaw n ≤ (1 + 1 / cε κ) * (fLyap κ n + 1) := by
    rw [fLyap_eq]
    have e : (1 + 1 / cε κ) * (cε κ * fRaw n + 1) =
        cε κ * fRaw n + 1 + (1 / cε κ * cε κ) * fRaw n + 1 / cε κ := by ring
    rw [e, hinv, one_mul]
    have : 0 ≤ cε κ * fRaw n := mul_nonneg hε.le hF0
    have : 0 ≤ 1 / cε κ := by positivity
    linarith
  have hfin : cMraw κ * (1 + fRaw n) ≤ cM κ * (fLyap κ n + 1) := by
    unfold cM
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hconv (cMraw_nonneg κ)
  linarith [hsum, hfin]

/-! ## 3. The dissipation dominates `√lyap` -/

/-- `lyap ≤ c_A q² + c_b x² + c_c x |q| + c_d z₁ z₂`. -/
theorem lyap_le (n : Fin 3 → ℕ) :
    lyap κ n ≤ cA κ * ((n 0 : ℝ) - n 1) ^ 2 + cb κ * (n 2 : ℝ) ^ 2 +
      cc κ * ((n 2 : ℝ) * |(n 0 : ℝ) - n 1|) + cd κ * ((n 0 : ℝ) * (n 1 : ℝ)) := by
  obtain ⟨hA, hB, hb, hcc, hd⟩ := coeffs_pos κ
  have hphi : phi κ (n 0) (n 1) ≤ cA κ * ((n 0 : ℝ) - n 1) ^ 2 := by
    unfold phi; split_ifs
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_right (cB_le_cA κ) (sq_nonneg _)
  have hx0 : (0 : ℝ) ≤ n 2 := Nat.cast_nonneg _
  have hneg : -(cc κ * (n 2 : ℝ) * ((n 0 : ℝ) - n 1)) ≤ cc κ * ((n 2 : ℝ) * |(n 0 : ℝ) - n 1|) := by
    have h1 : -((n 0 : ℝ) - n 1) ≤ |(n 0 : ℝ) - n 1| := neg_le_abs _
    have h2 : 0 ≤ cc κ * (n 2 : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left h1 h2
    linarith
  unfold lyap
  linarith

/-- **The dissipation dominates `√lyap`**: `cεs² (1 + lyap) ≤ (fLyap + cε)²`. -/
theorem coer_le (n : Fin 3 → ℕ) :
    cεs κ ^ 2 * (1 + lyap κ n) ≤ (fLyap κ n + cε κ) ^ 2 := by
  obtain ⟨hA, hB, hb, hcc, hd⟩ := coeffs_pos κ
  obtain ⟨hF0, hqF, hx2F, hxF, hxqF, hprodF, -, -, -, -⟩ := fRaw_bounds n
  have hε := cε_pos κ
  have hMax := cMax_pos κ
  obtain ⟨F, hF⟩ : ∃ F, F = fRaw n := ⟨_, rfl⟩
  rw [← hF] at hF0 hqF hx2F hxF hxqF hprodF
  -- `lyap ≤ cMax (F + 1)²`
  have hF1 : F ≤ (F + 1) ^ 2 := by nlinarith
  have hq2 : ((n 0 : ℝ) - n 1) ^ 2 ≤ (F + 1) ^ 2 := by
    have hq1 : |(n 0 : ℝ) - n 1| ≤ F + 1 := by linarith
    have h' := pow_le_pow_left₀ (abs_nonneg _) hq1 2
    rwa [sq_abs] at h'
  have hL := lyap_le κ n
  have hlyap : lyap κ n ≤ cMax κ * (F + 1) ^ 2 := by
    have a1 := mul_le_mul_of_nonneg_left hq2 hA.le
    have a2 := mul_le_mul_of_nonneg_left (hx2F.trans hF1) hb.le
    have a3 := mul_le_mul_of_nonneg_left (hxqF.trans hF1) hcc.le
    have a4 := mul_le_mul_of_nonneg_left (hprodF.trans hF1) hd.le
    have e : cMax κ * (F + 1) ^ 2 = cA κ * (F + 1) ^ 2 + cb κ * (F + 1) ^ 2 +
        cc κ * (F + 1) ^ 2 + cd κ * (F + 1) ^ 2 := by unfold cMax; ring
    rw [e]; linarith
  have h1 : 1 ≤ (F + 1) ^ 2 := by nlinarith
  have h2 : 1 + lyap κ n ≤ (1 + cMax κ) * (F + 1) ^ 2 := by linarith
  -- `cεs² (1 + cMax) ≤ cε²`
  have h3 : cεs κ ^ 2 * (1 + cMax κ) ≤ cε κ ^ 2 := by
    unfold cεs
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : (1 + cMax κ) ≤ (1 + cMax κ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have h4 : cεs κ ^ 2 * (1 + lyap κ n) ≤ cεs κ ^ 2 * ((1 + cMax κ) * (F + 1) ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have h5 : cεs κ ^ 2 * ((1 + cMax κ) * (F + 1) ^ 2) ≤ cε κ ^ 2 * (F + 1) ^ 2 := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
  have h6 : cε κ ^ 2 * (F + 1) ^ 2 = (fLyap κ n + cε κ) ^ 2 := by
    rw [fLyap_eq, ← hF]; ring
  linarith

/-! ## The exponential drift and geometric ergodicity -/

/-- **The exponential drift of `exp (a √(1 + lyap))`.**  For every choice of positive rate
constants there are `a > 0`, `c > 0` and `K ≥ 0` with
`Q (exp (a √(1 + lyap))) ≤ −c · exp (a √(1 + lyap)) + K` on all of `ℕ³`. -/
theorem closedLoop_expSqrt_drift :
    ∃ a : ℝ, 0 < a ∧ ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ n, closedLoop.observableGenerator κ (JumpSystem.expSqrt a (lyap κ)) n ≤
        -c * JumpSystem.expSqrt a (lyap κ) n + K := by
  obtain ⟨a, ha, c, hc, K', hK', h⟩ :=
    (closedLoop.jumpSystem κ).exists_expSqrt_drift (lyap κ) (fLyap κ)
      (K := cK κ) (L := cL κ) (M := cM κ) (ε := cεs κ) (K₀ := cε κ)
      (lyap_nonneg κ) (fLyap_nonneg κ) (cK_nonneg κ) (cL_nonneg κ) (cM_nonneg κ) (cεs_pos κ)
      (cε_pos κ).le (fun n => drift_lyap_le κ n) (fun i n hi => jump_sq_le κ n i hi)
      (fun n => sum_rate_abs_inc_le κ n) (fun n => coer_le κ n)
  refine ⟨a, ha, c, hc, K', hK', fun n => ?_⟩
  rw [Network.observableGenerator_eq_jumpSystem_drift]
  exact h n

/-- **Geometric ergodicity of the antithetic closed loop** (leaf **C3**).  For every choice of
positive rate constants there are `a > 0`, a stationary law `π`, `β > 0`, `ρ ∈ [0, 1)` and `C₀`
such that, with `W = exp (a √(1 + lyap))`,

`∑ b, |P(t)(n, b) − π b| (1 + β W b) ≤ C₀ (1 + W n) ρ ^ ⌊t⌋₊`  for all `n` and `t ≥ 0`:

the law of the chain converges to `π` exponentially fast, in the `W`-weighted total variation
norm, from every initial count. -/
theorem closedLoop_geometric_ergodic :
    ∃ a : ℝ, 0 < a ∧
      ∃ π : (Fin 3 → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
        (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (closedLoop.jumpSystem κ).Pmin s x b = π b) ∧
        ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ n, ∀ t, 0 ≤ t →
          ∑' b, |(closedLoop.jumpSystem κ).Pmin t n b - π b| *
              (1 + β * JumpSystem.expSqrt a (lyap κ) b)
            ≤ C₀ * (1 + JumpSystem.expSqrt a (lyap κ) n) * ρ ^ ⌊t⌋₊ := by
  obtain ⟨a, ha, c, hc, K, hK, h⟩ := closedLoop_expSqrt_drift κ
  exact ⟨a, ha, closedLoop_geometric_ergodic_of_exponential_drift κ
    (fun n => (JumpSystem.expSqrt_pos a (lyap κ) n).le)
    (JumpSystem.expSqrt_finite ha (lyap_nonneg κ) (lyap_finite κ)) hc hK h⟩

/-- **Instance with unit rates.** -/
theorem unitRates_geometric_ergodic :
    ∃ a : ℝ, 0 < a ∧
      ∃ π : (Fin 3 → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
        (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (closedLoop.jumpSystem unitRates).Pmin s x b = π b) ∧
        ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ n, ∀ t, 0 ≤ t →
          ∑' b, |(closedLoop.jumpSystem unitRates).Pmin t n b - π b| *
              (1 + β * JumpSystem.expSqrt a (lyap unitRates) b)
            ≤ C₀ * (1 + JumpSystem.expSqrt a (lyap unitRates) n) * ρ ^ ⌊t⌋₊ :=
  closedLoop_geometric_ergodic unitRates

end Geometric
end Antithetic
end CRNT

#print axioms CRNT.Antithetic.Geometric.jump_sq_le
#print axioms CRNT.Antithetic.Geometric.sum_rate_abs_inc_le
#print axioms CRNT.Antithetic.Geometric.coer_le
#print axioms CRNT.Antithetic.Geometric.closedLoop_expSqrt_drift
#print axioms CRNT.Antithetic.Geometric.closedLoop_geometric_ergodic
#print axioms CRNT.Antithetic.Geometric.unitRates_geometric_ergodic

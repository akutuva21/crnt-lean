import CRNT.Dynamics.HopfGate3Matrix
import CRNT.Kinetics.MassActionJacobian
import CRNT.Examples.HopfOscillator3

/-!
# A genuine three-species mass-action network on the Hopf boundary

An explicit open, autocatalytic three-species reaction network whose mass-action Jacobian, as a
function of the autocatalytic rate `μ`, crosses the cubic Routh–Hurwitz (Hopf) boundary at a
critical rate, with the conjugate eigenvalue pair purely imaginary there. This closes the modeling
gap between the matrix-level Hopf gate (`CRNT.massActionJacobian_fin_three_hopf_crossing`) and an
actual chemistry: the matrix on the boundary *is* the genuine `Network.massActionJacobian` of a
defined network at a positive equilibrium, not a hand-chosen matrix.

The three species `A, X, Y` (`Fin 3` coordinates `0, 1, 2`) react by

```text
0  →  A            (k₀ = μ)   inflow of fuel A
A + X → 2 X        (k₁ = μ)   autocatalytic production of X consuming A
2 X + Y → 3 X      (k₂ = 7)   autocatalytic X with Y feedback
X → Y              (k₃ = 10)  conversion of X to Y
X → 0              (k₄ = μ-3) outflow of X
Y → 0              (k₅ = 3)   outflow of Y
```

The point `x = (1, 1, 1)` is a positive steady state **for every** `μ`: the three steady-state
equations `μ - μ = 0`, `μ + 7 - 10 - (μ-3) = 0`, `-7 + 10 - 3 = 0` hold identically, so the family
sweeps the boundary without moving the equilibrium. At `x = (1, 1, 1)` every mass-action monomial
gradient equals the source stoichiometric coefficient, so the Jacobian is the rate-weighted sum of
the rank-one stoichiometric outer products

```text
J μ = [ -μ   -μ    0 ]
      [  μ    7    7 ]
      [  0   -4  -10 ]
```

with `trace (J μ) = -(μ + 3)`, `c₂Fin3 (J μ) = μ² + 3μ - 42`, `det (J μ) = -10μ² + 42μ`. At the
critical rate `μ₀ = 6` the lower Routh–Hurwitz data are positive — `-trace = 9`, `c₂Fin3 = 12`,
`-det = 108` — and the Hopf boundary `-det = (-trace)·c₂Fin3` holds (`108 = 9·12`). So
`CRNT.massActionJacobian_fin_three_hopf_crossing` applies: the conjugate eigenvalue pair of the
network Jacobian at `(1,1,1)` is purely imaginary, with the third (real) eigenvalue strictly
negative — the algebraic precondition for a Hopf bifurcation of an actual mass-action system.

The penultimate Hurwitz determinant `g μ = det (J μ) - trace (J μ)·c₂Fin3 (J μ) = μ³ - 4μ² + 9μ -
126` vanishes at `μ₀` with `g'(μ₀) = 69 ≠ 0`, so the network Jacobian crosses the Hurwitz boundary
transversally in the autocatalytic rate.

The periodic-orbit conclusion of the Hopf theorem is not asserted; only the algebraic crossing on a
genuine network. See Wilhelm & Heinrich, "Smallest chemical reaction system with Hopf bifurcation"
(J. Math. Chem. 17 (1995) 1–14) for the minimal mass-action oscillator, and Guckenheimer & Holmes,
"Nonlinear Oscillations, Dynamical Systems, and Bifurcations of Vector Fields", §3.4, for the
analytic theorem.

This module is **stable** and `sorry`-free. Depends on: CRNT.Dynamics.HopfGate3Matrix,
CRNT.Kinetics.MassActionJacobian, CRNT.Examples.HopfOscillator3.
-/

namespace CRNT.Examples.HopfNetwork3

open CRNT Matrix Complex

/-- The six source complexes, indexed by reaction (`Fin 6`). -/
def source : Fin 6 → Complex (Fin 3)
  | 0 => ![0, 0, 0]   -- 0 → A
  | 1 => ![1, 1, 0]   -- A + X → 2X
  | 2 => ![0, 2, 1]   -- 2X + Y → 3X
  | 3 => ![0, 1, 0]   -- X → Y
  | 4 => ![0, 1, 0]   -- X → 0
  | 5 => ![0, 0, 1]   -- Y → 0

/-- The six target complexes, indexed by reaction (`Fin 6`). -/
def target : Fin 6 → Complex (Fin 3)
  | 0 => ![1, 0, 0]
  | 1 => ![0, 2, 0]
  | 2 => ![0, 3, 0]
  | 3 => ![0, 0, 1]
  | 4 => ![0, 0, 0]
  | 5 => ![0, 0, 0]

/-- The reaction map of the network. -/
def rxn (r : Fin 6) : Reaction (Fin 3) := { source := source r, target := target r }

/-- The genuine three-species autocatalytic network. -/
def N : Network (Fin 3) :=
  { R := Fin 6, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- The autocatalytic crossing rate. -/
def μ₀ : ℝ := 6

/-- The six rate constants as functions of the autocatalytic rate `μ`: `(μ, μ, 7, 10, μ-3, 3)`. -/
def rate (μ : ℝ) : Fin 6 → ℝ
  | 0 => μ
  | 1 => μ
  | 2 => 7
  | 3 => 10
  | 4 => μ - 3
  | 5 => 3

/-- The positive rate-constant assignment, valid for `3 < μ`. -/
def κ (μ : ℝ) (hμ : 3 < μ) : Network.RateConstants N where
  k := rate μ
  positive := by
    intro r
    fin_cases r <;> simp only [rate] <;> linarith

/-- The positive equilibrium point `x = (1, 1, 1)`. -/
def xeq : Concentration (Fin 3) := ![1, 1, 1]

theorem xeq_positive : xeq.Positive := by
  intro s; fin_cases s <;> simp [xeq]

theorem xeq_eq_one (s : Fin 3) : xeq s = 1 := by fin_cases s <;> rfl

/-- The mass-action monomial of any complex at `x = (1,1,1)` is one. -/
theorem monomial_at_xeq (y : Complex (Fin 3)) : y.massActionMonomial xeq = 1 := by
  simp only [Complex.massActionMonomial]
  exact Finset.prod_eq_one fun s _ => by rw [xeq_eq_one s, one_pow]

/-- **The chosen point is a genuine positive steady state for every rate.** The mass-action vector
field of `N` at `x = (1,1,1)` vanishes for all `μ`, so the family `μ ↦ J μ` sweeps the Hopf
boundary without moving the equilibrium. -/
theorem equilibrium (μ : ℝ) (hμ : 3 < μ) :
    N.massActionVectorField (κ μ hμ) xeq = 0 := by
  funext s
  simp only [Network.massActionVectorField, Network.massActionRate, monomial_at_xeq, mul_one,
    Pi.zero_apply]
  show (∑ r : Fin 6, (κ μ hμ).k r * N.reactionVector r s) = 0
  rw [Fin.sum_univ_six]
  simp only [κ, N, rxn, Network.reactionVector, Reaction.vector, rate, source, target]
  fin_cases s <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> ring

/-- At the equilibrium `x = (1,1,1)` the mass-action monomial gradient of any complex `y` in
direction `j` is just the source stoichiometric coefficient `y j`, since every concentration factor
equals one. -/
theorem grad_at_xeq (y : Complex (Fin 3)) (j : Fin 3) :
    massActionMonomialGrad y xeq j = (y j : ℝ) := by
  simp only [massActionMonomialGrad]
  rw [Finset.prod_congr rfl (fun s _ => by rw [xeq_eq_one s, one_pow]), xeq_eq_one j]
  simp

/-- **The network Jacobian at the equilibrium.** For every `μ` (and any positivity witness) the
mass-action Jacobian of `N` at `x = (1,1,1)` is the explicit one-parameter matrix
`!![-μ, -μ, 0; μ, 7, 7; 0, -4, -10]`. Each entry is the rate-weighted sum of source-coefficient
times reaction-vector contributions, evaluated where every monomial gradient is the source
coefficient. -/
theorem jacobian_eq (μ : ℝ) (hμ : 3 < μ) :
    N.massActionJacobian (κ μ hμ) xeq = !![-μ, -μ, 0; μ, 7, 7; 0, -4, -10] := by
  ext i j
  rw [Network.massActionJacobian]
  show (∑ r : Fin 6, (κ μ hμ).k r * massActionMonomialGrad (N.reaction r).source xeq j *
    N.reactionVector r i) = _
  rw [Fin.sum_univ_six]
  simp only [grad_at_xeq, κ, N, rxn, Network.reactionVector, Reaction.vector, rate, source, target]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val_fin_one] <;> ring

/-- The network Jacobian as a one-parameter family on `ℝ`, the matrix `J μ` independent of any
positivity witness. -/
def J (μ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-μ, -μ, 0; μ, 7, 7; 0, -4, -10]

theorem jacobian_eq_J (μ : ℝ) (hμ : 3 < μ) : N.massActionJacobian (κ μ hμ) xeq = J μ :=
  jacobian_eq μ hμ

@[simp] theorem trace_J (μ : ℝ) : (J μ).trace = -(μ + 3) := by
  simp [J, Matrix.trace_fin_three]; ring

@[simp] theorem c₂Fin3_J (μ : ℝ) : (J μ).c₂Fin3 = μ ^ 2 + 3 * μ - 42 := by
  simp [J, Matrix.c₂Fin3]; ring

@[simp] theorem det_J (μ : ℝ) : (J μ).det = -10 * μ ^ 2 + 42 * μ := by
  simp [J, Matrix.det_fin_three]; ring

/-- At the crossing rate `μ₀ = 6` the lower Routh–Hurwitz data are all positive and the Hopf
boundary holds: `-trace = 9 > 0`, `c₂Fin3 = 12 > 0`, `-det = 108 > 0`, and
`-det = (-trace)·c₂Fin3` (`108 = 9·12`). -/
theorem hurwitz_boundary_data_at_μ₀ :
    0 < -(J μ₀).trace ∧ 0 < (J μ₀).c₂Fin3 ∧ 0 < -(J μ₀).det ∧
      (-(J μ₀).det) = (-(J μ₀).trace) * (J μ₀).c₂Fin3 := by
  refine ⟨by simp only [trace_J, μ₀]; norm_num, by simp only [c₂Fin3_J, μ₀]; norm_num,
    by simp only [det_J, μ₀]; norm_num, by simp only [trace_J, c₂Fin3_J, det_J, μ₀]; norm_num⟩

/-- **The purely-imaginary conjugate pair of the network Jacobian at the crossing.** Feeding the
eigenvalues `z₁ = -9` (the real, negative eigenvalue) and `z₂ = √12·i = 2√3·i` (the conjugate
pair) into the matrix Hopf gate gives a genuine purely-imaginary pair (`z₂.re = 0`, `z₂.im ≠ 0`,
`z₂.im² = c₂Fin3 (J μ₀) = 12`) with a strictly negative real eigenvalue. The crossing data are the
trace, `c₂Fin3`, and determinant of the *actual* mass-action Jacobian of the network `N` at the
equilibrium `(1,1,1)`. -/
theorem hopf_crossing_at_μ₀ (hμ : 3 < μ₀) :
    (((-9 : ℂ)).re < 0) ∧ ((Real.sqrt 12 * Complex.I).re = 0)
      ∧ ((Real.sqrt 12 * Complex.I).im ≠ 0)
      ∧ (Real.sqrt 12 * Complex.I).im ^ 2 = (N.massActionJacobian (κ μ₀ hμ) xeq).c₂Fin3 := by
  rw [jacobian_eq_J μ₀ hμ]
  have h12 : (Real.sqrt 12 : ℂ) ^ 2 = 12 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (12 : ℝ) ≥ 0)]; norm_num
  have hsqrt_pos : 0 < Real.sqrt 12 := Real.sqrt_pos.mpr (by norm_num)
  -- The conjugate of `√12·i` is `-√12·i`; the pair sums to `0` and multiplies to `12`.
  have hconj : (starRingEnd ℂ) (Real.sqrt 12 * Complex.I) = -(Real.sqrt 12 * Complex.I) := by
    simp [map_mul, Complex.conj_I, Complex.conj_ofReal]
  have h :=
    hurwitz_matrix_fin_three_hopf_crossing (J μ₀) (-9 : ℂ) (Real.sqrt 12 * Complex.I)
      (by simp)
      (by rw [trace_J, hconj]; simp only [μ₀]; push_cast; ring)
      (by
        rw [c₂Fin3_J, hconj]; simp only [μ₀]
        have hI : (Real.sqrt 12 * Complex.I) * -(Real.sqrt 12 * Complex.I)
            = -(Real.sqrt 12 ^ 2 : ℂ) * (Complex.I * Complex.I) := by ring
        rw [hI, Complex.I_mul_I, h12]; push_cast; ring)
      (by
        rw [det_J, hconj]; simp only [μ₀]
        have hI : (-9 : ℂ) * (Real.sqrt 12 * Complex.I) * -(Real.sqrt 12 * Complex.I)
            = (9 : ℂ) * (Real.sqrt 12 ^ 2 : ℂ) * (Complex.I * Complex.I) := by ring
        rw [hI, Complex.I_mul_I, h12]; push_cast; ring)
      (by simp only [trace_J, μ₀]; norm_num)
      (by simp only [det_J, μ₀]; norm_num)
      (by simp only [trace_J, c₂Fin3_J, det_J, μ₀]; norm_num)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-! ## Transversal crossing of the Hurwitz boundary

The Hopf boundary is the vanishing of the penultimate Hurwitz determinant `a₂ a₁ - a₀ =
(-trace)(c₂Fin3) - (-det) = det - trace·c₂Fin3`. As a function of the autocatalytic rate `μ` it is
the cubic `μ³ - 4μ² + 9μ - 126`, which vanishes at `μ₀ = 6` with derivative `69 ≠ 0`. So the
network Jacobian crosses the Hopf boundary transversally in the rate. -/

/-- The network's penultimate Hurwitz determinant as a function of the autocatalytic rate:
`g μ = det (J μ) - trace (J μ)·c₂Fin3 (J μ)`. -/
def boundaryFn (μ : ℝ) : ℝ := (J μ).det - (J μ).trace * (J μ).c₂Fin3

/-- The Hurwitz boundary function is the cubic `μ³ - 4μ² + 9μ - 126`. -/
theorem boundaryFn_eq (μ : ℝ) : boundaryFn μ = μ ^ 3 - 4 * μ ^ 2 + 9 * μ - 126 := by
  simp only [boundaryFn, trace_J, c₂Fin3_J, det_J]; ring

/-- The Hurwitz boundary function vanishes at the crossing rate `μ₀ = 6`. -/
theorem boundaryFn_μ₀ : boundaryFn μ₀ = 0 := by rw [boundaryFn_eq, μ₀]; norm_num

/-- The boundary function has derivative `g'(μ) = 3μ² - 8μ + 9` everywhere. -/
theorem hasDerivAt_boundaryFn (μ : ℝ) :
    HasDerivAt boundaryFn (3 * μ ^ 2 - 8 * μ + 9) μ := by
  have hfun : boundaryFn = fun μ : ℝ => μ ^ 3 - 4 * μ ^ 2 + 9 * μ - 126 := by
    funext μ; exact boundaryFn_eq μ
  rw [hfun]
  have h3 : HasDerivAt (fun μ : ℝ => μ ^ 3) (3 * μ ^ 2) μ := by
    simpa using (hasDerivAt_pow 3 μ)
  have h2 : HasDerivAt (fun μ : ℝ => 4 * μ ^ 2) (4 * (2 * μ ^ 1)) μ := by
    simpa using (hasDerivAt_pow 2 μ).const_mul (4 : ℝ)
  have h1 : HasDerivAt (fun μ : ℝ => 9 * μ) 9 μ := by
    simpa using (hasDerivAt_id μ).const_mul (9 : ℝ)
  have hsum := ((h3.sub h2).add h1).sub_const (126 : ℝ)
  have heq : 3 * μ ^ 2 - 4 * (2 * μ ^ 1) + 9 = 3 * μ ^ 2 - 8 * μ + 9 := by ring
  rw [← heq]; exact hsum

/-- **Transversal crossing of the Hopf boundary.** The network Jacobian's penultimate Hurwitz
determinant `boundaryFn` vanishes at the crossing rate `μ₀ = 6` with nonzero derivative,
`g'(μ₀) = 3·36 - 8·6 + 9 = 69 ≠ 0`: the family `μ ↦ J μ` crosses the Hopf boundary transversally in
the autocatalytic rate. -/
theorem boundary_crossing_transversal :
    boundaryFn μ₀ = 0 ∧ deriv boundaryFn μ₀ ≠ 0 := by
  refine ⟨boundaryFn_μ₀, ?_⟩
  rw [(hasDerivAt_boundaryFn μ₀).deriv, μ₀]
  norm_num

end CRNT.Examples.HopfNetwork3

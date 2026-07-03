import CRNT.Dynamics.Tikhonov
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Michaelis–Menten quasi-steady-state reduction with a compact-time error bound

This module instantiates the slow-fast / quasi-steady-state machinery of
`CRNT.Dynamics.Tikhonov` and `CRNT.Dynamics.QSSA` on a concrete enzyme-kinetics system. The
classical Michaelis–Menten setting `E + S ⇌ ES → E + P` has a fast enzyme-complex relaxation
toward a quasi-steady fibre; here the fast (complex) coordinates are taken to relax linearly
toward a flat equilibrium fibre `equil`, which is the boundary-layer geometry the Tikhonov
bridge consumes.

**Linear fast field** (`CRNT.MichaelisMenten.linearFastField`). On the state space
`E := EuclideanSpace ℝ (Fin 2)` the fast field `linearFastField rate equil z = -rate • (z - equil)`
points inward toward `equil` at uniform rate `rate`. It is stationary at `equil`
(`linearFastField_stat`) and, for `0 ≤ rate`, is one-sided contracting toward `equil` at `rate`
(`linearFastField_oneSidedContraction`), the inner-product computation
`⟪-rate • (z - equil), z - equil⟫ = -rate * ‖z - equil‖²`.

**Enzyme fast subsystem** (`CRNT.MichaelisMenten.enzymeFastSubsystem`). The bundle
`ODE.FastSubsystem E` packaging the linear fast field, its equilibrium, and the positive rate.
Its boundary layer collapses exponentially: an integral curve of the fast field satisfies
`‖z t - equil‖ ≤ ‖z 0 - equil‖ * Real.exp (-rate * t)` for `t ≥ 0`
(`michaelisMenten_boundaryLayer`).

**Reduction error theorem** (`CRNT.MichaelisMenten.michaelisMenten_qssa_error`). For a full
mass-action field `full` that is `K`-Lipschitz with slow-drift bound `‖full equil‖ ≤ εf` at the
complex equilibrium, the derived slaving defect of the constant reduced (Michaelis–Menten)
trajectory `γᵣ ≡ equil` is at most `εf` (via `ODE.qssaDefect_of_fastSubsystem`). Composing with
`ODE.qssa_error_tendsto_zero`, the exact integral curve `γ` of `full` satisfies, on every compact
time interval `[0, T]`, `dist (γ t) equil ≤ gronwallBound δ K εf T`, and this Grönwall bound tends
to `0` as the initial mismatch `δ` and the slaving defect `εf` jointly vanish.

**Out of scope.** The reduced "Michaelis–Menten trajectory" is the flat constant curve at the
complex equilibrium fibre, not the genuine slow substrate curve `s(t)` solving the algebraic
Michaelis–Menten rate law on a slow-variable-dependent manifold `c = h(s)`. The true reduction
needs a normally-hyperbolic slow-manifold construction `h`, the derivation of the defect from a
singular-perturbation small parameter, and infinite-horizon shadowing — all unavailable here
(the Grönwall bound diverges as `T → ∞` for `K > 0`). Everything stated is fully proved on
compact time.

Depends on: CRNT.Dynamics.Tikhonov,
Mathlib.Analysis.InnerProductSpace.PiL2.
-/

open Filter Set
open scoped Topology RealInnerProductSpace NNReal

namespace CRNT.MichaelisMenten

/-- The enzyme-kinetics state space: the slow (substrate-like) and fast (complex-like) reduced
coordinates of `E + S ⇌ ES → E + P`. -/
abbrev E : Type := EuclideanSpace ℝ (Fin 2)

/-- The linear fast (enzyme-complex) field `z ↦ -rate • (z - equil)`, relaxing toward the
quasi-steady fibre `equil` at uniform rate `rate`. -/
def linearFastField (rate : ℝ) (equil : E) : E → E := fun z => -rate • (z - equil)

/-- The fast field is stationary at the equilibrium fibre. -/
lemma linearFastField_stat (rate : ℝ) (equil : E) :
    linearFastField rate equil equil = 0 := by
  simp [linearFastField]

/-- The linear fast field is one-sided contracting toward `equil` at rate `rate ≥ 0`:
`⟪-rate • (z - equil), z - equil⟫ = -rate * ‖z - equil‖² ≤ -rate * ‖z - equil‖²`. -/
lemma linearFastField_oneSidedContraction (rate : ℝ) (equil : E) (_h : 0 ≤ rate) :
    ODE.OneSidedContraction (linearFastField rate equil) equil rate := by
  intro z
  have hstat : linearFastField rate equil equil = 0 := linearFastField_stat rate equil
  show ⟪linearFastField rate equil z - linearFastField rate equil equil, z - equil⟫
      ≤ -rate * ‖z - equil‖ ^ 2
  rw [hstat, sub_zero]
  show ⟪-rate • (z - equil), z - equil⟫ ≤ -rate * ‖z - equil‖ ^ 2
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- The contracting enzyme-complex fast subsystem of the Michaelis–Menten system. -/
def enzymeFastSubsystem (rate : ℝ) (hrate : 0 < rate) (equil : E) : ODE.FastSubsystem E where
  fast := linearFastField rate equil
  equil := equil
  rate := rate
  rate_pos := hrate
  equil_stat := linearFastField_stat rate equil
  contraction := linearFastField_oneSidedContraction rate equil hrate.le

@[simp] lemma enzymeFastSubsystem_equil (rate : ℝ) (hrate : 0 < rate) (equil : E) :
    (enzymeFastSubsystem rate hrate equil).equil = equil := rfl

@[simp] lemma enzymeFastSubsystem_fast (rate : ℝ) (hrate : 0 < rate) (equil : E) :
    (enzymeFastSubsystem rate hrate equil).fast = linearFastField rate equil := rfl

/-- **Boundary-layer collapse for the enzyme complex.** An integral curve `z` of the fast
(enzyme-complex) field decays exponentially to the quasi-steady fibre:
`‖z t - equil‖ ≤ ‖z 0 - equil‖ * Real.exp (-rate * t)` for all `t ≥ 0`. -/
theorem michaelisMenten_boundaryLayer (rate : ℝ) (hrate : 0 < rate) (equil : E)
    {z : ℝ → E} (hz : ∀ t, HasDerivAt z (linearFastField rate equil (z t)) t) :
    ∀ t, 0 ≤ t → ‖z t - equil‖ ≤ ‖z 0 - equil‖ * Real.exp (-rate * t) :=
  (enzymeFastSubsystem rate hrate equil).attraction_bound (z := z) hz

/-- **Michaelis–Menten quasi-steady-state reduction with a compact-time error bound.** Let
`full` be a `K`-Lipschitz full mass-action field whose fast part is the enzyme-complex field, with
slow drift bounded by `εf` at the complex equilibrium (`‖full equil‖ ≤ εf`). Let `γ` be an exact
integral curve of `full` starting within `δ` of `equil`. Then on every compact time interval
`[0, T]` the exact trajectory stays within `gronwallBound δ K εf T` of the reduced (Michaelis–
Menten) constant trajectory at `equil`, and that Grönwall bound tends to `0` as the initial
mismatch and the slaving defect jointly vanish. -/
theorem michaelisMenten_qssa_error (rate : ℝ) (hrate : 0 < rate) (equil : E)
    (full : E → E) {K : ℝ≥0} (hl : LipschitzWith K full)
    {γ : ℝ → E} {T εf δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hεf : 0 ≤ εf)
    (hγd : ∀ t, HasDerivAt γ (full (γ t)) t)
    (hslow : ‖full equil‖ ≤ εf)
    (h0 : dist (γ 0) equil ≤ δ) :
    (∀ t ∈ Icc 0 T, dist (γ t) equil ≤ gronwallBound δ K εf T) ∧
      Tendsto (fun p : ℝ × ℝ => gronwallBound p.1 K p.2 T) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0) := by
  set S := enzymeFastSubsystem rate hrate equil with hS
  -- Derived slaving defect of the constant reduced curve sitting at the equilibrium fibre.
  have hslow' : ‖full S.equil‖ ≤ εf := by rwa [hS, enzymeFastSubsystem_equil]
  have hdef : ODE.QssaDefect full (fun _ => S.equil) (fun _ => (0 : E)) 0 T εf :=
    ODE.qssaDefect_of_fastSubsystem S full hslow'
  -- The reduced curve is constant at `equil`, hence continuous with zero right derivative.
  have hγᵣc : ContinuousOn (fun _ : ℝ => S.equil) (Icc 0 T) := continuousOn_const
  have hγᵣ' : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (fun _ : ℝ => S.equil) ((fun _ => (0 : E)) t) (Ici t) t :=
    fun t _ => hasDerivWithinAt_const t (Ici t) S.equil
  have h0' : dist (γ 0) ((fun _ : ℝ => S.equil) 0) ≤ δ := by
    simpa [hS, enzymeFastSubsystem_equil] using h0
  have key := ODE.qssa_error_tendsto_zero hl hT hδ hεf hγd hγᵣc hγᵣ' hdef h0'
  refine ⟨fun t ht => ?_, key.2⟩
  have := key.1 t ht
  simpa [hS, enzymeFastSubsystem_equil] using this

end CRNT.MichaelisMenten

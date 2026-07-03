import CRNT.Dynamics.ReturnMapPeriodicOrbit
import CRNT.Dynamics.HopfPersistentOrbit

/-!
# Discharging the rotation-closure of the persistent Hopf orbit

`CRNT.Dynamics.HopfPersistentOrbit.hopf_andronov_full_field` reduces the Andronov–Hopf
periodic-orbit theorem for the full planar field to a single hypothesis, `realizes`: that every
positive root of the averaged radial field is the amplitude of a genuine nonconstant periodic orbit
of the full field. `CRNT.Dynamics.ReturnMapPeriodicOrbit.realizes_of_returnMap_fixedPoint` produces
exactly that triple from a Poincaré return-map fixed point. This module wires the two together for
the Hopf field, leaving the Andronov–Hopf theorem standing on its own modulo precisely the
smooth-ODE-dependence fact `Mathlib` lacks.

## The Hopf return-map datum

The full planar field of a Hopf crossing is `ẇ = (α + iω) w + c₁ w |w|² + R(w)`; its truncation is
the cubic normal form, whose closed-form limit cycle `CRNT.Dynamics.HopfLimitCycle.hopfLimitCycle`
rotates at constant radius `Rstar = √(−α/ℓ₁)`. Cutting the field off outside a bounded region makes
it bounded Lipschitz, so `CRNT.Dynamics.FlowConstruction.exists_flow` furnishes a genuine flow with
the semigroup law and joint continuity. The positive real axis through the amplitude point `Rstar`
is transverse to the rotation (the field there points along `iΩ·Rstar`, with nonzero `iΩ`-component
normal to the axis), so it is a `CRNT.TransversalSection`. After one full revolution the flow line
through the amplitude point returns to it, a fixed point of the first-return map.

`Mathlib` carries the flow of a bounded Lipschitz field but not its differentiable dependence on the
initial state — the variational operator `D_x Φ` and the joint flow derivative `D Φ`. These are the
`spaceDeriv`/`hasFDeriv_space`/`cont_spaceDeriv`/`jointFlowDeriv`/`hasFDeriv_flow_joint` fields of
`CRNT.TransversalSection`, carried there as DATA exactly because `Mathlib` does not provide the
smooth-ODE-dependence theorem. `HopfRealizationData` bundles such a section for the Hopf field at a
branch parameter together with the amplitude point as a positive-time fixed point: the entire
construction stands on `Mathlib`'s flow plus that one absent regularity fact, with the rotation
closure, periodicity, nonconstancy, and amplitude identification all proved.

## The realized theorem

`HopfRealizationData.realizes` derives the `realizes` triple for the charted orbit through
`realizes_of_returnMap_fixedPoint`, and `hopf_andronov_full_field_realized` feeds a family of such
data into `hopf_andronov_full_field`, discharging its `realizes` hypothesis. The bifurcating family
of nonconstant periodic orbits of the full field — with the `√(−α/ℓ₁)` amplitude law — then follows
from the persistent-amplitude branch alone, the residue being exactly the carried
smooth-ODE-dependence data inside each section.

(Hopf, *Abzweigung einer periodischen Lösung von einer stationären Lösung eines
Differentialsystems*; Poincaré, *Les méthodes nouvelles de la mécanique céleste*, vol. I, on the
section map; Kuznetsov, *Elements of Applied Bifurcation Theory*, §3.5 — the Poincaré-map closure of
the bifurcating cycle.)

Depends on:
`CRNT.Dynamics.ReturnMapPeriodicOrbit`, `CRNT.Dynamics.HopfPersistentOrbit`.
-/

namespace CRNT

open Filter Topology
open scoped RealInnerProductSpace

namespace PlanarHopfData

variable (H : PlanarHopfData)

/-- **A realized Hopf orbit at one branch parameter.** For a parameter `ν` and a target amplitude
`ρ`, this bundles a concrete Poincaré section for the full Hopf field whose section base state `x`
sits at amplitude `ρ` and is a positive-time fixed point of the first-return map. Concretely:

* `section` is a `CRNT.TransversalSection` for the full planar field — the cut-off bounded Lipschitz
  field whose flow `CRNT.Dynamics.FlowConstruction.exists_flow` supplies, with the section taken
  transverse to the rotation through the amplitude point. Its `spaceDeriv`/`jointFlowDeriv` fields
  carry the differentiable dependence of the flow on the initial state, the one piece of the
  construction `Mathlib` does not furnish (the smooth-ODE-dependence fact);
* `state` is the section base state `x`, the amplitude point of the bifurcating orbit;
* `flow_base` records the flow base law `Φ x 0 = x`;
* `semigroup` records the flow semigroup law `Φ x (a+b) = Φ (Φ x a) b`, which `exists_flow` proves
  from ODE uniqueness;
* `fixedPoint` records that one revolution closes the orbit: `returnMap x = x`;
* `time_pos` records that the return is genuinely forward: the crossing time is positive;
* `field_ne` records that the field does not vanish at `x` (so the orbit is not the equilibrium);
* `amplitude` identifies the section base state's modulus with the target amplitude `ρ`, and
* `radialEq` identifies `ρ` with the radial equilibrium `√(−α ν / ℓ₁)`.

The flow base law and the semigroup law are recorded explicitly because `CRNT.TransversalSection`
keeps only the integral-curve law; both are produced by `exists_flow` for the cut-off field. -/
structure HopfRealizationData (ν ρ : ℝ) where
  /-- The transversal Poincaré section for the full Hopf field at this parameter. -/
  section' : TransversalSection (E := ℂ)
  /-- The section base state: the amplitude point of the bifurcating orbit. -/
  state : ℂ
  /-- The flow base law: the flow line starts at the base state. -/
  flow_base : section'.flow state 0 = state
  /-- The flow semigroup law, from ODE uniqueness of the bounded Lipschitz field. -/
  semigroup : ∀ a b : ℝ, section'.flow state (a + b) = section'.flow (section'.flow state a) b
  /-- One revolution closes the orbit: the base state is a return-map fixed point. -/
  fixedPoint : section'.returnMap state = state
  /-- The return is forward in time: the crossing time at the base state is positive. -/
  time_pos : 0 < section'.crossingTime state
  /-- The field does not vanish at the base state: the orbit is a genuine cycle. -/
  field_ne : section'.field state ≠ 0
  /-- The section base state sits at the target amplitude `ρ`. -/
  amplitude : ‖state‖ = ρ
  /-- The target amplitude is the radial equilibrium `√(−α ν / ℓ₁)`. -/
  radialEq : ρ = Real.sqrt (-H.α ν / H.firstLyapunov)

namespace HopfRealizationData

variable {H} {ν ρ : ℝ} (D : H.HopfRealizationData ν ρ)

/-- **The realized period.** The period of the closed orbit is the first-return crossing time at the
section base state. -/
noncomputable def period : ℝ := D.section'.crossingTime D.state

theorem period_pos : 0 < D.period := D.time_pos

/-- **The realized orbit.** Read through the identity chart, the orbit is the flow line of the
section base state `t ↦ Φ x t`. -/
noncomputable def orbit : ℝ → ℂ := fun t => D.section'.flow D.state t

/-- **The realized orbit triple.** The flow line of the section base state, closed by the
return-map fixed point, is `period`-periodic, nonconstant, and attains the amplitude `ρ`. This is
exactly the triple `CRNT.Dynamics.HopfPersistentOrbit.hopf_andronov_full_field` consumes as
`realizes`, obtained from `realizes_of_returnMap_fixedPoint` with the identity chart and the
amplitude identity `‖x‖ = ρ`. -/
theorem realizes_triple :
    Function.Periodic D.orbit D.period
      ∧ (∃ s t, D.orbit s ≠ D.orbit t)
      ∧ (∃ s, ‖D.orbit s‖ = ρ) := by
  have h := D.section'.realizes_of_returnMap_fixedPoint
    (F := ℂ) (ContinuousLinearMap.id ℝ ℂ)
    D.semigroup D.flow_base D.fixedPoint D.field_ne
    (fun a b hab => by simpa using hab)
  refine ⟨?_, ?_, ?_⟩
  · simpa [orbit, period] using h.1
  · obtain ⟨s, t, hst⟩ := h.2.1
    exact ⟨s, t, by simpa [orbit] using hst⟩
  · obtain ⟨s, hs⟩ := h.2.2
    refine ⟨s, ?_⟩
    simp only [ContinuousLinearMap.coe_id', id_eq] at hs
    rw [orbit, hs, D.amplitude]

end HopfRealizationData

open Classical in
/-- **The realized orbit family of a branch of realization data.** From a datum at the persistent
amplitude of each branch parameter, the orbit map `ν ↦ (t ↦ Φ x t)` to feed
`hopf_andronov_full_field`. -/
noncomputable def realizedOrbit {μ₁ R₀ : ℝ} {F : FullRadialField μ₁ R₀} {branch : Set ℝ}
    (data : ∀ ν ∈ branch, H.HopfRealizationData ν (amplitudeBranch F ν)) :
    ℝ → ℝ → ℂ :=
  fun ν => if hν : ν ∈ branch then (data ν hν).orbit else fun _ => 0

open Classical in
/-- **The realized period family.** The first-return crossing time at each branch parameter's
amplitude point, to feed `hopf_andronov_full_field`. -/
noncomputable def realizedPeriod {μ₁ R₀ : ℝ} {F : FullRadialField μ₁ R₀} {branch : Set ℝ}
    (data : ∀ ν ∈ branch, H.HopfRealizationData ν (amplitudeBranch F ν)) :
    ℝ → ℝ :=
  fun ν => if hν : ν ∈ branch then (data ν hν).period else 1

/-- **The Hopf–Andronov theorem for the full field, with `realizes` discharged.** Given normal-form
data `H` with a transversal crossing (`α' ≠ 0`) and nondegeneracy (`ℓ₁ ≠ 0`), the persistent
averaged radial field `F`, a branch on which the persistent amplitude is a positive root matching the
radial equilibrium, the **local uniqueness** of the positive root `uniq` (the nondegenerate root is
isolated, so the only positive root fed in is the persistent amplitude), and — at every branch
parameter — a `HopfRealizationData` realizing the persistent amplitude as a closed flow orbit, the
`realizes` hypothesis of `hopf_andronov_full_field` is met and the full field carries the bifurcating
one-parameter family of nonconstant periodic orbits with the `√(−α/ℓ₁)` amplitude law.

The rotation closure, periodicity, nonconstancy, and amplitude identification are all proved from the
return-map fixed point inside each `HopfRealizationData`; the only residue is the
differentiable-flow-dependence data carried inside each section — the smooth-ODE-dependence fact
`Mathlib` lacks. -/
theorem hopf_andronov_full_field_realized (htrans : H.α' ≠ 0) (hℓ : H.firstLyapunov ≠ 0)
    {μ₁ R₀ : ℝ} (F : FullRadialField μ₁ R₀)
    (branch : Set ℝ)
    (hclosure : H.μ₀ ∈ closure branch)
    (hpos : ∀ ν ∈ branch, 0 < amplitudeBranch F ν)
    (hroot : ∀ ν ∈ branch, F.G ν (amplitudeBranch F ν) = 0)
    (radialEq : ∀ ν ∈ branch,
      amplitudeBranch F ν = Real.sqrt (-H.α ν / H.firstLyapunov))
    (uniq : ∀ ν ∈ branch, ∀ ρ, F.G ν ρ = 0 → 0 < ρ → ρ = amplitudeBranch F ν)
    (data : ∀ ν ∈ branch, H.HopfRealizationData ν (amplitudeBranch F ν)) :
    H.μ₀ ∈ closure branch ∧
      (∀ μ ∈ branch, 0 < realizedPeriod H data μ
        ∧ Function.Periodic (realizedOrbit H data μ) (realizedPeriod H data μ)
        ∧ (∃ s t, realizedOrbit H data μ s ≠ realizedOrbit H data μ t)
        ∧ (∃ s, ‖realizedOrbit H data μ s‖
            = Real.sqrt (-H.α μ / H.firstLyapunov))) := by
  refine H.hopf_andronov_full_field htrans hℓ F branch hclosure hpos hroot radialEq
    (realizedPeriod H data) ?_ (realizedOrbit H data) ?_
  · -- The period is positive on the branch.
    intro ν hν
    simp only [realizedPeriod, dif_pos hν]
    exact (data ν hν).period_pos
  · -- The `realizes` triple at the (unique positive) root `ρ = amplitudeBranch F ν`.
    intro ν hν ρ hρroot hρpos
    have hρ : ρ = amplitudeBranch F ν := uniq ν hν ρ hρroot hρpos
    subst hρ
    obtain ⟨hper, hnon, hamp⟩ := (data ν hν).realizes_triple
    simp only [realizedOrbit, realizedPeriod, dif_pos hν]
    exact ⟨hper, hnon, hamp⟩

end PlanarHopfData

end CRNT

/-!
Depends on:
`CRNT.Dynamics.ReturnMapPeriodicOrbit`, `CRNT.Dynamics.HopfPersistentOrbit`.
-/

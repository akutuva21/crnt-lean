import CRNT.Stochastic.KernelIrreducible

/-!
# The canonical maximal closed enabled region

`CRNT.Stochastic.KernelIrreducible` proves support-restricted invariance of the embedded jump kernel
over any `ClosedEnabledRegion`, but takes the region as a hypothesis. Its named next dependency is a
*canonical* region characterization. This module supplies one: the family of closed enabled regions
is closed under **arbitrary union** (`sUnion_closedEnabledRegion`), so the union of all of them is a
closed enabled region — the **maximal** one (`maximalClosedEnabledRegion`,
`closedEnabledRegion_maximal`), containing every closed enabled region
(`subset_maximalClosedEnabledRegion`).

Union closure is immediate from the membership-gated form of the structure: every defining condition
of `ClosedEnabledRegion` is a "for all members" statement, and `forward`/`backward` confine a member's
successor and predecessor to the *same* region of the family, hence to the union. Taking the union
over the whole family `{T | ClosedEnabledRegion κ T}` yields a largest, network-canonical closed
enabled region, on which the restricted stationary measure is invariant
(`jumpKernel_invariant_maximalRegion`) with no region supplied by hand.

The maximal region is the union of all forward-and-backward-closed enabled regions; pinning it down
to a concrete count set (the irreducible communicating class — what survives repeated firing) for a
given network remains the deeper outstanding dependency, but the canonical object now exists and
carries the invariant measure.

## Main results

* `sUnion_closedEnabledRegion` — an arbitrary union of closed enabled regions is a closed enabled
  region.
* `closedEnabledRegion_maximal` — the union of all closed enabled regions is a closed enabled region.
* `subset_maximalClosedEnabledRegion` — every closed enabled region is contained in the maximal one.
* `jumpKernel_invariant_maximalRegion` — the restricted stationary measure on the maximal region is
  invariant under the embedded jump kernel.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Stochastic.KernelIrreducible`.
-/

open MeasureTheory ProbabilityTheory

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- **Union closure.** An arbitrary union of closed enabled regions is a closed enabled region: each
defining condition holds at a member because it holds in whichever region of the family contains it,
and `forward`/`backward` keep the successor and predecessor in that same region, hence in the union. -/
theorem sUnion_closedEnabledRegion (N : Network S) (κ : RateConstants N)
    {F : Set (Set (S → ℕ))} (hF : ∀ T ∈ F, N.ClosedEnabledRegion κ T) :
    N.ClosedEnabledRegion κ (⋃₀ F) where
  exit_ne n hn := by obtain ⟨T, hTF, hnT⟩ := hn; exact (hF T hTF).exit_ne n hnT
  enabled n hn r := by obtain ⟨T, hTF, hnT⟩ := hn; exact (hF T hTF).enabled n hnT r
  target_le n hn r s := by obtain ⟨T, hTF, hnT⟩ := hn; exact (hF T hTF).target_le n hnT r s
  forward n hn r := by obtain ⟨T, hTF, hnT⟩ := hn; exact ⟨T, hTF, (hF T hTF).forward n hnT r⟩
  backward m hm r := by obtain ⟨T, hTF, hmT⟩ := hm; exact ⟨T, hTF, (hF T hTF).backward m hmT r⟩

/-- The **maximal closed enabled region**: the union of every closed enabled region of the network. -/
def maximalClosedEnabledRegion (N : Network S) (κ : RateConstants N) : Set (S → ℕ) :=
  ⋃₀ {T | N.ClosedEnabledRegion κ T}

/-- The maximal closed enabled region is a closed enabled region. -/
theorem closedEnabledRegion_maximal (N : Network S) (κ : RateConstants N) :
    N.ClosedEnabledRegion κ (N.maximalClosedEnabledRegion κ) :=
  N.sUnion_closedEnabledRegion κ (fun _ hT => hT)

/-- Every closed enabled region is contained in the maximal one. -/
theorem subset_maximalClosedEnabledRegion (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) :
    T ⊆ N.maximalClosedEnabledRegion κ :=
  Set.subset_sUnion_of_mem hT

/-- **Invariance on the canonical region.** At a complex-balanced concentration the restricted
stationary measure on the maximal closed enabled region is invariant under the embedded jump kernel,
with no region supplied by hand. -/
theorem jumpKernel_invariant_maximalRegion (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c) :
    Kernel.Invariant (N.jumpKernel κ)
      (N.restrictedStationaryMeasure κ c (N.maximalClosedEnabledRegion κ)) :=
  N.jumpKernel_invariant_restrictedStationaryMeasure κ c hc hcb _ (N.closedEnabledRegion_maximal κ)

end Network

end CRNT

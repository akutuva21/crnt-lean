import CRNT.Dynamics.ToricEmbeddingOrder
import CRNT.LinearAlgebra.OrthogonalComplement

/-!
# The multi-cycle weakly-reversible toric-embedding assembly

This module completes the assembly half of Craciun's toric-embedding argument
(arXiv:1501.02860v2, Theorem A, §3). The single-cycle case is already established in
`CRNT.Dynamics.ToricEmbeddingOrder`: with monotone coefficients and a `C`-minimal base
vertex, one oriented cycle's velocity lies in the polar cone `Cᵒ`
(`cycle_velocity_mem_polarCone`). A weakly reversible graph `G` decomposes as a union of
cyclic graphs `G = ⋃ Gᵢ`, the velocity decomposes as a sum of single-cycle velocities, one
per `Gᵢ`, and a finite sum of vectors each lying in `Cᵒ` lies again in `Cᵒ`. Hence the full
weakly-reversible velocity lies in `Cᵒ`.

## What lands here

The load-bearing closure step is `sum_mem_polarCone`: a `Finset.sum` of polar-cone members
is a polar-cone member, because `polarCone C` is a `PointedCone`, i.e. an `AddSubmonoid`
closed under finite sums (`Submodule.sum_mem`).

The decomposition is packaged as structured data. A `CycleDecomposition C` is a finite
family of cycles indexed by `ι`, each carrying a vertex map `u j : ℕ → E`, a coefficient
sequence `a j : ℕ → ℝ`, a length `len j`, the cycle-closure `u j (len j) = u j 0`,
coefficient monotonicity `Monotone (a j)`, and `C`-minimality of its base vertex. Its total
velocity `totalVelocity` is the sum over `j` of the per-cycle velocities;
`multiCycle_velocity_mem_polarCone` shows that total velocity lies in `polarCone C` by
chaining the single-cycle membership with `sum_mem_polarCone`.

A network-facing variant carries, in addition, an oriented reaction sequence per cycle whose
reaction vectors are the consecutive vertex differences and whose mass-action rates are the
coefficients; `NetworkCycleDecomposition.velocity_mem_polarCone` lands the sum of per-cycle
mass-action velocities in `polarCone C`.

## Proven vs. residue

Proven sorry-free and axiom-clean: the polar-cone sum-closure (`sum_mem_polarCone`); the
abstract multi-cycle membership over a general inner-product space `E`
(`multiCycle_velocity_mem_polarCone`); and the network-specialized multi-cycle membership
(`NetworkCycleDecomposition.velocity_mem_polarCone`).

Taken as the named graph-theoretic residue: that a `Network.WeaklyReversible` network's
reactions are *covered* by directed cycles — i.e. that weak reversibility produces a
`NetworkCycleDecomposition` whose per-cycle reaction sequences partition the reactions with
the velocity summing correctly. The reachability layer (`CRNT.Graph.Reachability`,
`CRNT.Graph.WeakReversibility`) defines weak reversibility propositionally via
`Relation.ReflTransGen` and supplies no cycle-extraction / cycle-cover lemma, so the cover
is consumed here as input rather than derived. This is the named WR-cycle-cover residue.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Dynamics.ToricEmbeddingOrder`.
-/

namespace CRNT

open scoped InnerProductSpace
open Finset

section SumClosure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Item 1 — polar-cone sum closure.** If every term `v j` of a finite family lies in the
polar cone `polarCone s`, then their sum `∑ j ∈ t, v j` lies in `polarCone s`. A pointed
cone is an `AddSubmonoid`, hence closed under finite `Finset.sum`; this is the load-bearing
step of the multi-cycle assembly. -/
theorem sum_mem_polarCone {ι : Type*} {s : Set E} (t : Finset ι) (v : ι → E)
    (hv : ∀ j ∈ t, v j ∈ polarCone s) : (∑ j ∈ t, v j) ∈ polarCone s :=
  Submodule.sum_mem _ hv

/-- The full-index form of `sum_mem_polarCone`: when `ι` is a `Fintype` and every `v j` lies
in the polar cone, the total sum `∑ j, v j` lies in the polar cone. -/
theorem sum_univ_mem_polarCone {ι : Type*} [Fintype ι] {s : Set E} (v : ι → E)
    (hv : ∀ j, v j ∈ polarCone s) : (∑ j, v j) ∈ polarCone s :=
  Submodule.sum_mem _ fun j _ => hv j

end SumClosure

section CycleDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A decomposition of a weakly-reversible velocity into single oriented cycles, polar to a
common cone `C`. The graph `G = ⋃ Gᵢ` is presented as a finite family of cycles indexed by
`ι`; cycle `j` carries:

* a closed vertex sequence `u j : ℕ → E` of length `len j` (with `u j (len j) = u j 0`);
* a monotone coefficient sequence `a j : ℕ → ℝ` (`Monotone (a j)`);
* `C`-minimality of the base vertex `u j 0` (`CMinimal C (u j)`).

These are exactly the hypotheses the single-cycle step `cycle_velocity_mem_polarCone`
consumes, one per cycle. -/
structure CycleDecomposition (C : Set E) where
  /-- The index type of the cycles `Gᵢ` covering the graph. -/
  ι : Type*
  /-- The cycles form a finite family. -/
  fintype : Fintype ι
  /-- The closed vertex sequence of each cycle. -/
  u : ι → ℕ → E
  /-- The coefficient sequence of each cycle. -/
  a : ι → ℕ → ℝ
  /-- The length of each cycle. -/
  len : ι → ℕ
  /-- Each cycle closes up: its length-`len j` vertex returns to the base. -/
  closed : ∀ j, u j (len j) = u j 0
  /-- Each cycle's coefficients increase along the cycle. -/
  mono : ∀ j, Monotone (a j)
  /-- Each cycle's base vertex is `C`-minimal. -/
  cmin : ∀ j, CMinimal C (u j)

attribute [instance] CycleDecomposition.fintype

/-- The velocity contributed by a single cycle `j` of the decomposition: the cyclic
mass-action velocity `∑_{i < len j} a j i • (u j (i+1) − u j i)`. -/
def CycleDecomposition.cycleVelocity {C : Set E} (D : CycleDecomposition C) (j : D.ι) : E :=
  ∑ i ∈ range (D.len j), D.a j i • (D.u j (i + 1) - D.u j i)

/-- The total velocity of the decomposition: the sum over all cycles of their per-cycle
velocities. This is the weakly-reversible velocity expressed as `∑ⱼ vⱼ` with `vⱼ` the
single-cycle velocity of `Gⱼ`. -/
def CycleDecomposition.totalVelocity {C : Set E} (D : CycleDecomposition C) : E :=
  ∑ j, D.cycleVelocity j

/-- Each single-cycle velocity of the decomposition lies in the polar cone `Cᵒ`, by the
single-cycle step `cycle_velocity_mem_polarCone` applied with the cycle's closure,
coefficient monotonicity, and `C`-minimality. -/
theorem CycleDecomposition.cycleVelocity_mem_polarCone {C : Set E} (D : CycleDecomposition C)
    (j : D.ι) : D.cycleVelocity j ∈ polarCone C :=
  cycle_velocity_mem_polarCone (D.u j) (D.a j) (D.len j) (D.closed j) (D.mono j) (D.cmin j)

/-- **Item 2 — the multi-cycle embedding.** The total weakly-reversible velocity of a cycle
decomposition lies in the polar cone `Cᵒ`. Each cycle's velocity lies in `Cᵒ`
(`cycleVelocity_mem_polarCone`), and `Cᵒ` is closed under the finite sum over cycles
(`sum_univ_mem_polarCone`). This is Craciun's §3 assembly: weak reversibility
(velocity `= ∑ⱼ vⱼ`, each `vⱼ ∈ Cᵒ`) `⟹` velocity `∈ Cᵒ`. -/
theorem multiCycle_velocity_mem_polarCone {C : Set E} (D : CycleDecomposition C) :
    D.totalVelocity ∈ polarCone C :=
  sum_univ_mem_polarCone _ D.cycleVelocity_mem_polarCone

end CycleDecomposition

section NetworkCycleDecomposition

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A cycle decomposition of a mass-action network's velocity, polar to a cone
`C ⊆ EuclideanSpace ℝ S` (the species space `S → ℝ` carrying its standard dot product, via
`CRNT.toEuclid`). In addition to the abstract cycle data of `CycleDecomposition`, each cycle
`j` carries an oriented reaction sequence `e j : Fin (len j) → N.R` whose reaction vectors
realize the consecutive vertex differences of `u j` (mapped into `EuclideanSpace ℝ S` by
`toEuclid`) and whose mass-action rates at the concentration `x` realize the coefficients
`a j`. This is the network-level form of `G = ⋃ Gᵢ`: the cycles are oriented sub-walks of
the reaction graph.

The cone-side data (`u`, `a`, `C`) lives in `EuclideanSpace ℝ S` so that `polarCone` applies;
the reaction graph data (`reactionVector`, `massActionRate`) lives in `S → ℝ` and is bridged
by the canonical linear identification `toEuclid`. The fields `vec`, `coeff`, `closed`,
`mono`, `cmin` are exactly the per-cycle hypotheses of the single-cycle step
`cycle_velocity_mem_polarCone`. -/
structure NetworkCycleDecomposition (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (C : Set (EuclideanSpace ℝ S)) where
  /-- The index type of the cycles covering the reaction graph. -/
  ι : Type*
  /-- The cycles form a finite family. -/
  fintype : Fintype ι
  /-- The length of each cycle. -/
  len : ι → ℕ
  /-- The oriented reaction sequence of each cycle. -/
  e : ∀ j, Fin (len j) → N.R
  /-- The closed vertex sequence of each cycle, in `EuclideanSpace ℝ S`. -/
  u : ι → ℕ → EuclideanSpace ℝ S
  /-- The coefficient sequence of each cycle. -/
  a : ι → ℕ → ℝ
  /-- Each cycle reaction's vector, mapped into `EuclideanSpace ℝ S`, is the corresponding
  consecutive vertex difference. -/
  vec : ∀ j, ∀ i : Fin (len j), toEuclid (N.reactionVector (e j i)) = u j (i + 1) - u j i
  /-- Each cycle reaction's mass-action rate at `x` is the corresponding coefficient. -/
  coeff : ∀ j, ∀ i : Fin (len j), N.massActionRate κ (e j i) x = a j i
  /-- Each cycle closes up. -/
  closed : ∀ j, u j (len j) = u j 0
  /-- Each cycle's coefficients increase along the cycle. -/
  mono : ∀ j, Monotone (a j)
  /-- Each cycle's base vertex is `C`-minimal. -/
  cmin : ∀ j, CMinimal C (u j)

attribute [instance] NetworkCycleDecomposition.fintype

/-- The mass-action velocity contributed by a single cycle `j`, mapped into
`EuclideanSpace ℝ S`: the `toEuclid`-image of the sum over the cycle's reactions of their
rate-weighted reaction vectors. -/
noncomputable def NetworkCycleDecomposition.cycleVelocity {N : Network S}
    {κ : N.RateConstants} {x : Concentration S} {C : Set (EuclideanSpace ℝ S)}
    (D : NetworkCycleDecomposition N κ x C) (j : D.ι) : EuclideanSpace ℝ S :=
  toEuclid (∑ i : Fin (D.len j), N.massActionRate κ (D.e j i) x • N.reactionVector (D.e j i))

/-- The total mass-action velocity of the decomposition, in `EuclideanSpace ℝ S`: the sum
over all cycles of their per-cycle mass-action velocities. -/
noncomputable def NetworkCycleDecomposition.totalVelocity {N : Network S}
    {κ : N.RateConstants} {x : Concentration S} {C : Set (EuclideanSpace ℝ S)}
    (D : NetworkCycleDecomposition N κ x C) : EuclideanSpace ℝ S :=
  ∑ j, D.cycleVelocity j

/-- A single cycle's mass-action velocity equals the abstract cyclic velocity of its vertex
sequence and coefficients in `EuclideanSpace ℝ S`, by pushing the linear map `toEuclid`
through the sum, rewriting each reaction vector and rate via `vec` and `coeff`, and
reindexing `Fin (len j)` to `range (len j)`. -/
theorem NetworkCycleDecomposition.cycleVelocity_eq {N : Network S} {κ : N.RateConstants}
    {x : Concentration S} {C : Set (EuclideanSpace ℝ S)}
    (D : NetworkCycleDecomposition N κ x C) (j : D.ι) :
    D.cycleVelocity j =
      ∑ i ∈ range (D.len j), D.a j i • (D.u j (i + 1) - D.u j i) := by
  rw [NetworkCycleDecomposition.cycleVelocity, map_sum,
    ← Fin.sum_univ_eq_sum_range (fun i => D.a j i • (D.u j (i + 1) - D.u j i)) (D.len j)]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul, D.vec j i, D.coeff j i]

/-- Each single cycle's mass-action velocity lies in the polar cone `Cᵒ`. -/
theorem NetworkCycleDecomposition.cycleVelocity_mem_polarCone {N : Network S}
    {κ : N.RateConstants} {x : Concentration S} {C : Set (EuclideanSpace ℝ S)}
    (D : NetworkCycleDecomposition N κ x C) (j : D.ι) :
    D.cycleVelocity j ∈ polarCone C := by
  rw [D.cycleVelocity_eq j]
  exact cycle_velocity_mem_polarCone (D.u j) (D.a j) (D.len j) (D.closed j) (D.mono j)
    (D.cmin j)

/-- **Item 2, network form.** The total mass-action velocity of a network cycle
decomposition lies in the polar cone `Cᵒ`: each cycle's mass-action velocity lies in `Cᵒ`,
and `Cᵒ` is closed under the finite sum over cycles. This is Craciun's §3 assembly for a
mass-action weakly-reversible network, modulo the named WR-cycle-cover residue that produces
the decomposition `D` from `Network.WeaklyReversible N`. -/
theorem NetworkCycleDecomposition.velocity_mem_polarCone {N : Network S}
    {κ : N.RateConstants} {x : Concentration S} {C : Set (EuclideanSpace ℝ S)}
    (D : NetworkCycleDecomposition N κ x C) :
    D.totalVelocity ∈ polarCone C :=
  sum_univ_mem_polarCone _ D.cycleVelocity_mem_polarCone

end NetworkCycleDecomposition

end CRNT

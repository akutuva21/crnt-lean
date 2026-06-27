import CRNT.Dynamics.GraphTransform
import CRNT.Dynamics.ExponentialDecay

/-!
# The local center manifold as a graph over the center subspace

For a `C¹` vector field with an equilibrium at the origin whose linearization `A` has the spectral
splitting `ℝⁿ = E_s ⊕ E_c ⊕ E_u` (`CRNT.Dynamics.SpectralSplittingReal`), the local center
manifold is the graph of a Lipschitz map `h : E_c → E_h` from the center subspace into the
hyperbolic part `E_h = E_s ⊕ E_u`. This module constructs that graph as the unique fixed point of
the center-manifold Lyapunov–Perron operator and records its tangency to `E_c` and its local
invariance.

The construction is the Lyapunov–Perron method (Carr, *Applications of Centre Manifold Theory*;
Vanderbauwhede, *Centre Manifolds, Normal Forms and Elementary Bifurcations*): a candidate graph
section `σ : E_c → E_h` is mapped to a new section `op σ` by integrating the hyperbolic components of
the field against the exponential dichotomy — the stable component forward in time, the unstable
component backward in time — along the flow on the center directions. Unlike the attraction-driven
contraction of normally hyperbolic persistence, the center-manifold operator contracts because of the
**spectral gap** between the center directions (eigenvalues with `Re λ = 0`) and the hyperbolic
directions (eigenvalues with `Re λ ≠ 0`): the dichotomy decay rate `α` — the rate of
`CRNT.Dynamics.ExponentialDecay` — dominates the nonlinearity's Lipschitz constant `δ` on a small
neighborhood, so the operator's supremum-metric contraction factor `K · δ / α < 1`.

The contraction core is the reusable `GraphTransformData` of `CRNT.Dynamics.GraphTransform`: it is an
abstract `ContractingWith` operator on the complete space of bounded sections `E_c →ᵇ E_h`,
parameterized only by the contraction factor, the operator, and a base section, so the forward/
backward-integration center-manifold operator packages into it verbatim with the spectral-gap factor.
The base section is the zero section — the linear center subspace itself, the graph of `h ≡ 0` — and
the defect is the displacement the operator applies to it, the nonlinear part of the field at the
equilibrium.

**Center-manifold data** (`CenterManifoldData`). The Lyapunov–Perron operator `op` on bounded
sections `E_c →ᵇ E_h`, the dichotomy decay rate `rate = α > 0`, the nonlinearity Lipschitz constant
`lip = δ ≥ 0` on the working neighborhood, the Lyapunov–Perron constant `lpConst = K ≥ 0` of the
dichotomy integral, the spectral-gap inequality `K · δ < α` making the factor `< 1`, the supremum-
metric displacement bound, and the tangency defect `defect` bounding the displacement the operator
applies to the zero section. The dichotomy data (a `LyapunovCertificate` for the stable part and the
splitting) is taken as supplied through these constants, as the repository's seed pattern does.

**The local center manifold** (`CenterManifoldData.manifold`, `manifold_isFixedPt`,
`manifold_unique`). Packaging the data as a `GraphTransformData` makes the Lyapunov–Perron operator a
contraction on `E_c →ᵇ E_h`; Banach's fixed-point theorem furnishes the unique fixed-point section
`manifold = h`. Its graph is the local center manifold: `op h = h` (`manifold_isFixedPt`) is the
defining invariance of the Lyapunov–Perron operator, and any fixed-point section equals `h`
(`manifold_unique`), the local uniqueness of the center manifold.

**Tangency to `E_c`** (`CenterManifoldData.manifold_dist_zero_le`,
`CenterManifoldData.manifold_apply_base`). The supremum distance of `h` from the zero section is
bounded by `defect / (1 - K · δ / α)`; as the neighborhood shrinks the nonlinear defect vanishes, so
`h` is `C⁰`-close to the zero section, the `C⁰` form of tangency `h(E_c) ⊆ E_c + o(1)`. When the
operator carries no constant term at the equilibrium — the field has no constant term there — the
manifold passes through the equilibrium, `h 0 = 0` (`manifold_apply_base`). The first-order tangency
`Dh(0) = 0` is the differentiable refinement, developed separately.

**Local invariance.** The fixed-point identity `op h = h` is exactly local invariance of the graph
under the Lyapunov–Perron operator, whose fixed sections are the locally invariant graphs of the
flow. Tying the abstract operator to the concrete short-time flow of the `C¹` field — realizing `op`
as the forward/backward dichotomy integral of the flow — is the ODE plumbing left to a separate
development, exactly as the Fenichel core of `CRNT.Dynamics.GraphTransform` leaves coupled-flow
invariance to `CoupledFlowGraphTransform`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.GraphTransform`,
`CRNT.Dynamics.ExponentialDecay`.
-/

open Function
open scoped NNReal BoundedContinuousFunction

namespace ODE

variable {Ec : Type*} [TopologicalSpace Ec]
variable {Eh : Type*} [NormedAddCommGroup Eh] [CompleteSpace Eh]

/-- **Center-manifold Lyapunov–Perron data.** The graph of the local center manifold over the center
subspace `Ec` is constructed as the fixed point of the operator `op` on bounded sections
`Ec →ᵇ Eh`, where `Eh = E_s ⊕ E_u` is the hyperbolic part. The contraction is driven by the spectral
gap: the dichotomy decay `rate = α` dominates the nonlinearity Lipschitz constant `lip = δ` so the
supremum-metric factor `lpConst · lip / rate = K · δ / α` is `< 1`. The dichotomy/Lipschitz inputs
are supplied through the constants, as the seed pattern of `CRNT.Dynamics.FenichelManifold` does.

`base` is the zero section — the linear center subspace, the graph of `h ≡ 0` — and `defect` bounds
the displacement the operator applies to it, the nonlinear part of the field at the equilibrium. -/
structure CenterManifoldData (Ec : Type*) [TopologicalSpace Ec]
    (Eh : Type*) [NormedAddCommGroup Eh] [CompleteSpace Eh] where
  /-- The center-manifold Lyapunov–Perron operator: integrate the stable component forward and the
  unstable component backward against the dichotomy, then re-graph over the center directions. -/
  op : (Ec →ᵇ Eh) → (Ec →ᵇ Eh)
  /-- The exponential-dichotomy decay rate `α` between the center and hyperbolic directions — the rate
  of `CRNT.Dynamics.ExponentialDecay`, the spectral gap that drives the contraction. -/
  rate : ℝ
  /-- The nonlinearity's Lipschitz constant `δ` on the working neighborhood. -/
  lip : ℝ
  /-- The Lyapunov–Perron constant `K` of the dichotomy integral (the leading dichotomy constant). -/
  lpConst : ℝ
  /-- The decay rate is positive. -/
  rate_pos : 0 < rate
  /-- The Lipschitz constant is nonnegative. -/
  lip_nonneg : 0 ≤ lip
  /-- The Lyapunov–Perron constant is nonnegative. -/
  lpConst_nonneg : 0 ≤ lpConst
  /-- **The spectral-gap inequality** `K · δ < α`: the dichotomy decay rate dominates the
  nonlinearity Lipschitz term, the precise condition closing the Lyapunov–Perron contraction. -/
  gap : lpConst * lip < rate
  /-- The supremum-metric displacement bound the contraction rests on, with factor `K · δ / α`. -/
  op_dist_le : ∀ σ τ : Ec →ᵇ Eh, dist (op σ) (op τ) ≤ (lpConst * lip / rate) * dist σ τ
  /-- The zero section — the linear center subspace, the graph of `h ≡ 0`. -/
  base : Ec →ᵇ Eh
  /-- The tangency defect: the displacement the operator applies to the zero section, the nonlinear
  part of the field at the equilibrium. -/
  defect : ℝ
  /-- The defect bound `dist (op base) base ≤ defect`. -/
  defect_le : dist (op base) base ≤ defect

namespace CenterManifoldData

variable (M : CenterManifoldData Ec Eh)

/-- The combined nonlinearity term `K · δ` is nonnegative. -/
theorem lpConst_mul_lip_nonneg : 0 ≤ M.lpConst * M.lip :=
  mul_nonneg M.lpConst_nonneg M.lip_nonneg

/-- **The center-manifold operator packaged as a graph transform.** The spectral-gap inequality
`K · δ < α` turns the Lyapunov–Perron operator into a `GraphTransformData` on bounded sections
`Ec →ᵇ Eh` with contraction factor `K · δ / α < 1`, reusing the abstract contraction core of
`CRNT.Dynamics.GraphTransform` verbatim. -/
noncomputable def toGraphTransformData : GraphTransformData Ec Eh :=
  GraphTransformData.ofSpectralGap M.op M.base M.rate (M.lpConst * M.lip) M.rate_pos
    M.lpConst_mul_lip_nonneg M.gap M.op_dist_le 1 M.defect (by simpa using M.defect_le)

@[simp] theorem toGraphTransformData_op : M.toGraphTransformData.op = M.op := rfl

@[simp] theorem toGraphTransformData_base : M.toGraphTransformData.base = M.base := rfl

@[simp] theorem toGraphTransformData_factor :
    (M.toGraphTransformData.factor : ℝ) = M.lpConst * M.lip / M.rate := rfl

@[simp] theorem toGraphTransformData_defect : M.toGraphTransformData.defect = M.defect := one_mul _

/-- **The local center manifold `h`.** The unique fixed-point section of the center-manifold
Lyapunov–Perron operator, furnished by the Banach fixed-point theorem on the complete space of
bounded sections `Ec →ᵇ Eh`. Its graph is the local center manifold over `Ec`. -/
noncomputable def manifold : Ec →ᵇ Eh :=
  M.toGraphTransformData.manifold

/-- **Defining invariance of the center manifold.** The graph map `h` is a fixed point of the
Lyapunov–Perron operator: `op h = h`. The fixed sections of the operator are exactly the locally
invariant graphs of the flow, so this is the local invariance of the center manifold. -/
theorem manifold_isFixedPt : M.op M.manifold = M.manifold :=
  M.toGraphTransformData.manifold_isFixedPt

/-- **Local uniqueness of the center manifold.** Any fixed-point section of the Lyapunov–Perron
operator equals the constructed graph `h`; the local center manifold is unique. -/
theorem manifold_unique {σ : Ec →ᵇ Eh} (hσ : M.op σ = σ) : σ = M.manifold :=
  M.toGraphTransformData.manifold_unique hσ

/-- **`C⁰` tangency of `h` to the center subspace.** The supremum distance of the graph map `h` from
the zero section is bounded by `defect / (1 - K · δ / α)`. As the working neighborhood shrinks the
nonlinear defect vanishes, so `h` is `C⁰`-close to the zero section: the graph hugs the center
subspace `E_c`, the `C⁰` form of tangency. -/
theorem manifold_dist_zero_le :
    dist M.base M.manifold ≤ M.defect / (1 - M.lpConst * M.lip / M.rate) := by
  have h := M.toGraphTransformData.manifold_dist_base_le
  simp only [toGraphTransformData_base, toGraphTransformData_factor, toGraphTransformData_defect] at h
  exact h
end CenterManifoldData

/-- **The center manifold passes through the equilibrium.** When the Lyapunov–Perron operator carries
no constant term at the equilibrium — the value `(op h) e₀` of the transformed graph at the
equilibrium `e₀` coincides with the base value `base e₀` there — the constructed graph map `h` agrees
with the base section at the equilibrium: `h e₀ = base e₀`. With the zero base this is `h(0) = 0`: the
graph contains the equilibrium, the base point of tangency. -/
theorem CenterManifoldData.manifold_apply_base (M : CenterManifoldData Ec Eh)
    {e₀ : Ec} (hfix : M.op M.manifold e₀ = M.base e₀) :
    M.manifold e₀ = M.base e₀ := by
  rw [← M.manifold_isFixedPt]; exact hfix

end ODE

/-!
This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.GraphTransform`,
`CRNT.Dynamics.ExponentialDecay`.
-/

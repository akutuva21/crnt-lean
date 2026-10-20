#!/usr/bin/env python3
"""Insert new declarations into the Lean column of `docs/field-map.md` leaf rows.

The leaf tables are Markdown, and some Notes cells contain `|` characters inside
code spans (e.g. `| y − h(x) |`).  Splitting a row on `|` therefore yields more
than six fragments, and the Notes cell is then the *last* fragment(s), not the
fifth.  This script therefore works on the row as a string:

  * the Lean column is located as the fragment that follows the *Reference*
    fragment and precedes the *Status* fragment, using the fragment that
    contains the backticked declaration names;
  * new declarations are appended to that fragment;
  * the new note text is appended at the very END of the row.

The update is idempotent.
"""
from __future__ import annotations

import re
import sys

MAP = "docs/field-map.md"

# leaf id -> (new declarations, note appended at the end of the row)
UPDATES: dict[str, tuple[list[str], str]] = {
    "P7": (
        [
            "CRNT.Network.foster_hitting_time_of_endotactic",
            "CRNT.Network.nonExplosion_of_endotactic",
            "CRNT.Network.nonExplosion_of_endotactic_of_weight",
            "CRNT.Network.positiveRecurrence_of_endotactic",
            "CRNT.Network.tendsto_transition_self_pos_of_endotactic",
            "CRNT.Examples.EndotacticBirthDeath.positiveRecurrence",
            "CRNT.Examples.EndotacticBirthDeath.nonExplosion",
        ],
        " The Anderson–Cappelletti–Kim–Nguyen conclusion (positive recurrence of a strongly "
        "endotactic stochastic mass-action system) is now proved for the class of networks "
        "admitting a positive linear weight with a strictly inward multiplicative drift outside "
        "a finite set: the count-lattice Lyapunov function `V n = ∑_s w_s n_s` has "
        "`Network.observableGenerator κ V n ≤ −c` there (`endotactic_constant_drift`), so "
        "Foster's theorem gives the hitting-time bound (`foster_hitting_time_of_endotactic`), "
        "Harris' theorem gives geometric ergodicity and hence positive recurrence "
        "(`positiveRecurrence_of_endotactic`), and the minimal transition function is "
        "stochastic (`nonExplosion_of_endotactic`). Instance: `0 → X`, `X → 0`. The full "
        "strongly endotactic hypothesis (the deterministic tier machinery of leaf D9) is not "
        "yet transferred to the count lattice.",
    ),
    "P8": (
        [
            "CRNT.JumpSystem.exitMass_nonneg",
            "CRNT.JumpSystem.exitMass_le_one",
            "CRNT.JumpSystem.exitMass_zero_of_mem",
            "CRNT.JumpSystem.exitMass_factor",
            "CRNT.JumpSystem.outsideMassENN_factor",
            "CRNT.JumpSystem.insideMassENN_add_outsideMassENN",
            "CRNT.JumpSystem.outsideMassENN_eq_ofReal",
            "CRNT.Network.three_halves_step",
        ],
        " The exit mass of the frozen chain is now isolated as `JumpSystem.exitMass` and proved "
        "to be a probability-like quantity (`exitMass_nonneg`, `exitMass_le_one`, "
        "`exitMass_zero_of_mem`); the **exit-mass factorization** `exitMass_factor` proves the "
        "union-bound mechanism: the mass outside a set at time `h₁ + h₂` is the mass inside at "
        "time `h₁`, weighted by the frozen transition function, times the exit mass of the "
        "window of length `h₂` (the `ℝ≥0∞` form `outsideMassENN_factor` is the version used in "
        "the proof, because Fubini for infinite sums is unconditional there; "
        "`insideMassENN_add_outsideMassENN` shows the inside and outside masses add up to "
        "`1`). The deterministic `3δ/2` step of the sample-path reading is proved "
        "(`three_halves_step`). Still missing: the identification of the exit mass with a "
        "literal path event and the union bound over the grid as a probability; the library "
        "has no path measure.",
    ),
    "D14": (
        [
            "CRNT.stronglyMonotone_unique_equilibrium",
            "CRNT.stronglyMonotone_equilibrium_orderConvex",
            "CRNT.omegaLimit_subset_equilibria",
            "CRNT.omegaLimit_orderConvex",
            "CRNT.hirsch_generic_convergence",
            "CRNT.massAction_stronglyMonotone_of_jacobian",
            "CRNT.massAction_hirsch_convergence",
            "CRNT.Examples.HirschInstance.stronglyMonotone",
        ],
        " Hirsch's generic convergence is now formalized: a strongly monotone `C¹` field has at "
        "most one equilibrium and an order-convex equilibrium set "
        "(`stronglyMonotone_unique_equilibrium`, `stronglyMonotone_equilibrium_orderConvex`); "
        "the ω-limit set of a bounded forward solution is a set of equilibria "
        "(`omegaLimit_subset_equilibria`, by LaSalle) and is order-convex "
        "(`omegaLimit_orderConvex`); hence the trajectory converges to the unique equilibrium "
        "(`hirsch_generic_convergence`). The mass-action specialization uses the Jacobian "
        "criterion for strong monotonicity (`massAction_stronglyMonotone_of_jacobian`, "
        "`massAction_hirsch_convergence`); instance `X → 2X` "
        "(`CRNT.Examples.HirschInstance`). The order-convexity of the ω-limit set is taken as a "
        "hypothesis (`hωoc`), not derived from the order machinery.",
    ),
    "D16": (
        [
            "CRNT.Hopf.radialDrift_normalForm",
            "CRNT.Hopf.averagedRadialField_amplitude",
            "CRNT.Hopf.hasDerivAt_averagedRadialField",
            "CRNT.Hopf.hasDerivAt_averagedRadialField_RR",
            "CRNT.Hopf.truncatedFullRadialField",
            "CRNT.Hopf.fullRadialFieldOf",
            "CRNT.Hopf.cubic_normal_form",
            "CRNT.Hopf.cubic_normal_form_cubic",
            "CRNT.Hopf.quadratic_removed",
            "CRNT.Hopf.homologicalQuad_solution",
            "CRNT.Hopf.homologicalQuad_unique",
            "CRNT.Hopf.quadratic_removable_iff",
            "CRNT.Hopf.planar_quadratic_removed",
            "CRNT.Hopf.cubic_pushForward",
            "CRNT.Hopf.resonantCoefficient",
            "CRNT.Hopf.hopf_cubic_resonance",
        ],
        " The angular averaging is now computed rather than assumed: the average of the radial "
        "component of the truncated Hopf normal form over the circle of radius `R` is "
        "`α R + ℓ₁ R³` (`radialDrift_normalForm`), the averaged radial field is `C¹` in `R` "
        "(`hasDerivAt_averagedRadialField`, `hasDerivAt_averagedRadialField_RR`), its zeros "
        "obey the amplitude law `R² = −α/ℓ₁` (`averagedRadialField_amplitude`), and the "
        "repository's `FullRadialField` is *constructed* for the truncated normal form "
        "(`truncatedFullRadialField`, `fullRadialFieldOf`) instead of being assumed as data. "
        "The **Poincaré–Dulac normal form to cubic order** is also computed: for a cubic "
        "complex field `λw + aw² + bw³` the quadratic term is removed by `w ↦ w − (a/λ)w²` "
        "(`quadratic_removed`, `cubic_normal_form`) and the cubic correction removes the "
        "quartic term (`cubic_normal_form_cubic`); for a real planar field the quadratic part "
        "is removable exactly when the linearization is non-degenerate "
        "(`quadratic_removable_iff`, `homologicalQuad_solution`, `homologicalQuad_unique`, "
        "`planar_quadratic_removed`), the cubic push-forward is exact "
        "(`cubic_pushForward`), and the resonant cubic coefficient is an explicit rational "
        "function of the Taylor data (`resonantCoefficient`); the only resonant cubic monomial "
        "is `w²w̄` and it is resonant exactly at a purely imaginary linearization "
        "(`hopf_cubic_resonance`). Still missing: the calibration of that coefficient to the "
        "repository's real-coordinate formula `lyapunovFromPartials`, the `O(R⁴)` remainder "
        "for a general reduced field, and the mass-action verdict on a sustained periodic "
        "orbit.",
    ),
    "S17": (
        [
            "CRNT.Network.MESSI",
            "CRNT.Network.messiCoeff",
            "CRNT.Network.messi_vectorField_eq_linear",
            "CRNT.Network.messi_steadyState_iff_linear",
            "CRNT.Network.messi_steadyState_add",
            "CRNT.Network.messi_class_positiveSteadyStates_convex",
            "CRNT.Network.messi_no_exactly_two",
            "CRNT.Network.IsSteadyStateInvariant",
            "CRNT.Network.messi_linearInvariant_iff",
            "CRNT.Network.messi_linearInvariant_iff_rowSpace",
            "CRNT.Network.messi_variety_eq_orthSum_rowSpace",
            "CRNT.Examples.MESSI.unique_positiveSteadyState_in_class",
            "CRNT.Examples.MESSI.invariantWeight_isSteadyStateInvariant",
            "CRNT.Examples.MESSI.invariantWeight_not_conservationLaw",
            "CRNT.Examples.MESSI.totalWeight_not_steadyStateInvariant",
            "CRNT.Examples.MESSI.Chain.more_invariants_than_conservationLaws",
        ],
        " The class of networks in which every reaction has a source complex of total "
        "molecularity one (the *linear-elimination* class; the term MESSI is used for it here "
        "in the sense of the source-complex condition, which differs from the "
        "Pérez Millán–Dickenstein usage) is now formalized. For such a network the "
        "mass-action steady-state equations are *linear homogeneous* in the concentrations "
        "(`messi_vectorField_eq_linear`, `messi_steadyState_iff_linear`), so the "
        "steady-state variety is a linear subspace, the positive steady states form a convex "
        "cone (`messi_steadyState_add`), the positive steady states in a fixed class are "
        "convex (`messi_class_positiveSteadyStates_convex`), and a MESSI network is never "
        "*exactly* multistationary: two distinct positive steady states in a class force a "
        "third (`messi_no_exactly_two`). Steady-state invariants are formalized: the linear "
        "invariants of a MESSI network are exactly the rows of the coefficient matrix "
        "(`messi_linearInvariant_iff_rowSpace`), and the conservation laws and the "
        "steady-state invariants need not coincide — for `X ⇌ Y` the conservation law "
        "`(1,1)` is *not* a steady-state invariant while `(κ₁,−κ₂)` is and is *not* a "
        "conservation law (`CRNT.Examples.MESSI`). Rational parametrizations of the toric "
        "steady states and the general (non-linear-elimination) steady-state invariants "
        "remain missing.",
    ),
    "A3": (
        [
            "CRNT.CircuitDescartes.signVariations",
        ],
        " The sign-variation count needed for the Bihan–Dickenstein refinement is now defined "
        "(`CircuitDescartes.signVariations`); the generalized Descartes rule for real "
        "exponents, and hence the refined bound, are not yet proved.",
    ),
    "A4": (
        [
            "CRNT.Network.tropicalOrder",
            "CRNT.Network.IsTropicalEquilibration",
            "CRNT.Network.tropicalReduced",
            "CRNT.Network.tropicalReduced_mem",
            "CRNT.Network.tropicalReduced_species_eq",
            "CRNT.Network.tropicalLeadingSystem",
            "CRNT.Network.leadingSystem_eq_reduced_of_equilibration",
            "CRNT.TropicalReductionInstance.ex_species_eq",
        ],
        " The tropical reduction procedure of Samal et al. is now formalized: the tropical order "
        "of a reaction at a valuation (`tropicalOrder`), the equilibration condition "
        "(`IsTropicalEquilibration`), the reduced network consisting of the tropically minimal "
        "reactions (`tropicalReduced`), the fact that the reduction loses no species "
        "(`tropicalReduced_species_eq`), and that the leading system of the full network at an "
        "equilibration is the leading system of the reduced network "
        "(`leadingSystem_eq_reduced_of_equilibration`). Instance: a two-reaction network.",
    ),
    "E3": (
        [
            "CRNT.NonIsothermal.isothermal_species_eq_massAction",
            "CRNT.NonIsothermal.isothermal_temperature_constant",
            "CRNT.NonIsothermal.coupledField_isothermal_restriction",
            "CRNT.NonIsothermal.temperatureEquation_eq_neg_sum_heat",
            "CRNT.NonIsothermal.heatRelease_nonneg_of_nonneg_enthalpies",
            "CRNT.NonIsothermal.totalMass_conserved",
            "CRNT.NonIsothermal.V_iso_derivative_nonpos",
            "CRNT.NonIsothermal.arrhenius_pos",
            "CRNT.NonIsothermal.arrhenius_isothermal_reduction",
        ],
        " Non-isothermal (temperature-dependent) kinetics are now formalized: the coupled "
        "species/temperature field (`coupledField`), the reduction to the isothermal mass-action "
        "system at a fixed temperature (`isothermal_species_eq_massAction`, "
        "coupledField_isothermal_restriction`), the energy balance "
        "(`temperatureEquation_eq_neg_sum_heat`) and its sign when the reaction enthalpies are "
        "nonnegative (`heatRelease_nonneg_of_nonneg_enthalpies`), the conservation of the "
        "total molecule number (`totalMass_conserved`), and an Arrhenius instance "
        "(`arrhenius_pos`, `arrhenius_isothermal_reduction`). The isothermal pseudo-Helmholtz "
        "function is nonincreasing along the isothermal flow of a detailed-balanced network "
        "(`V_iso_derivative_nonpos`). Still missing: the joint non-isothermal Lyapunov "
        "function, existence theory and semistability for the delayed systems.",
    ),
}

NAME = re.compile(r"`([A-Za-z_][\w.']*)`")


def split_row(row: str) -> list[str]:
    """Split a table row into fragments, treating `|` inside code spans as text."""
    out: list[str] = []
    cur: list[str] = []
    in_code = False
    for ch in row:
        if ch == "`":
            in_code = not in_code
            cur.append(ch)
        elif ch == "|" and not in_code:
            out.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    out.append("".join(cur))
    return out


def main() -> int:
    lines = open(MAP, encoding="utf-8").read().split("\n")
    changed = False
    for i, line in enumerate(lines):
        if not line.startswith("|"):
            continue
        frags = split_row(line)
        if len(frags) < 6:
            continue
        leaf = frags[1].strip() if len(frags) > 1 else ""
        if leaf not in UPDATES:
            continue
        names, note = UPDATES[leaf]
        # The Lean column is the fragment holding the declaration names: it is the
        # third data cell (index 4 counting the leading empty fragment).
        lean_idx = 4
        while lean_idx < len(frags) and not NAME.search(frags[lean_idx]):
            lean_idx += 1
        if lean_idx >= len(frags):
            print(f"{leaf}: no Lean column found", file=sys.stderr)
            continue
        added = [n for n in names if f"`{n}`" not in frags[lean_idx]]
        if added:
            frags[lean_idx] = frags[lean_idx].rstrip() + ", " + ", ".join(f"`{n}`" for n in added)
            print(f"{leaf}: +{len(added)} declarations")
        note = note.strip()
        # Strip a previously inserted (mis-placed) copy of the note.
        frags = [f.replace(note, "") for f in frags]
        row = "|".join(frags)
        row = row.rstrip()
        if not row.endswith("|"):
            row += " |"
        row = row[:-1].rstrip() + note + " |"
        lines[i] = row
        changed = True
    if not changed:
        print("no leaf rows updated")
        return 1
    open(MAP, "w", encoding="utf-8").write("\n".join(lines))
    return 0


if __name__ == "__main__":
    sys.exit(main())

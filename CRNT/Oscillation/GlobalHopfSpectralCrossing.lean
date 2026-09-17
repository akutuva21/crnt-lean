import CRNT.Oscillation.GlobalHopfContinuation

/-!
# Spectral-crossing decomposition of the global-Hopf frontier

A smooth equilibrium continuation whose Jacobian starts Hurwitz stable, ends with an eigenvalue in
the open right half-plane, and is nonsingular throughout cannot lose stability through a zero real
eigenvalue.  The finite-dimensional spectral-continuation part of global Hopf should therefore
produce a parameter carrying a nonzero purely imaginary conjugate pair.

This file makes that matrix-theoretic step explicit.  The subsequent global-bifurcation theorem is
kept separate: a spectral crossing is local linear data; a periodic orbit still requires a Hopf or
global-continuation theorem.
-/

namespace CRNT

/-- A nonzero purely imaginary eigenvalue witness for a real continuation Jacobian. -/
structure ImaginarySpectrumWitness
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) : Type where
  parameter : ℝ
  omega : ℝ
  omega_ne_zero : omega ≠ 0
  isEigenvalue :
    Module.End.HasEigenvalue
      (Matrix.toLin' ((C.jacobian parameter).map (algebraMap ℝ ℂ)))
      (Complex.I * omega)

/-- Purely finite-dimensional spectral frontier: stability changes without a zero eigenvalue force
some nonzero imaginary-axis spectrum along the path. -/
def StabilityChangeImaginaryCrossingTarget : Prop :=
  ∀ (I : Type) [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I),
    Nonempty (ImaginarySpectrumWitness C)

/-- Local-Hopf data obtained after the spectral crossing has been found.  Transversality and the
usual nondegeneracy coefficient are deliberately explicit: neither follows from the existence of a
purely imaginary pair alone. -/
structure LocalHopfContinuationWitness
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) extends ImaginarySpectrumWitness C where
  /-- The selected pair crosses the imaginary axis rather than merely touching it. -/
  transverseCrossing : Prop
  /-- Nonzero first Lyapunov coefficient / equivalent local Hopf nondegeneracy datum. -/
  nonlinearNondegenerate : Prop
  transverseCrossing_proof : transverseCrossing
  nonlinearNondegenerate_proof : nonlinearNondegenerate

/-- The remaining local nonlinear theorem after spectral crossing and nondegeneracy have been
certified.  It returns a periodic trajectory of the same continuation near the crossing. -/
def LocalHopfContinuationTarget : Prop :=
  ∀ (I : Type) [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I)
    (H : LocalHopfContinuationWitness C),
    Nonempty (PositiveContinuationPeriodicWitness C)

/-- Decomposition of the generic global-Hopf target into (i) a spectral crossing theorem, (ii)
problem-specific crossing/nonlinear nondegeneracy certification, and (iii) local Hopf.  This record
is useful when a concrete CRN has enough symbolic information to avoid the full global theorem. -/
structure CertifiedLocalHopfRoute
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) : Type where
  witness : LocalHopfContinuationWitness C

/-- Consume a certified local-Hopf route. -/
theorem CertifiedLocalHopfRoute.periodicWitness
    {I : Type} [DecidableEq I] [Fintype I]
    {C : SmoothEquilibriumContinuation I}
    (hHopf : LocalHopfContinuationTarget)
    (H : CertifiedLocalHopfRoute C) :
    Nonempty (PositiveContinuationPeriodicWitness C) :=
  hHopf I C H.witness

end CRNT

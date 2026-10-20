module

public import RequestProject.NSPhaseGalerkinFourierWeakLimit
public import RequestProject.NSGalerkinFourierIntegral

/-!
# Identification of finite Galerkin rates with the completed-space rate

For every finite Galerkin field, the projected Fourier rate used by the finite
ODE is exactly the `L²`-completed rate evaluated on its embedded velocity
curve.  This is the pointwise bridge needed before passing the integrated
coefficient equation to a limit.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

/-- The finite Galerkin Fourier RHS is the completed-space Fourier RHS evaluated
on the actual embedded Galerkin velocity curve. -/
theorem phaseL2FourierRHSCurve_galerkin_eq
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ)
    (k : Fin 2 → ℤ) (i : Fin 2) (t : GalerkinTime) :
    phaseL2FourierRHSCurve ν phase k i
        (phaseGalerkinL2Curve ν hν phase N) t =
      galerkinFourierRHS ν
        (phaseGalerkinVelocity ν hν phase N t.1) (gForce phase t.1) k i := by
  rw [phaseL2FourierRHSCurve_apply]
  rw [l2FourierCoeff_phaseGalerkinL2Curve]
  unfold galerkinFourierRHS nonlinearFourierFluxVector
  have hnl : (WithLp.toLp 2 (fun j =>
      torusNonlinearFourierFlux k j
        (phaseGalerkinL2Curve ν hν phase N t))) =
      (WithLp.toLp 2 (fun j => nonlinearFourierFlux
        (phaseGalerkinVelocity ν hν phase N t.1) k j)) := by
    ext j
    exact torusNonlinearFourierCurve_phaseGalerkin ν hν phase N k j t
  rw [hnl]

end AnomDiss

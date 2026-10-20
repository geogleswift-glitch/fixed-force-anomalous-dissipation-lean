$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$probeDirectory = Join-Path (Join-Path $projectRoot '.lake') 'verification'
New-Item -ItemType Directory -Force -Path $probeDirectory | Out-Null
$probePath = Join-Path $probeDirectory 'AxiomProbe.lean'

# Lean 4.35 records each exported declaration's transitive axiom dependencies
# in its module. The public collector reads that data for imported declarations
# and traverses local declarations; a type-only check is not an axiom audit.
$probeSource = @'
import Solution
import RequestProject.MainRegularity
import RequestProject.ExistenceInterfaces
import RequestProject.HolderTimeContinuity
import RequestProject.NSPhaseGalerkinRHSBridge
import RequestProject.ScalarGlobalC2Bridge
import RequestProject.ScalarMildTimeEquation
import RequestProject.NSPhaseGalerkinEvolution
import RequestProject.NSPhaseGalerkinMild
import RequestProject.ScalarFluxDerivativeRegularity
import RequestProject.ScalarSchauderSpatial
import RequestProject.ScalarGlobalTimeEquation
import RequestProject.ScalarHessianSchauder
import RequestProject.ScalarHeatTimeSchauder
import RequestProject.HeatDuhamelTimeHolder
import RequestProject.NSPhaseGalerkinSobolevProduct
import RequestProject.ParabolicHolderOperations
import RequestProject.MainWithScalarExistence
import RequestProject.NSPhaseGalerkinQuadraticConvolution
import RequestProject.NSPhaseGalerkinSobolevGain
import RequestProject.FourierSeriesRegularity
import RequestProject.PhaseForceHeatRegularity
import RequestProject.NSPhaseGalerkinH2
import RequestProject.NSPhaseGalerkinHigherHeat
import RequestProject.NSPhaseGalerkinContinuousVelocity
import RequestProject.NSPhaseGalerkinVelocitySpatial
import RequestProject.NSPhaseGalerkinPressureSobolev
import RequestProject.NSPhaseGalerkinPressureReal
import RequestProject.NSPhaseGalerkinTimeBelowOne
import RequestProject.FourierContinuousUniqueness
import RequestProject.MainUnconditional

open Lean Elab Term

run_elab do
  let declarations : Array Name := #[
    `AnomDiss.main_theorem,
    `AnomDiss.main_theorem_all_beta,
    `AnomDiss.main_theorem_from_existence,
    `AnomDiss.IsSmoothHolderValued.exists_continuous_derivatives,
    `AnomDiss.phaseL2FourierRHSCurve_galerkin_eq,
    `AnomDiss.scalar_mild_fixedPoint_contDiff_two_of_flux_derivative_holder,
    `AnomDiss.scalar_mild_fixedPoint_hasDerivWithinAt_of_flux_derivative_holder,
    `AnomDiss.exists_phaseGalerkin_l2_fourier_differentiable_evolution,
    `AnomDiss.exists_phaseGalerkin_l2_fourier_heat_duhamel,
    `AnomDiss.exists_real_periodic_global_scalar_mild_C2,
    `AnomDiss.pd2_heatDuhamel_spatial_schauder,
    `AnomDiss.scalar_mild_fixedPoint_fderiv_spatial_holder,
    `AnomDiss.scalar_mild_fixedPoint_flux_derivative_regular,
    `AnomDiss.exists_real_periodic_global_scalar_bounded_derivatives_equation,
    `AnomDiss.scalar_mild_fixedPoint_hessian_spatial_holder,
    `AnomDiss.pd2_heatOp_timeHolder,
    `AnomDiss.pd_heatOp_timeHolder,
    `AnomDiss.timeHolder_pd2_heatDuhamel_holder,
    `AnomDiss.timeHolder_pd_heatDuhamel_holder,
    `AnomDiss.phaseGalerkin_l2_limit_heat_weighted_gradient_energy,
    `AnomDiss.phaseGalerkin_l2_limit_convolution_coordinate_bound,
    `AnomDiss.scalarClassicalExistence_proved,
    `AnomDiss.externalScalar_proved,
    `AnomDiss.main_theorem_all_beta_with_proved_scalar,
    `AnomDiss.main_theorem_zero_data_with_proved_scalar,
    `AnomDiss.phaseGalerkin_l2_limit_quadraticFourierMoment_eq_tsum,
    `AnomDiss.phaseGalerkin_l2_limit_nonlinearFourierFlux_eq_tsum,
    `AnomDiss.phaseGalerkin_l2_limit_quadratic_fourier_fractional_energy,
    `AnomDiss.phaseGalerkin_l2_limit_source_negative_energy,
    `AnomDiss.exists_phaseGalerkin_l2_limit_uniform_sobolev_below_two,
    `AnomDiss.fourier_heatDuhamel_uniform_sobolev_gain,
    `AnomDiss.contDiff_one_and_pd_holder_complexFourierSeries,
    `AnomDiss.gForce_parHolder,
    `AnomDiss.heatDuhamel_isParabolicC12,
    `AnomDiss.phaseForceHeatComponent_isParabolicC12,
    `AnomDiss.phaseForceHeatComponent_uniform_h2_energy,
    `AnomDiss.phaseForceHeatComponent_fourier_leray,
    `AnomDiss.exists_phaseGalerkin_l2_limit_uniform_h2_energy,
    `AnomDiss.phaseGalerkin_l2_limit_uniform_nonlinear_heat_energy_below_three,
    `AnomDiss.exists_phaseGalerkin_l2_limit_continuous_velocity,
    `AnomDiss.phaseGalerkin_l2_limit_spatial_C1_holder,
    `AnomDiss.phaseGalerkin_l2_limit_continuousVelocity_solenoidal,
    `AnomDiss.gForce_uniform_sobolev_energy,
    `AnomDiss.phaseGalerkin_l2_limit_uniform_sobolev_below_three,
    `AnomDiss.phaseGalerkin_l2_limit_uniform_pressure_sobolev_energy,
    `AnomDiss.phaseGalerkin_l2_limit_real_pressure_gradient_fourier,
    `AnomDiss.phaseGalerkin_l2_limit_uniform_first_moment_time_holder,
    `AnomDiss.continuous_periodic_eq_of_fc_eq,
    `AnomDiss.exists_phase_classical_all_beta,
    `AnomDiss.true_horizontal_existence_proved,
    `AnomDiss.main_theorem_unconditional,
    `AnomDiss.fixed_force_anomalous_dissipation]
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  for declaration in declarations do
    unless env.contains declaration do
      throwError "Missing audited declaration: {declaration}"
    let axioms ← collectAxioms declaration
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on forbidden axiom {axiomName}"
    logInfo m!"Verified {declaration}; transitive axioms {axioms}"
'@

[System.IO.File]::WriteAllText($probePath, $probeSource, [System.Text.UTF8Encoding]::new($false))
Push-Location $projectRoot
try {
    & lake env lean $probePath
    if ($LASTEXITCODE -ne 0) {
        throw "Lean axiom audit failed with exit code $LASTEXITCODE"
    }
} finally {
    Pop-Location
}

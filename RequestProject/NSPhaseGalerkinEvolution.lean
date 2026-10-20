module

public import RequestProject.NSPhaseGalerkinRHSBridge

/-!
# The genuine completed-space Fourier evolution equation

The actual Galerkin solutions converge strongly in the continuous `L²` curve
space. Every fixed frequency is eventually retained, so their exact integrated
equations pass to that same velocity limit. No PDE solution or PDE existence
assertion is supplied as an assumption.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

/-- Strong convergence of the genuine Galerkin velocities passes the exact
integrated equation to the Fourier coefficients of the same `L²` limit. -/
theorem phaseGalerkin_l2_limit_fourier_integral_eq
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (k : Fin 2 → ℤ) (i : Fin 2) (t : GalerkinTime) :
    l2FourierCoeff k i (U t) =
      galerkinTimeIntegralCLM t (phaseL2FourierRHSCurve ν phase k i U) := by
  have hcoeff := phaseGalerkin_l2_coefficient_curve_tendsto ν hν phase hU k i
  have hleft := ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto
    ((l2FourierCoeff k i).compLeftContinuousBounded GalerkinTime U)).comp hcoeff
  have hright := galerkinTimeIntegralCLM_tendsto t
    (phaseL2FourierRHSCurve_tendsto ν phase k i hU)
  have heq : ∀ᶠ n : ℕ in atTop,
      phaseGalerkinCoefficientCurve ν hν phase (φ n) (k, i) t =
        galerkinTimeIntegralCLM t
          (phaseL2FourierRHSCurve ν phase k i (phaseGalerkinL2Curve ν hν phase (φ n))) := by
    filter_upwards [hφ.tendsto_atTop.eventually (fourierFrequencyBox_eventually_mem k)] with n hn
    rw [galerkinTimeIntegralCLM_eq_of_values t _
      (fun s => galerkinFourierRHS ν
        (phaseGalerkinVelocity ν hν phase (φ n) s) (gForce phase s) k i)]
    · exact phaseGalerkin_coefficient_integral_eq ν hν phase (φ n) hn i t.2
    · intro s hs
      exact phaseL2FourierRHSCurve_galerkin_eq ν hν phase (φ n) k i ⟨s, hs⟩
  have heq' : (fun n => galerkinTimeIntegralCLM t
      (phaseL2FourierRHSCurve ν phase k i (phaseGalerkinL2Curve ν hν phase (φ n)))) =ᶠ[atTop]
      (fun n => phaseGalerkinCoefficientCurve ν hν phase (φ n) (k, i) t) := by
    filter_upwards [heq] with n hn using hn.symm
  exact tendsto_nhds_unique hleft (hright.congr' heq')

/-- An actual continuous `L²` velocity curve with zero initial data, the
Galerkin energy bound, and every genuine integrated Fourier equation exists. -/
theorem exists_phaseGalerkin_l2_fourier_evolution
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) :
    ∃ U : GalerkinTime →ᵇ TorusVelocityL2,
      U ⟨0, by norm_num⟩ = 0 ∧
      (∀ t : GalerkinTime, ‖U t‖ ^ 2 ≤ phaseGalerkinEnergyBound phase) ∧
      ∀ k i t, l2FourierCoeff k i (U t) =
        galerkinTimeIntegralCLM t (phaseL2FourierRHSCurve ν phase k i U) := by
  obtain ⟨a, φ, U, hφ, hU, hz, hE, -, -⟩ :=
    exists_phaseGalerkin_l2_limit_with_fourier_identification ν hν phase
  exact ⟨U, hz, hE, phaseGalerkin_l2_limit_fourier_integral_eq ν hν phase hφ hU⟩

/-- The Fourier coefficient of the actual limit is differentiable within the
whole closed time interval, including both endpoints, with its genuine rate. -/
theorem phaseGalerkin_l2_limit_fourier_hasDerivWithinAt
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (k : Fin 2 → ℤ) (i : Fin 2) (t : GalerkinTime) :
    HasDerivWithinAt
      (extendGalerkinTimeCurve
        ((l2FourierCoeff k i).compLeftContinuousBounded GalerkinTime U))
      (phaseL2FourierRHSCurve ν phase k i U t) (Icc 0 1) t.1 := by
  let F := phaseL2FourierRHSCurve ν phase k i U
  have hc := continuous_extendGalerkinTimeCurve F
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t.1)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  rw [extendGalerkinTimeCurve_of_mem F t.2] at hd
  apply hd.hasDerivWithinAt.congr_of_mem _ t.2
  intro s hs
  rw [extendGalerkinTimeCurve_of_mem _ hs]
  exact phaseGalerkin_l2_limit_fourier_integral_eq ν hν phase hφ hU k i ⟨s, hs⟩

/-- Hence every genuine limit Fourier coefficient satisfies the projected
Navier--Stokes ODE at every interior time. -/
theorem phaseGalerkin_l2_limit_fourier_hasDerivAt
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (k : Fin 2 → ℤ) (i : Fin 2) (t : GalerkinTime) (ht : t.1 ∈ Ioo 0 1) :
    HasDerivAt
      (extendGalerkinTimeCurve
        ((l2FourierCoeff k i).compLeftContinuousBounded GalerkinTime U))
      (phaseL2FourierRHSCurve ν phase k i U t) t.1 := by
  exact (phaseGalerkin_l2_limit_fourier_hasDerivWithinAt ν hν phase hφ hU k i t).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- The unconditional output of Galerkin compactness is a genuine `L²`
velocity whose actual Fourier coefficients obey the projected evolution.
This statement asserts coefficient differentiability, not classical spatial
regularity of the velocity. -/
theorem exists_phaseGalerkin_l2_fourier_differentiable_evolution
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) :
    ∃ U : GalerkinTime →ᵇ TorusVelocityL2,
      U ⟨0, by norm_num⟩ = 0 ∧
      (∀ t : GalerkinTime, ‖U t‖ ^ 2 ≤ phaseGalerkinEnergyBound phase) ∧
      (∀ k i t, l2FourierCoeff k i (U t) =
        galerkinTimeIntegralCLM t (phaseL2FourierRHSCurve ν phase k i U)) ∧
      ∀ k i t, HasDerivWithinAt
        (extendGalerkinTimeCurve
          ((l2FourierCoeff k i).compLeftContinuousBounded GalerkinTime U))
        (phaseL2FourierRHSCurve ν phase k i U t) (Icc 0 1) t.1 := by
  obtain ⟨a, φ, U, hφ, hU, hz, hE, -, -⟩ :=
    exists_phaseGalerkin_l2_limit_with_fourier_identification ν hν phase
  exact ⟨U, hz, hE, phaseGalerkin_l2_limit_fourier_integral_eq ν hν phase hφ hU,
    phaseGalerkin_l2_limit_fourier_hasDerivWithinAt ν hν phase hφ hU⟩

end AnomDiss

module

public import RequestProject.FourierTimeEnergy
public import RequestProject.FourierEnergyOperations
public import RequestProject.NSPhaseGalerkinSobolevGain

/-!
# Time energy estimates for the same genuine NS limit

The integrated projected equation gives every actual Fourier increment
as the integral of its actual rate. Uniform rate energy therefore gives
a Lipschitz energy estimate, including both endpoints. The rate estimate
is obtained from genuine velocity and projected-source energies.
-/

@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction
noncomputable section
namespace AnomDiss

theorem phaseGalerkin_l2_limit_fourier_increment_eq_integral
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (i : Fin 2) (k : Fin 2 → ℤ) (s t : GalerkinTime) :
    l2FourierCoeff k i (U t) - l2FourierCoeff k i (U s) =
      ∫ r in s.1..t.1, extendGalerkinTimeCurve (phaseL2FourierRHSCurve ν phase k i U) r := by
  rw [phaseGalerkin_l2_limit_fourier_integral_eq ν hν phase hφ hU k i t,
    phaseGalerkin_l2_limit_fourier_integral_eq ν hν phase hφ hU k i s,
    galerkinTimeIntegralCLM_eq_integral, galerkinTimeIntegralCLM_eq_integral]
  exact intervalIntegral.integral_interval_sub_left
    ((continuous_extendGalerkinTimeCurve _).intervalIntegrable 0 t.1)
    ((continuous_extendGalerkinTimeCurve _).intervalIntegrable 0 s.1)

theorem phaseGalerkin_l2_limit_fourier_increment_energy_of_rate_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {p B : ℝ} (hB : 0 ≤ B) (i : Fin 2)
    (henergy : ∀ r : GalerkinTime,
      Summable (fun k => (1 + fourierEigenvalue k) ^ p *
        ‖phaseL2FourierRHSCurve ν phase k i U r‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ p *
        ‖phaseL2FourierRHSCurve ν phase k i U r‖ ^ 2) ≤ B)
    (s t : GalerkinTime) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ p *
      ‖l2FourierCoeff k i (U t) - l2FourierCoeff k i (U s)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ p *
        ‖l2FourierCoeff k i (U t) - l2FourierCoeff k i (U s)‖ ^ 2) ≤ B * |t.1-s.1| ^ 2 := by
  have hordered (s t : GalerkinTime) (hst : s.1 ≤ t.1) :
      Summable (fun k => (1 + fourierEigenvalue k) ^ p *
        ‖l2FourierCoeff k i (U t) - l2FourierCoeff k i (U s)‖ ^ 2) ∧
        (∑' k, (1 + fourierEigenvalue k) ^ p *
          ‖l2FourierCoeff k i (U t) - l2FourierCoeff k i (U s)‖ ^ 2) ≤ B * |t.1-s.1| ^ 2 := by
    have hh := fourier_integral_energy_le (p := p) hst hB
      (fun r k => extendGalerkinTimeCurve (phaseL2FourierRHSCurve ν phase k i U) r)
      (fun k => continuous_extendGalerkinTimeCurve _) (fun r hr => by
        have hr1 : r ∈ Icc (0 : ℝ) 1 := ⟨s.2.1.trans hr.1, hr.2.trans t.2.2⟩
        simp_rw [extendGalerkinTimeCurve_of_mem _ hr1]
        exact henergy ⟨r, hr1⟩)
    simp_rw [← phaseGalerkin_l2_limit_fourier_increment_eq_integral ν hν phase hφ hU i _ s t] at hh
    simpa only [sq_abs] using hh
  rcases le_total s.1 t.1 with hst | hts
  · exact hordered s t hst
  · have hh := hordered t s hts
    simpa only [norm_sub_rev, abs_sub_comm] using hh

theorem phaseGalerkin_l2_limit_rate_energy_of_velocity_source_energy
    (ν : ℝ) (phase : Phase) (U : GalerkinTime →ᵇ TorusVelocityL2)
    {p A B : ℝ} (i : Fin 2) (t : GalerkinTime)
    (hvelocity : Summable (fun k => (1 + fourierEigenvalue k) ^ (p+2) *
      ‖l2FourierCoeff k i (U t)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ (p+2) * ‖l2FourierCoeff k i (U t)‖ ^ 2) ≤ A)
    (hsource : Summable (fun k => (1 + fourierEigenvalue k) ^ p *
      ‖phaseL2FourierSourceCurve phase k i U t‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ p * ‖phaseL2FourierSourceCurve phase k i U t‖ ^ 2) ≤ B) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ p *
      ‖phaseL2FourierRHSCurve ν phase k i U t‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ p *
        ‖phaseL2FourierRHSCurve ν phase k i U t‖ ^ 2) ≤ 2*(ν^2*A) + 2*B := by
  obtain ⟨hd, hD⟩ := fourier_energy_damping_bound ν
    (fun k => l2FourierCoeff k i (U t)) hvelocity.1 hvelocity.2
  have h := fourier_energy_add_bound
    (fun k => ((-(ν * fourierEigenvalue k) : ℝ) : ℂ) * l2FourierCoeff k i (U t))
    (fun k => phaseL2FourierSourceCurve phase k i U t) hd hsource.1 hD hsource.2
  simpa only [phaseL2FourierRHSCurve_eq_damping_add_source] using h

end AnomDiss

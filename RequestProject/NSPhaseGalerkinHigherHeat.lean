module

public import RequestProject.NSPhaseGalerkinH2

/-!
# Almost-third-order energy of the genuine nonlinear heat contribution

The already proved second-order energy of the actual Galerkin limit gives
first-order energy of its true projected nonlinear source. The genuine
Fourier heat Duhamel estimate consequently supplies every Sobolev order
strictly below three for its nonlinear contribution, uniformly up to time
zero. The final exports obtain the required second-order bound from the
constructed limit itself.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

/-- The explicit first-order nonlinear source energy obtained from a
second-order component energy bound `B`. -/
def phaseNonlinearFirstEnergyBound (B : ℝ) : ℝ :=
  4 * quadraticSobolevAlgebraBound 2 B

theorem phaseNonlinearFirstEnergyBound_nonneg (B : ℝ) :
    0 ≤ phaseNonlinearFirstEnergyBound B :=
  mul_nonneg (by norm_num) (quadraticSobolevAlgebraBound_nonneg 2 B)

/-- The actual nonlinear source has genuine first-order Fourier energy
whenever the component second-order bound has been established. -/
theorem phaseGalerkin_l2_limit_leray_nonlinear_first_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j : Fin 2,
      Summable (fun k => (1 + fourierEigenvalue k) ^ 2 * ‖l2FourierCoeff k j (U t)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ 2 * ‖l2FourierCoeff k j (U t)‖ ^ 2) ≤ B)
    (i : Fin 2) :
    Summable (fun k => (1 + fourierEigenvalue k) *
      ‖fourierLeray k (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q (U t))) i‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) *
        ‖fourierLeray k (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q (U t))) i‖ ^ 2) ≤
          phaseNonlinearFirstEnergyBound B := by
  have he : ∀ j : Fin 2,
      Summable (fun k => (1 + fourierEigenvalue k) ^ (2 : ℝ) *
        ‖l2FourierCoeff k j (U t)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ (2 : ℝ) *
        ‖l2FourierCoeff k j (U t)‖ ^ 2) ≤ B := by
    simpa only [Real.rpow_two] using henergy
  have hh := phaseGalerkin_l2_limit_leray_nonlinear_higher_energy
    ν hν phase hU t (r := 2) (by norm_num) hB he i
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    phaseNonlinearFirstEnergyBound] using hh

/-- The explicit uniform higher heat energy bound for the actual nonlinear
contribution at order `s`, in terms of a proved second-order velocity bound. -/
def phaseHigherNonlinearHeatEnergyBound (ν B s : ℝ) : ℝ :=
  fourierHeatRealGainConstant ((s - 1) / 2) ^ 2 * phaseNonlinearFirstEnergyBound B *
    (1 + ν ^ (-((s - 1) / 2)) * (1 / (1 - (s - 1) / 2))) ^ 2

theorem phaseHigherNonlinearHeatEnergyBound_nonneg (ν B s : ℝ) :
    0 ≤ phaseHigherNonlinearHeatEnergyBound ν B s :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (phaseNonlinearFirstEnergyBound_nonneg B))
    (sq_nonneg _)

/-- Actual negative projected nonlinear heat coefficients gain every
Sobolev order from one through, but excluding, three. -/
theorem phaseGalerkin_l2_limit_nonlinear_heat_energy_below_three_of_h2_bound
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + fourierEigenvalue k) ^ 2 * ‖l2FourierCoeff k j (U t)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ 2 * ‖l2FourierCoeff k j (U t)‖ ^ 2) ≤ B)
    {s : ℝ} (hs₀ : 1 ≤ s) (hs₁ : s < 3) (i : Fin 2) (t : GalerkinTime) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ s *
      ‖heatDuhamelCoefficient fourierEigenvalue ν (phaseL2NonlinearSourceExtension i U) t.1 k‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ s *
        ‖heatDuhamelCoefficient fourierEigenvalue ν (phaseL2NonlinearSourceExtension i U) t.1 k‖ ^ 2) ≤
          phaseHigherNonlinearHeatEnergyBound ν B s := by
  have he : ∀ r ∈ Icc (0 : ℝ) 1, ∀ S : Finset (Fin 2 → ℤ),
      (∑ k ∈ S, (1 + fourierEigenvalue k) ^ (1 : ℝ) *
        ‖phaseL2NonlinearSourceExtension i U r k‖ ^ 2) ≤ phaseNonlinearFirstEnergyBound B := by
    intro r hr S
    obtain ⟨hsum, hbound⟩ := phaseGalerkin_l2_limit_leray_nonlinear_first_energy
      ν hν phase hU ⟨r, hr⟩ hB (fun j => henergy j ⟨r, hr⟩) i
    simp_rw [phaseL2NonlinearSourceExtension_of_mem i U hr, norm_neg, Real.rpow_one]
    exact (hsum.sum_le_tsum S (fun k _ =>
      mul_nonneg (by positivity [fourierEigenvalue_nonneg k]) (sq_nonneg _))).trans hbound
  have hh := fourier_heatDuhamel_uniform_sobolev_gain (p := 1) (γ := s - 1)
    (sub_nonneg.mpr hs₀) (by linarith : s - 1 < 2) hν
    (phaseNonlinearFirstEnergyBound_nonneg B)
    (phaseL2NonlinearSourceExtension i U) (continuous_phaseL2NonlinearSourceExtension i U)
    he t.1 t.2
  simpa only [show (1 : ℝ) + (s - 1) = s by ring, Real.one_rpow,
    phaseHigherNonlinearHeatEnergyBound] using hh

/-- The genuine Galerkin limit itself supplies a single second-order
bound sufficient for every nonlinear heat energy order below three.
There is no second-order velocity or classical-solution premise. -/
theorem phaseGalerkin_l2_limit_uniform_nonlinear_heat_energy_below_three
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, 1 ≤ s → s < 3 → ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + fourierEigenvalue k) ^ s *
        ‖heatDuhamelCoefficient fourierEigenvalue ν (phaseL2NonlinearSourceExtension i U) t.1 k‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ s *
        ‖heatDuhamelCoefficient fourierEigenvalue ν (phaseL2NonlinearSourceExtension i U) t.1 k‖ ^ 2) ≤
          phaseHigherNonlinearHeatEnergyBound ν B s := by
  obtain ⟨B, hB, henergy⟩ := phaseGalerkin_l2_limit_uniform_h2_energy ν hν phase hφ hU
  exact ⟨B, hB, fun _ hs₀ hs₁ i t =>
    phaseGalerkin_l2_limit_nonlinear_heat_energy_below_three_of_h2_bound
      ν hν phase hU hB henergy hs₀ hs₁ i t⟩

/-- Unconditional construction of the same actual zero-initial Galerkin
limit together with all nonlinear heat energies below order three. -/
theorem exists_phaseGalerkin_l2_limit_uniform_nonlinear_heat_energy_below_three
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) :
    ∃ (φ : ℕ → ℕ) (U : GalerkinTime →ᵇ TorusVelocityL2), StrictMono φ ∧
      Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U) ∧
      U ⟨0, by norm_num⟩ = 0 ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, 1 ≤ s → s < 3 → ∀ i : Fin 2, ∀ t : GalerkinTime,
        Summable (fun k => (1 + fourierEigenvalue k) ^ s *
          ‖heatDuhamelCoefficient fourierEigenvalue ν (phaseL2NonlinearSourceExtension i U) t.1 k‖ ^ 2) ∧
        (∑' k, (1 + fourierEigenvalue k) ^ s *
          ‖heatDuhamelCoefficient fourierEigenvalue ν (phaseL2NonlinearSourceExtension i U) t.1 k‖ ^ 2) ≤
            phaseHigherNonlinearHeatEnergyBound ν B s := by
  obtain ⟨φ, U, hφ, hU, hz, _⟩ := exists_phaseGalerkin_l2_limit_uniform_h2_energy ν hν phase
  exact ⟨φ, U, hφ, hU, hz,
    phaseGalerkin_l2_limit_uniform_nonlinear_heat_energy_below_three ν hν phase hφ hU⟩

end AnomDiss

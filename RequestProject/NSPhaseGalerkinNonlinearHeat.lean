module

public import RequestProject.NSPhaseGalerkinHigherProduct

/-!
# Above-second-order smoothing of the actual nonlinear heat contribution

The source is the genuine negative projected quadratic flux of the actual
Galerkin limit. Its proved half-order energy yields order nine-fourths
for its causal heat integral. The linear force contribution is kept
separate; no higher energy of the full velocity is assumed.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction
noncomputable section

namespace AnomDiss

def phaseL2NonlinearSourceExtension (i : Fin 2)
    (U : GalerkinTime →ᵇ TorusVelocityL2) : ℝ → (Fin 2 → ℤ) → ℂ :=
  fun s k => -extendGalerkinTimeCurve
    (lerayFourierCurveComponent k i (fun j => torusNonlinearFourierCurve k j U)) s

theorem continuous_phaseL2NonlinearSourceExtension (i : Fin 2)
    (U : GalerkinTime →ᵇ TorusVelocityL2) (k : Fin 2 → ℤ) :
    Continuous (fun s => phaseL2NonlinearSourceExtension i U s k) :=
  (continuous_extendGalerkinTimeCurve _).neg

theorem phaseL2NonlinearSourceExtension_of_mem (i : Fin 2)
    (U : GalerkinTime →ᵇ TorusVelocityL2) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (k : Fin 2 → ℤ) :
    phaseL2NonlinearSourceExtension i U s k =
      -fourierLeray k (WithLp.toLp 2
        (fun q => torusNonlinearFourierFlux k q (U ⟨s, hs⟩))) i := by
  unfold phaseL2NonlinearSourceExtension
  rw [extendGalerkinTimeCurve_of_mem _ hs, lerayFourierCurveComponent_apply]
  rfl

def phaseNonlinearHalfEnergyBound (ν : ℝ) (phase : Phase) : ℝ :=
  4 * quadraticSobolevAlgebraBound (3 / 2) (phaseL2VelocitySobolevGainBound ν phase (3 / 2))

theorem phaseNonlinearHalfEnergyBound_nonneg (ν : ℝ) (phase : Phase) :
    0 ≤ phaseNonlinearHalfEnergyBound ν phase :=
  mul_nonneg (by norm_num) (quadraticSobolevAlgebraBound_nonneg _ _)

def phaseNonlinearHeatEnergyBound (ν : ℝ) (phase : Phase) : ℝ :=
  fourierHeatRealGainConstant (7 / 8) ^ 2 * phaseNonlinearHalfEnergyBound ν phase *
    (1 + ν ^ (-(7 / 8 : ℝ)) * (1 / (1 - 7 / 8))) ^ 2

theorem phaseNonlinearHeatEnergyBound_nonneg (ν : ℝ) (phase : Phase) :
    0 ≤ phaseNonlinearHeatEnergyBound ν phase :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (phaseNonlinearHalfEnergyBound_nonneg ν phase)) (sq_nonneg _)

/-- The actual nonlinear causal heat term has uniform `H^{9/4}` energy.
The only solution input is the already constructed strong Galerkin limit. -/
theorem phaseGalerkin_l2_limit_nonlinear_heat_energy_nine_fourths
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (i : Fin 2) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ (9 / 4 : ℝ) *
      ‖heatDuhamelCoefficient fourierEigenvalue ν (phaseL2NonlinearSourceExtension i U) t.1 k‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ (9 / 4 : ℝ) *
        ‖heatDuhamelCoefficient fourierEigenvalue ν (phaseL2NonlinearSourceExtension i U) t.1 k‖ ^ 2) ≤
          phaseNonlinearHeatEnergyBound ν phase := by
  have he : ∀ s ∈ Icc (0 : ℝ) 1, ∀ S : Finset (Fin 2 → ℤ),
      (∑ k ∈ S, (1 + fourierEigenvalue k) ^ (1 / 2 : ℝ) *
        ‖phaseL2NonlinearSourceExtension i U s k‖ ^ 2) ≤ phaseNonlinearHalfEnergyBound ν phase := by
    intro s hs S
    obtain ⟨hsum, hbound⟩ := phaseGalerkin_l2_limit_leray_nonlinear_half_energy
      ν hν phase hφ hU ⟨s, hs⟩ i
    simp_rw [phaseL2NonlinearSourceExtension_of_mem i U hs, norm_neg]
    exact (hsum.sum_le_tsum S (fun k _ =>
      mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _))).trans hbound
  have hh := fourier_heatDuhamel_uniform_sobolev_gain (p := 1 / 2) (γ := 7 / 4)
    (by norm_num) (by norm_num) hν (phaseNonlinearHalfEnergyBound_nonneg ν phase)
    (phaseL2NonlinearSourceExtension i U) (continuous_phaseL2NonlinearSourceExtension i U)
    he t.1 t.2
  simpa only [show (1 / 2 : ℝ) + 7 / 4 = 9 / 4 by norm_num,
    show (7 / 4 : ℝ) / 2 = 7 / 8 by norm_num, Real.one_rpow,
    phaseNonlinearHeatEnergyBound] using hh

end AnomDiss

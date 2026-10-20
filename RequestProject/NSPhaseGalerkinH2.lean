module

public import RequestProject.NSPhaseGalerkinNonlinearHeat
public import RequestProject.NSPhaseForceHeatFourier

/-!
# Second-order Sobolev energy of the actual NS Galerkin limit

The true coefficient equation splits into the actual linear force heat
contribution and the actual negative nonlinear heat contribution. The
former has second-order energy by its proved classical heat regularity;
the latter has order nine-fourths by the nonlinear bootstrap. This gives
second-order energy of the original velocity, including time zero.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction
noncomputable section

namespace AnomDiss

theorem phaseGalerkin_l2_limit_fourier_force_nonlinear_split
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (i : Fin 2) (k : Fin 2 → ℤ) :
    l2FourierCoeff k i (U t) = fc (phaseForceHeatComponent ν phase i t.1) k +
      heatDuhamelCoefficient fourierEigenvalue ν (phaseL2NonlinearSourceExtension i U) t.1 k := by
  have hsource (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      phaseL2FourierSourceExtension phase i U s k - phaseL2NonlinearSourceExtension i U s k =
        fourierLeray k (vectorFourierCoeff (gForce phase s) k) i := by
    rw [phaseL2NonlinearSourceExtension_of_mem i U hs,
      phaseL2FourierSourceExtension, extendGalerkinTimeCurve_of_mem _ hs,
      phaseL2FourierSourceCurve_apply]
    ring
  let E : ℝ → ℝ := fun s => Real.exp (-(ν * (t.1 - s) * fourierEigenvalue k))
  have hE : Continuous E := by dsimp only [E]; fun_prop
  have hC : Continuous (fun s : ℝ => Real.exp (-(ν * (t.1 - s) * fourierEigenvalue k)) •
      phaseL2FourierSourceExtension phase i U s k) :=
    hE.fun_smul (continuous_phaseL2FourierSourceExtension phase i U k)
  have hN : Continuous (fun s : ℝ => Real.exp (-(ν * (t.1 - s) * fourierEigenvalue k)) •
      phaseL2NonlinearSourceExtension i U s k) :=
    hE.fun_smul (continuous_phaseL2NonlinearSourceExtension i U k)
  have heq : fc (phaseForceHeatComponent ν phase i t.1) k =
      heatDuhamelCoefficient fourierEigenvalue ν (phaseL2FourierSourceExtension phase i U) t.1 k -
        heatDuhamelCoefficient fourierEigenvalue ν (phaseL2NonlinearSourceExtension i U) t.1 k := by
    rw [phaseForceHeatComponent_fourier_leray hν.le phase i t.2.1 k]
    simp only [heatDuhamelCoefficient_eq_standard]
    rw [← intervalIntegral.integral_sub (hC.intervalIntegrable 0 t.1) (hN.intervalIntegrable 0 t.1)]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.2.1] at hs
    have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans t.2.2⟩
    change E s • _ = E s • _ - E s • _
    rw [← smul_sub, hsource s hs1]
  rw [← phaseGalerkin_l2_limit_fourier_eq_heatDuhamelCoefficient ν hν phase hφ hU k i t] at heq
  exact (sub_eq_iff_eq_add).mp heq.symm

/-- The actual velocity has uniformly bounded `H²` coefficient energy.
No classical solution or second-order velocity energy is assumed. -/
theorem phaseGalerkin_l2_limit_uniform_h2_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U)) :
    ∃ B, 0 ≤ B ∧ ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + fourierEigenvalue k) ^ 2 * ‖l2FourierCoeff k i (U t)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ 2 * ‖l2FourierCoeff k i (U t)‖ ^ 2) ≤ B := by
  classical
  choose BF hBF hForce using fun i : Fin 2 => phaseForceHeatComponent_uniform_h2_energy hν phase i
  refine ⟨2 * (BF 0 + BF 1) + 2 * phaseNonlinearHeatEnergyBound ν phase, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg (by norm_num) (add_nonneg (hBF 0) (hBF 1)))
      (mul_nonneg (by norm_num) (phaseNonlinearHeatEnergyBound_nonneg ν phase))
  intro i t
  let N : (Fin 2 → ℤ) → ℂ := fun k =>
    heatDuhamelCoefficient fourierEigenvalue ν (phaseL2NonlinearSourceExtension i U) t.1 k
  obtain ⟨hsN9, hN9⟩ := phaseGalerkin_l2_limit_nonlinear_heat_energy_nine_fourths
    ν hν phase hφ hU t i
  have hNpoint (k : Fin 2 → ℤ) :
      (1 + fourierEigenvalue k) ^ 2 * ‖N k‖ ^ 2 ≤
        (1 + fourierEigenvalue k) ^ (9 / 4 : ℝ) * ‖N k‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      (by linarith [fourierEigenvalue_nonneg k] : 1 ≤ 1 + fourierEigenvalue k)
      (by norm_num : (2 : ℝ) ≤ 9 / 4)
  have hnN : ∀ k, 0 ≤ (1 + fourierEigenvalue k) ^ 2 * ‖N k‖ ^ 2 :=
    fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsN := hsN9.of_nonneg_of_le hnN hNpoint
  have hNbound := (Summable.tsum_le_tsum hNpoint hsN hsN9).trans hN9
  obtain ⟨hsF, hFbound⟩ := hForce i t.1 t.2
  have hmajor := (hsF.mul_left 2).add (hsN.mul_left 2)
  have hdom (k : Fin 2 → ℤ) :
      (1 + fourierEigenvalue k) ^ 2 * ‖l2FourierCoeff k i (U t)‖ ^ 2 ≤
        2 * ((1 + fourierEigenvalue k) ^ 2 * ‖fc (phaseForceHeatComponent ν phase i t.1) k‖ ^ 2) +
          2 * ((1 + fourierEigenvalue k) ^ 2 * ‖N k‖ ^ 2) := by
    rw [phaseGalerkin_l2_limit_fourier_force_nonlinear_split ν hν phase hφ hU t i k]
    have he : ‖fc (phaseForceHeatComponent ν phase i t.1) k + N k‖ ^ 2 ≤
        2 * ‖fc (phaseForceHeatComponent ν phase i t.1) k‖ ^ 2 + 2 * ‖N k‖ ^ 2 := by
      have hh := (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_add_le
          (fc (phaseForceHeatComponent ν phase i t.1) k) (N k))
      nlinarith [sq_nonneg (‖fc (phaseForceHeatComponent ν phase i t.1) k‖ - ‖N k‖)]
    have hh := mul_le_mul_of_nonneg_left he (sq_nonneg (1 + fourierEigenvalue k))
    dsimp only [N] at hh
    nlinarith only [hh]
  have hs := hmajor.of_nonneg_of_le
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hdom
  refine ⟨hs, (Summable.tsum_le_tsum hdom hs hmajor).trans ?_⟩
  rw [(hsF.mul_left 2).tsum_add (hsN.mul_left 2), tsum_mul_left, tsum_mul_left]
  have hFi : BF i ≤ BF 0 + BF 1 := by
    fin_cases i
    · change BF 0 ≤ BF 0 + BF 1
      linarith [hBF 1]
    · change BF 1 ≤ BF 0 + BF 1
      linarith [hBF 0]
  linarith

/-- Unconditional existence of the same genuine strong limit with
uniform second-order Fourier energy. -/
theorem exists_phaseGalerkin_l2_limit_uniform_h2_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) :
    ∃ (φ : ℕ → ℕ) (U : GalerkinTime →ᵇ TorusVelocityL2), StrictMono φ ∧
      Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U) ∧
      U ⟨0, by norm_num⟩ = 0 ∧
      ∃ B, 0 ≤ B ∧ ∀ i : Fin 2, ∀ t : GalerkinTime,
        Summable (fun k => (1 + fourierEigenvalue k) ^ 2 * ‖l2FourierCoeff k i (U t)‖ ^ 2) ∧
        (∑' k, (1 + fourierEigenvalue k) ^ 2 * ‖l2FourierCoeff k i (U t)‖ ^ 2) ≤ B := by
  obtain ⟨φ, U, hφ, hU, hz, _⟩ := exists_phaseGalerkin_l2_limit_uniform_sobolev_below_two ν hν phase
  exact ⟨φ, U, hφ, hU, hz, phaseGalerkin_l2_limit_uniform_h2_energy ν hν phase hφ hU⟩

end AnomDiss

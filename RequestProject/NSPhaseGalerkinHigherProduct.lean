module

public import RequestProject.FourierSobolevAlgebra
public import RequestProject.NSPhaseGalerkinSobolevGain

/-!
# Higher Sobolev estimates for the actual nonlinear Fourier source

The convolution algebra is applied to the actual limit coefficients. The
physical derivative and Leray estimates already proved for arbitrary real
weight exponents transfer the quadratic estimate to the true nonlinear
term. The final half-order bound uses the proved three-halves velocity
energy, without a classical-solution or higher-regularity premise.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction
noncomputable section

namespace AnomDiss

def quadraticSobolevAlgebraBound (r B : ℝ) : ℝ :=
  4 * (2 ^ r) ^ 2 * (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-r)) * B ^ 2

theorem quadraticSobolevAlgebraBound_nonneg (r B : ℝ) :
    0 ≤ quadraticSobolevAlgebraBound r B := by
  unfold quadraticSobolevAlgebraBound
  have hK : 0 ≤ ∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-r) :=
    tsum_nonneg fun k => Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _
  positivity

theorem phaseGalerkin_l2_limit_quadratic_higher_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) {r B : ℝ} (hr : 1 < r) (hB : 0 ≤ B)
    (henergy : ∀ j : Fin 2,
      Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k j (U t)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k j (U t)‖ ^ 2) ≤ B)
    (j i : Fin 2) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ r *
      ‖torusQuadraticFourierMoment k j i (U t)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ r *
        ‖torusQuadraticFourierMoment k j i (U t)‖ ^ 2) ≤ quadraticSobolevAlgebraBound r B := by
  obtain ⟨_, hs, hb⟩ := fourier_sobolev_convolution_algebra
    (fun k => l2FourierCoeff k j (U t)) (fun k => l2FourierCoeff k i (U t))
    hr (henergy j).1 (henergy i).1
  simp_rw [← phaseGalerkin_l2_limit_quadraticFourierMoment_eq_tsum ν hν phase hU t] at hs hb
  refine ⟨hs, hb.trans ?_⟩
  have hj0 : 0 ≤ ∑' k, (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k j (U t)‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  have hi0 : 0 ≤ ∑' k, (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k i (U t)‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  have hm := mul_le_mul (henergy j).2 (henergy i).2 hi0 hB
  have hK : 0 ≤ ∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-r) :=
    tsum_nonneg fun k => Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _
  unfold quadraticSobolevAlgebraBound
  calc
    _ = (4 * (2 ^ r) ^ 2 * (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-r))) *
        ((∑' k, (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k j (U t)‖ ^ 2) *
          ∑' k, (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k i (U t)‖ ^ 2) := by ring
    _ ≤ (4 * (2 ^ r) ^ 2 * (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-r))) * (B * B) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

theorem phaseGalerkin_l2_limit_leray_nonlinear_higher_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) {r B : ℝ} (hr : 1 < r) (hB : 0 ≤ B)
    (henergy : ∀ j : Fin 2,
      Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k j (U t)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k j (U t)‖ ^ 2) ≤ B)
    (i : Fin 2) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ (r - 1) *
      ‖fourierLeray k (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q (U t))) i‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ (r - 1) *
        ‖fourierLeray k (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q (U t))) i‖ ^ 2) ≤
          4 * quadraticSobolevAlgebraBound r B := by
  let Q := fun (j q : Fin 2) (k : Fin 2 → ℤ) =>
    (1 + fourierEigenvalue k) ^ r * ‖torusQuadraticFourierMoment k j q (U t)‖ ^ 2
  have hQ (j q : Fin 2) : Summable (Q j q) ∧
      (∑' k, Q j q k) ≤ quadraticSobolevAlgebraBound r B :=
    phaseGalerkin_l2_limit_quadratic_higher_energy ν hν phase hU t hr hB henergy j q
  have hsTensor : Summable (quadraticFourierFractionalTensorEnergy (1 - r) (U t)) := by
    have hs := (((hQ 0 0).1.add (hQ 1 0).1).add ((hQ 0 1).1.add (hQ 1 1).1))
    change Summable (fun k => ∑ q : Fin 2, ∑ j : Fin 2,
      (1 + fourierEigenvalue k) ^ (1 - (1 - r)) * ‖torusQuadraticFourierMoment k j q (U t)‖ ^ 2)
    simpa only [quadraticFourierFractionalTensorEnergy, Fin.sum_univ_two,
      show 1 - (1 - r) = r by ring, Q] using hs
  have hbTensor : (∑' k, quadraticFourierFractionalTensorEnergy (1 - r) (U t) k) ≤
      4 * quadraticSobolevAlgebraBound r B := by
    change (∑' k, ∑ q : Fin 2, ∑ j : Fin 2,
      (1 + fourierEigenvalue k) ^ (1 - (1 - r)) * ‖torusQuadraticFourierMoment k j q (U t)‖ ^ 2) ≤ _
    simp only [show 1 - (1 - r) = r by ring, Fin.sum_univ_two]
    change (∑' k, ((Q 0 0 k + Q 1 0 k) + (Q 0 1 k + Q 1 1 k))) ≤ _
    rw [((hQ 0 0).1.add (hQ 1 0).1).tsum_add ((hQ 0 1).1.add (hQ 1 1).1),
      (hQ 0 0).1.tsum_add (hQ 1 0).1, (hQ 0 1).1.tsum_add (hQ 1 1).1]
    linarith [(hQ 0 0).2, (hQ 1 0).2, (hQ 0 1).2, (hQ 1 1).2]
  have hp := fun k => leray_nonlinear_negative_weight_le_tensor k i (U t) (1 - r)
  simp only [show -(1 - r) = r - 1 by ring] at hp
  have hn : ∀ k, 0 ≤ (1 + fourierEigenvalue k) ^ (r - 1) *
      ‖fourierLeray k (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q (U t))) i‖ ^ 2 :=
    fun k => mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  have hs := hsTensor.of_nonneg_of_le hn hp
  exact ⟨hs, (Summable.tsum_le_tsum hp hs hsTensor).trans hbTensor⟩

/-- The actual nonlinear term has positive half-order Fourier energy,
uniformly in time, from the already proved three-halves velocity energy. -/
theorem phaseGalerkin_l2_limit_leray_nonlinear_half_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (i : Fin 2) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ (1 / 2 : ℝ) *
      ‖fourierLeray k (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q (U t))) i‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ (1 / 2 : ℝ) *
        ‖fourierLeray k (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q (U t))) i‖ ^ 2) ≤
          4 * quadraticSobolevAlgebraBound (3 / 2) (phaseL2VelocitySobolevGainBound ν phase (3 / 2)) := by
  have hh := phaseGalerkin_l2_limit_leray_nonlinear_higher_energy ν hν phase hU t
    (r := 3 / 2) (B := phaseL2VelocitySobolevGainBound ν phase (3 / 2))
    (by norm_num) (phaseL2VelocitySobolevGainBound_nonneg ν phase _) (fun j =>
      phaseGalerkin_l2_limit_positive_sobolev_gain ν hν phase hφ hU
        (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num) j t) i
  simpa only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] using hh

end AnomDiss

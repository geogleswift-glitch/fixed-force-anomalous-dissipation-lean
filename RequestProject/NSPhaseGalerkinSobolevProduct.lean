module

public import RequestProject.NSPhaseGalerkinMild

/-!
# Fourier energy, finite products, and positive-time heat smoothing

These are estimates for the actual completed-space velocity coefficients.
The Sobolev bounds are transferred from the genuine Galerkin limit.  The
heat estimate gains arbitrarily many Fourier derivatives at positive heat
time; it is a statement about the heat-regularized coefficients, not yet a
regularity theorem for the nonlinear Navier--Stokes solution itself.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

/-- The true squared Fourier energy of a completed-space velocity. -/
def l2VelocityFourierEnergy (U : TorusVelocityL2) (k : Fin 2 → ℤ) : ℝ :=
  ∑ i : Fin 2, ‖l2FourierCoeff k i U‖ ^ 2

theorem l2VelocityFourierEnergy_nonneg (U : TorusVelocityL2) (k : Fin 2 → ℤ) :
    0 ≤ l2VelocityFourierEnergy U k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Genuine limit coefficients inherit the actual kinetic Fourier bound. -/
theorem phaseGalerkin_l2_limit_fourier_finite_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (S : Finset (Fin 2 → ℤ)) :
    ∑ k ∈ S, l2VelocityFourierEnergy (U t) k ≤ phaseGalerkinEnergyBound phase := by
  have hlim := fun m : GalerkinCoefficientIndex =>
    phaseGalerkin_l2_coefficient_curve_tendsto ν hν phase hU m.1 m.2
  exact phaseGalerkin_limit_finite_energy hlim t S

/-- Genuine limit coefficients inherit the actual squared-gradient bound. -/
theorem phaseGalerkin_l2_limit_fourier_finite_gradient_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (S : Finset (Fin 2 → ℤ)) :
    ∑ k ∈ S, fourierEigenvalue k * l2VelocityFourierEnergy (U t) k ≤
      phaseGalerkinGradientBound ν phase := by
  have hlim := fun m : GalerkinCoefficientIndex =>
    phaseGalerkin_l2_coefficient_curve_tendsto ν hν phase hU m.1 m.2
  exact phaseGalerkin_limit_finite_gradient_energy hlim t S

/-- The genuine completed-space limit has summable kinetic and gradient
Fourier energies, with the proven uniform Galerkin bounds. -/
theorem phaseGalerkin_l2_limit_fourier_sobolev_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) :
    Summable (l2VelocityFourierEnergy (U t)) ∧
      (∑' k, l2VelocityFourierEnergy (U t) k) ≤ phaseGalerkinEnergyBound phase ∧
    Summable (fun k => fourierEigenvalue k * l2VelocityFourierEnergy (U t) k) ∧
      (∑' k, fourierEigenvalue k * l2VelocityFourierEnergy (U t) k) ≤
        phaseGalerkinGradientBound ν phase := by
  have hlim := fun m : GalerkinCoefficientIndex =>
    phaseGalerkin_l2_coefficient_curve_tendsto ν hν phase hU m.1 m.2
  exact ⟨phaseGalerkin_limit_energy_summable hlim t,
    phaseGalerkin_limit_energy_bound hlim t,
    phaseGalerkin_limit_gradient_energy_summable hlim t,
    phaseGalerkin_limit_gradient_energy_bound hlim t⟩

/-- An explicit polynomial-versus-heat multiplier estimate. -/
theorem pow_mul_exp_neg_le_factorial_div {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x)
    (m : ℕ) :
    x ^ m * Real.exp (-(r * x)) ≤ (m.factorial : ℝ) / r ^ m := by
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hexp := Real.pow_div_factorial_le_exp (r * x) (mul_nonneg hr.le hx) m
  have hp : (r * x) ^ m ≤ (m.factorial : ℝ) * Real.exp (r * x) := by
    exact (div_le_iff₀ hfac).mp hexp |>.trans_eq (mul_comm _ _)
  have h := mul_le_mul_of_nonneg_right hp (Real.exp_nonneg (-(r * x)))
  have hcancel : Real.exp (r * x) * Real.exp (-(r * x)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [mul_assoc, hcancel, mul_one, mul_pow] at h
  apply (le_div_iff₀ (pow_pos hr m)).mpr
  nlinarith [h]

/-- Positive heat time gains any prescribed number of Fourier derivatives
from one genuinely summable derivative energy. -/
theorem summable_heat_weighted_gradient_energy
    {E : (Fin 2 → ℤ) → ℝ} (hE : ∀ k, 0 ≤ E k)
    (hs : Summable (fun k => fourierEigenvalue k * E k))
    {r : ℝ} (hr : 0 < r) (m : ℕ) :
    Summable (fun k => fourierEigenvalue k ^ (m + 1) *
      Real.exp (-(r * fourierEigenvalue k)) * E k) := by
  apply (hs.mul_left ((m.factorial : ℝ) / r ^ m)).of_nonneg_of_le
  · intro k
    positivity [fourierEigenvalue_nonneg k, hE k]
  · intro k
    calc
      fourierEigenvalue k ^ (m + 1) * Real.exp (-(r * fourierEigenvalue k)) * E k =
          (fourierEigenvalue k ^ m * Real.exp (-(r * fourierEigenvalue k))) *
            (fourierEigenvalue k * E k) := by ring
      _ ≤ ((m.factorial : ℝ) / r ^ m) * (fourierEigenvalue k * E k) :=
        mul_le_mul_of_nonneg_right
          (pow_mul_exp_neg_le_factorial_div hr (fourierEigenvalue_nonneg k) m)
          (mul_nonneg (fourierEigenvalue_nonneg k) (hE k))

/-- Uniform high-order heat smoothing of the actual strong NS limit's
coefficients, with an explicit constant and no spatial regularity premise. -/
theorem phaseGalerkin_l2_limit_heat_weighted_gradient_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    Summable (fun k => fourierEigenvalue k ^ (m + 1) *
      Real.exp (-(r * fourierEigenvalue k)) * l2VelocityFourierEnergy (U t) k) ∧
    (∑' k, fourierEigenvalue k ^ (m + 1) *
      Real.exp (-(r * fourierEigenvalue k)) * l2VelocityFourierEnergy (U t) k) ≤
        ((m.factorial : ℝ) / r ^ m) * phaseGalerkinGradientBound ν phase := by
  have hE := l2VelocityFourierEnergy_nonneg (U t)
  obtain ⟨-, -, hs, hG⟩ := phaseGalerkin_l2_limit_fourier_sobolev_energy ν hν phase hU t
  have hs' := summable_heat_weighted_gradient_energy hE hs hr m
  refine ⟨hs', ?_⟩
  have hmajor := (hs.mul_left ((m.factorial : ℝ) / r ^ m))
  have hbound : ∀ k,
      fourierEigenvalue k ^ (m + 1) * Real.exp (-(r * fourierEigenvalue k)) *
          l2VelocityFourierEnergy (U t) k ≤
        ((m.factorial : ℝ) / r ^ m) *
          (fourierEigenvalue k * l2VelocityFourierEnergy (U t) k) := by
    intro k
    calc
      _ = (fourierEigenvalue k ^ m * Real.exp (-(r * fourierEigenvalue k))) *
          (fourierEigenvalue k * l2VelocityFourierEnergy (U t) k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_mul_exp_neg_le_factorial_div hr (fourierEigenvalue_nonneg k) m)
        (mul_nonneg (fourierEigenvalue_nonneg k) (hE k))
  calc
    _ ≤ ∑' k, ((m.factorial : ℝ) / r ^ m) *
        (fourierEigenvalue k * l2VelocityFourierEnergy (U t) k) :=
      Summable.tsum_le_tsum hbound hs' hmajor
    _ = ((m.factorial : ℝ) / r ^ m) *
        ∑' k, fourierEigenvalue k * l2VelocityFourierEnergy (U t) k := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hG (by positivity)

/-- An integer frequency multiplier is controlled by the mode's true
Laplace eigenvalue. The physical derivative additionally has factor `2πi`. -/
theorem intFrequency_sq_le_fourierEigenvalue (k : Fin 2 → ℤ) (j : Fin 2) :
    (k j : ℝ) ^ 2 ≤ fourierEigenvalue k := by
  have hs : (k j : ℝ) ^ 2 ≤ ∑ i : Fin 2, (k i : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun i : Fin 2 => (k i : ℝ) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have hp : 1 ≤ 4 * π ^ 2 := by
    have := Real.pi_gt_three
    nlinarith
  have hn : 0 ≤ ∑ i : Fin 2, (k i : ℝ) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  calc
    (k j : ℝ) ^ 2 ≤ ∑ i : Fin 2, (k i : ℝ) ^ 2 := hs
    _ ≤ 4 * π ^ 2 * ∑ i : Fin 2, (k i : ℝ) ^ 2 := by nlinarith
    _ = fourierEigenvalue k := by
      unfold fourierEigenvalue euclNorm intVec
      rw [Real.sq_sqrt hn]

/-- The actual single-coordinate Fourier energy is bounded by the vector
energy. -/
theorem l2FourierCoeff_sq_le_energy (U : TorusVelocityL2) (k : Fin 2 → ℤ) (i : Fin 2) :
    ‖l2FourierCoeff k i U‖ ^ 2 ≤ l2VelocityFourierEnergy U k := by
  exact Finset.single_le_sum (f := fun j : Fin 2 => ‖l2FourierCoeff k j U‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem l2FourierCoeff_coordinate_derivative_sq_le (U : TorusVelocityL2)
    (k : Fin 2 → ℤ) (j i : Fin 2) :
    ‖(k j : ℂ) * l2FourierCoeff k i U‖ ^ 2 ≤
      fourierEigenvalue k * l2VelocityFourierEnergy U k := by
  calc
    _ = (k j : ℝ) ^ 2 * ‖l2FourierCoeff k i U‖ ^ 2 := by
      simp only [norm_mul, mul_pow, Complex.norm_intCast, sq_abs]
    _ ≤ fourierEigenvalue k * ‖l2FourierCoeff k i U‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (intFrequency_sq_le_fourierEigenvalue k j) (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (l2FourierCoeff_sq_le_energy U k i)
      (fourierEigenvalue_nonneg k)

private theorem sum_frequency_sub_image (S : Finset (Fin 2 → ℤ))
    (k : Fin 2 → ℤ) (F : (Fin 2 → ℤ) → ℝ) :
    (∑ l ∈ S, F (k - l)) = ∑ l ∈ S.image (fun l => k - l), F l := by
  rw [Finset.sum_image]
  intro a _ b _ hab
  exact sub_right_inj.mp hab

/-- The integer frequency multiplier of a finite Fourier product is
distributed onto either factor, using genuine Cauchy--Schwarz energies. -/
theorem finite_fourier_convolution_coordinate_bound
    (S : Finset (Fin 2 → ℤ)) (a b : (Fin 2 → ℤ) → ℂ)
    (k : Fin 2 → ℤ) (j : Fin 2) :
    ‖(k j : ℂ) * ∑ l ∈ S, a l * b (k - l)‖ ≤
      Real.sqrt (∑ l ∈ S, ‖(l j : ℂ) * a l‖ ^ 2) *
        Real.sqrt (∑ l ∈ S, ‖b (k - l)‖ ^ 2) +
      Real.sqrt (∑ l ∈ S, ‖a l‖ ^ 2) *
        Real.sqrt (∑ l ∈ S, ‖((k - l) j : ℂ) * b (k - l)‖ ^ 2) := by
  have hdecomp : (k j : ℂ) * ∑ l ∈ S, a l * b (k - l) =
      ∑ l ∈ S, (((l j : ℂ) * a l) * b (k - l) +
        a l * (((k - l) j : ℂ) * b (k - l))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    simp only [Pi.sub_apply, Int.cast_sub]
    ring
  rw [hdecomp]
  calc
    _ ≤ ∑ l ∈ S, ‖((l j : ℂ) * a l) * b (k - l) +
        a l * (((k - l) j : ℂ) * b (k - l))‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ S, (‖(l j : ℂ) * a l‖ * ‖b (k - l)‖ +
        ‖a l‖ * ‖((k - l) j : ℂ) * b (k - l)‖) := by
      apply Finset.sum_le_sum
      intro l _
      simpa only [norm_mul] using norm_add_le
        (((l j : ℂ) * a l) * b (k - l))
        (a l * (((k - l) j : ℂ) * b (k - l)))
    _ = (∑ l ∈ S, ‖(l j : ℂ) * a l‖ * ‖b (k - l)‖) +
        ∑ l ∈ S, ‖a l‖ * ‖((k - l) j : ℂ) * b (k - l)‖ :=
      Finset.sum_add_distrib
    _ ≤ _ := add_le_add
      (Real.sum_mul_le_sqrt_mul_sqrt S (fun l => ‖(l j : ℂ) * a l‖)
        (fun l => ‖b (k - l)‖))
      (Real.sum_mul_le_sqrt_mul_sqrt S (fun l => ‖a l‖)
        (fun l => ‖((k - l) j : ℂ) * b (k - l)‖))

/-- Genuine Galerkin-limit coefficients satisfy a uniform finite product
integer-frequency bound. This is the Fourier form of the elementary H¹ × H¹
product estimate into W¹,¹; it is not yet fractional H¹ product regularity. -/
theorem phaseGalerkin_l2_limit_finite_convolution_coordinate_bound
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (S : Finset (Fin 2 → ℤ)) (k : Fin 2 → ℤ)
    (j i q : Fin 2) :
    ‖(k j : ℂ) * ∑ l ∈ S, l2FourierCoeff l i (U t) * l2FourierCoeff (k - l) q (U t)‖ ≤
      2 * Real.sqrt (phaseGalerkinGradientBound ν phase) *
        Real.sqrt (phaseGalerkinEnergyBound phase) := by
  have hE (R : Finset (Fin 2 → ℤ)) (v : Fin 2) :
      ∑ l ∈ R, ‖l2FourierCoeff l v (U t)‖ ^ 2 ≤ phaseGalerkinEnergyBound phase :=
    (Finset.sum_le_sum fun l _ => l2FourierCoeff_sq_le_energy (U t) l v).trans
      (phaseGalerkin_l2_limit_fourier_finite_energy ν hν phase hU t R)
  have hG (R : Finset (Fin 2 → ℤ)) (v : Fin 2) :
      ∑ l ∈ R, ‖(l j : ℂ) * l2FourierCoeff l v (U t)‖ ^ 2 ≤
        phaseGalerkinGradientBound ν phase :=
    (Finset.sum_le_sum fun l _ => l2FourierCoeff_coordinate_derivative_sq_le (U t) l j v).trans
      (phaseGalerkin_l2_limit_fourier_finite_gradient_energy ν hν phase hU t R)
  have hEshift : ∑ l ∈ S, ‖l2FourierCoeff (k - l) q (U t)‖ ^ 2 ≤
      phaseGalerkinEnergyBound phase := by
    rw [sum_frequency_sub_image S k (fun l => ‖l2FourierCoeff l q (U t)‖ ^ 2)]
    exact hE _ q
  have hGshift : ∑ l ∈ S, ‖((k - l) j : ℂ) * l2FourierCoeff (k - l) q (U t)‖ ^ 2 ≤
      phaseGalerkinGradientBound ν phase := by
    rw [sum_frequency_sub_image S k
      (fun l => ‖(l j : ℂ) * l2FourierCoeff l q (U t)‖ ^ 2)]
    exact hG _ q
  apply (finite_fourier_convolution_coordinate_bound S
    (fun l => l2FourierCoeff l i (U t)) (fun l => l2FourierCoeff l q (U t)) k j).trans
  calc
    _ ≤ Real.sqrt (phaseGalerkinGradientBound ν phase) * Real.sqrt (phaseGalerkinEnergyBound phase) +
        Real.sqrt (phaseGalerkinEnergyBound phase) * Real.sqrt (phaseGalerkinGradientBound ν phase) :=
      add_le_add
        (mul_le_mul (Real.sqrt_le_sqrt (hG S i)) (Real.sqrt_le_sqrt hEshift)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (mul_le_mul (Real.sqrt_le_sqrt (hE S i)) (Real.sqrt_le_sqrt hGshift)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- The convolution defining the Fourier coefficients of a product of
actual limit components is absolutely convergent at every frequency. -/
theorem phaseGalerkin_l2_limit_convolution_norm_summable
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (k : Fin 2 → ℤ) (i q : Fin 2) :
    Summable (fun l => ‖l2FourierCoeff l i (U t) * l2FourierCoeff (k - l) q (U t)‖) := by
  have hE (R : Finset (Fin 2 → ℤ)) (v : Fin 2) :
      ∑ l ∈ R, ‖l2FourierCoeff l v (U t)‖ ^ 2 ≤ phaseGalerkinEnergyBound phase :=
    (Finset.sum_le_sum fun l _ => l2FourierCoeff_sq_le_energy (U t) l v).trans
      (phaseGalerkin_l2_limit_fourier_finite_energy ν hν phase hU t R)
  apply summable_of_sum_le (fun l => norm_nonneg _)
    (c := Real.sqrt (phaseGalerkinEnergyBound phase) * Real.sqrt (phaseGalerkinEnergyBound phase))
  intro S
  have hEshift : ∑ l ∈ S, ‖l2FourierCoeff (k - l) q (U t)‖ ^ 2 ≤
      phaseGalerkinEnergyBound phase := by
    rw [sum_frequency_sub_image S k (fun l => ‖l2FourierCoeff l q (U t)‖ ^ 2)]
    exact hE _ q
  simp_rw [norm_mul]
  exact (Real.sum_mul_le_sqrt_mul_sqrt S (fun l => ‖l2FourierCoeff l i (U t)‖)
    (fun l => ‖l2FourierCoeff (k - l) q (U t)‖)).trans
    (mul_le_mul (Real.sqrt_le_sqrt (hE S i)) (Real.sqrt_le_sqrt hEshift)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- The finite H¹ product integer-frequency bound passes to the absolutely
convergent infinite convolution of actual velocity Fourier coefficients. -/
theorem phaseGalerkin_l2_limit_convolution_coordinate_bound
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (k : Fin 2 → ℤ) (j i q : Fin 2) :
    ‖(k j : ℂ) * ∑' l, l2FourierCoeff l i (U t) * l2FourierCoeff (k - l) q (U t)‖ ≤
      2 * Real.sqrt (phaseGalerkinGradientBound ν phase) *
        Real.sqrt (phaseGalerkinEnergyBound phase) := by
  have hs : Summable (fun l => l2FourierCoeff l i (U t) * l2FourierCoeff (k - l) q (U t)) :=
    (summable_norm_iff).mp (phaseGalerkin_l2_limit_convolution_norm_summable ν hν phase hU t k i q)
  have ht := (hs.hasSum.mul_left (k j : ℂ)).norm
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro S
  simpa only [← Finset.mul_sum] using
    phaseGalerkin_l2_limit_finite_convolution_coordinate_bound ν hν phase hU t S k j i q

end AnomDiss

module

public import RequestProject.NSPhaseGalerkinContinuousVelocity
public import RequestProject.NSPhaseGalerkinSobolevBelowThree

/-!
# Spatial C¹ and Hölder regularity of the actual velocity

A genuine uniform Sobolev energy above 2+β gives a summable physical
first-derivative moment and the exact real derivative character series.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction ComplexConjugate

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 1200000

/-- A uniform square-energy bound supplies the genuine covering-space
moment used to differentiate the actual Fourier reconstruction. -/
theorem phaseL2_uniform_covering_moment_of_sobolev
    {U : GalerkinTime →ᵇ TorusVelocityL2} {r q B : ℝ}
    (hq : 0 ≤ q) (hgap : 1 < r-q) (hB : 0 ≤ B)
    (henergy : ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + fourierEigenvalue k)^r * ‖l2FourierCoeff k i (U t)‖^2) ∧
        (∑' k, (1 + fourierEigenvalue k)^r * ‖l2FourierCoeff k i (U t)‖^2) ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + ‖intVec k‖)^q * ‖l2FourierCoeff k i (U t)‖) ∧
        (∑' k, (1 + ‖intVec k‖)^q * ‖l2FourierCoeff k i (U t)‖) ≤ M := by
  let M := 2^q * (Real.sqrt B *
    Real.sqrt (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k)^(-(r-q))))
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro i t
  obtain ⟨hs, hb⟩ := fourier_covering_weighted_l1_of_sobolev hq hgap (henergy i t).1
  refine ⟨hs, hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (henergy i t).2) (Real.sqrt_nonneg _))
    (by positivity)

lemma summable_absolute_and_first_moment_of_holder_moment
    {a : (Fin 2 → ℤ) → ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hm : Summable (fun k => (1 + ‖intVec k‖)^(1+β) * ‖a k‖)) :
    Summable (fun k => ‖a k‖) ∧ Summable (fun k => ‖intVec k‖ * ‖a k‖) := by
  have hW (k : Fin 2 → ℤ) : 1 ≤ 1 + ‖intVec k‖ := by linarith [norm_nonneg (intVec k)]
  have hp (k : Fin 2 → ℤ) : 1 + ‖intVec k‖ ≤ (1 + ‖intVec k‖)^(1+β) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (hW k)
      (show (1 : ℝ) ≤ 1+β by linarith)
  refine ⟨hm.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_),
    hm.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun k => ?_)⟩
  · exact (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ((hW k).trans (hp k)) (norm_nonneg (a k)))
  · exact mul_le_mul_of_nonneg_right ((by linarith [norm_nonneg (intVec k)] :
      ‖intVec k‖ ≤ 1+‖intVec k‖).trans (hp k)) (norm_nonneg _)

/-- The differentiated character series has a true uniform bound controlled
by the original coefficient moment. -/
theorem norm_pd_complexFourierSeries_of_holder_moment
    {a : (Fin 2 → ℤ) → ℂ} {β M : ℝ} (hβ : 0 ≤ β)
    (hm : Summable (fun k => (1 + ‖intVec k‖)^(1+β) * ‖a k‖))
    (hM : (∑' k, (1 + ‖intVec k‖)^(1+β) * ‖a k‖) ≤ M)
    (j : Fin 2) (x : Pt 2) :
    ‖pd j (complexFourierSeries a) x‖ ≤ ‖(2 * π * Complex.I : ℂ)‖ * M := by
  obtain ⟨ha, hd⟩ := summable_absolute_and_first_moment_of_holder_moment hβ hm
  have hterm (k : Fin 2 → ℤ) :
      ‖(2 * π * Complex.I * (k j : ℂ)) * a k * expChar (intVec k) x‖ ≤
        ‖(2 * π * Complex.I : ℂ)‖ * ((1 + ‖intVec k‖)^(1+β) * ‖a k‖) := by
    have hk : ‖(k j : ℂ)‖ ≤ ‖intVec k‖ := by
      simpa only [Complex.norm_intCast, ← Real.norm_eq_abs, intVec] using norm_le_pi_norm (intVec k) j
    have hW : 1 ≤ 1+‖intVec k‖ := by linarith [norm_nonneg (intVec k)]
    have hp : 1+‖intVec k‖ ≤ (1+‖intVec k‖)^(1+β) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hW
        (show (1 : ℝ) ≤ 1+β by linarith)
    have hk' : ‖(k j : ℂ)‖ ≤ (1+‖intVec k‖)^(1+β) :=
      hk.trans ((by linarith : ‖intVec k‖ ≤ 1+‖intVec k‖).trans hp)
    rw [norm_mul, norm_expChar, mul_one, norm_mul, norm_mul]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk' (norm_nonneg _))
      (norm_nonneg _)).trans_eq (by ring)
  rw [pd_complexFourierSeries ha hd]
  have hb := tsum_of_norm_bounded (hm.mul_left ‖(2 * π * Complex.I : ℂ)‖).hasSum hterm
  rw [tsum_mul_left] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hM (norm_nonneg _))

/-- The original real vector reconstruction has a genuine continuous first
spatial derivative whenever its actual coefficients have this moment. -/
theorem contDiff_phaseL2ContinuousVelocity_of_holder_moment
    {U : GalerkinTime →ᵇ TorusVelocityL2} {β : ℝ} (hβ : 0 ≤ β)
    (hm : ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + ‖intVec k‖)^(1+β) * ‖l2FourierCoeff k i (U t)‖))
    (t : GalerkinTime) : ContDiff ℝ 1 (phaseL2ContinuousVelocity U t) := by
  apply contDiff_pi.mpr
  intro i
  obtain ⟨ha, hd⟩ := summable_absolute_and_first_moment_of_holder_moment hβ (hm i t)
  change ContDiff ℝ 1 (fun x => Complex.reCLM
    (complexFourierSeries (fun k => l2FourierCoeff k i (U t)) x))
  exact Complex.reCLM.contDiff.comp (contDiff_one_complexFourierSeries ha hd)

/-- The actual real vector partial is the real part of the genuine complex
series partial; the assertion is proved by the real chain rule. -/
theorem pd_phaseL2ContinuousVelocity_component_of_holder_moment
    {U : GalerkinTime →ᵇ TorusVelocityL2} {β : ℝ} (hβ : 0 ≤ β)
    (hm : ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + ‖intVec k‖)^(1+β) * ‖l2FourierCoeff k i (U t)‖))
    (t : GalerkinTime) (j i : Fin 2) (x : Pt 2) :
    pd j (phaseL2ContinuousVelocity U t) x i =
      (pd j (complexFourierSeries (fun k => l2FourierCoeff k i (U t))) x).re := by
  have hv := contDiff_phaseL2ContinuousVelocity_of_holder_moment hβ hm t
  rw [← pd_component _ x (hv.differentiable one_ne_zero x)]
  obtain ⟨ha, hd⟩ := summable_absolute_and_first_moment_of_holder_moment hβ (hm i t)
  change pd j (fun y => Complex.reCLM
    (complexFourierSeries (fun k => l2FourierCoeff k i (U t)) y)) x = _
  rw [pd_clm_fun Complex.reCLM _ j
    ((contDiff_one_complexFourierSeries ha hd).differentiable one_ne_zero)]
  rfl

/-- The true physical first derivative contains the complete unit-torus
multiplier 2π i k_j and is an absolutely convergent character series. -/
theorem pd_phaseL2ContinuousVelocity_series_of_holder_moment
    {U : GalerkinTime →ᵇ TorusVelocityL2} {β : ℝ} (hβ : 0 ≤ β)
    (hm : ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + ‖intVec k‖)^(1+β) * ‖l2FourierCoeff k i (U t)‖))
    (t : GalerkinTime) (j i : Fin 2) (x : Pt 2) :
    pd j (phaseL2ContinuousVelocity U t) x i =
      (∑' k, (2 * π * Complex.I * (k j : ℂ)) *
        l2FourierCoeff k i (U t) * expChar (intVec k) x).re := by
  rw [pd_phaseL2ContinuousVelocity_component_of_holder_moment hβ hm]
  obtain ⟨ha, hd⟩ := summable_absolute_and_first_moment_of_holder_moment hβ (hm i t)
  rw [pd_complexFourierSeries ha hd]

/-- One common moment bound gives common actual gradient and spatial
Hölder bounds for the real vector velocity, uniformly throughout time. -/
theorem phaseL2ContinuousVelocity_spatial_regular_of_holder_moment
    {U : GalerkinTime →ᵇ TorusVelocityL2} {β M : ℝ}
    (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (hM : 0 ≤ M)
    (hm : ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + ‖intVec k‖)^(1+β) * ‖l2FourierCoeff k i (U t)‖) ∧
        (∑' k, (1 + ‖intVec k‖)^(1+β) * ‖l2FourierCoeff k i (U t)‖) ≤ M) :
    (∀ t, ContDiff ℝ 1 (phaseL2ContinuousVelocity U t)) ∧
      (∀ t j x, ‖pd j (phaseL2ContinuousVelocity U t) x‖ ≤
        ‖(2 * π * Complex.I : ℂ)‖ * M) ∧
      ∀ t j x y, ‖pd j (phaseL2ContinuousVelocity U t) x -
        pd j (phaseL2ContinuousVelocity U t) y‖ ≤
          (fourierSeriesDerivativeHolderConstant β * M) * ‖x-y‖^β := by
  let hs := fun i t => (hm i t).1
  refine ⟨contDiff_phaseL2ContinuousVelocity_of_holder_moment hβ₀ hs, ?_, ?_⟩
  · intro t j x
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) hM)).mpr
    intro i
    rw [pd_phaseL2ContinuousVelocity_component_of_holder_moment hβ₀ hs]
    have hr := Complex.abs_re_le_norm
      (pd j (complexFourierSeries (fun k => l2FourierCoeff k i (U t))) x)
    rw [Real.norm_eq_abs]
    exact hr.trans (norm_pd_complexFourierSeries_of_holder_moment hβ₀ (hm i t).1 (hm i t).2 j x)
  · intro t j x y
    apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg (mul_nonneg (fourierSeriesDerivativeHolderConstant_nonneg β) hM)
        (Real.rpow_nonneg (norm_nonneg _) _))).mpr
    intro i
    simp only [Pi.sub_apply, pd_phaseL2ContinuousVelocity_component_of_holder_moment hβ₀ hs]
    rw [Real.norm_eq_abs, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans
      (pd_holder_complexFourierSeries_of_moment_bound hβ₀ hβ₁ (hm i t).1 (hm i t).2 j x y)

/-- The genuine continuous representative retains the actual zero initial
value coefficient by coefficient. -/
theorem phaseGalerkin_l2_limit_continuousVelocity_initial
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U)) :
    phaseL2ContinuousVelocity U ⟨0, by norm_num⟩ = 0 := by
  ext x i
  simp only [phaseL2ContinuousVelocity, complexFourierSeries, complexFourierSeriesTerm,
    phaseGalerkin_l2_limit_fourier_initial_zero ν hν phase hU,
    zero_mul, tsum_zero, Complex.zero_re, Pi.zero_apply]

/-- The actual NS limit has a common physical first-derivative Hölder
moment for every β<1, earned from its proved H^r energy with r>2+β. -/
theorem phaseGalerkin_l2_limit_spatial_holder_moment
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + ‖intVec k‖)^(1+β) * ‖l2FourierCoeff k i (U t)‖) ∧
        (∑' k, (1 + ‖intVec k‖)^(1+β) * ‖l2FourierCoeff k i (U t)‖) ≤ M := by
  let r := (β+5)/2
  have hr₀ : 0 < r := by dsimp [r]; linarith
  have hr₃ : r < 3 := by dsimp [r]; linarith
  obtain ⟨B, hB, henergy⟩ := phaseGalerkin_l2_limit_uniform_sobolev_below_three
    ν hν phase hφ hU hr₀ hr₃
  exact phaseL2_uniform_covering_moment_of_sobolev (by linarith)
    (show 1 < r-(1+β) by dsimp [r]; linarith) hB henergy

/-- The actual real velocity is C¹ in space and its actual first partials
have common global β-Hölder and uniform bounds, for every original β<1. -/
theorem phaseGalerkin_l2_limit_spatial_C1_holder
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ t, ContDiff ℝ 1 (phaseL2ContinuousVelocity U t)) ∧
      (∀ t j x, ‖pd j (phaseL2ContinuousVelocity U t) x‖ ≤
        ‖(2 * π * Complex.I : ℂ)‖ * M) ∧
      ∀ t j x y, ‖pd j (phaseL2ContinuousVelocity U t) x -
        pd j (phaseL2ContinuousVelocity U t) y‖ ≤
          (fourierSeriesDerivativeHolderConstant β * M) * ‖x-y‖^β := by
  obtain ⟨M, hM, hm⟩ := phaseGalerkin_l2_limit_spatial_holder_moment ν hν phase hφ hU hβ₀ hβ₁
  exact ⟨M, hM, phaseL2ContinuousVelocity_spatial_regular_of_holder_moment hβ₀ hβ₁.le hM hm⟩

theorem phaseGalerkin_l2_limit_continuousVelocity_contDiff
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) : ContDiff ℝ 1 (phaseL2ContinuousVelocity U t) := by
  obtain ⟨M, hM, hc, hbound, hholder⟩ := phaseGalerkin_l2_limit_spatial_C1_holder
    ν hν phase hφ hU (β := 0) (by norm_num) (by norm_num)
  exact hc t

/-- The physical derivative series belongs to the actual limit and has no
regularity premise in addition to the genuine Galerkin-limit witness. -/
theorem phaseGalerkin_l2_limit_continuousVelocity_partial_series
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (j i : Fin 2) (x : Pt 2) :
    pd j (phaseL2ContinuousVelocity U t) x i =
      (∑' k, (2 * π * Complex.I * (k j : ℂ)) *
        l2FourierCoeff k i (U t) * expChar (intVec k) x).re := by
  obtain ⟨M, hM, hm⟩ := phaseGalerkin_l2_limit_spatial_holder_moment
    ν hν phase hφ hU (β := 0) (by norm_num) (by norm_num)
  exact pd_phaseL2ContinuousVelocity_series_of_holder_moment
    (by norm_num : (0 : ℝ) ≤ 0) (fun i t => (hm i t).1) t j i x

/-- Fourier incompressibility of the original Galerkin limit becomes the
actual pointwise zero-divergence equation for its earned C¹ field. -/
theorem phaseGalerkin_l2_limit_continuousVelocity_solenoidal
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (x : Pt 2) : divergence (phaseL2ContinuousVelocity U t) x = 0 := by
  obtain ⟨M, hM, hm⟩ := phaseGalerkin_l2_limit_spatial_holder_moment
    ν hν phase hφ hU (β := 0) (by norm_num) (by norm_num)
  have hd (i : Fin 2) := (summable_absolute_and_first_moment_of_holder_moment
    (by norm_num : (0 : ℝ) ≤ 0) (hm i t).1).2
  have hs (i : Fin 2) := summable_pd_complexFourierSeries (hd i) i x
  have hlim := fun m : GalerkinCoefficientIndex =>
    phaseGalerkin_l2_coefficient_curve_tendsto ν hν phase hU m.1 m.2
  have hz (k : Fin 2 → ℤ) :
      (2 * π * Complex.I * (k 0 : ℂ)) * l2FourierCoeff k 0 (U t) * expChar (intVec k) x +
        (2 * π * Complex.I * (k 1 : ℂ)) * l2FourierCoeff k 1 (U t) * expChar (intVec k) x = 0 := by
    have hdiv := phaseGalerkin_limit_coefficient_solenoidal hlim t k
    simp only [Fin.sum_univ_two] at hdiv
    change (k 0 : ℂ) * l2FourierCoeff k 0 (U t) +
      (k 1 : ℂ) * l2FourierCoeff k 1 (U t) = 0 at hdiv
    calc
      _ = (2 * π * Complex.I * expChar (intVec k) x) *
          ((k 0 : ℂ) * l2FourierCoeff k 0 (U t) + (k 1 : ℂ) * l2FourierCoeff k 1 (U t)) := by ring
      _ = 0 := by rw [hdiv, mul_zero]
  simp only [divergence, Fin.sum_univ_two,
    phaseGalerkin_l2_limit_continuousVelocity_partial_series ν hν phase hφ hU]
  rw [← Complex.add_re, ← (hs 0).tsum_add (hs 1)]
  simp only [hz, tsum_zero, Complex.zero_re]

end AnomDiss

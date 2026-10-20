module

public import RequestProject.NSPhaseGalerkinPressureSobolev
public import RequestProject.NSPhaseGalerkinContinuousVelocity

/-!
# Genuine real pressure and the complementary Leray gradient

Reality of the actual quadratic Fourier moments gives reality of the
pressure coefficients. Their true real character series is periodic and
has the spatial regularity earned by the pressure Sobolev estimates.
The Fourier gradient has the sign `P N - N` in the momentum equation.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction ComplexConjugate

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 1600000

theorem torusQuadraticFourierMoment_neg_conj (V : TorusVelocityL2)
    (k : Fin 2 → ℤ) (j i : Fin 2) :
    torusQuadraticFourierMoment (-k) j i V = conj (torusQuadraticFourierMoment k j i V) := by
  unfold torusQuadraticFourierMoment
  rw [torusQuadraticFourierBilinear_integral, torusQuadraticFourierBilinear_integral,
    ← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [map_mul, Complex.conj_ofReal, ← expChar_neg_eq_conj, intVec_neg, neg_neg]

theorem fourierEigenvalue_neg (k : Fin 2 → ℤ) :
    fourierEigenvalue (-k) = fourierEigenvalue k := by
  simp only [fourierEigenvalue, intVec_neg, euclNorm_neg]

theorem torusPressureFourierCoefficient_neg_conj (V : TorusVelocityL2) (k : Fin 2 → ℤ) :
    torusPressureFourierCoefficient V (-k) = conj (torusPressureFourierCoefficient V k) := by
  by_cases hk : k = 0
  · subst k
    simp [torusPressureFourierCoefficient]
  have hneg : -k ≠ 0 := neg_ne_zero.mpr hk
  have hd (i : Fin 2) : (2 * π * Complex.I * ((-k) i : ℂ)) =
      conj (2 * π * Complex.I * (k i : ℂ)) := by
    simp only [Pi.neg_apply, Int.cast_neg, map_mul, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I, map_intCast]
    ring
  unfold torusPressureFourierCoefficient
  rw [if_neg hneg, if_neg hk, map_div₀, Complex.conj_ofReal, fourierEigenvalue_neg]
  congr 1
  simp only [map_sum, map_mul, torusQuadraticFourierMoment_neg_conj, hd]

theorem continuous_torusPressureFourierCoefficient (k : Fin 2 → ℤ) :
    Continuous (fun V : TorusVelocityL2 => torusPressureFourierCoefficient V k) := by
  unfold torusPressureFourierCoefficient
  split_ifs
  · exact continuous_const
  · exact (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      continuous_const.mul (continuous_torusQuadraticFourierMoment k j i)).div_const _

/-- The actual real pressure is one fixed series, independent of the
Hölder exponent used to estimate it. -/
def torusRealPressure (V : TorusVelocityL2) (x : Pt 2) : ℝ :=
  (complexFourierSeries (torusPressureFourierCoefficient V) x).re

def phaseL2PressureExtension (U : GalerkinTime →ᵇ TorusVelocityL2)
    (s : ℝ) (x : Pt 2) : ℝ :=
  torusRealPressure (U (projIcc 0 1 (by norm_num) s)) x

theorem phaseL2PressureExtension_of_mem (U : GalerkinTime →ᵇ TorusVelocityL2)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    phaseL2PressureExtension U s = torusRealPressure (U ⟨s, hs⟩) := by
  funext x
  change torusRealPressure (U (projIcc 0 1 (by norm_num) s)) x = _
  rw [projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hs]

theorem isPeriodic_torusRealPressure (V : TorusVelocityL2) : IsPeriodic (torusRealPressure V) := by
  intro x m
  exact congrArg Complex.re (isPeriodic_complexFourierSeries (torusPressureFourierCoefficient V) x m)

theorem phaseGalerkin_l2_limit_pressure_absolute
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) : Summable (fun k => ‖torusPressureFourierCoefficient (U t) k‖) := by
  obtain ⟨C, hC, henergy⟩ := phaseGalerkin_l2_limit_uniform_pressure_sobolev_energy
    ν hν phase hφ hU (δ := 1/2) (by norm_num) (by norm_num)
  obtain ⟨hs, _⟩ := fourier_weighted_l1_of_sobolev (q := 0)
    (by norm_num : (1 : ℝ) < (3-1/2)-0) (henergy t).1
  simpa only [Real.rpow_zero, one_mul] using hs

theorem phaseGalerkin_l2_limit_pressure_series_eq_real
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) :
    (fun x => (torusRealPressure (U t) x : ℂ)) =
      complexFourierSeries (torusPressureFourierCoefficient (U t)) := by
  funext x
  apply Complex.ext
  · rfl
  · exact (complexFourierSeries_real_of_symmetry
      (phaseGalerkin_l2_limit_pressure_absolute ν hν phase hφ hU t)
      (torusPressureFourierCoefficient_neg_conj (U t)) x).symm

theorem contDiff_torusRealPressure_slice
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) : ContDiff ℝ 1 (torusRealPressure (U t)) :=
  Complex.reCLM.contDiff.comp
    ((phaseGalerkin_l2_limit_pressure_spatial_C1_holder ν hν phase hφ hU
      (β := 0) (by norm_num) (by norm_num)).1 t)

theorem pd_torusRealPressure_slice
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (j : Fin 2) (x : Pt 2) :
    pd j (torusRealPressure (U t)) x =
      (pd j (complexFourierSeries (torusPressureFourierCoefficient (U t))) x).re := by
  have hc := (phaseGalerkin_l2_limit_pressure_spatial_C1_holder ν hν phase hφ hU
    (β := 0) (by norm_num) (by norm_num)).1 t
  change pd j (fun y => Complex.reCLM (complexFourierSeries
    (torusPressureFourierCoefficient (U t)) y)) x = _
  rw [pd_clm_fun Complex.reCLM _ j (hc.differentiable one_ne_zero)]
  rfl

theorem phaseGalerkin_l2_limit_real_pressure_spatial_holder
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) :
    ∃ H, 0 ≤ H ∧ ∀ t : GalerkinTime, ∀ j x y,
      ‖pd j (torusRealPressure (U t)) x - pd j (torusRealPressure (U t)) y‖ ≤ H * ‖x-y‖ ^ β := by
  obtain ⟨_, H, hH, hh⟩ := phaseGalerkin_l2_limit_pressure_spatial_C1_holder
    ν hν phase hφ hU hβ₀ hβ₁
  refine ⟨H, hH, ?_⟩
  intro t j x y
  rw [pd_torusRealPressure_slice ν hν phase hφ hU,
    pd_torusRealPressure_slice ν hν phase hφ hU]
  have hr := Complex.abs_re_le_norm
    (pd j (complexFourierSeries (torusPressureFourierCoefficient (U t))) x -
      pd j (complexFourierSeries (torusPressureFourierCoefficient (U t))) y)
  have hreal : ‖(pd j (complexFourierSeries (torusPressureFourierCoefficient (U t))) x).re -
      (pd j (complexFourierSeries (torusPressureFourierCoefficient (U t))) y).re‖ ≤
      ‖pd j (complexFourierSeries (torusPressureFourierCoefficient (U t))) x -
        pd j (complexFourierSeries (torusPressureFourierCoefficient (U t))) y‖ := by
    simpa only [Real.norm_eq_abs, Complex.sub_re] using hr
  exact hreal.trans (hh t j x y)

theorem fourierEigenvalue_eq_wave_norm_sq (k : Fin 2 → ℤ) :
    fourierEigenvalue k = 4 * π ^ 2 * ‖fourierWave k‖ ^ 2 := by
  unfold fourierEigenvalue euclNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), norm_fourierWave_sq]
  rfl

/-- The actual pressure gradient is the negative complementary Leray
part of the nonlinear flux: this is the sign needed in `N + ∇p = P N`. -/
theorem torus_pressure_gradient_coefficient_eq_leray_complement
    (V : TorusVelocityL2) (k : Fin 2 → ℤ) (i : Fin 2) :
    (2 * π * Complex.I * (k i : ℂ)) * torusPressureFourierCoefficient V k =
      fourierLeray k (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q V)) i -
        torusNonlinearFourierFlux k i V := by
  by_cases hk : k = 0
  · subst k
    simp only [Pi.zero_apply, Int.cast_zero, mul_zero, zero_mul, fourierLeray_zero_mode,
      PiLp.toLp_apply, sub_self]
  let C : ℂ := 2 * π * Complex.I
  let N : FourierVelocity := WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q V)
  let W : ℂ := ((‖fourierWave k‖ ^ 2 : ℝ) : ℂ)
  have hEig : (fourierEigenvalue k : ℂ) ≠ 0 := by
    have hr : fourierEigenvalue k ≠ 0 := ne_of_gt
      (lt_of_lt_of_le zero_lt_one (one_le_fourierEigenvalue_of_ne_zero k hk))
    exact_mod_cast hr
  have hfactor : C * C * W = -(fourierEigenvalue k : ℂ) := by
    rw [fourierEigenvalue_eq_wave_norm_sq]
    dsimp [C, W]
    push_cast
    calc
      _ = 4 * (π : ℂ) ^ 2 * Complex.I ^ 2 * (‖fourierWave k‖ : ℂ) ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hW : W ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfactor
    exact hEig (neg_eq_zero.mp hfactor.symm)
  have hquot : (C*C) / (fourierEigenvalue k : ℂ) = (-1) / W :=
    (div_eq_div_iff hEig hW).mpr (by simpa only [neg_one_mul] using hfactor)
  have hsource : (∑ p : Fin 2, ∑ j : Fin 2,
      ((2 * π * Complex.I * (k p : ℂ)) * (2 * π * Complex.I * (k j : ℂ))) *
        torusQuadraticFourierMoment k j p V) = C * fourierDivSymbol k N := by
    simp only [fourierDivSymbol, N, torusNonlinearFourierFlux,
      Fin.sum_univ_two, C]
    ring
  rw [fourierLeray_apply_formula]
  change (C * (k i : ℂ)) * torusPressureFourierCoefficient V k =
    N i - (fourierDivSymbol k N / W) * (k i : ℂ) - N i
  rw [torusPressureFourierCoefficient, if_neg hk, hsource]
  calc
    _ = ((C*C) / (fourierEigenvalue k : ℂ)) * ((k i : ℂ) * fourierDivSymbol k N) := by ring
    _ = ((-1) / W) * ((k i : ℂ) * fourierDivSymbol k N) := by rw [hquot]
    _ = _ := by ring

/-- The integral Fourier coefficients of the genuine real pressure are
exactly the coefficients from the original quadratic tensor. -/
theorem phaseGalerkin_l2_limit_real_pressure_fourier
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (k : Fin 2 → ℤ) :
    fc (fun x => (torusRealPressure (U t) x : ℂ)) k = torusPressureFourierCoefficient (U t) k := by
  exact fc_re_complexFourierSeries
    (phaseGalerkin_l2_limit_pressure_absolute ν hν phase hφ hU t)
    (torusPressureFourierCoefficient_neg_conj (U t)) k

/-- The genuine spatial pressure derivative, tested by the original
cell integral, is the negative complementary Leray nonlinear component. -/
theorem phaseGalerkin_l2_limit_real_pressure_gradient_fourier
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (k : Fin 2 → ℤ) (i : Fin 2) :
    fc (fun x => ((pd i (torusRealPressure (U t)) x : ℝ) : ℂ)) k =
      fourierLeray k (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q (U t))) i -
        torusNonlinearFourierFlux k i (U t) := by
  have hc := contDiff_torusRealPressure_slice ν hν phase hφ hU t
  have he : pd i (fun x => (torusRealPressure (U t) x : ℂ)) =
      fun x => ((pd i (torusRealPressure (U t)) x : ℝ) : ℂ) :=
    pd_clm_fun Complex.ofRealCLM _ i (hc.differentiable one_ne_zero)
  have hcc : ContDiff ℝ 1 (fun x => (torusRealPressure (U t) x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hc
  rw [← he, fc_pd _ hcc
    (fun x m => by rw [isPeriodic_torusRealPressure (U t) x m]) i k,
    phaseGalerkin_l2_limit_real_pressure_fourier ν hν phase hφ hU t k]
  exact torus_pressure_gradient_coefficient_eq_leray_complement (U t) k i

end AnomDiss

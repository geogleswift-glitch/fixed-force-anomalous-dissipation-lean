module

public import RequestProject.NSPhaseGalerkinSobolevProduct

/-!
# Real-order heat multipliers and integrable Duhamel smoothing kernels

These estimates concern the genuine heat exponential and the true Laplace
symbol. They do not assume smoothness of a Navier–Stokes solution.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

/-- A concrete constant for arbitrary nonnegative real smoothing gain. -/
def fourierHeatRealGainConstant (α : ℝ) : ℝ :=
  2 ^ α * max (1 : ℝ) ((Nat.ceil α).factorial : ℝ)

lemma fourierHeatRealGainConstant_nonneg (α : ℝ) :
    0 ≤ fourierHeatRealGainConstant α := by
  unfold fourierHeatRealGainConstant
  positivity

/-- A real power times a decaying exponential is bounded explicitly, without
rounding the time singularity up to an integer power. -/
theorem rpow_mul_exp_neg_le_ceil_factorial {α y : ℝ}
    (hα : 0 ≤ α) (hy : 0 ≤ y) :
    y ^ α * Real.exp (-y) ≤ max (1 : ℝ) ((Nat.ceil α).factorial : ℝ) := by
  by_cases hy1 : y ≤ 1
  · have hp : y ^ α ≤ 1 := Real.rpow_le_one hy hy1 hα
    have he : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)
    exact ((mul_le_mul hp he (Real.exp_nonneg _) (by norm_num)).trans_eq
      (one_mul (1 : ℝ))).trans (le_max_left _ _)
  · have hy1' : 1 ≤ y := (lt_of_not_ge hy1).le
    have hp : y ^ α ≤ y ^ (Nat.ceil α : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hy1' (Nat.le_ceil α)
    have hn := pow_mul_exp_neg_le_factorial_div (r := 1) (x := y) (by norm_num) hy (Nat.ceil α)
    simp only [one_mul, one_pow, div_one] at hn
    exact ((mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)).trans
      (by simpa only [Real.rpow_natCast] using hn)).trans (le_max_right _ _)

/-- The exact real-order time singularity of the homogeneous heat multiplier. -/
theorem rpow_mul_exp_neg_mul_le {α r x : ℝ}
    (hα : 0 ≤ α) (hr : 0 < r) (hx : 0 ≤ x) :
    x ^ α * Real.exp (-(r * x)) ≤
      max (1 : ℝ) ((Nat.ceil α).factorial : ℝ) * r ^ (-α) := by
  have hb := rpow_mul_exp_neg_le_ceil_factorial hα (mul_nonneg hr.le hx)
  have hid : x ^ α * Real.exp (-(r * x)) =
      r ^ (-α) * ((r * x) ^ α * Real.exp (-(r * x))) := by
    rw [Real.mul_rpow hr.le hx, Real.rpow_neg hr.le]
    have hne : r ^ α ≠ 0 := (Real.rpow_pos_of_pos hr α).ne'
    field_simp
  rw [hid]
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hr.le _)).trans_eq (mul_comm _ _)

/-- Positive heat time gives arbitrary real inhomogeneous Fourier gain,
with exactly the real-order singularity `r^(-α)`. -/
theorem one_add_rpow_mul_exp_neg_mul_le {α r x : ℝ}
    (hα : 0 ≤ α) (hr : 0 < r) (hx : 0 ≤ x) :
    (1 + x) ^ α * Real.exp (-(r * x)) ≤
      fourierHeatRealGainConstant α * (1 + r ^ (-α)) := by
  let A : ℝ := max (1 : ℝ) ((Nat.ceil α).factorial : ℝ)
  have hA : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hA1 : 1 ≤ A := le_max_left _ _
  have hpow : 0 ≤ (2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
  have hrpow : 0 ≤ r ^ (-α) := Real.rpow_nonneg hr.le _
  by_cases hx1 : x ≤ 1
  · have hp : (1 + x) ^ α ≤ (2 : ℝ) ^ α :=
      Real.rpow_le_rpow (by positivity) (by linarith) hα
    have he : Real.exp (-(r * x)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hr.le hx))
    have hAA : 1 ≤ A * (1 + r ^ (-α)) :=
      hA1.trans (le_mul_of_one_le_right hA (by linarith))
    calc
      _ ≤ (2 : ℝ) ^ α := by
        exact (mul_le_mul hp he (Real.exp_nonneg _) hpow).trans_eq (mul_one _)
      _ ≤ (2 : ℝ) ^ α * (A * (1 + r ^ (-α))) :=
        le_mul_of_one_le_right hpow hAA
      _ = _ := by unfold fourierHeatRealGainConstant; dsimp [A]; ring
  · have hx1' : 1 ≤ x := (lt_of_not_ge hx1).le
    have hp : (1 + x) ^ α ≤ (2 * x) ^ α :=
      Real.rpow_le_rpow (by positivity) (by linarith) hα
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx] at hp
    calc
      _ ≤ ((2 : ℝ) ^ α * x ^ α) * Real.exp (-(r * x)) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
      _ = (2 : ℝ) ^ α * (x ^ α * Real.exp (-(r * x))) := by ring
      _ ≤ (2 : ℝ) ^ α * (A * r ^ (-α)) :=
        mul_le_mul_of_nonneg_left (rpow_mul_exp_neg_mul_le hα hr hx) hpow
      _ ≤ (2 : ℝ) ^ α * (A * (1 + r ^ (-α))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by linarith : r ^ (-α) ≤ 1 + r ^ (-α)) hA) hpow
      _ = _ := by unfold fourierHeatRealGainConstant; dsimp [A]; ring

/-- The genuine Laplace symbol satisfies the arbitrary-real-gain multiplier
bound at every positive heat time. -/
theorem fourier_heat_real_gain_multiplier {α r : ℝ}
    (hα : 0 ≤ α) (hr : 0 < r) (k : Fin 2 → ℤ) :
    (1 + fourierEigenvalue k) ^ α * Real.exp (-(r * fourierEigenvalue k)) ≤
      fourierHeatRealGainConstant α * (1 + r ^ (-α)) :=
  one_add_rpow_mul_exp_neg_mul_le hα hr (fourierEigenvalue_nonneg k)

/-- Positive heat time upgrades any genuinely summable real-order Fourier
energy by any nonnegative real gain. -/
theorem summable_heat_real_gain_energy {E : (Fin 2 → ℤ) → ℝ} {p α r : ℝ}
    (hE : ∀ k, 0 ≤ E k)
    (hs : Summable (fun k => (1 + fourierEigenvalue k) ^ p * E k))
    (hα : 0 ≤ α) (hr : 0 < r) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ (p + α) *
      Real.exp (-(r * fourierEigenvalue k)) * E k) := by
  apply (hs.mul_left (fourierHeatRealGainConstant α * (1 + r ^ (-α)))).of_nonneg_of_le
  · intro k
    positivity [fourierEigenvalue_nonneg k, hE k]
  · intro k
    have hp : 0 < 1 + fourierEigenvalue k := by positivity [fourierEigenvalue_nonneg k]
    calc
      _ = ((1 + fourierEigenvalue k) ^ α * Real.exp (-(r * fourierEigenvalue k))) *
          ((1 + fourierEigenvalue k) ^ p * E k) := by
        rw [Real.rpow_add hp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (fourier_heat_real_gain_multiplier hα hr k)
        (mul_nonneg (Real.rpow_nonneg hp.le _) (hE k))

/-- The singular kernel needed for less than two real derivative gains is
integrable at zero heat time. -/
theorem intervalIntegrable_fourier_heat_gain_kernel {γ T : ℝ} (hγ : γ < 2) :
    IntervalIntegrable (fun r : ℝ => 1 + r ^ (-γ / 2)) volume 0 T :=
  (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 T).add
    (intervalIntegral.intervalIntegrable_rpow'
    (by linarith : (-1 : ℝ) < -γ / 2))

/-- Explicit integral of the subcritical heat-gain kernel. -/
theorem integral_fourier_heat_gain_kernel {γ T : ℝ} (hγ : γ < 2) :
    (∫ r in (0 : ℝ)..T, (1 + r ^ (-γ / 2))) =
      T + T ^ (1 - γ / 2) / (1 - γ / 2) := by
  have hi : IntervalIntegrable (fun r : ℝ => r ^ (-γ / 2)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  rw [intervalIntegral.integral_add intervalIntegrable_const hi,
    intervalIntegral.integral_const, integral_rpow (Or.inl (by linarith))]
  have he : -γ / 2 + 1 = 1 - γ / 2 := by ring
  rw [he, Real.zero_rpow (by linarith : 1 - γ / 2 ≠ (0 : ℝ))]
  simp only [sub_zero, smul_eq_mul, mul_one]


/-- A finite family of genuine coefficients with an inhomogeneous real
Sobolev weight, viewed in the actual Euclidean coefficient Hilbert space. -/
def finiteFourierWeightedVector {ι : Type*} [Fintype ι]
    (eigen : ι → ℝ) (p : ℝ) (a : ι → ℂ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun k => (1 + eigen k) ^ (p / 2) • a k)

@[simp] lemma finiteFourierWeightedVector_apply {ι : Type*} [Fintype ι]
    (eigen : ι → ℝ) (p : ℝ) (a : ι → ℂ) (k : ι) :
    finiteFourierWeightedVector eigen p a k = (1 + eigen k) ^ (p / 2) • a k := rfl

/-- The coefficient Hilbert norm is exactly the weighted square energy. -/
theorem norm_sq_finiteFourierWeightedVector {ι : Type*} [Fintype ι]
    (eigen : ι → ℝ) (heigen : ∀ k, 0 ≤ eigen k) (p : ℝ) (a : ι → ℂ) :
    ‖finiteFourierWeightedVector eigen p a‖ ^ 2 =
      ∑ k, (1 + eigen k) ^ p * ‖a k‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [finiteFourierWeightedVector_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hp : ((1 + eigen k) ^ (p / 2)) ^ 2 = (1 + eigen k) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [heigen k] : 0 ≤ 1 + eigen k)]
    congr 1
    push_cast
    ring
  rw [hp]

/-- The actual finite coefficient heat operator gains `2α` Sobolev-energy
powers with the sharp `r^(-α)` norm singularity. -/
theorem norm_finiteFourierWeightedVector_heat_le {ι : Type*} [Fintype ι]
    (eigen : ι → ℝ) (heigen : ∀ k, 0 ≤ eigen k) {p α r B : ℝ}
    (hα : 0 ≤ α) (hr : 0 < r) (hB : 0 ≤ B) (a : ι → ℂ)
    (henergy : (∑ k, (1 + eigen k) ^ p * ‖a k‖ ^ 2) ≤ B) :
    ‖finiteFourierWeightedVector eigen (p + 2 * α)
      (fun k => Real.exp (-(r * eigen k)) • a k)‖ ≤
        (fourierHeatRealGainConstant α * (1 + r ^ (-α))) * Real.sqrt B := by
  let M := fourierHeatRealGainConstant α * (1 + r ^ (-α))
  have hM : 0 ≤ M := mul_nonneg (fourierHeatRealGainConstant_nonneg α)
    (by positivity : 0 ≤ 1 + r ^ (-α))
  have hb : ∀ k,
      (1 + eigen k) ^ (p + 2 * α) * ‖Real.exp (-(r * eigen k)) • a k‖ ^ 2 ≤
        M ^ 2 * ((1 + eigen k) ^ p * ‖a k‖ ^ 2) := by
    intro k
    have hp : 0 < 1 + eigen k := by positivity [heigen k]
    have hm := one_add_rpow_mul_exp_neg_mul_le hα hr (heigen k)
    have hs : ((1 + eigen k) ^ α * Real.exp (-(r * eigen k))) ^ 2 ≤ M ^ 2 :=
      (sq_le_sq₀ (by positivity) hM).mpr hm
    calc
      _ = ((1 + eigen k) ^ α * Real.exp (-(r * eigen k))) ^ 2 *
          ((1 + eigen k) ^ p * ‖a k‖ ^ 2) := by
        rw [show p + 2 * α = p + (α + α) by ring, Real.rpow_add hp, Real.rpow_add hp]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (by positivity)
  have hn : ‖finiteFourierWeightedVector eigen (p + 2 * α)
      (fun k => Real.exp (-(r * eigen k)) • a k)‖ ^ 2 ≤ M ^ 2 * B := by
    rw [norm_sq_finiteFourierWeightedVector eigen heigen]
    calc
      _ ≤ ∑ k, M ^ 2 * ((1 + eigen k) ^ p * ‖a k‖ ^ 2) := Finset.sum_le_sum fun k _ => hb k
      _ = M ^ 2 * ∑ k, (1 + eigen k) ^ p * ‖a k‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
  have hsqrt := Real.sq_sqrt hB
  have hright : 0 ≤ M * Real.sqrt B := mul_nonneg hM (Real.sqrt_nonneg _)
  change ‖finiteFourierWeightedVector eigen (p + 2 * α)
    (fun k => Real.exp (-(r * eigen k)) • a k)‖ ≤ M * Real.sqrt B
  nlinarith [norm_nonneg (finiteFourierWeightedVector eigen (p + 2 * α)
    (fun k => Real.exp (-(r * eigen k)) • a k))]

/-- The actual finite weighted coefficient Duhamel integral gains any
`2α<2` powers from a uniformly bounded source energy. No smoothness of the
unknown solution is assumed. -/
theorem norm_integral_finiteFourierWeightedVector_heat_le {ι : Type*} [Fintype ι]
    (eigen : ι → ℝ) (heigen : ∀ k, 0 ≤ eigen k) {p α ν t B : ℝ}
    (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hν : 0 < ν) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (F : ℝ → ι → ℂ)
    (henergy : ∀ s ∈ Icc (0 : ℝ) t, (∑ k, (1 + eigen k) ^ p * ‖F s k‖ ^ 2) ≤ B) :
    ‖∫ r in (0 : ℝ)..t, finiteFourierWeightedVector eigen (p + 2 * α)
      (fun k => Real.exp (-(ν * r * eigen k)) • F (t - r) k)‖ ≤
        (fourierHeatRealGainConstant α * Real.sqrt B) *
          (t + ν ^ (-α) * (t ^ (1 - α) / (1 - α))) := by
  let C := fourierHeatRealGainConstant α * Real.sqrt B
  have hi : IntervalIntegrable (fun r : ℝ => r ^ (-α)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hki : IntervalIntegrable (fun r : ℝ => C * (1 + ν ^ (-α) * r ^ (-α))) volume 0 t :=
    ((intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 t).add
      (hi.const_mul (ν ^ (-α)))).const_mul C
  have hbound : ∀ r ∈ Ioc (0 : ℝ) t,
      ‖finiteFourierWeightedVector eigen (p + 2 * α)
        (fun k => Real.exp (-(ν * r * eigen k)) • F (t - r) k)‖ ≤
          C * (1 + ν ^ (-α) * r ^ (-α)) := by
    intro r hr
    have hs : t - r ∈ Icc (0 : ℝ) t := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have hh := norm_finiteFourierWeightedVector_heat_le eigen heigen hα₀
      (mul_pos hν hr.1) hB (F (t - r)) (henergy _ hs)
    rw [Real.mul_rpow hν.le hr.1.le] at hh
    exact hh.trans_eq (by dsimp [C]; ring)
  calc
    _ ≤ ∫ r in (0 : ℝ)..t, C * (1 + ν ^ (-α) * r ^ (-α)) :=
      intervalIntegral.norm_integral_le_of_norm_le ht
        (Eventually.of_forall fun r hr => hbound r hr) hki
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add intervalIntegrable_const (hi.const_mul _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -α))]
      have he : -α + 1 = 1 - α := by ring
      rw [he, Real.zero_rpow (by linarith : 1 - α ≠ (0 : ℝ))]
      simp only [sub_zero, smul_eq_mul, mul_one]
      rfl


/-- The actual Fourier coefficient Duhamel integral in lag coordinates. -/
def heatDuhamelCoefficient {ι : Type*} (eigen : ι → ℝ) (ν : ℝ)
    (F : ℝ → ι → ℂ) (t : ℝ) (k : ι) : ℂ :=
  ∫ r in (0 : ℝ)..t, Real.exp (-(ν * r * eigen k)) • F (t - r) k

/-- For continuous source coefficients, the Hilbert-space Duhamel integral
is exactly the vector of the genuine coefficient integrals. -/
theorem integral_finiteFourierWeightedVector_heat {ι : Type*} [Fintype ι]
    (eigen : ι → ℝ) (ν p t : ℝ) (F : ℝ → ι → ℂ)
    (hF : ∀ k, Continuous (fun s => F s k)) :
    (∫ r in (0 : ℝ)..t, finiteFourierWeightedVector eigen p
      (fun k => Real.exp (-(ν * r * eigen k)) • F (t - r) k)) =
      finiteFourierWeightedVector eigen p (heatDuhamelCoefficient eigen ν F t) := by
  let H : ℝ → EuclideanSpace ℂ ι := fun r => finiteFourierWeightedVector eigen p
    (fun k => Real.exp (-(ν * r * eigen k)) • F (t - r) k)
  have hc : Continuous H := by
    apply (PiLp.continuous_toLp 2 (fun _ : ι => ℂ)).comp
    apply continuous_pi
    intro k
    have hsource : Continuous (fun r : ℝ => F (t - r) k) := by
      simpa only [Function.comp_def] using (hF k).comp
        (show Continuous (fun r : ℝ => t - r) from by fun_prop)
    exact (continuous_const : Continuous (fun _ : ℝ => (1 + eigen k) ^ (p / 2))).fun_smul
      ((by fun_prop : Continuous (fun r : ℝ => Real.exp (-(ν * r * eigen k)))).fun_smul
        hsource)
  have hi : IntervalIntegrable H volume 0 t := hc.intervalIntegrable _ _
  apply PiLp.ext
  intro k
  let L : EuclideanSpace ℂ ι →L[ℝ] ℂ := PiLp.proj 2 (fun _ : ι => ℂ) k
  change L (∫ r in (0 : ℝ)..t, H r) = _
  rw [← L.intervalIntegral_comp_comm hi]
  change (∫ r in (0 : ℝ)..t, (1 + eigen k) ^ (p / 2) •
    (Real.exp (-(ν * r * eigen k)) • F (t - r) k)) = _
  rw [intervalIntegral.integral_smul]
  rfl

/-- A genuine finite coefficient Duhamel square-energy estimate with any
real gain strictly below two derivative powers. -/
theorem finite_heatDuhamel_real_gain_energy {ι : Type*} [Fintype ι]
    (eigen : ι → ℝ) (heigen : ∀ k, 0 ≤ eigen k) {p α ν t B : ℝ}
    (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hν : 0 < ν) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (F : ℝ → ι → ℂ) (hF : ∀ k, Continuous (fun s => F s k))
    (henergy : ∀ s ∈ Icc (0 : ℝ) t, (∑ k, (1 + eigen k) ^ p * ‖F s k‖ ^ 2) ≤ B) :
    (∑ k, (1 + eigen k) ^ (p + 2 * α) * ‖heatDuhamelCoefficient eigen ν F t k‖ ^ 2) ≤
      fourierHeatRealGainConstant α ^ 2 * B *
        (t + ν ^ (-α) * (t ^ (1 - α) / (1 - α))) ^ 2 := by
  have hn := norm_integral_finiteFourierWeightedVector_heat_le eigen heigen
    hα₀ hα₁ hν ht hB F henergy
  rw [integral_finiteFourierWeightedVector_heat eigen ν (p + 2 * α) t F hF] at hn
  have hright : 0 ≤ (fourierHeatRealGainConstant α * Real.sqrt B) *
      (t + ν ^ (-α) * (t ^ (1 - α) / (1 - α))) := by
    have hC := fourierHeatRealGainConstant_nonneg α
    have hden : 0 < 1 - α := by linarith
    positivity
  have hs := (sq_le_sq₀ (norm_nonneg _) hright).mpr hn
  rw [norm_sq_finiteFourierWeightedVector eigen heigen] at hs
  have he : ((fourierHeatRealGainConstant α * Real.sqrt B) *
      (t + ν ^ (-α) * (t ^ (1 - α) / (1 - α)))) ^ 2 =
      fourierHeatRealGainConstant α ^ 2 * B *
        (t + ν ^ (-α) * (t ^ (1 - α) / (1 - α))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hB]
  exact hs.trans_eq he

/-- Uniformly bounded genuine source square energy yields a summable
higher-order Duhamel energy on the actual infinite Fourier lattice. -/
theorem summable_fourier_heatDuhamel_real_gain_energy
    {p α ν t B : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hν : 0 < ν) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (F : ℝ → (Fin 2 → ℤ) → ℂ) (hF : ∀ k, Continuous (fun s => F s k))
    (henergy : ∀ s ∈ Icc (0 : ℝ) t, ∀ S : Finset (Fin 2 → ℤ),
      (∑ k ∈ S, (1 + fourierEigenvalue k) ^ p * ‖F s k‖ ^ 2) ≤ B) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ (p + 2 * α) *
      ‖heatDuhamelCoefficient fourierEigenvalue ν F t k‖ ^ 2) ∧
    (∑' k, (1 + fourierEigenvalue k) ^ (p + 2 * α) *
      ‖heatDuhamelCoefficient fourierEigenvalue ν F t k‖ ^ 2) ≤
      fourierHeatRealGainConstant α ^ 2 * B *
        (t + ν ^ (-α) * (t ^ (1 - α) / (1 - α))) ^ 2 := by
  have hn : ∀ k, 0 ≤ (1 + fourierEigenvalue k) ^ (p + 2 * α) *
      ‖heatDuhamelCoefficient fourierEigenvalue ν F t k‖ ^ 2 := by
    intro k
    positivity [fourierEigenvalue_nonneg k]
  have hfinite : ∀ S : Finset (Fin 2 → ℤ),
      (∑ k ∈ S, (1 + fourierEigenvalue k) ^ (p + 2 * α) *
        ‖heatDuhamelCoefficient fourierEigenvalue ν F t k‖ ^ 2) ≤
        fourierHeatRealGainConstant α ^ 2 * B *
          (t + ν ^ (-α) * (t ^ (1 - α) / (1 - α))) ^ 2 := by
    intro S
    have hh := finite_heatDuhamel_real_gain_energy (p := p)
      (fun k : S => fourierEigenvalue k) (fun k => fourierEigenvalue_nonneg k)
      hα₀ hα₁ hν ht hB (fun s (k : S) => F s k) (fun k => hF k)
      (fun s hs => by
        rw [Finset.sum_coe_sort S (fun k : Fin 2 → ℤ =>
          (1 + fourierEigenvalue k) ^ p * ‖F s k‖ ^ 2)]
        exact henergy s hs S)
    have hsum := Finset.sum_coe_sort S (fun k : Fin 2 → ℤ =>
      (1 + fourierEigenvalue k) ^ (p + 2 * α) *
        ‖heatDuhamelCoefficient fourierEigenvalue ν F t k‖ ^ 2)
    rw [← hsum]
    exact hh
  exact ⟨summable_of_sum_le hn hfinite, Real.tsum_le_of_sum_le hn hfinite⟩


/-- The lag-coordinate coefficient integral is exactly the usual causal
Duhamel coefficient appearing in the genuine Fourier mild equation. -/
theorem heatDuhamelCoefficient_eq_standard {ι : Type*}
    (eigen : ι → ℝ) (ν : ℝ) (F : ℝ → ι → ℂ) (t : ℝ) (k : ι) :
    heatDuhamelCoefficient eigen ν F t k =
      ∫ s in (0 : ℝ)..t, Real.exp (-(ν * (t - s) * eigen k)) • F s k := by
  have hh := intervalIntegral.integral_comp_sub_left
    (fun r => Real.exp (-(ν * r * eigen k)) • F (t - r) k) (a := 0) (b := t) t
  simpa only [sub_self, sub_zero, sub_sub_cancel, heatDuhamelCoefficient] using hh.symm


/-- The coefficient Duhamel smoothing theorem stated with the actual
Sobolev gain `γ`, for every `0≤γ<2`. -/
theorem fourier_heatDuhamel_sobolev_gain {p γ ν t B : ℝ}
    (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 2) (hν : 0 < ν) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (F : ℝ → (Fin 2 → ℤ) → ℂ) (hF : ∀ k, Continuous (fun s => F s k))
    (henergy : ∀ s ∈ Icc (0 : ℝ) t, ∀ S : Finset (Fin 2 → ℤ),
      (∑ k ∈ S, (1 + fourierEigenvalue k) ^ p * ‖F s k‖ ^ 2) ≤ B) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ (p + γ) *
      ‖heatDuhamelCoefficient fourierEigenvalue ν F t k‖ ^ 2) ∧
    (∑' k, (1 + fourierEigenvalue k) ^ (p + γ) *
      ‖heatDuhamelCoefficient fourierEigenvalue ν F t k‖ ^ 2) ≤
      fourierHeatRealGainConstant (γ / 2) ^ 2 * B *
        (t + ν ^ (-(γ / 2)) * (t ^ (1 - γ / 2) / (1 - γ / 2))) ^ 2 := by
  have hh := summable_fourier_heatDuhamel_real_gain_energy (p := p) (α := γ / 2)
    (by linarith) (by linarith) hν ht hB F hF henergy
  simpa only [show 2 * (γ / 2) = γ by ring] using hh

/-- The same genuine Duhamel gain is uniform on the full supplied slab.
The source premise is an actual weighted square-energy bound. -/
theorem fourier_heatDuhamel_uniform_sobolev_gain {p γ ν T B : ℝ}
    (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 2) (hν : 0 < ν) (hB : 0 ≤ B)
    (F : ℝ → (Fin 2 → ℤ) → ℂ) (hF : ∀ k, Continuous (fun s => F s k))
    (henergy : ∀ s ∈ Icc (0 : ℝ) T, ∀ S : Finset (Fin 2 → ℤ),
      (∑ k ∈ S, (1 + fourierEigenvalue k) ^ p * ‖F s k‖ ^ 2) ≤ B) :
    ∀ t ∈ Icc (0 : ℝ) T,
      Summable (fun k => (1 + fourierEigenvalue k) ^ (p + γ) *
        ‖heatDuhamelCoefficient fourierEigenvalue ν F t k‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ (p + γ) *
        ‖heatDuhamelCoefficient fourierEigenvalue ν F t k‖ ^ 2) ≤
        fourierHeatRealGainConstant (γ / 2) ^ 2 * B *
          (T + ν ^ (-(γ / 2)) * (T ^ (1 - γ / 2) / (1 - γ / 2))) ^ 2 := by
  intro t ht
  obtain ⟨hs, hsum⟩ := fourier_heatDuhamel_sobolev_gain hγ₀ hγ₁ hν ht.1 hB F hF
    (fun s hs S => henergy s ⟨hs.1, hs.2.trans ht.2⟩ S)
  refine ⟨hs, hsum.trans ?_⟩
  have ht0 : 0 ≤ t := ht.1
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hden : 0 < 1 - γ / 2 := by linarith
  have hp : t ^ (1 - γ / 2) ≤ T ^ (1 - γ / 2) :=
    Real.rpow_le_rpow ht.1 ht.2 hden.le
  have hk : t + ν ^ (-(γ / 2)) * (t ^ (1 - γ / 2) / (1 - γ / 2)) ≤
      T + ν ^ (-(γ / 2)) * (T ^ (1 - γ / 2) / (1 - γ / 2)) :=
    add_le_add ht.2 (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hp hden.le) (Real.rpow_nonneg hν.le _))
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) hB)
  exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hk

end AnomDiss




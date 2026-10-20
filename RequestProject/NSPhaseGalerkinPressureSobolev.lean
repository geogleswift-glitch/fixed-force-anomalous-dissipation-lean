module

public import RequestProject.FourierSobolevAlgebra
public import RequestProject.NSPhaseGalerkinSourceSobolev
public import RequestProject.NSPhaseGalerkinH2
public import RequestProject.FourierSeriesRegularity

/-!
# Pressure coefficients from the actual derivative convolution

An explicit H² velocity energy gives H¹ derivative coefficient energies.
The genuine fractional product estimate and inversion of the true nonzero
Laplace eigenvalues give H^{3−δ} pressure energy. The pressure convention
is positive `S_k / λ_k`, corresponding to `Δp = -S`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 1600000

def fourierSpatialDerivativeCoefficient (a : (Fin 2 → ℤ) → ℂ)
    (i : Fin 2) (k : Fin 2 → ℤ) : ℂ :=
  (2 * π * Complex.I * (k i : ℂ)) * a k

def fourierPressureProduct (a : Fin 2 → (Fin 2 → ℤ) → ℂ)
    (i j : Fin 2) (k : Fin 2 → ℤ) : ℂ :=
  ∑' l, fourierSpatialDerivativeCoefficient (a j) i l *
    fourierSpatialDerivativeCoefficient (a i) j (k-l)

def fourierPressureSource (a : Fin 2 → (Fin 2 → ℤ) → ℂ) (k : Fin 2 → ℤ) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2, fourierPressureProduct a i j k

def fourierPressureCoefficient (a : Fin 2 → (Fin 2 → ℤ) → ℂ) (k : Fin 2 → ℤ) : ℂ :=
  if k = 0 then 0 else fourierPressureSource a k / (fourierEigenvalue k : ℂ)

def pressureDerivativeProductBound (δ B : ℝ) : ℝ :=
  4 * (2 ^ (1-δ)) ^ 2 *
    (∑' k : Fin 2 → ℤ, (1+fourierEigenvalue k) ^ (-(1+δ))) * B ^ 2

theorem pressureDerivativeProductBound_nonneg (δ B : ℝ) :
    0 ≤ pressureDerivativeProductBound δ B := by
  have hK : 0 ≤ ∑' k : Fin 2 → ℤ, (1+fourierEigenvalue k) ^ (-(1+δ)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _
  unfold pressureDerivativeProductBound
  positivity

theorem norm_fourierDerivativeFactor_sq_le_eigenvalue (k : Fin 2 → ℤ) (i : Fin 2) :
    ‖(2 * π * Complex.I * (k i : ℂ))‖ ^ 2 ≤ fourierEigenvalue k := by
  rw [← sum_norm_fourierDerivativeFactor_sq]
  exact Finset.single_le_sum (f := fun j : Fin 2 => ‖(2 * π * Complex.I * (k j : ℂ))‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- H² coefficient energy bounds the genuine physical derivative at H¹. -/
theorem fourier_derivative_h1_of_h2 {a : (Fin 2 → ℤ) → ℂ} {B : ℝ}
    (ha : Summable (fun k => (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖a k‖ ^ 2))
    (hbound : (∑' k, (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖a k‖ ^ 2) ≤ B)
    (i : Fin 2) :
    Summable (fun k => (1+fourierEigenvalue k) *
      ‖fourierSpatialDerivativeCoefficient a i k‖ ^ 2) ∧
    (∑' k, (1+fourierEigenvalue k) * ‖fourierSpatialDerivativeCoefficient a i k‖ ^ 2) ≤ B := by
  have hp (k : Fin 2 → ℤ) :
      (1+fourierEigenvalue k) * ‖fourierSpatialDerivativeCoefficient a i k‖ ^ 2 ≤
        (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖a k‖ ^ 2 := by
    rw [fourierSpatialDerivativeCoefficient, norm_mul, mul_pow, Real.rpow_two]
    have hd := norm_fourierDerivativeFactor_sq_le_eigenvalue k i
    calc
      _ ≤ (1+fourierEigenvalue k) * (fourierEigenvalue k * ‖a k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd (sq_nonneg _))
          (by positivity [fourierEigenvalue_nonneg k])
      _ ≤ (1+fourierEigenvalue k) * ((1+fourierEigenvalue k) * ‖a k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
          (by positivity [fourierEigenvalue_nonneg k])
      _ = _ := by ring
  have hs := ha.of_nonneg_of_le (fun k => mul_nonneg
    (by positivity [fourierEigenvalue_nonneg k]) (sq_nonneg _)) hp
  exact ⟨hs, (Summable.tsum_le_tsum hp hs ha).trans hbound⟩

/-- Each actual derivative-product convolution is absolutely convergent
and has the fractional energy supplied by H¹ × H¹. -/
theorem fourier_pressure_product_fractional_energy
    (a : Fin 2 → (Fin 2 → ℤ) → ℂ) {δ B : ℝ}
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hB : 0 ≤ B)
    (henergy : ∀ j : Fin 2,
      Summable (fun k => (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖a j k‖ ^ 2) ∧
      (∑' k, (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖a j k‖ ^ 2) ≤ B)
    (i j : Fin 2) :
    (∀ k, Summable (fun l => ‖fourierSpatialDerivativeCoefficient (a j) i l *
      fourierSpatialDerivativeCoefficient (a i) j (k-l)‖)) ∧
    Summable (fun k => (1+fourierEigenvalue k) ^ (1-δ) * ‖fourierPressureProduct a i j k‖ ^ 2) ∧
    (∑' k, (1+fourierEigenvalue k) ^ (1-δ) * ‖fourierPressureProduct a i j k‖ ^ 2) ≤
      pressureDerivativeProductBound δ B := by
  obtain ⟨hA, hbA⟩ := fourier_derivative_h1_of_h2 (henergy j).1 (henergy j).2 i
  obtain ⟨hC, hbC⟩ := fourier_derivative_h1_of_h2 (henergy i).1 (henergy i).2 j
  obtain ⟨habs, hs, hb⟩ := fourier_h1_product_fractional
    (fourierSpatialDerivativeCoefficient (a j) i) (fourierSpatialDerivativeCoefficient (a i) j)
    hδ₀ hδ₁ hA hC
  simp only [fourierSobolevWeight_fractional_energy_eq] at hs hb
  refine ⟨habs, hs, hb.trans ?_⟩
  have hEA : 0 ≤ ∑' k, (1+fourierEigenvalue k) *
      ‖fourierSpatialDerivativeCoefficient (a j) i k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (by positivity [fourierEigenvalue_nonneg k]) (sq_nonneg _)
  have hEC : 0 ≤ ∑' k, (1+fourierEigenvalue k) *
      ‖fourierSpatialDerivativeCoefficient (a i) j k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (by positivity [fourierEigenvalue_nonneg k]) (sq_nonneg _)
  have hm := mul_le_mul hbA hbC hEC hB
  let K : ℝ := 4 * (2 ^ (1-δ)) ^ 2 *
    (∑' k : Fin 2 → ℤ, (1+fourierEigenvalue k) ^ (-(1+δ)))
  have hK : 0 ≤ K := by
    have hk : 0 ≤ ∑' k : Fin 2 → ℤ, (1+fourierEigenvalue k) ^ (-(1+δ)) := tsum_nonneg fun k =>
      Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k] : 0 ≤ 1+fourierEigenvalue k) (-(1+δ))
    dsimp [K]
    positivity
  change K * _ * _ ≤ K * B ^ 2
  calc
    _ = K * ((∑' k, (1+fourierEigenvalue k) *
        ‖fourierSpatialDerivativeCoefficient (a j) i k‖ ^ 2) *
        (∑' k, (1+fourierEigenvalue k) *
        ‖fourierSpatialDerivativeCoefficient (a i) j k‖ ^ 2)) := by ring
    _ ≤ K * (B*B) := mul_le_mul_of_nonneg_left hm hK
    _ = _ := by ring

private lemma norm_sum_fin2_fin2_sq_le (F : Fin 2 → Fin 2 → ℂ) :
    ‖∑ i : Fin 2, ∑ j : Fin 2, F i j‖ ^ 2 ≤
      4 * ∑ i : Fin 2, ∑ j : Fin 2, ‖F i j‖ ^ 2 := by
  have hn : ‖∑ i : Fin 2, ∑ j : Fin 2, F i j‖ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖F i j‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)).mpr hn
  simp only [Fin.sum_univ_two] at hs ⊢
  nlinarith [sq_nonneg (‖F 0 0‖ - ‖F 0 1‖), sq_nonneg (‖F 0 0‖ - ‖F 1 0‖),
    sq_nonneg (‖F 0 0‖ - ‖F 1 1‖), sq_nonneg (‖F 0 1‖ - ‖F 1 0‖),
    sq_nonneg (‖F 0 1‖ - ‖F 1 1‖), sq_nonneg (‖F 1 0‖ - ‖F 1 1‖)]

theorem fourier_pressure_source_fractional_energy
    (a : Fin 2 → (Fin 2 → ℤ) → ℂ) {δ B : ℝ}
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hB : 0 ≤ B)
    (henergy : ∀ j : Fin 2,
      Summable (fun k => (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖a j k‖ ^ 2) ∧
      (∑' k, (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖a j k‖ ^ 2) ≤ B) :
    Summable (fun k => (1+fourierEigenvalue k) ^ (1-δ) * ‖fourierPressureSource a k‖ ^ 2) ∧
    (∑' k, (1+fourierEigenvalue k) ^ (1-δ) * ‖fourierPressureSource a k‖ ^ 2) ≤
      16 * pressureDerivativeProductBound δ B := by
  let Q := fun (i j : Fin 2) (k : Fin 2 → ℤ) =>
    (1+fourierEigenvalue k) ^ (1-δ) * ‖fourierPressureProduct a i j k‖ ^ 2
  have hQ (i j : Fin 2) : Summable (Q i j) ∧ (∑' k, Q i j k) ≤ pressureDerivativeProductBound δ B :=
    (fourier_pressure_product_fractional_energy a hδ₀ hδ₁ hB henergy i j).2
  have ht : Summable (fun k => ∑ i : Fin 2, ∑ j : Fin 2, Q i j k) := by
    simpa only [Fin.sum_univ_two] using
      (((hQ 0 0).1.add (hQ 0 1).1).add ((hQ 1 0).1.add (hQ 1 1).1))
  have hp (k : Fin 2 → ℤ) :
      (1+fourierEigenvalue k) ^ (1-δ) * ‖fourierPressureSource a k‖ ^ 2 ≤
        4 * ∑ i : Fin 2, ∑ j : Fin 2, Q i j k := by
    have h := mul_le_mul_of_nonneg_left
      (norm_sum_fin2_fin2_sq_le (fun i j => fourierPressureProduct a i j k))
      (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k] : 0 ≤ 1+fourierEigenvalue k) (1-δ))
    exact h.trans_eq (by simp only [Q, Fin.sum_univ_two]; ring)
  have hs := (ht.mul_left 4).of_nonneg_of_le (fun k => mul_nonneg
    (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)) hp
  refine ⟨hs, (Summable.tsum_le_tsum hp hs (ht.mul_left 4)).trans ?_⟩
  rw [tsum_mul_left]
  simp only [Fin.sum_univ_two]
  rw [((hQ 0 0).1.add (hQ 0 1).1).tsum_add ((hQ 1 0).1.add (hQ 1 1).1),
    (hQ 0 0).1.tsum_add (hQ 0 1).1, (hQ 1 0).1.tsum_add (hQ 1 1).1]
  linarith [(hQ 0 0).2, (hQ 0 1).2, (hQ 1 0).2, (hQ 1 1).2]

/-- Every nonzero integer frequency has a genuine spectral gap. -/
theorem one_le_fourierEigenvalue_of_ne_zero (k : Fin 2 → ℤ) (hk : k ≠ 0) :
    1 ≤ fourierEigenvalue k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hk
    exact funext h
  have hsq : (1 : ℝ) ≤ (k i : ℝ) ^ 2 := by
    exact_mod_cast (one_le_sq_iff_one_le_abs (k i)).mpr (Int.one_le_abs hi)
  have hd := norm_fourierDerivativeFactor_sq_le_eigenvalue k i
  rw [norm_fourierDerivativeFactor_sq] at hd
  have hc : 1 ≤ 4 * π ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hsq)]

theorem fourier_pressure_elliptic_energy_pointwise
    (a : Fin 2 → (Fin 2 → ℤ) → ℂ) (δ : ℝ) (k : Fin 2 → ℤ) :
    (1+fourierEigenvalue k) ^ (3-δ) * ‖fourierPressureCoefficient a k‖ ^ 2 ≤
      4 * ((1+fourierEigenvalue k) ^ (1-δ) * ‖fourierPressureSource a k‖ ^ 2) := by
  by_cases hk : k = 0
  · simp only [fourierPressureCoefficient, if_pos hk, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    positivity [fourierEigenvalue_nonneg k]
  have hEig := one_le_fourierEigenvalue_of_ne_zero k hk
  have hEigpos : 0 < fourierEigenvalue k := by linarith
  have hb : 0 < 1+fourierEigenvalue k := by linarith
  have hratio : (‖fourierPressureSource a k‖ / fourierEigenvalue k) ^ 2 * fourierEigenvalue k ^ 2 =
      ‖fourierPressureSource a k‖ ^ 2 := by
    field_simp [ne_of_gt hEigpos]
  have hcore : (1+fourierEigenvalue k) ^ 2 *
      (‖fourierPressureSource a k‖ / fourierEigenvalue k) ^ 2 ≤
        4 * ‖fourierPressureSource a k‖ ^ 2 := by
    have hb2 : (1+fourierEigenvalue k) ^ 2 ≤ 4 * fourierEigenvalue k ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hb2)
      (sq_nonneg (‖fourierPressureSource a k‖ / fourierEigenvalue k))]
  rw [fourierPressureCoefficient, if_neg hk, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hEigpos.le,
    show 3-δ = (1-δ)+(2 : ℝ) by ring,
    Real.rpow_add hb, Real.rpow_two]
  calc
    _ = (1+fourierEigenvalue k) ^ (1-δ) *
        ((1+fourierEigenvalue k) ^ 2 * (‖fourierPressureSource a k‖ / fourierEigenvalue k) ^ 2) := by ring
    _ ≤ (1+fourierEigenvalue k) ^ (1-δ) * (4 * ‖fourierPressureSource a k‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcore (Real.rpow_nonneg hb.le _)
    _ = _ := by ring

/-- An explicit H² velocity energy gives actual H^{3−δ} pressure
coefficient summability and its finite quantitative bound. -/
theorem fourier_pressure_sobolev_energy
    (a : Fin 2 → (Fin 2 → ℤ) → ℂ) {δ B : ℝ}
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hB : 0 ≤ B)
    (henergy : ∀ j : Fin 2,
      Summable (fun k => (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖a j k‖ ^ 2) ∧
      (∑' k, (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖a j k‖ ^ 2) ≤ B) :
    Summable (fun k => (1+fourierEigenvalue k) ^ (3-δ) * ‖fourierPressureCoefficient a k‖ ^ 2) ∧
    (∑' k, (1+fourierEigenvalue k) ^ (3-δ) * ‖fourierPressureCoefficient a k‖ ^ 2) ≤
      64 * pressureDerivativeProductBound δ B := by
  obtain ⟨hs, hb⟩ := fourier_pressure_source_fractional_energy a hδ₀ hδ₁ hB henergy
  have hp := fourier_pressure_elliptic_energy_pointwise a δ
  have hresult := (hs.mul_left 4).of_nonneg_of_le (fun k => mul_nonneg
    (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)) hp
  refine ⟨hresult, (Summable.tsum_le_tsum hp hresult (hs.mul_left 4)).trans ?_⟩
  rw [tsum_mul_left]
  linarith

private lemma sum_fin2_fin2_tsum {F : Fin 2 → Fin 2 → (Fin 2 → ℤ) → ℂ}
    (hF : ∀ i j, Summable (F i j)) :
    (∑ i : Fin 2, ∑ j : Fin 2, ∑' l, F i j l) =
      ∑' l, ∑ i : Fin 2, ∑ j : Fin 2, F i j l := by
  simp only [Fin.sum_univ_two]
  rw [((hF 0 0).add (hF 0 1)).tsum_add ((hF 1 0).add (hF 1 1)),
    (hF 0 0).tsum_add (hF 0 1), (hF 1 0).tsum_add (hF 1 1)]

/-- Incompressibility cancels all extra frequency factors inside the
actual convolution, before any infinite sums are interchanged. -/
lemma fourier_pressure_source_integrand_of_solenoidal
    (a : Fin 2 → (Fin 2 → ℤ) → ℂ)
    (hsol : ∀ k, ∑ i : Fin 2, (k i : ℂ) * a i k = 0)
    (k l : Fin 2 → ℤ) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      fourierSpatialDerivativeCoefficient (a j) i l *
        fourierSpatialDerivativeCoefficient (a i) j (k-l)) =
    ∑ i : Fin 2, ∑ j : Fin 2,
      ((2 * π * Complex.I * (k i : ℂ)) * (2 * π * Complex.I * (k j : ℂ))) *
        (a j l * a i (k-l)) := by
  let d := fun (i : Fin 2) (m : Fin 2 → ℤ) => (2 * π * Complex.I * (m i : ℂ))
  have hs (m : Fin 2 → ℤ) : ∑ i : Fin 2, d i m * a i m = 0 := by
    calc
      _ = (2 * π * Complex.I) * ∑ i : Fin 2, (m i : ℂ) * a i m := by
        simp only [Fin.sum_univ_two, d]
        ring
      _ = 0 := by rw [hsol m, mul_zero]
  have hd (i : Fin 2) : d i k = d i l + d i (k-l) := by
    dsimp [d]
    simp only [Int.cast_sub]
    ring
  have hx : (d 0 k * a 0 l + d 1 k * a 1 l) =
      d 0 (k-l) * a 0 l + d 1 (k-l) * a 1 l := by
    have h := hs l
    simp only [Fin.sum_univ_two] at h
    rw [hd 0, hd 1]
    linear_combination h
  have hy : (d 0 k * a 0 (k-l) + d 1 k * a 1 (k-l)) =
      d 0 l * a 0 (k-l) + d 1 l * a 1 (k-l) := by
    have h := hs (k-l)
    simp only [Fin.sum_univ_two] at h
    rw [hd 0, hd 1]
    linear_combination h
  change (∑ i : Fin 2, ∑ j : Fin 2, (d i l * a j l) * (d j (k-l) * a i (k-l))) =
    ∑ i : Fin 2, ∑ j : Fin 2, (d i k * d j k) * (a j l * a i (k-l))
  calc
    _ = (d 0 l * a 0 (k-l) + d 1 l * a 1 (k-l)) *
        (d 0 (k-l) * a 0 l + d 1 (k-l) * a 1 l) := by
      simp only [Fin.sum_univ_two]
      ring
    _ = (d 0 k * a 0 (k-l) + d 1 k * a 1 (k-l)) *
        (d 0 k * a 0 l + d 1 k * a 1 l) := by rw [hx, hy]
    _ = _ := by simp only [Fin.sum_univ_two]; ring

/-- The derivative-product source is exactly the double physical
derivative of the ordinary quadratic coefficient convolution. All
convolutions occurring here are proved absolutely convergent. -/
theorem fourier_pressure_source_eq_tensor_of_solenoidal
    (a : Fin 2 → (Fin 2 → ℤ) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j : Fin 2,
      Summable (fun k => (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖a j k‖ ^ 2) ∧
      (∑' k, (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖a j k‖ ^ 2) ≤ B)
    (hsol : ∀ k, ∑ i : Fin 2, (k i : ℂ) * a i k = 0) (k : Fin 2 → ℤ) :
    fourierPressureSource a k = ∑ i : Fin 2, ∑ j : Fin 2,
      ((2 * π * Complex.I * (k i : ℂ)) * (2 * π * Complex.I * (k j : ℂ))) *
        (∑' l, a j l * a i (k-l)) := by
  have hder (i j : Fin 2) : Summable (fun l =>
      fourierSpatialDerivativeCoefficient (a j) i l *
        fourierSpatialDerivativeCoefficient (a i) j (k-l)) :=
    summable_norm_iff.mp ((fourier_pressure_product_fractional_energy a
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num) hB henergy i j).1 k)
  have hraw (i j : Fin 2) : Summable (fun l => a j l * a i (k-l)) := by
    exact summable_norm_iff.mp ((fourier_sobolev_convolution_algebra (a j) (a i)
      (by norm_num : (1 : ℝ) < 2) (henergy j).1 (henergy i).1).1 k)
  calc
    _ = ∑' l, ∑ i : Fin 2, ∑ j : Fin 2,
        fourierSpatialDerivativeCoefficient (a j) i l *
          fourierSpatialDerivativeCoefficient (a i) j (k-l) := sum_fin2_fin2_tsum hder
    _ = ∑' l, ∑ i : Fin 2, ∑ j : Fin 2,
        ((2 * π * Complex.I * (k i : ℂ)) * (2 * π * Complex.I * (k j : ℂ))) *
          (a j l * a i (k-l)) :=
      tsum_congr fun l => fourier_pressure_source_integrand_of_solenoidal a hsol k l
    _ = ∑ i : Fin 2, ∑ j : Fin 2, ∑' l,
        ((2 * π * Complex.I * (k i : ℂ)) * (2 * π * Complex.I * (k j : ℂ))) *
          (a j l * a i (k-l)) :=
      (sum_fin2_fin2_tsum (fun i j => (hraw i j).mul_left _)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact tsum_mul_left

theorem phaseGalerkin_l2_limit_coefficient_solenoidal
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (k : Fin 2 → ℤ) :
    ∑ i : Fin 2, (k i : ℂ) * l2FourierCoeff k i (U t) = 0 := by
  exact phaseGalerkin_limit_coefficient_solenoidal
    (a := fun m => (l2FourierCoeff m.1 m.2).compLeftContinuousBounded GalerkinTime U)
    (fun m => phaseGalerkin_l2_coefficient_curve_tendsto ν hν phase hU m.1 m.2) t k

/-- The actual strong Galerkin limit has precisely the pressure source
formed from its genuine spatial quadratic Fourier moments. The explicit
H² energy premise is retained until the velocity bootstrap supplies it. -/
theorem phaseGalerkin_l2_limit_pressure_source_eq_quadratic_tensor
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j : Fin 2,
      Summable (fun k => (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖l2FourierCoeff k j (U t)‖ ^ 2) ∧
      (∑' k, (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖l2FourierCoeff k j (U t)‖ ^ 2) ≤ B)
    (k : Fin 2 → ℤ) :
    fourierPressureSource (fun j m => l2FourierCoeff m j (U t)) k =
      ∑ i : Fin 2, ∑ j : Fin 2,
        ((2 * π * Complex.I * (k i : ℂ)) * (2 * π * Complex.I * (k j : ℂ))) *
          torusQuadraticFourierMoment k j i (U t) := by
  rw [fourier_pressure_source_eq_tensor_of_solenoidal _ hB henergy
    (phaseGalerkin_l2_limit_coefficient_solenoidal ν hν phase hU t)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [phaseGalerkin_l2_limit_quadraticFourierMoment_eq_tsum ν hν phase hU t]

/-- Concrete pressure coefficients of the actual velocity, with the
correct sign for `Δp = - Σ ∂i u_j ∂j u_i`. -/
def torusPressureFourierCoefficient (V : TorusVelocityL2) (k : Fin 2 → ℤ) : ℂ :=
  if k = 0 then 0 else
    (∑ i : Fin 2, ∑ j : Fin 2,
      ((2 * π * Complex.I * (k i : ℂ)) * (2 * π * Complex.I * (k j : ℂ))) *
        torusQuadraticFourierMoment k j i V) / (fourierEigenvalue k : ℂ)

theorem phaseGalerkin_l2_limit_pressure_coefficient_eq
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j : Fin 2,
      Summable (fun k => (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖l2FourierCoeff k j (U t)‖ ^ 2) ∧
      (∑' k, (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖l2FourierCoeff k j (U t)‖ ^ 2) ≤ B)
    (k : Fin 2 → ℤ) :
    torusPressureFourierCoefficient (U t) k =
      fourierPressureCoefficient (fun j m => l2FourierCoeff m j (U t)) k := by
  unfold torusPressureFourierCoefficient fourierPressureCoefficient
  rw [phaseGalerkin_l2_limit_pressure_source_eq_quadratic_tensor ν hν phase hU t hB henergy]

/-- The actual pressure coefficients have H^{3−δ} energy, quantitatively
from the same velocity's explicit H² energy. -/
theorem phaseGalerkin_l2_limit_pressure_sobolev_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) {δ B : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hB : 0 ≤ B)
    (henergy : ∀ j : Fin 2,
      Summable (fun k => (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖l2FourierCoeff k j (U t)‖ ^ 2) ∧
      (∑' k, (1+fourierEigenvalue k) ^ (2 : ℝ) * ‖l2FourierCoeff k j (U t)‖ ^ 2) ≤ B) :
    Summable (fun k => (1+fourierEigenvalue k) ^ (3-δ) * ‖torusPressureFourierCoefficient (U t) k‖ ^ 2) ∧
    (∑' k, (1+fourierEigenvalue k) ^ (3-δ) * ‖torusPressureFourierCoefficient (U t) k‖ ^ 2) ≤
      64 * pressureDerivativeProductBound δ B := by
  simpa only [phaseGalerkin_l2_limit_pressure_coefficient_eq ν hν phase hU t hB henergy] using
    fourier_pressure_sobolev_energy (fun j k => l2FourierCoeff k j (U t)) hδ₀ hδ₁ hB henergy

/-- Signed Fourier Poisson identity, including the zero mode. -/
theorem torusPressureFourierCoefficient_poisson (V : TorusVelocityL2) (k : Fin 2 → ℤ) :
    (-(fourierEigenvalue k : ℂ)) * torusPressureFourierCoefficient V k =
      -(∑ i : Fin 2, ∑ j : Fin 2,
        ((2 * π * Complex.I * (k i : ℂ)) * (2 * π * Complex.I * (k j : ℂ))) *
          torusQuadraticFourierMoment k j i V) := by
  by_cases hk : k = 0
  · subst k
    simp [torusPressureFourierCoefficient]
  have heig : (fourierEigenvalue k : ℂ) ≠ 0 := by
    have hr : fourierEigenvalue k ≠ 0 := ne_of_gt
      (lt_of_lt_of_le zero_lt_one (one_le_fourierEigenvalue_of_ne_zero k hk))
    exact_mod_cast hr
  unfold torusPressureFourierCoefficient
  rw [if_neg hk]
  field_simp [heig]

/-- The earned H² velocity bootstrap gives pressure energy uniformly in
the original closed time interval, with no higher-energy premise. -/
theorem phaseGalerkin_l2_limit_uniform_pressure_sobolev_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ C, 0 ≤ C ∧ ∀ t : GalerkinTime,
      Summable (fun k => (1+fourierEigenvalue k) ^ (3-δ) *
        ‖torusPressureFourierCoefficient (U t) k‖ ^ 2) ∧
      (∑' k, (1+fourierEigenvalue k) ^ (3-δ) *
        ‖torusPressureFourierCoefficient (U t) k‖ ^ 2) ≤ C := by
  obtain ⟨B, hB, henergy⟩ := phaseGalerkin_l2_limit_uniform_h2_energy ν hν phase hφ hU
  refine ⟨64 * pressureDerivativeProductBound δ B,
    mul_nonneg (by norm_num) (pressureDerivativeProductBound_nonneg δ B), ?_⟩
  intro t
  apply phaseGalerkin_l2_limit_pressure_sobolev_energy ν hν phase hU t hδ₀ hδ₁ hB
  intro j
  simpa only [Real.rpow_two] using henergy j t

/-- For every β below one the same actual pressure coefficients have a
uniform first-plus-β absolute moment suitable for actual C¹ reconstruction. -/
theorem phaseGalerkin_l2_limit_uniform_pressure_covering_moment
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) :
    ∃ M, 0 ≤ M ∧ ∀ t : GalerkinTime,
      Summable (fun k => (1+‖intVec k‖) ^ (1+β) * ‖torusPressureFourierCoefficient (U t) k‖) ∧
      (∑' k, (1+‖intVec k‖) ^ (1+β) * ‖torusPressureFourierCoefficient (U t) k‖) ≤ M := by
  let δ := (1-β)/2
  have hδ₀ : 0 < δ := by dsimp [δ]; linarith
  have hδ₁ : δ < 1 := by dsimp [δ]; linarith
  obtain ⟨C, hC, henergy⟩ :=
    phaseGalerkin_l2_limit_uniform_pressure_sobolev_energy ν hν phase hφ hU hδ₀ hδ₁
  let K : ℝ := ∑' k : Fin 2 → ℤ, (1+fourierEigenvalue k) ^ (-((3-δ)-(1+β)))
  refine ⟨2 ^ (1+β) * (Real.sqrt C * Real.sqrt K), by positivity, ?_⟩
  intro t
  obtain ⟨hs, hb⟩ := fourier_covering_weighted_l1_of_sobolev
    (a := torusPressureFourierCoefficient (U t)) (r := 3-δ) (q := 1+β)
    (by linarith) (by dsimp [δ]; linarith) (henergy t).1
  refine ⟨hs, hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (henergy t).2) (Real.sqrt_nonneg K))
    (by positivity)

/-- The same actual pressure series has true C¹ spatial slices and a
β-Hölder spatial-gradient bound common to all times. This theorem makes
no claim about the temporal Hölder fields of a classical pressure. -/
theorem phaseGalerkin_l2_limit_pressure_spatial_C1_holder
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) :
    (∀ t : GalerkinTime, ContDiff ℝ 1 (complexFourierSeries (torusPressureFourierCoefficient (U t)))) ∧
    ∃ H, 0 ≤ H ∧ ∀ t : GalerkinTime, ∀ j x y,
      ‖pd j (complexFourierSeries (torusPressureFourierCoefficient (U t))) x -
        pd j (complexFourierSeries (torusPressureFourierCoefficient (U t))) y‖ ≤ H * ‖x-y‖ ^ β := by
  obtain ⟨M, hM, hmoment⟩ :=
    phaseGalerkin_l2_limit_uniform_pressure_covering_moment ν hν phase hφ hU hβ₀ hβ₁
  refine ⟨fun t => (contDiff_one_and_pd_holder_complexFourierSeries_quantitative
    hβ₀ hβ₁.le (hmoment t).1).1,
    fourierSeriesDerivativeHolderConstant β * M,
    mul_nonneg (fourierSeriesDerivativeHolderConstant_nonneg β) hM, ?_⟩
  intro t j x y
  exact pd_holder_complexFourierSeries_of_moment_bound hβ₀ hβ₁.le
    (hmoment t).1 (hmoment t).2 j x y

end AnomDiss

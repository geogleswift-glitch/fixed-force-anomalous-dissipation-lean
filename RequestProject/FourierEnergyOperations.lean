module

public import RequestProject.FourierSobolevInterpolation

/-! # Elementary operations on genuine weighted Fourier energies -/

@[expose] public section
open MeasureTheory Set Filter Topology Real
noncomputable section
namespace AnomDiss

theorem fourier_energy_add_bound (a b : (Fin 2 → ℤ) → ℂ) {r A B : ℝ}
    (ha : Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2))
    (hb : Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖b k‖ ^ 2))
    (hA : (∑' k, (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2) ≤ A)
    (hB : (∑' k, (1 + fourierEigenvalue k) ^ r * ‖b k‖ ^ 2) ≤ B) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖a k + b k‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ r * ‖a k + b k‖ ^ 2) ≤ 2*A + 2*B := by
  have hpoint (k : Fin 2 → ℤ) :
      (1 + fourierEigenvalue k) ^ r * ‖a k + b k‖ ^ 2 ≤
        2 * ((1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2) +
        2 * ((1 + fourierEigenvalue k) ^ r * ‖b k‖ ^ 2) := by
    have hn := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (norm_add_le (a k) (b k))
    have hsq : ‖a k + b k‖ ^ 2 ≤ 2*‖a k‖ ^ 2 + 2*‖b k‖ ^ 2 := by
      nlinarith [sq_nonneg (‖a k‖ - ‖b k‖)]
    have h := mul_le_mul_of_nonneg_left hsq
      (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k] : 0 ≤ 1 + fourierEigenvalue k) r)
    nlinarith only [h]
  have hmajor := (ha.mul_left 2).add (hb.mul_left 2)
  have hs := hmajor.of_nonneg_of_le (fun k => mul_nonneg
    (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) r) (sq_nonneg _)) hpoint
  refine ⟨hs, (Summable.tsum_le_tsum hpoint hs hmajor).trans ?_⟩
  rw [(ha.mul_left 2).tsum_add (hb.mul_left 2), tsum_mul_left, tsum_mul_left]
  linarith

theorem fourier_energy_sub_bound (a b : (Fin 2 → ℤ) → ℂ) {r A B : ℝ}
    (ha : Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2))
    (hb : Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖b k‖ ^ 2))
    (hA : (∑' k, (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2) ≤ A)
    (hB : (∑' k, (1 + fourierEigenvalue k) ^ r * ‖b k‖ ^ 2) ≤ B) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖a k - b k‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ r * ‖a k - b k‖ ^ 2) ≤ 2*A + 2*B := by
  have hb' : Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖-b k‖ ^ 2) := by simpa using hb
  have hB' : (∑' k, (1 + fourierEigenvalue k) ^ r * ‖-b k‖ ^ 2) ≤ B := by simpa using hB
  simpa only [sub_eq_add_neg] using fourier_energy_add_bound a (fun k => -b k) ha hb' hA hB'

theorem fourier_energy_lower_bound (a : (Fin 2 → ℤ) → ℂ) {p q B : ℝ} (hpq : p ≤ q)
    (hs : Summable (fun k => (1 + fourierEigenvalue k) ^ q * ‖a k‖ ^ 2))
    (hb : (∑' k, (1 + fourierEigenvalue k) ^ q * ‖a k‖ ^ 2) ≤ B) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ p * ‖a k‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ p * ‖a k‖ ^ 2) ≤ B := by
  have hpoint (k : Fin 2 → ℤ) :
      (1 + fourierEigenvalue k) ^ p * ‖a k‖ ^ 2 ≤
        (1 + fourierEigenvalue k) ^ q * ‖a k‖ ^ 2 :=
    mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by linarith [fourierEigenvalue_nonneg k]) hpq) (sq_nonneg _)
  have h := hs.of_nonneg_of_le (fun k => mul_nonneg
    (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) p) (sq_nonneg _)) hpoint
  exact ⟨h, (Summable.tsum_le_tsum hpoint h hs).trans hb⟩

theorem fourier_energy_damping_bound (ν : ℝ) (a : (Fin 2 → ℤ) → ℂ) {p B : ℝ}
    (hs : Summable (fun k => (1 + fourierEigenvalue k) ^ (p+2) * ‖a k‖ ^ 2))
    (hb : (∑' k, (1 + fourierEigenvalue k) ^ (p+2) * ‖a k‖ ^ 2) ≤ B) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ p *
      ‖((-(ν * fourierEigenvalue k) : ℝ) : ℂ) * a k‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ p *
        ‖((-(ν * fourierEigenvalue k) : ℝ) : ℂ) * a k‖ ^ 2) ≤ ν ^ 2 * B := by
  have hpoint (k : Fin 2 → ℤ) :
      (1 + fourierEigenvalue k) ^ p * ‖((-(ν * fourierEigenvalue k) : ℝ) : ℂ) * a k‖ ^ 2 ≤
        ν ^ 2 * ((1 + fourierEigenvalue k) ^ (p+2) * ‖a k‖ ^ 2) := by
    have he := fourierEigenvalue_nonneg k
    have hbase : 0 < 1 + fourierEigenvalue k := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      neg_sq, mul_pow, Real.rpow_add hbase, Real.rpow_two]
    have hh := mul_nonneg
      (mul_nonneg (sq_nonneg ν) (Real.rpow_nonneg hbase.le p))
      (mul_nonneg (by nlinarith : 0 ≤ (1 + fourierEigenvalue k)^2 - (fourierEigenvalue k)^2)
        (sq_nonneg ‖a k‖))
    nlinarith only [hh]
  have hmajor := hs.mul_left (ν^2)
  have h := hmajor.of_nonneg_of_le (fun k => mul_nonneg
    (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) p) (sq_nonneg _)) hpoint
  refine ⟨h, (Summable.tsum_le_tsum hpoint h hmajor).trans ?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)

end AnomDiss

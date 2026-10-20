module

public import RequestProject.FourierSobolevAlgebra
public import Mathlib.Analysis.MeanInequalities

/-!
# Quantitative interpolation of genuine coefficient energies

Hölder's inequality interpolates two summable weighted square energies.
The estimates below apply to actual coefficient differences, so they can
transfer a weak time estimate and a stronger spatial bound to pointwise
time regularity without a common pointwise summable majorant.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
noncomputable section

namespace AnomDiss

theorem summable_geometric_interpolation {ι : Type*} (x y : ι → ℝ)
    (hx : ∀ k, 0 ≤ x k) (hy : ∀ k, 0 ≤ y k)
    (hsx : Summable x) (hsy : Summable y) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Summable (fun k => (x k) ^ (1 - θ) * (y k) ^ θ) ∧
      (∑' k, (x k) ^ (1 - θ) * (y k) ^ θ) ≤
        (∑' k, x k) ^ (1 - θ) * (∑' k, y k) ^ θ := by
  have hθ : 0 < 1 - θ := sub_pos.mpr hθ1
  have hpq : ((1 - θ)⁻¹).HolderConjugate θ⁻¹ :=
    Real.holderConjugate_iff.mpr ⟨(one_lt_inv₀ hθ).mpr (by linarith), by simp⟩
  have hxp : (fun k => ((x k) ^ (1 - θ)) ^ ((1 - θ)⁻¹)) = x := by
    funext k
    rw [← Real.rpow_mul (hx k), mul_inv_cancel₀ hθ.ne', Real.rpow_one]
  have hyp : (fun k => ((y k) ^ θ) ^ θ⁻¹) = y := by
    funext k
    rw [← Real.rpow_mul (hy k), mul_inv_cancel₀ hθ0.ne', Real.rpow_one]
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq
    (fun k => Real.rpow_nonneg (hx k) _) (fun k => Real.rpow_nonneg (hy k) _)
    (hxp.symm ▸ hsx) (hyp.symm ▸ hsy)
  simpa only [hxp, hyp, one_div, inv_inv] using h

theorem fourier_energy_interpolation (a : (Fin 2 → ℤ) → ℂ) {p q θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp : Summable (fun k => (1 + fourierEigenvalue k) ^ p * ‖a k‖ ^ 2))
    (hq : Summable (fun k => (1 + fourierEigenvalue k) ^ q * ‖a k‖ ^ 2)) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ ((1 - θ) * p + θ * q) * ‖a k‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ ((1 - θ) * p + θ * q) * ‖a k‖ ^ 2) ≤
        (∑' k, (1 + fourierEigenvalue k) ^ p * ‖a k‖ ^ 2) ^ (1 - θ) *
        (∑' k, (1 + fourierEigenvalue k) ^ q * ‖a k‖ ^ 2) ^ θ := by
  have he (k : Fin 2 → ℤ) :
      ((1 + fourierEigenvalue k) ^ p * ‖a k‖ ^ 2) ^ (1 - θ) *
        ((1 + fourierEigenvalue k) ^ q * ‖a k‖ ^ 2) ^ θ =
      (1 + fourierEigenvalue k) ^ ((1 - θ) * p + θ * q) * ‖a k‖ ^ 2 := by
    have hb : 0 < 1 + fourierEigenvalue k := by positivity [fourierEigenvalue_nonneg k]
    rw [Real.mul_rpow (Real.rpow_nonneg hb.le _) (sq_nonneg _),
      Real.mul_rpow (Real.rpow_nonneg hb.le _) (sq_nonneg _),
      ← Real.rpow_mul hb.le, ← Real.rpow_mul hb.le]
    calc
      _ = ((1 + fourierEigenvalue k) ^ (p * (1 - θ)) *
          (1 + fourierEigenvalue k) ^ (q * θ)) *
          ((‖a k‖ ^ 2) ^ (1 - θ) * (‖a k‖ ^ 2) ^ θ) := by ring
      _ = _ := by
        rw [← Real.rpow_add hb, ← Real.rpow_add' (sq_nonneg _) (by linarith : 1 - θ + θ ≠ (0 : ℝ)),
          show 1 - θ + θ = 1 by ring, Real.rpow_one]
        congr 2 <;> ring
  have h := summable_geometric_interpolation
    (fun k => (1 + fourierEigenvalue k) ^ p * ‖a k‖ ^ 2)
    (fun k => (1 + fourierEigenvalue k) ^ q * ‖a k‖ ^ 2)
    (fun k => mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _))
    (fun k => mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _))
    hp hq hθ0 hθ1
  simpa only [he] using h

theorem fourier_energy_interpolation_bound (a : (Fin 2 → ℤ) → ℂ) {p q θ A B : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp : Summable (fun k => (1 + fourierEigenvalue k) ^ p * ‖a k‖ ^ 2))
    (hq : Summable (fun k => (1 + fourierEigenvalue k) ^ q * ‖a k‖ ^ 2))
    (hA : (∑' k, (1 + fourierEigenvalue k) ^ p * ‖a k‖ ^ 2) ≤ A)
    (hB : (∑' k, (1 + fourierEigenvalue k) ^ q * ‖a k‖ ^ 2) ≤ B) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ ((1 - θ) * p + θ * q) * ‖a k‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ ((1 - θ) * p + θ * q) * ‖a k‖ ^ 2) ≤
        A ^ (1 - θ) * B ^ θ := by
  obtain ⟨hs, hb⟩ := fourier_energy_interpolation a hθ0 hθ1 hp hq
  have hn (r : ℝ) : 0 ≤ ∑' k, (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg
      (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  exact ⟨hs, hb.trans (mul_le_mul
    (Real.rpow_le_rpow (hn p) hA (by linarith))
    (Real.rpow_le_rpow (hn q) hB hθ0.le)
    (Real.rpow_nonneg (hn q) _) (Real.rpow_nonneg ((hn p).trans hA) _))⟩

end AnomDiss

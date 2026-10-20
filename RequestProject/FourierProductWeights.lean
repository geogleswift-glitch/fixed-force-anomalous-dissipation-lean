module

public import RequestProject.FourierDifferential

/-!
# Inhomogeneous Fourier weights for fractional product estimates

The actual unit-torus Laplace eigenvalues control addition of frequencies.
A small loss in the product exponent can be assigned to either factor as
a negative weight, the form needed for the discrete Young inequality.
-/

@[expose] public section

open Real
noncomputable section

namespace AnomDiss

def fourierSobolevWeight (k : Fin 2 → ℤ) : ℝ :=
  Real.sqrt (1 + fourierEigenvalue k)

theorem fourierSobolevWeight_nonneg (k : Fin 2 → ℤ) :
    0 ≤ fourierSobolevWeight k := Real.sqrt_nonneg _

theorem fourierSobolevWeight_sq (k : Fin 2 → ℤ) :
    fourierSobolevWeight k ^ 2 = 1 + fourierEigenvalue k :=
  Real.sq_sqrt (by linarith [fourierEigenvalue_nonneg k])

theorem one_le_fourierSobolevWeight (k : Fin 2 → ℤ) :
    1 ≤ fourierSobolevWeight k := by
  have he := fourierSobolevWeight_sq k
  have hn := fourierSobolevWeight_nonneg k
  nlinarith [fourierEigenvalue_nonneg k]

private theorem eigenvalue_coordinates (k : Fin 2 → ℤ) :
    fourierEigenvalue k = 4 * π ^ 2 * ((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2) := by
  unfold fourierEigenvalue euclNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [intVec, Fin.sum_univ_two]

theorem fourierEigenvalue_add_le (k l : Fin 2 → ℤ) :
    fourierEigenvalue (k + l) ≤ 2 * (fourierEigenvalue k + fourierEigenvalue l) := by
  simp_rw [eigenvalue_coordinates]
  simp only [Pi.add_apply, Int.cast_add]
  have he : ((k 0 : ℝ) + l 0) ^ 2 + ((k 1 : ℝ) + l 1) ^ 2 ≤
      2 * (((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2) +
        ((l 0 : ℝ) ^ 2 + (l 1 : ℝ) ^ 2)) := by
    nlinarith [sq_nonneg ((k 0 : ℝ) - l 0), sq_nonneg ((k 1 : ℝ) - l 1)]
  nlinarith [mul_nonneg (by positivity : 0 ≤ 4 * π ^ 2) (sub_nonneg.2 he)]

theorem fourierSobolevWeight_add_le (k l : Fin 2 → ℤ) :
    fourierSobolevWeight (k + l) ≤ 2 * max (fourierSobolevWeight k) (fourierSobolevWeight l) := by
  let M := max (fourierSobolevWeight k) (fourierSobolevWeight l)
  have hM : 0 ≤ M := (fourierSobolevWeight_nonneg k).trans (le_max_left _ _)
  have hk : fourierSobolevWeight k ^ 2 ≤ M ^ 2 :=
    (sq_le_sq₀ (fourierSobolevWeight_nonneg k) hM).mpr (le_max_left _ _)
  have hl : fourierSobolevWeight l ^ 2 ≤ M ^ 2 :=
    (sq_le_sq₀ (fourierSobolevWeight_nonneg l) hM).mpr (le_max_right _ _)
  apply (sq_le_sq₀ (fourierSobolevWeight_nonneg (k + l)) (by positivity : 0 ≤ 2 * M)).mp
  nlinarith [fourierSobolevWeight_sq k, fourierSobolevWeight_sq l,
    fourierSobolevWeight_sq (k + l), fourierEigenvalue_add_le k l]

private theorem fractional_weight_product_bound {w a b δ : ℝ}
    (hw0 : 0 ≤ w) (ha : 0 < a) (hb : 0 < b) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hw : w ≤ 2 * max a b) :
    w ^ (1 - δ) ≤ 2 ^ (1 - δ) * (a * b ^ (-δ) + b * a ^ (-δ)) := by
  have hordered : ∀ a b : ℝ, 0 < a → 0 < b → a ≤ b → w ≤ 2 * b →
      w ^ (1 - δ) ≤ 2 ^ (1 - δ) * (a * b ^ (-δ) + b * a ^ (-δ)) := by
    intro a b ha hb hab hwb
    have hpow := Real.rpow_le_rpow hw0 hwb (by linarith : 0 ≤ 1 - δ)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hb.le] at hpow
    have he : b ^ (1 - δ) = b * b ^ (-δ) := by
      rw [show 1 - δ = 1 + (-δ) by ring, Real.rpow_add hb, Real.rpow_one]
    have hneg : b ^ (-δ) ≤ a ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos ha hab (by linarith)
    calc
      w ^ (1 - δ) ≤ 2 ^ (1 - δ) * b ^ (1 - δ) := hpow
      _ = 2 ^ (1 - δ) * (b * b ^ (-δ)) := by rw [he]
      _ ≤ 2 ^ (1 - δ) * (b * a ^ (-δ)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hneg hb.le) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (mul_nonneg ha.le (Real.rpow_nonneg hb.le _)))
        (by positivity)
  rcases le_total a b with hab | hba
  · exact hordered a b ha hb hab (by simpa only [max_eq_right hab] using hw)
  · simpa only [add_comm] using
      hordered b a hb ha hba (by simpa only [max_eq_left hba] using hw)

/-- The true fractional Fourier output weight is dominated by two
first-order/negative-order input weight products. -/
theorem fourierSobolevWeight_product_bound (k l : Fin 2 → ℤ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    fourierSobolevWeight (k + l) ^ (1 - δ) ≤ 2 ^ (1 - δ) *
      (fourierSobolevWeight k * fourierSobolevWeight l ^ (-δ) +
        fourierSobolevWeight l * fourierSobolevWeight k ^ (-δ)) :=
  fractional_weight_product_bound (fourierSobolevWeight_nonneg _)
    (lt_of_lt_of_le zero_lt_one (one_le_fourierSobolevWeight k))
    (lt_of_lt_of_le zero_lt_one (one_le_fourierSobolevWeight l))
    hδ0 hδ1 (fourierSobolevWeight_add_le k l)

end AnomDiss

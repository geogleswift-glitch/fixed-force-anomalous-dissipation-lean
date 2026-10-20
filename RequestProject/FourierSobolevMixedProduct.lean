module

public import RequestProject.FourierSobolevAlgebra

/-!
# Mixed Sobolev convolution estimates for actual Fourier increments

A weak positive Sobolev coefficient family can be multiplied by a
weighted absolutely summable family. Both genuine convolution convergence
and the squared output energy are proved by discrete Young inequalities.
-/

@[expose] public section

open Set Filter Topology Real
noncomputable section

namespace AnomDiss

set_option maxHeartbeats 1200000

/-- Actual `H^p × ℓ¹_p → H^p` convolution, valid for every `p≥0`.
The strong factor's weighted absolute moment is the only ℓ¹ premise. -/
theorem fourier_sobolev_mixed_product
    (a b : (Fin 2 → ℤ) → ℂ) {p : ℝ} (hp : 0 ≤ p)
    (ha : Summable (fun k => (1+fourierEigenvalue k) ^ p * ‖a k‖ ^ 2))
    (hb : Summable (fun k => fourierSobolevWeight k ^ p * ‖b k‖)) :
    (∀ k, Summable (fun l => ‖a l * b (k-l)‖)) ∧
    Summable (fun k => (1+fourierEigenvalue k) ^ p * ‖∑' l, a l * b (k-l)‖ ^ 2) ∧
    (∑' k, (1+fourierEigenvalue k) ^ p * ‖∑' l, a l * b (k-l)‖ ^ 2) ≤
      4 * (2 ^ p) ^ 2 * (∑' k, fourierSobolevWeight k ^ p * ‖b k‖) ^ 2 *
        (∑' k, (1+fourierEigenvalue k) ^ p * ‖a k‖ ^ 2) := by
  let A := fun k => ‖a k‖
  let B := fun k => ‖b k‖
  let AP := fun k => fourierSobolevWeight k ^ p * ‖a k‖
  let BP := fun k => fourierSobolevWeight k ^ p * ‖b k‖
  let E := ∑' k, (1+fourierEigenvalue k) ^ p * ‖a k‖ ^ 2
  let L := ∑' k, BP k
  let C : ℝ := 2 ^ p
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA : ∀ k, 0 ≤ A k := fun k => norm_nonneg _
  have hB : ∀ k, 0 ≤ B k := fun k => norm_nonneg _
  have hAP : ∀ k, 0 ≤ AP k := fun k =>
    mul_nonneg (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _) (norm_nonneg _)
  have hBP : ∀ k, 0 ≤ BP k := fun k =>
    mul_nonneg (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _) (norm_nonneg _)
  have hAs : Summable (fun k => AP k ^ 2) := by
    simpa only [AP, fourierSobolevWeight_fractional_energy_eq] using ha
  have hAe : (∑' k, AP k ^ 2) = E := by
    simp only [E, AP, fourierSobolevWeight_fractional_energy_eq]
  have hBpoint (k : Fin 2 → ℤ) : B k ≤ BP k := by
    simpa only [B, BP, one_mul] using mul_le_mul_of_nonneg_right
      (Real.one_le_rpow (one_le_fourierSobolevWeight k) hp) (norm_nonneg (b k))
  have hBraw : Summable B := hb.of_nonneg_of_le hB hBpoint
  have hApoint (k : Fin 2 → ℤ) : A k ^ 2 ≤ (1+fourierEigenvalue k) ^ p * ‖a k‖ ^ 2 := by
    simpa only [A, one_mul] using mul_le_mul_of_nonneg_right
      (Real.one_le_rpow (by linarith [fourierEigenvalue_nonneg k] : 1 ≤ 1+fourierEigenvalue k) hp)
      (sq_nonneg ‖a k‖)
  have hAraw : Summable (fun k => A k ^ 2) := ha.of_nonneg_of_le (fun k => sq_nonneg _) hApoint
  have hArawBound : (∑' k, A k ^ 2) ≤ E := Summable.tsum_le_tsum hApoint hAraw ha
  have hBrawBound : (∑' k, B k) ≤ L := Summable.tsum_le_tsum hBpoint hBraw hb
  obtain ⟨hconv1, hsq1, hy1⟩ := discrete_young_l2_l1_nonneg AP B hAP hB hAs hBraw
  obtain ⟨hconv2, hsq2, hy2⟩ := discrete_young_l2_l1_nonneg A BP hA hBP hAraw hb
  let C1 := fun k => ∑' l, AP l * B (k-l)
  let C2 := fun k => ∑' l, A l * BP (k-l)
  have hC1 : ∀ k, 0 ≤ C1 k := fun k => tsum_nonneg fun l => mul_nonneg (hAP l) (hB _)
  have hC2 : ∀ k, 0 ≤ C2 k := fun k => tsum_nonneg fun l => mul_nonneg (hA l) (hBP _)
  have hterm (k l : Fin 2 → ℤ) :
      fourierSobolevWeight k ^ p * ‖a l * b (k-l)‖ ≤
        C * (AP l * B (k-l) + A l * BP (k-l)) := by
    have hw := fourierSobolevWeight_power_add_bound l (k-l) hp
    have he : l+(k-l) = k := by abel
    rw [he] at hw
    apply (mul_le_mul_of_nonneg_right hw (norm_nonneg (a l * b (k-l)))).trans_eq
    simp only [AP, BP, A, B, C, norm_mul]
    ring
  have hdom (k : Fin 2 → ℤ) :
      Summable (fun l => C * (AP l * B (k-l) + A l * BP (k-l))) :=
    ((hconv1 k).add (hconv2 k)).mul_left C
  have habs (k : Fin 2 → ℤ) : Summable (fun l => ‖a l * b (k-l)‖) := by
    apply (hdom k).of_nonneg_of_le (fun l => norm_nonneg _)
    intro l
    have hw := Real.one_le_rpow (one_le_fourierSobolevWeight k) hp
    have hn : ‖a l * b (k-l)‖ ≤ fourierSobolevWeight k ^ p * ‖a l * b (k-l)‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg (a l * b (k-l)))
    exact hn.trans (hterm k l)
  have hpoint (k : Fin 2 → ℤ) :
      fourierSobolevWeight k ^ p * ‖∑' l, a l * b (k-l)‖ ≤ C * (C1 k+C2 k) := by
    calc
      _ ≤ fourierSobolevWeight k ^ p * ∑' l, ‖a l * b (k-l)‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (habs k))
          (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _)
      _ = ∑' l, fourierSobolevWeight k ^ p * ‖a l * b (k-l)‖ := tsum_mul_left.symm
      _ ≤ ∑' l, C * (AP l * B (k-l)+A l * BP (k-l)) :=
        Summable.tsum_le_tsum (hterm k) ((habs k).mul_left _) (hdom k)
      _ = _ := by rw [tsum_mul_left, (hconv1 k).tsum_add (hconv2 k)]
  have hsquare (k : Fin 2 → ℤ) :
      (fourierSobolevWeight k ^ p * ‖∑' l, a l * b (k-l)‖) ^ 2 ≤
        2 * C ^ 2 * (C1 k ^ 2+C2 k ^ 2) := by
    have h := (sq_le_sq₀
      (mul_nonneg (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _) (norm_nonneg _))
      (mul_nonneg hC (add_nonneg (hC1 k) (hC2 k)))).mpr (hpoint k)
    have htwo : (C1 k+C2 k) ^ 2 ≤ 2 * (C1 k ^ 2+C2 k ^ 2) := by
      nlinarith [sq_nonneg (C1 k-C2 k)]
    calc
      _ ≤ C ^ 2 * (C1 k+C2 k) ^ 2 := by simpa only [mul_pow] using h
      _ ≤ C ^ 2 * (2 * (C1 k ^ 2+C2 k ^ 2)) :=
        mul_le_mul_of_nonneg_left htwo (sq_nonneg C)
      _ = _ := by ring
  have hmajor : Summable (fun k => 2 * C ^ 2 * (C1 k ^ 2+C2 k ^ 2)) :=
    (hsq1.add hsq2).mul_left _
  have hs := hmajor.of_nonneg_of_le (fun k => sq_nonneg _) hsquare
  have hE : 0 ≤ E := tsum_nonneg fun k => mul_nonneg
    (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  have hL : 0 ≤ L := tsum_nonneg hBP
  have hB2 : (∑' k, B k) ^ 2 ≤ L ^ 2 :=
    (sq_le_sq₀ (tsum_nonneg hB) hL).mpr hBrawBound
  rw [hAe] at hy1
  have hY1 : (∑' k, C1 k ^ 2) ≤ L ^ 2 * E :=
    hy1.trans (mul_le_mul_of_nonneg_right hB2 hE)
  have hY2 : (∑' k, C2 k ^ 2) ≤ L ^ 2 * E :=
    hy2.trans (mul_le_mul_of_nonneg_left hArawBound (sq_nonneg L))
  have hbfinal : (∑' k, (fourierSobolevWeight k ^ p * ‖∑' l, a l * b (k-l)‖) ^ 2) ≤
      4 * C ^ 2 * L ^ 2 * E := by
    calc
      _ ≤ ∑' k, 2 * C ^ 2 * (C1 k ^ 2+C2 k ^ 2) :=
        Summable.tsum_le_tsum hsquare hs hmajor
      _ = 2 * C ^ 2 * ((∑' k, C1 k ^ 2)+∑' k, C2 k ^ 2) := by
        rw [tsum_mul_left, hsq1.tsum_add hsq2]
      _ ≤ 2 * C ^ 2 * (L ^ 2 * E+L ^ 2 * E) :=
        mul_le_mul_of_nonneg_left (add_le_add hY1 hY2) (by positivity)
      _ = _ := by ring
  exact ⟨habs, by simpa only [fourierSobolevWeight_fractional_energy_eq] using hs,
    by simpa only [fourierSobolevWeight_fractional_energy_eq, C, L, BP, E] using hbfinal⟩

private def mixedSubEquiv (k : Fin 2 → ℤ) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun l := k-l
  invFun l := k-l
  left_inv l := by dsimp; abel
  right_inv l := by dsimp; abel

theorem fourier_convolution_comm (a b : (Fin 2 → ℤ) → ℂ) (k : Fin 2 → ℤ) :
    (∑' l, a l * b (k-l)) = ∑' l, b l * a (k-l) := by
  have h := (mixedSubEquiv k).tsum_eq (fun l => b l * a (k-l))
  have he (l : Fin 2 → ℤ) : k-(k-l) = l := by abel
  simpa only [mixedSubEquiv, Equiv.coe_fn_mk, he, mul_comm] using h

end AnomDiss

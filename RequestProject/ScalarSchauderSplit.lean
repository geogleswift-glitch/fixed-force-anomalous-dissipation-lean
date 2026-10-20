module

public import RequestProject.ScalarDuhamelGradientContinuity

/-! # The actual near/far time-integral estimate for spatial Schauder regularity -/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

lemma integral_schauder_far_le {a t β : ℝ} (ha : 0 < a) (hat : a ≤ t) (hβ : β < 1) :
    (∫ r in a..t, r ^ ((β - 3) / 2)) ≤
      2 / (1 - β) * a ^ ((β - 1) / 2) := by
  have hzero : (0 : ℝ) ∉ uIcc a t := by
    rw [uIcc_of_le hat]
    exact fun h => (not_le_of_gt ha) h.1
  rw [integral_rpow (Or.inr ⟨(by linarith : (β - 3) / 2 ≠ (-1 : ℝ)), hzero⟩)]
  have he : (β - 3) / 2 + 1 = (β - 1) / 2 := by ring
  rw [he]
  calc
    (t ^ ((β - 1) / 2) - a ^ ((β - 1) / 2)) / ((β - 1) / 2)
        = (2 / (1 - β)) * (a ^ ((β - 1) / 2) - t ^ ((β - 1) / 2)) := by
      have hβ' : β ≠ 1 := by linarith
      field_simp [hβ']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sub_le_self _ (Real.rpow_nonneg (ha.le.trans hat) _))
      (div_nonneg (by norm_num) (by linarith))

/-- Splitting at the square of the spatial distance combines a cancelled second
derivative bound and a third-derivative Lipschitz bound, preserving the input exponent. -/
theorem norm_integral_schauder_split {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {A B β d t : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hd : 0 < d) (ht : 0 ≤ t) (hf : IntervalIntegrable f volume 0 t)
    (hnear : ∀ r, 0 < r → ‖f r‖ ≤ A * r ^ ((β - 2) / 2))
    (hfar : ∀ r, 0 < r → ‖f r‖ ≤ B * d * r ^ ((β - 3) / 2)) :
    ‖∫ r in (0 : ℝ)..t, f r‖ ≤ (2 * A / β + 2 * B / (1 - β)) * d ^ β := by
  let a := d ^ 2
  have ha : 0 < a := sq_pos_of_pos hd
  have han : (a : ℝ) ^ (β / 2) = d ^ β := by
    dsimp [a]
    rw [← Real.rpow_two, ← Real.rpow_mul hd.le]
    congr 1
    ring
  have haf : d * a ^ ((β - 1) / 2) = d ^ β := by
    have he : a ^ ((β - 1) / 2) = d ^ (β - 1) := by
      dsimp [a]
      rw [← Real.rpow_two, ← Real.rpow_mul hd.le]
      congr 1
      ring
    rw [he]
    calc
      d * d ^ (β - 1) = d ^ (1 : ℝ) * d ^ (β - 1) := by rw [Real.rpow_one]
      _ = d ^ ((1 : ℝ) + (β - 1)) := (Real.rpow_add hd 1 (β - 1)).symm
      _ = _ := by congr 1; ring
  have near_bound {s : ℝ} (hs : 0 ≤ s) :
      ‖∫ r in (0 : ℝ)..s, f r‖ ≤ 2 * A / β * s ^ (β / 2) := by
    have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := s)
      (show (-1 : ℝ) < (β - 2) / 2 by linarith)).const_mul A
    calc
      ‖∫ r in (0 : ℝ)..s, f r‖ ≤ ∫ r in (0 : ℝ)..s, A * r ^ ((β - 2) / 2) :=
        intervalIntegral.norm_integral_le_of_norm_le hs
          (Eventually.of_forall fun r hr => hnear r hr.1) hi
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_derivative_rpow hβ₀]
        ring
  by_cases hat : t ≤ a
  · calc
      ‖∫ r in (0 : ℝ)..t, f r‖ ≤ 2 * A / β * t ^ (β / 2) := near_bound ht
      _ ≤ 2 * A / β * a ^ (β / 2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ht hat (by positivity)) (div_nonneg (mul_nonneg (by norm_num) hA) hβ₀.le)
      _ = 2 * A / β * d ^ β := by rw [han]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num) hB) (by linarith)))
        (Real.rpow_nonneg hd.le _)
  · have hat' : a ≤ t := (lt_of_not_ge hat).le
    have hf₀a : IntervalIntegrable f volume 0 a := hf.mono_set (by
      rw [uIcc_of_le ha.le, uIcc_of_le ht]
      exact Icc_subset_Icc_right hat')
    have hfat : IntervalIntegrable f volume a t := hf.mono_set (by
      rw [uIcc_of_le hat', uIcc_of_le ht]
      exact Icc_subset_Icc_left ha.le)
    have far_bound : ‖∫ r in a..t, f r‖ ≤ 2 * B / (1 - β) * d ^ β := by
      have hzero : (0 : ℝ) ∉ uIcc a t := by
        rw [uIcc_of_le hat']
        exact fun h => (not_le_of_gt ha) h.1
      have hi := (intervalIntegral.intervalIntegrable_rpow (μ := (volume : Measure ℝ))
        (a := a) (b := t) (r := (β - 3) / 2) (Or.inr hzero)).const_mul (B * d)
      calc
        ‖∫ r in a..t, f r‖ ≤ ∫ r in a..t, (B * d) * r ^ ((β - 3) / 2) :=
          intervalIntegral.norm_integral_le_of_norm_le hat'
            (Eventually.of_forall fun r hr => hfar r (ha.trans hr.1)) hi
        _ ≤ (B * d) * (2 / (1 - β) * a ^ ((β - 1) / 2)) := by
          rw [intervalIntegral.integral_const_mul]
          exact mul_le_mul_of_nonneg_left (integral_schauder_far_le ha hat' hβ₁) (mul_nonneg hB hd.le)
        _ = _ := by
          calc
            (B * d) * (2 / (1 - β) * a ^ ((β - 1) / 2))
                = (2 * B / (1 - β)) * (d * a ^ ((β - 1) / 2)) := by ring
            _ = _ := by rw [haf]
    rw [← intervalIntegral.integral_add_adjacent_intervals hf₀a hfat]
    calc
      ‖(∫ r in (0 : ℝ)..a, f r) + ∫ r in a..t, f r‖
          ≤ ‖∫ r in (0 : ℝ)..a, f r‖ + ‖∫ r in a..t, f r‖ := norm_add_le _ _
      _ ≤ 2 * A / β * a ^ (β / 2) + 2 * B / (1 - β) * d ^ β :=
        add_le_add (near_bound ha.le) far_bound
      _ = _ := by rw [han]; ring

end AnomDiss

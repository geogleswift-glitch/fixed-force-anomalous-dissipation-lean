module

public import RequestProject.ScalarDuhamel
public import RequestProject.ScalarHeatFractionalSmoothing

/-! # Spatial Hölder regularity supplied by the actual Duhamel operator -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

def duhamelFractionalScale (ν C α : ℝ) : ℝ :=
  heatGradientFractionalConstant C α * (2 * ν) ^ (-(1 + α) / 2)

lemma duhamelFractionalScale_nonneg {ν C α : ℝ} (hν : 0 ≤ ν) (hC : 0 ≤ C) :
    0 ≤ duhamelFractionalScale ν C α :=
  mul_nonneg (heatGradientFractionalConstant_nonneg hC)
    (Real.rpow_nonneg (by positivity) _)

lemma integral_fractional_rpow {α t : ℝ} (hα : α < 1) :
    (∫ r in (0 : ℝ)..t, r ^ (-(1 + α) / 2)) =
      2 / (1 - α) * t ^ ((1 - α) / 2) := by
  rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -(1 + α) / 2))]
  have he : -(1 + α) / 2 + 1 = (1 - α) / 2 := by ring
  rw [he, Real.zero_rpow (by linarith : (1 - α) / 2 ≠ (0 : ℝ)), sub_zero]
  field_simp

lemma laggedDuhamelKernel_fractional_distance {ν α : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (i : Fin 2) (t : ℝ) (x y : Pt 2)
    {r : ℝ} (hr : 0 < r) :
    ‖laggedDuhamelKernel ν F i (t, x) r - laggedDuhamelKernel ν F i (t, y) r‖ ≤
      duhamelFractionalScale ν C α * r ^ (-(1 + α) / 2) * ‖x - y‖ ^ α := by
  have hfc : Continuous (F (t - r)) := hF.comp (continuous_const.prodMk continuous_id)
  have hv : 0 < (Real.toNNReal (2 * ν * r) : ℝ) := by
    rw [Real.coe_toNNReal _ (by positivity)]
    positivity
  have h := heatGradientKernel_fractional_distance hfc (hFp (t - r))
    (hC (t - r)) hα₀ hα₁ hv i x y
  unfold laggedDuhamelKernel
  apply h.trans_eq
  rw [Real.coe_toNNReal _ (by positivity), Real.mul_rpow (by positivity) hr.le]
  unfold duhamelFractionalScale
  ring

/-- Bounded continuous periodic sources give a spatial Hölder Duhamel output for
every exponent strictly below one, uniformly from time zero. -/
theorem duhamelComponent_fractional_distance {ν α : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hα₀ : 0 ≤ α) (hα₁ : α < 1) (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) (x y : Pt 2) :
    ‖duhamelComponent ν F i t x - duhamelComponent ν F i t y‖ ≤
      (2 * duhamelFractionalScale ν C α / (1 - α) * t ^ ((1 - α) / 2)) * ‖x - y‖ ^ α := by
  simp_rw [duhamelComponent_eq_lagged]
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_laggedDuhamelKernel hν hF hC i (t, x) ht)
    (intervalIntegrable_laggedDuhamelKernel hν hF hC i (t, y) ht)]
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
    (show (-1 : ℝ) < -(1 + α) / 2 by linarith)).const_mul
      (duhamelFractionalScale ν C α * ‖x - y‖ ^ α)
  calc
    ‖∫ r in (0 : ℝ)..t,
        (laggedDuhamelKernel ν F i (t, x) r - laggedDuhamelKernel ν F i (t, y) r)‖
        ≤ ∫ r in (0 : ℝ)..t,
            (duhamelFractionalScale ν C α * ‖x - y‖ ^ α) * r ^ (-(1 + α) / 2) := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht
        (Eventually.of_forall fun r hr => ?_) hi
      apply (laggedDuhamelKernel_fractional_distance hν hF hFp hC hα₀ hα₁.le i t x y hr.1).trans_eq
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_fractional_rpow hα₁]
      ring

end AnomDiss

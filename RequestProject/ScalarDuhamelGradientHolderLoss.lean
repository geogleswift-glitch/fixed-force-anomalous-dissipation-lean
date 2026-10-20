module

public import RequestProject.ScalarDuhamelGradientContinuity
public import RequestProject.ScalarHeatHessianHolderLoss

/-! # Positive Hölder regularity of the actual Duhamel spatial derivative -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

def duhamelGradientHolderLossScale (ν H β α : ℝ) : ℝ :=
  2 * heatHessianHolderLossConstant H β α * ν ^ ((β - α - 2) / 2)

lemma duhamelGradientHolderLossScale_nonneg {ν H β α : ℝ} (hν : 0 ≤ ν) (hH : 0 ≤ H) :
    0 ≤ duhamelGradientHolderLossScale ν H β α := by
  unfold duhamelGradientHolderLossScale
  exact mul_nonneg (mul_nonneg (by norm_num) (heatHessianHolderLossConstant_nonneg hH))
    (Real.rpow_nonneg hν _)

lemma intervalIntegrable_laggedDuhamelSpaceDerivative_holder {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i : Fin 2) (t : ℝ) (x : Pt 2) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (laggedDuhamelSpaceDerivative ν F i t x) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  have hb := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T)
    (show (-1 : ℝ) < (β - 2) / 2 by linarith)).const_mul (duhamelSpaceDerivativeScale ν H β)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at hb
  refine hb.mono' (aestronglyMeasurable_laggedDuhamelSpaceDerivative hν hF hC i t x T) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
  exact norm_laggedDuhamelSpaceDerivative_holder_le hν hF hFp hC hH hβ hholder i t x hr.1

lemma laggedDuhamelSpaceDerivative_holder_loss_distance {ν β α : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β) (hα₀ : 0 ≤ α) (hαβ : α < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i : Fin 2) (t : ℝ) (x y : Pt 2) {r : ℝ} (hr : 0 < r) :
    ‖laggedDuhamelSpaceDerivative ν F i t x r - laggedDuhamelSpaceDerivative ν F i t y r‖ ≤
      duhamelGradientHolderLossScale ν H β α * r ^ ((β - α - 2) / 2) * ‖x - y‖ ^ α := by
  let v := Real.toNNReal (2 * ν * r)
  have hv : 0 < (v : ℝ) := by
    change 0 < (Real.toNNReal (2 * ν * r) : ℝ)
    rw [Real.coe_toNNReal _ (by positivity)]
    positivity
  have hfc : Continuous (F (t - r)) := hF.comp (continuous_const.prodMk continuous_id)
  have he : heatGradientKernel v (F (t - r)) i = pd i (heatOp v (F (t - r))) :=
    funext fun z => (pd_heatOp_continuous_periodic hfc (hFp (t - r)) hv i z).symm
  unfold laggedDuhamelSpaceDerivative laggedDuhamelKernel
  change ‖fderiv ℝ (heatGradientKernel v (F (t - r)) i) x -
    fderiv ℝ (heatGradientKernel v (F (t - r)) i) y‖ ≤ _
  rw [he]
  have h := norm_clm_pt2_le (fderiv ℝ (pd i (heatOp v (F (t - r)))) x -
    fderiv ℝ (pd i (heatOp v (F (t - r)))) y)
  change ‖fderiv ℝ (pd i (heatOp v (F (t - r)))) x - fderiv ℝ (pd i (heatOp v (F (t - r)))) y‖ ≤
    ‖pd 0 (pd i (heatOp v (F (t - r)))) x - pd 0 (pd i (heatOp v (F (t - r)))) y‖ +
    ‖pd 1 (pd i (heatOp v (F (t - r)))) x - pd 1 (pd i (heatOp v (F (t - r)))) y‖ at h
  have h₀ := pd2_heatOp_holder_loss_distance hfc (hFp (t - r)) (hC (t - r)) hH hβ hα₀ hαβ
    (hholder (t - r)) hv 0 i x y
  have h₁ := pd2_heatOp_holder_loss_distance hfc (hFp (t - r)) (hC (t - r)) hH hβ hα₀ hαβ
    (hholder (t - r)) hv 1 i x y
  apply (h.trans (add_le_add h₀ h₁)).trans_eq
  have hv' : (v : ℝ) / 2 = ν * r := by
    change (Real.toNNReal (2 * ν * r) : ℝ) / 2 = ν * r
    rw [Real.coe_toNNReal _ (by positivity)]
    ring
  rw [hv', Real.mul_rpow hν.le hr.le]
  unfold duhamelGradientHolderLossScale
  ring

/-- The actual Duhamel gradient is uniformly spatially Hölder for every strictly
smaller exponent than that of the source. -/
theorem fderiv_duhamelComponent_holder_loss_distance {ν β α : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β) (hα₀ : 0 ≤ α) (hαβ : α < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) (x y : Pt 2) :
    ‖fderiv ℝ (duhamelComponent ν F i t) x - fderiv ℝ (duhamelComponent ν F i t) y‖ ≤
      (2 * duhamelGradientHolderLossScale ν H β α / (β - α) * t ^ ((β - α) / 2)) * ‖x - y‖ ^ α := by
  rw [(hasFDerivAt_duhamelComponent_holder hν hF hFp hC hH hβ hholder i ht x).fderiv,
    (hasFDerivAt_duhamelComponent_holder hν hF hFp hC hH hβ hholder i ht y).fderiv,
    ← intervalIntegral.integral_sub
      (intervalIntegrable_laggedDuhamelSpaceDerivative_holder hν hF hFp hC hH hβ hholder i t x ht)
      (intervalIntegrable_laggedDuhamelSpaceDerivative_holder hν hF hFp hC hH hβ hholder i t y ht)]
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
    (show (-1 : ℝ) < (β - α - 2) / 2 by linarith)).const_mul
      (duhamelGradientHolderLossScale ν H β α * ‖x - y‖ ^ α)
  calc
    ‖∫ r in (0 : ℝ)..t,
        (laggedDuhamelSpaceDerivative ν F i t x r - laggedDuhamelSpaceDerivative ν F i t y r)‖
        ≤ ∫ r in (0 : ℝ)..t,
          (duhamelGradientHolderLossScale ν H β α * ‖x - y‖ ^ α) * r ^ ((β - α - 2) / 2) := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht (Eventually.of_forall fun r hr => ?_) hi
      apply (laggedDuhamelSpaceDerivative_holder_loss_distance hν hF hFp hC hH hβ hα₀ hαβ
        hholder i t x y hr.1).trans_eq
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_derivative_rpow (sub_pos.2 hαβ)]
      ring

end AnomDiss

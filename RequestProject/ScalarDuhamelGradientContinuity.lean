module

public import RequestProject.ScalarDuhamelDifferentiability
public import RequestProject.HeatSecondKernel

/-! # Joint continuity and uniform bounds for actual Duhamel spatial derivatives -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

lemma duhamelSpaceDerivativeScale_nonneg {ν H β : ℝ} (hν : 0 ≤ ν) (hH : 0 ≤ H) :
    0 ≤ duhamelSpaceDerivativeScale ν H β := by
  unfold duhamelSpaceDerivativeScale
  have hg₀ := gmom_nonneg (β + 1)
  have hg₁ := gmom_nonneg 1
  positivity

lemma continuous_laggedDuhamelSpaceDerivative_param {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (i : Fin 2) {r : ℝ} (hr : 0 < r) :
    Continuous fun p : ℝ × Pt 2 => laggedDuhamelSpaceDerivative ν F i p.1 p.2 r := by
  let v := Real.toNNReal (2 * ν * r)
  have hv : 0 < (v : ℝ) := by
    change 0 < (Real.toNNReal (2 * ν * r) : ℝ)
    rw [Real.coe_toNNReal _ (by positivity)]
    positivity
  have he : (fun p : ℝ × Pt 2 => laggedDuhamelSpaceDerivative ν F i p.1 p.2 r) =
      fun p => ∑ k : Fin 2, (ContinuousLinearMap.proj k).smulRight
        (pd k (pd i (heatOp v (F (p.1 - r)))) p.2) := by
    funext p
    have hfc : Continuous (F (p.1 - r)) := hF.comp (continuous_const.prodMk continuous_id)
    have hk : heatGradientKernel v (F (p.1 - r)) i = pd i (heatOp v (F (p.1 - r))) :=
      funext fun y => (pd_heatOp_continuous_periodic hfc (hFp (p.1 - r)) hv i y).symm
    unfold laggedDuhamelSpaceDerivative laggedDuhamelKernel
    change fderiv ℝ (heatGradientKernel v (F (p.1 - r)) i) p.2 = _
    rw [hk]
    apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply]
    exact fderiv_apply_eq_sum_pd p.2 z
  rw [he]
  refine continuous_finset_sum _ fun k _ => ?_
  apply (ContinuousLinearMap.smulRightL ℝ (Pt 2) ℂ (ContinuousLinearMap.proj k)).continuous.comp
  refine continuous_iff_continuousAt.2 fun p => ?_
  exact (continuousAt_pd2_heatOp_with_param hF hC hFp k i
    (p := (p.1 - r, v, p.2)) hv).comp
      (f := fun q : ℝ × Pt 2 => (q.1 - r, v, q.2)) (by fun_prop)

def truncatedDuhamelSpaceDerivative (ν : ℝ) (F : ℝ → Pt 2 → ℂ) (i : Fin 2)
    (T : ℝ) (p : ℝ × Pt 2) : Pt 2 →L[ℝ] ℂ :=
  ∫ r in (0 : ℝ)..T, (Iic p.1).indicator (laggedDuhamelSpaceDerivative ν F i p.1 p.2) r

theorem continuous_truncatedDuhamelSpaceDerivative {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i : Fin 2) {T : ℝ} (hT : 0 ≤ T) :
    Continuous (truncatedDuhamelSpaceDerivative ν F i T) := by
  have hscale := duhamelSpaceDerivativeScale_nonneg hν.le hH (β := β)
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T)
    (show (-1 : ℝ) < (β - 2) / 2 by linarith)).const_mul (duhamelSpaceDerivativeScale ν H β)
  refine continuous_iff_continuousAt.2 fun p => ?_
  unfold truncatedDuhamelSpaceDerivative
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun r => duhamelSpaceDerivativeScale ν H β * r ^ ((β - 2) / 2))
    (Eventually.of_forall fun q => ?_) (Eventually.of_forall fun q => ?_) hi ?_
  · simpa only [uIoc_of_le hT] using
      (aestronglyMeasurable_laggedDuhamelSpaceDerivative hν hF hC i q.1 q.2 T).indicator
        measurableSet_Iic
  · exact Eventually.of_forall fun r hr => by
      rw [uIoc_of_le hT] at hr
      by_cases hm : r ∈ Iic q.1
      · rw [Set.indicator_of_mem hm]
        exact norm_laggedDuhamelSpaceDerivative_holder_le hν hF hFp hC hH hβ hholder i q.1 q.2 hr.1
      · rw [Set.indicator_of_notMem hm, norm_zero]
        exact mul_nonneg hscale (Real.rpow_nonneg hr.1.le _)
  · filter_upwards [volume.ae_ne p.1] with r hrne
    intro hr
    rw [uIoc_of_le hT] at hr
    rcases lt_or_gt_of_ne hrne with hlt | hgt
    · have he : (fun q : ℝ × Pt 2 =>
          (Iic q.1).indicator (laggedDuhamelSpaceDerivative ν F i q.1 q.2) r)
          =ᶠ[𝓝 p] (fun q => laggedDuhamelSpaceDerivative ν F i q.1 q.2 r) := by
        filter_upwards [continuous_fst.continuousAt.eventually (Ioi_mem_nhds hlt)] with q hq
        exact Set.indicator_of_mem (show r ∈ Iic q.1 from hq.le) _
      exact ((continuous_laggedDuhamelSpaceDerivative_param hν hF hFp hC i hr.1).continuousAt).congr_of_eventuallyEq he
    · have he : (fun q : ℝ × Pt 2 =>
          (Iic q.1).indicator (laggedDuhamelSpaceDerivative ν F i q.1 q.2) r)
          =ᶠ[𝓝 p] (fun _ => (0 : Pt 2 →L[ℝ] ℂ)) := by
        filter_upwards [continuous_fst.continuousAt.eventually (Iio_mem_nhds hgt)] with q hq
        exact Set.indicator_of_notMem (show r ∉ Iic q.1 from not_le.2 hq) _
      exact continuousAt_const.congr_of_eventuallyEq he

/-- The spatial derivative is jointly continuous from the actual initial time onwards. -/
theorem continuousOn_fderiv_duhamelComponent_holder {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i : Fin 2) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun p : ℝ × Pt 2 => fderiv ℝ (duhamelComponent ν F i p.1) p.2)
      {p | p.1 ∈ Icc (0 : ℝ) T} := by
  refine (continuous_truncatedDuhamelSpaceDerivative hν hF hFp hC hH hβ hholder i hT).continuousOn.congr ?_
  intro p hp
  unfold truncatedDuhamelSpaceDerivative
  change fderiv ℝ (duhamelComponent ν F i p.1) p.2 =
    ∫ r in (0 : ℝ)..T, {r | r ≤ p.1}.indicator (laggedDuhamelSpaceDerivative ν F i p.1 p.2) r
  rw [intervalIntegral.integral_indicator hp]
  exact (hasFDerivAt_duhamelComponent_holder hν hF hFp hC hH hβ hholder i hp.1 p.2).fderiv

lemma integral_derivative_rpow {β t : ℝ} (hβ : 0 < β) :
    (∫ r in (0 : ℝ)..t, r ^ ((β - 2) / 2)) = 2 / β * t ^ (β / 2) := by
  rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < (β - 2) / 2))]
  have he : (β - 2) / 2 + 1 = β / 2 := by ring
  rw [he, Real.zero_rpow (by positivity : β / 2 ≠ (0 : ℝ)), sub_zero]
  field_simp

theorem norm_fderiv_duhamelComponent_holder_le {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) (x : Pt 2) :
    ‖fderiv ℝ (duhamelComponent ν F i t) x‖ ≤
      (2 * duhamelSpaceDerivativeScale ν H β / β) * t ^ (β / 2) := by
  rw [(hasFDerivAt_duhamelComponent_holder hν hF hFp hC hH hβ hholder i ht x).fderiv]
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
    (show (-1 : ℝ) < (β - 2) / 2 by linarith)).const_mul (duhamelSpaceDerivativeScale ν H β)
  calc
    ‖∫ r in (0 : ℝ)..t, laggedDuhamelSpaceDerivative ν F i t x r‖
        ≤ ∫ r in (0 : ℝ)..t, duhamelSpaceDerivativeScale ν H β * r ^ ((β - 2) / 2) := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht (Eventually.of_forall fun r hr => ?_) hi
      exact norm_laggedDuhamelSpaceDerivative_holder_le hν hF hFp hC hH hβ hholder i t x hr.1
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_derivative_rpow hβ]
      ring

end AnomDiss

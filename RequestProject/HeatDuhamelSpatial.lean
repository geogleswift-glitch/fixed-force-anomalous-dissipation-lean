module

public import RequestProject.HeatDuhamelFoundation
public import RequestProject.ScalarDuhamelDifferentiability

/-!
# Genuine spatial derivatives of ordinary-source heat Duhamel integration

One derivative needs only a bounded continuous periodic source. Its coordinate
derivatives are the previously constructed divergence-form Duhamel integrals.
Spatial Hölder sources therefore give actual second derivatives as well.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

def laggedHeatDuhamelKernel (ν : ℝ) (F : ℝ → Pt 2 → ℂ)
    (t : ℝ) (x : Pt 2) (r : ℝ) : ℂ :=
  heatOp (Real.toNNReal (2 * ν * r)) (F (t - r)) x

def laggedHeatDuhamelDerivative (ν : ℝ) (F : ℝ → Pt 2 → ℂ)
    (t : ℝ) (x : Pt 2) (r : ℝ) : Pt 2 →L[ℝ] ℂ :=
  fderiv ℝ (fun y => laggedHeatDuhamelKernel ν F t y r) x

theorem heatDuhamel_eq_lagged (ν : ℝ) (F : ℝ → Pt 2 → ℂ) (t : ℝ) (x : Pt 2) :
    heatDuhamel ν F t x = ∫ r in (0 : ℝ)..t, laggedHeatDuhamelKernel ν F t x r := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun r => laggedHeatDuhamelKernel ν F t x r) (a := 0) (b := t) t
  simpa [heatDuhamel, laggedHeatDuhamelKernel] using h

theorem continuous_laggedHeatDuhamelKernel (ν : ℝ) {F : ℝ → Pt 2 → ℂ}
    (hF : Continuous (Function.uncurry F)) {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (t : ℝ) : Continuous (fun p : ℝ × Pt 2 => laggedHeatDuhamelKernel ν F t p.2 p.1) :=
  (continuous_heatOp_with_param hF hC).comp
    (by fun_prop : Continuous (fun p : ℝ × Pt 2 =>
      (t - p.1, Real.toNNReal (2 * ν * p.1), p.2)))

theorem measurable_laggedHeatDuhamelDerivative (ν : ℝ) {F : ℝ → Pt 2 → ℂ}
    (hF : Continuous (Function.uncurry F)) {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (t : ℝ) (x : Pt 2) : Measurable (laggedHeatDuhamelDerivative ν F t x) := by
  let G : ℝ → Pt 2 → ℂ := fun r y => laggedHeatDuhamelKernel ν F t y r
  have hc : Continuous (Function.uncurry G) := continuous_laggedHeatDuhamelKernel ν hF hC t
  exact (measurable_fderiv_with_param ℝ hc).comp
    (measurable_id.prodMk measurable_const)

theorem norm_laggedHeatDuhamelDerivative_le {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (t : ℝ) (x : Pt 2) {r : ℝ} (hr : 0 < r) :
    ‖laggedHeatDuhamelDerivative ν F t x r‖ ≤
      2 * duhamelScale ν C * r ^ (-(1 / 2 : ℝ)) := by
  have hv : 0 < (Real.toNNReal (2 * ν * r) : ℝ) := by
    rw [Real.coe_toNNReal _ (by positivity)]
    positivity
  have hf : Continuous (F (t - r)) := hF.comp (continuous_const.prodMk continuous_id)
  have he (i : Fin 2) :
      laggedHeatDuhamelDerivative ν F t x r (Pi.single i 1) =
        laggedDuhamelKernel ν F i (t, x) r :=
    pd_heatOp_continuous_periodic hf (hp (t - r)) hv i x
  have h := norm_clm_pt2_le (laggedHeatDuhamelDerivative ν F t x r)
  rw [he 0, he 1] at h
  have h₀ := norm_laggedDuhamelKernel_le hν hF hC 0 (t, x) hr
  have h₁ := norm_laggedDuhamelKernel_le hν hF hC 1 (t, x) hr
  nlinarith

theorem intervalIntegrable_laggedHeatDuhamelDerivative {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    {t : ℝ} (ht : 0 ≤ t) (x : Pt 2) :
    IntervalIntegrable (laggedHeatDuhamelDerivative ν F t x) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  have hb := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
    (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul (2 * duhamelScale ν C)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at hb
  refine hb.mono' (measurable_laggedHeatDuhamelDerivative ν hF hC t x).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
  exact norm_laggedHeatDuhamelDerivative_le hν hF hp hC t x hr.1

/-- The displayed integral is the true spatial Fréchet derivative of the ordinary Duhamel term. -/
theorem hasFDerivAt_heatDuhamel {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    {t : ℝ} (ht : 0 ≤ t) (x : Pt 2) :
    HasFDerivAt (heatDuhamel ν F t)
      (∫ r in (0 : ℝ)..t, laggedHeatDuhamelDerivative ν F t x r) x := by
  have he : heatDuhamel ν F t = fun y =>
      ∫ r in (0 : ℝ)..t, laggedHeatDuhamelKernel ν F t y r :=
    funext (heatDuhamel_eq_lagged ν F t)
  rw [he]
  have hc := continuous_laggedHeatDuhamelKernel ν hF hC t
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s := univ) (bound := fun r => 2 * duhamelScale ν C * r ^ (-(1 / 2 : ℝ)))
    (by simp) (Eventually.of_forall fun y => ?_) ?_ ?_ ?_ ?_ ?_
  · exact ((hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable).restrict
  · exact (hc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  · exact (measurable_laggedHeatDuhamelDerivative ν hF hC t x).aestronglyMeasurable.restrict
  · rw [uIoc_of_le ht]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    intro y _
    exact norm_laggedHeatDuhamelDerivative_le hν hF hp hC t y hr.1
  · exact (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
      (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul _
  · rw [uIoc_of_le ht]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    intro y _
    have hr₀ : 0 < r := hr.1
    have hv : 0 < (Real.toNNReal (2 * ν * r) : ℝ) := by
      rw [Real.coe_toNNReal _ (by positivity)]
      positivity
    exact ((contDiff_one_heatOp_continuous_periodic
      (hF.comp (continuous_const.prodMk continuous_id)) (hp (t - r)) hv).differentiable
      one_ne_zero y).hasFDerivAt

theorem pd_heatDuhamel_eq_duhamelComponent {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    {t : ℝ} (ht : 0 ≤ t) (i : Fin 2) (x : Pt 2) :
    pd i (heatDuhamel ν F t) x = duhamelComponent ν F i t x := by
  unfold pd
  rw [(hasFDerivAt_heatDuhamel hν hF hp hC ht x).fderiv,
    ContinuousLinearMap.intervalIntegral_apply
      (intervalIntegrable_laggedHeatDuhamelDerivative hν hF hp hC ht x)]
  rw [duhamelComponent_eq_lagged]
  apply intervalIntegral.integral_congr_ae
  rw [uIoc_of_le ht]
  exact Eventually.of_forall fun r hr => by
    have hr₀ : 0 < r := hr.1
    have hv : 0 < (Real.toNNReal (2 * ν * r) : ℝ) := by
      rw [Real.coe_toNNReal _ (by positivity)]
      positivity
    exact pd_heatOp_continuous_periodic
      (hF.comp (continuous_const.prodMk continuous_id)) (hp (t - r)) hv i x

/-- Spatial Hölder cancellation yields actual `C²` regularity of the ordinary Duhamel term. -/
theorem contDiff_two_heatDuhamel_holder {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ 2 (heatDuhamel ν F t) := by
  apply contDiff_two_of_contDiff_partials
    (fun x => (hasFDerivAt_heatDuhamel hν hF hp hC ht x).differentiableAt)
  intro i
  have he : pd i (heatDuhamel ν F t) = duhamelComponent ν F i t :=
    funext (pd_heatDuhamel_eq_duhamelComponent hν hF hp hC ht i)
  rw [he]
  exact contDiff_one_duhamelComponent_holder hν hF hp hC hH hβ hholder i ht

end AnomDiss

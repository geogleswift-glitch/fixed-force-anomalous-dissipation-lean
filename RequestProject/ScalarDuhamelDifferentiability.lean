module

public import RequestProject.ScalarDuhamelHolder
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Actual spatial differentiation of divergence-form Duhamel integration

Spatial Hölder cancellation makes the second heat derivative time-integrable.
The resulting derivative is the actual Fréchet derivative of the Bochner integral.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

def laggedDuhamelSpaceDerivative (ν : ℝ) (F : ℝ → Pt 2 → ℂ) (i : Fin 2)
    (t : ℝ) (x : Pt 2) (r : ℝ) : Pt 2 →L[ℝ] ℂ :=
  fderiv ℝ (fun y => laggedDuhamelKernel ν F i (t, y) r) x

lemma continuous_laggedDuhamelKernel_pos_param {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F)) {C : ℝ}
    (hC : ∀ s x, ‖F s x‖ ≤ C) (i : Fin 2) (t : ℝ) :
    Continuous fun p : Ioi (0 : ℝ) × Pt 2 => laggedDuhamelKernel ν F i (t, p.2) p.1 := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  have hr : 0 < (p.1 : ℝ) := p.1.property
  have hv : 0 < (Real.toNNReal (2 * ν * (p.1 : ℝ)) : ℝ) := by
    rw [Real.coe_toNNReal _ (by positivity)]
    exact mul_pos (mul_pos (by norm_num) hν) p.1.property
  exact (continuousAt_heatGradientKernel_with_param hF hC i
    (p := (t - (p.1 : ℝ), Real.toNNReal (2 * ν * (p.1 : ℝ)), p.2)) hv).comp
      (f := fun q : Ioi (0 : ℝ) × Pt 2 =>
        (t - (q.1 : ℝ), Real.toNNReal (2 * ν * (q.1 : ℝ)), q.2)) (by fun_prop)

/-- Derivatives of the actual kernel are measurable in elapsed time, obtained
from the general measurable parameter-derivative theorem on the positive half-line. -/
lemma aestronglyMeasurable_laggedDuhamelSpaceDerivative {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F)) {C : ℝ}
    (hC : ∀ s x, ‖F s x‖ ≤ C) (i : Fin 2) (t : ℝ) (x : Pt 2) (T : ℝ) :
    AEStronglyMeasurable (laggedDuhamelSpaceDerivative ν F i t x)
      (volume.restrict (Ioc (0 : ℝ) T)) := by
  let G : Ioi (0 : ℝ) → Pt 2 → ℂ := fun r y => laggedDuhamelKernel ν F i (t, y) r
  have hc : Continuous (Function.uncurry G) := continuous_laggedDuhamelKernel_pos_param hν hF hC i t
  have hm : Measurable (fun r : Ioi (0 : ℝ) => laggedDuhamelSpaceDerivative ν F i t x r) :=
    (measurable_fderiv_with_param ℝ hc).comp (measurable_id.prodMk measurable_const)
  have hm' := hm.dite (measurable_const : Measurable
    (fun _ : ((Ioi (0 : ℝ))ᶜ : Set ℝ) => (0 : Pt 2 →L[ℝ] ℂ))) measurableSet_Ioi
  have ha : AEStronglyMeasurable
      (fun r : ℝ => if hr : r ∈ Ioi (0 : ℝ)
        then laggedDuhamelSpaceDerivative ν F i t x r else 0)
      (volume.restrict (Ioc (0 : ℝ) T)) := hm'.aestronglyMeasurable
  refine ha.congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
  simp only [mem_Ioi, dif_pos hr.1]

def duhamelSpaceDerivativeScale (ν H β : ℝ) : ℝ :=
  4 * H * gmom (β + 1) * gmom 1 * ν ^ ((β - 2) / 2)

/-- The full spatial derivative has the genuine cancelled, integrable time bound. -/
lemma norm_laggedDuhamelSpaceDerivative_holder_le {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i : Fin 2) (t : ℝ) (x : Pt 2) {r : ℝ} (hr : 0 < r) :
    ‖laggedDuhamelSpaceDerivative ν F i t x r‖ ≤
      duhamelSpaceDerivativeScale ν H β * r ^ ((β - 2) / 2) := by
  let v := Real.toNNReal (2 * ν * r)
  have hv : 0 < (v : ℝ) := by
    change 0 < (Real.toNNReal (2 * ν * r) : ℝ)
    rw [Real.coe_toNNReal _ (by positivity)]
    positivity
  have hfc : Continuous (F (t - r)) := hF.comp (continuous_const.prodMk continuous_id)
  have he : heatGradientKernel v (F (t - r)) i = pd i (heatOp v (F (t - r))) :=
    funext fun y => (pd_heatOp_continuous_periodic hfc (hFp (t - r)) hv i y).symm
  unfold laggedDuhamelSpaceDerivative laggedDuhamelKernel
  change ‖fderiv ℝ (heatGradientKernel v (F (t - r)) i) x‖ ≤ _
  rw [he]
  have h := norm_clm_pt2_le (fderiv ℝ (pd i (heatOp v (F (t - r)))) x)
  change ‖fderiv ℝ (pd i (heatOp v (F (t - r)))) x‖ ≤
    ‖pd 0 (pd i (heatOp v (F (t - r)))) x‖ + ‖pd 1 (pd i (heatOp v (F (t - r)))) x‖ at h
  have h₀ := norm_pd2_heatOp_holder_le hfc (hFp (t - r)) (hC (t - r))
    hH hβ (hholder (t - r)) hv 0 i x
  have h₁ := norm_pd2_heatOp_holder_le hfc (hFp (t - r)) (hC (t - r))
    hH hβ (hholder (t - r)) hv 1 i x
  apply (h.trans (add_le_add h₀ h₁)).trans_eq
  have hv' : (v : ℝ) / 2 = ν * r := by
    change (Real.toNNReal (2 * ν * r) : ℝ) / 2 = ν * r
    rw [Real.coe_toNNReal _ (by positivity)]
    ring
  rw [hv', Real.mul_rpow hν.le hr.le]
  unfold duhamelSpaceDerivativeScale
  ring

/-- The displayed derivative integral is the true Fréchet derivative of `D_iF`. -/
theorem hasFDerivAt_duhamelComponent_holder {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) (x : Pt 2) :
    HasFDerivAt (duhamelComponent ν F i t)
      (∫ r in (0 : ℝ)..t, laggedDuhamelSpaceDerivative ν F i t x r) x := by
  have he : duhamelComponent ν F i t =
      fun y => ∫ r in (0 : ℝ)..t, laggedDuhamelKernel ν F i (t, y) r :=
    funext fun y => duhamelComponent_eq_lagged ν F i t y
  rw [he]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s := univ) (bound := fun r => duhamelSpaceDerivativeScale ν H β * r ^ ((β - 2) / 2))
    (by simp) (Eventually.of_forall fun y => ?_)
    (intervalIntegrable_laggedDuhamelKernel hν hF hC i (t, x) ht) ?_ ?_ ?_ ?_
  · simpa only [uIoc_of_le ht] using aestronglyMeasurable_laggedDuhamelKernel hν hF hC i (t, y) t
  · simpa only [uIoc_of_le ht] using
      aestronglyMeasurable_laggedDuhamelSpaceDerivative hν hF hC i t x t
  · rw [uIoc_of_le ht]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    intro y _
    exact norm_laggedDuhamelSpaceDerivative_holder_le hν hF hFp hC hH hβ hholder i t y hr.1
  · exact (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
      (show (-1 : ℝ) < (β - 2) / 2 by linarith)).const_mul _
  · rw [uIoc_of_le ht]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    intro y _
    have hr₀ : 0 < r := hr.1
    have hv : 0 < (Real.toNNReal (2 * ν * r) : ℝ) := by
      rw [Real.coe_toNNReal _ (by positivity)]
      positivity
    have hfc : Continuous (F (t - r)) := hF.comp (continuous_const.prodMk continuous_id)
    exact ((contDiff_one_heatGradientKernel_continuous_periodic hfc (hFp (t - r)) hv i).differentiable
      one_ne_zero y).hasFDerivAt

/-- Hölder sources give actual continuous first spatial derivatives of the Duhamel output. -/
theorem contDiff_one_duhamelComponent_holder {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ 1 (duhamelComponent ν F i t) := by
  have hd := hasFDerivAt_duhamelComponent_holder hν hF hFp hC hH hβ hholder i ht
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  have he : fderiv ℝ (duhamelComponent ν F i t) =
      fun x => ∫ r in (0 : ℝ)..t, laggedDuhamelSpaceDerivative ν F i t x r :=
    funext fun x => (hd x).fderiv
  rw [he]
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
    (show (-1 : ℝ) < (β - 2) / 2 by linarith)).const_mul (duhamelSpaceDerivativeScale ν H β)
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun r => duhamelSpaceDerivativeScale ν H β * r ^ ((β - 2) / 2))
    (Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_) hi ?_
  · simpa only [uIoc_of_le ht] using
      aestronglyMeasurable_laggedDuhamelSpaceDerivative hν hF hC i t y t
  · exact Eventually.of_forall fun r hr => by
      rw [uIoc_of_le ht] at hr
      exact norm_laggedDuhamelSpaceDerivative_holder_le hν hF hFp hC hH hβ hholder i t y hr.1
  · exact Eventually.of_forall fun r hr => by
      rw [uIoc_of_le ht] at hr
      have hr₀ : 0 < r := hr.1
      have hv : 0 < (Real.toNNReal (2 * ν * r) : ℝ) := by
        rw [Real.coe_toNNReal _ (by positivity)]
        positivity
      have hfc : Continuous (F (t - r)) := hF.comp (continuous_const.prodMk continuous_id)
      exact ((contDiff_one_heatGradientKernel_continuous_periodic hfc (hFp (t - r)) hv i).continuous_fderiv
        one_ne_zero).continuousAt

end AnomDiss

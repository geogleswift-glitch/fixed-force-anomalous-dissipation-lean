module

public import RequestProject.ScalarHeatSmoothing

/-!
# Divergence-form Duhamel integration

The time singularity is `r⁻¹/²`.  The source is an actual bounded continuous function,
not an existence or regularity hypothesis for a PDE solution.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-- The constant in the first-derivative heat estimate at physical diffusivity `ν`. -/
def duhamelScale (ν C : ℝ) : ℝ := C * gmom 1 / Real.sqrt (2 * ν)

/-- A single component of `∫₀ᵗ ∂ᵢH_{2ν(t-s)} F(s) ds`. -/
def duhamelComponent (ν : ℝ) (F : ℝ → Pt 2 → ℂ) (i : Fin 2) (t : ℝ) (x : Pt 2) : ℂ :=
  ∫ s in (0 : ℝ)..t, heatGradientKernel (Real.toNNReal (2 * ν * (t - s))) (F s) i x

/-- The same integrand in the elapsed-time variable `r = t-s`. -/
def laggedDuhamelKernel (ν : ℝ) (F : ℝ → Pt 2 → ℂ) (i : Fin 2)
    (p : ℝ × Pt 2) (r : ℝ) : ℂ :=
  heatGradientKernel (Real.toNNReal (2 * ν * r)) (F (p.1 - r)) i p.2

lemma duhamelComponent_eq_lagged (ν : ℝ) (F : ℝ → Pt 2 → ℂ) (i : Fin 2)
    (t : ℝ) (x : Pt 2) : duhamelComponent ν F i t x =
      ∫ r in (0 : ℝ)..t, laggedDuhamelKernel ν F i (t, x) r := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun r => laggedDuhamelKernel ν F i (t, x) r) (a := 0) (b := t) t
  simpa [duhamelComponent, laggedDuhamelKernel] using h

lemma integral_rpow_neg_half (t : ℝ) :
    (∫ r in (0 : ℝ)..t, r ^ (-(1 / 2 : ℝ))) = 2 * Real.sqrt t := by
  rw [integral_rpow (Or.inl (by norm_num))]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  ring

lemma duhamelScale_nonneg {ν C : ℝ} (hC : 0 ≤ C) : 0 ≤ duhamelScale ν C :=
  div_nonneg (mul_nonneg hC (gmom_nonneg 1)) (Real.sqrt_nonneg _)

lemma continuousAt_laggedDuhamelKernel {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F)) {C : ℝ}
    (hC : ∀ s x, ‖F s x‖ ≤ C) (i : Fin 2) (p : ℝ × Pt 2) {r : ℝ} (hr : 0 < r) :
    ContinuousAt (laggedDuhamelKernel ν F i p) r := by
  have hv : 0 < (Real.toNNReal (2 * ν * r) : ℝ) := by
    rw [Real.coe_toNNReal _ (by positivity)]
    positivity
  exact (continuousAt_heatGradientKernel_with_param hF hC i
    (p := (p.1 - r, Real.toNNReal (2 * ν * r), p.2)) hv).comp
      (f := fun r : ℝ => (p.1 - r, Real.toNNReal (2 * ν * r), p.2))
      (by fun_prop : ContinuousAt
        (fun r : ℝ => (p.1 - r, Real.toNNReal (2 * ν * r), p.2)) r)

lemma continuous_laggedDuhamelKernel_param {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F)) {C : ℝ}
    (hC : ∀ s x, ‖F s x‖ ≤ C) (i : Fin 2) {r : ℝ} (hr : 0 < r) :
    Continuous fun p : ℝ × Pt 2 => laggedDuhamelKernel ν F i p r := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  have hv : 0 < (Real.toNNReal (2 * ν * r) : ℝ) := by
    rw [Real.coe_toNNReal _ (by positivity)]
    positivity
  exact (continuousAt_heatGradientKernel_with_param hF hC i
    (p := (p.1 - r, Real.toNNReal (2 * ν * r), p.2)) hv).comp
      (f := fun p : ℝ × Pt 2 => (p.1 - r, Real.toNNReal (2 * ν * r), p.2))
      (by fun_prop : ContinuousAt
        (fun p : ℝ × Pt 2 => (p.1 - r, Real.toNNReal (2 * ν * r), p.2)) p)

lemma norm_laggedDuhamelKernel_le {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F)) {C : ℝ}
    (hC : ∀ s x, ‖F s x‖ ≤ C) (i : Fin 2) (p : ℝ × Pt 2) {r : ℝ} (hr : 0 < r) :
    ‖laggedDuhamelKernel ν F i p r‖ ≤ duhamelScale ν C * r ^ (-(1 / 2 : ℝ)) := by
  have hFa : Continuous (F (p.1 - r)) := hF.comp (continuous_const.prodMk continuous_id)
  have h := norm_heatGradientKernel_le hFa (hC (p.1 - r))
      (Real.toNNReal (2 * ν * r)) i p.2
  rw [Real.coe_toNNReal _ (by positivity), Real.sqrt_mul (by positivity)] at h
  apply h.trans_eq
  rw [duhamelScale, Real.rpow_neg hr.le, ← Real.sqrt_eq_rpow, div_mul_eq_div_div, div_eq_mul_inv]

lemma aestronglyMeasurable_laggedDuhamelKernel {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F)) {C : ℝ}
    (hC : ∀ s x, ‖F s x‖ ≤ C) (i : Fin 2) (p : ℝ × Pt 2) (T : ℝ) :
    AEStronglyMeasurable (laggedDuhamelKernel ν F i p) (volume.restrict (Ioc 0 T)) := by
  have hc : ContinuousOn (laggedDuhamelKernel ν F i p) (Ioc 0 T) := fun r hr =>
    (continuousAt_laggedDuhamelKernel hν hF hC i p hr.1).continuousWithinAt
  exact hc.aestronglyMeasurable measurableSet_Ioc

/-- The singular time integrand is genuinely Bochner integrable on each finite time interval. -/
theorem intervalIntegrable_laggedDuhamelKernel {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F)) {C : ℝ}
    (hC : ∀ s x, ‖F s x‖ ≤ C) (i : Fin 2) (p : ℝ × Pt 2) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (laggedDuhamelKernel ν F i p) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  have hb := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T)
    (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul (duhamelScale ν C)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at hb
  refine hb.mono' (aestronglyMeasurable_laggedDuhamelKernel hν hF hC i p T) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
  exact norm_laggedDuhamelKernel_le hν hF hC i p hr.1

/-- Integrability of the original `s`-variable Duhamel integrand. -/
theorem intervalIntegrable_duhamelComponent {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F)) {C : ℝ}
    (hC : ∀ s x, ‖F s x‖ ≤ C) (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) (x : Pt 2) :
    IntervalIntegrable
      (fun s => heatGradientKernel (Real.toNNReal (2 * ν * (t - s))) (F s) i x) volume 0 t := by
  have h := (intervalIntegrable_laggedDuhamelKernel hν hF hC i (t, x) ht).comp_sub_left t
  simpa [laggedDuhamelKernel] using h.symm

/-- The sup norm of one Duhamel component grows at most as `√t`. -/
theorem norm_duhamelComponent_le {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F)) {C : ℝ}
    (hC : ∀ s x, ‖F s x‖ ≤ C) (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) (x : Pt 2) :
    ‖duhamelComponent ν F i t x‖ ≤ 2 * duhamelScale ν C * Real.sqrt t := by
  rw [duhamelComponent_eq_lagged]
  have hb := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
    (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul (duhamelScale ν C)
  calc
    ‖∫ r in (0 : ℝ)..t, laggedDuhamelKernel ν F i (t, x) r‖
        ≤ ∫ r in (0 : ℝ)..t, duhamelScale ν C * r ^ (-(1 / 2 : ℝ)) := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht
        (Eventually.of_forall fun r hr => norm_laggedDuhamelKernel_le hν hF hC i (t, x) hr.1) hb
    _ = 2 * duhamelScale ν C * Real.sqrt t := by
      rw [intervalIntegral.integral_const_mul, integral_rpow_neg_half]
      ring

@[simp] theorem duhamelComponent_zero (ν : ℝ) (F : ℝ → Pt 2 → ℂ) (i : Fin 2) (x : Pt 2) :
    duhamelComponent ν F i 0 x = 0 := by simp [duhamelComponent]

lemma heatGradientKernel_sub {f g : Pt 2 → ℂ} (hf : Continuous f) (hg : Continuous g)
    {Cf Cg : ℝ} (hCf : ∀ x, ‖f x‖ ≤ Cf) (hCg : ∀ x, ‖g x‖ ≤ Cg)
    (v : ℝ≥0) (i : Fin 2) (x : Pt 2) :
    heatGradientKernel v (fun y => f y - g y) i x =
      heatGradientKernel v f i x - heatGradientKernel v g i x := by
  unfold heatGradientKernel
  rw [← smul_sub, ← integral_sub (integrable_heatGradientKernel_integrand hf hCf v i x)
    (integrable_heatGradientKernel_integrand hg hCg v i x)]
  congr 2
  funext ζ
  rw [mul_sub]

/-- Uniform source differences give a `√t` Lipschitz estimate for the Duhamel integral. -/
theorem duhamelComponent_uniform_distance {ν : ℝ} (hν : 0 < ν)
    {F G : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hG : Continuous (Function.uncurry G)) {Cf Cg D : ℝ}
    (hCf : ∀ s x, ‖F s x‖ ≤ Cf) (hCg : ∀ s x, ‖G s x‖ ≤ Cg)
    (hD : ∀ s x, ‖F s x - G s x‖ ≤ D) (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) (x : Pt 2) :
    ‖duhamelComponent ν F i t x - duhamelComponent ν G i t x‖ ≤
      2 * duhamelScale ν D * Real.sqrt t := by
  have he : duhamelComponent ν F i t x - duhamelComponent ν G i t x =
      duhamelComponent ν (fun s y => F s y - G s y) i t x := by
    unfold duhamelComponent
    rw [← intervalIntegral.integral_sub
      (intervalIntegrable_duhamelComponent hν hF hCf i ht x)
      (intervalIntegrable_duhamelComponent hν hG hCg i ht x)]
    apply intervalIntegral.integral_congr
    intro s _
    exact (heatGradientKernel_sub
      (hF.comp (continuous_const.prodMk continuous_id))
      (hG.comp (continuous_const.prodMk continuous_id)) (hCf s) (hCg s) _ i x).symm
  rw [he]
  exact norm_duhamelComponent_le (F := fun s y => F s y - G s y) hν (hF.sub hG) hD i ht x

/-- A fixed-interval representation, with the moving upper time encoded by an indicator. -/
def truncatedDuhamelComponent (ν : ℝ) (F : ℝ → Pt 2 → ℂ) (i : Fin 2)
    (T : ℝ) (p : ℝ × Pt 2) : ℂ :=
  ∫ r in (0 : ℝ)..T, (Iic p.1).indicator (laggedDuhamelKernel ν F i p) r

lemma truncatedDuhamelComponent_eq {ν : ℝ} {F : ℝ → Pt 2 → ℂ} {i : Fin 2}
    {T : ℝ} {p : ℝ × Pt 2} (hp : p.1 ∈ Icc (0 : ℝ) T) :
    truncatedDuhamelComponent ν F i T p = duhamelComponent ν F i p.1 p.2 := by
  unfold truncatedDuhamelComponent
  change (∫ r in (0 : ℝ)..T, {r | r ≤ p.1}.indicator (laggedDuhamelKernel ν F i p) r) = _
  rw [intervalIntegral.integral_indicator hp]
  exact (duhamelComponent_eq_lagged ν F i p.1 p.2).symm

/-- Dominated convergence handles both the moving time boundary and the singular kernel. -/
theorem continuous_truncatedDuhamelComponent {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F)) {C : ℝ}
    (hC : ∀ s x, ‖F s x‖ ≤ C) (i : Fin 2) {T : ℝ} (hT : 0 ≤ T) :
    Continuous (truncatedDuhamelComponent ν F i T) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 0)
  have hscale : 0 ≤ duhamelScale ν C := duhamelScale_nonneg hC0
  have hb := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T)
    (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul (duhamelScale ν C)
  refine continuous_iff_continuousAt.2 fun p => ?_
  unfold truncatedDuhamelComponent
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun r => duhamelScale ν C * r ^ (-(1 / 2 : ℝ)))
    (Eventually.of_forall fun q => ?_) (Eventually.of_forall fun q => ?_) hb ?_
  · simpa only [uIoc_of_le hT] using
      (aestronglyMeasurable_laggedDuhamelKernel hν hF hC i q T).indicator measurableSet_Iic
  · exact Eventually.of_forall fun r hr => by
      rw [uIoc_of_le hT] at hr
      by_cases hm : r ∈ Iic q.1
      · rw [Set.indicator_of_mem hm]
        exact norm_laggedDuhamelKernel_le hν hF hC i q hr.1
      · rw [Set.indicator_of_notMem hm, norm_zero]
        exact mul_nonneg hscale (Real.rpow_nonneg hr.1.le _)
  · filter_upwards [volume.ae_ne p.1] with r hrne
    intro hr
    rw [uIoc_of_le hT] at hr
    rcases lt_or_gt_of_ne hrne with hlt | hgt
    · have he : (fun q : ℝ × Pt 2 => (Iic q.1).indicator (laggedDuhamelKernel ν F i q) r)
          =ᶠ[𝓝 p] (fun q => laggedDuhamelKernel ν F i q r) := by
        filter_upwards [continuous_fst.continuousAt.eventually (Ioi_mem_nhds hlt)] with q hq
        exact Set.indicator_of_mem (show r ∈ Iic q.1 from hq.le) _
      exact (continuous_laggedDuhamelKernel_param hν hF hC i hr.1).continuousAt.congr_of_eventuallyEq he
    · have he : (fun q : ℝ × Pt 2 => (Iic q.1).indicator (laggedDuhamelKernel ν F i q) r)
          =ᶠ[𝓝 p] (fun _ => (0 : ℂ)) := by
        filter_upwards [continuous_fst.continuousAt.eventually (Iio_mem_nhds hgt)] with q hq
        exact Set.indicator_of_notMem (show r ∉ Iic q.1 from not_le.2 hq) _
      exact continuousAt_const.congr_of_eventuallyEq he

/-- Joint continuity of the actual Duhamel integral on a finite closed time slab,
including time zero. -/
theorem continuousOn_duhamelComponent {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F)) {C : ℝ}
    (hC : ∀ s x, ‖F s x‖ ≤ C) (i : Fin 2) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun p : ℝ × Pt 2 => duhamelComponent ν F i p.1 p.2)
      {p | p.1 ∈ Icc (0 : ℝ) T} := by
  refine (continuous_truncatedDuhamelComponent hν hF hC i hT).continuousOn.congr ?_
  exact fun p hp => (truncatedDuhamelComponent_eq hp).symm

end AnomDiss

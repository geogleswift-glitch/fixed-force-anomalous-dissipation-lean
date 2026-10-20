module

public import RequestProject.ScalarSchauderSplit
public import RequestProject.ScalarHeatThirdSmoothing
public import RequestProject.ScalarDuhamelGradientHolderLoss
public import RequestProject.HeatDuhamelSpatial

/-!
# Spatial Schauder estimate without loss of exponent

Cancellation controls short heat times and a third derivative controls long
heat times. Splitting at the square of the spatial distance preserves the
source Hölder exponent in the actual Duhamel Hessian.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

theorem pd2_heatOp_lipschitz_of_pd3_bound {f : Pt 2 → ℂ}
    (hf : Continuous f) (hp : IsPeriodic f) {v : ℝ≥0} (hv : 0 < (v : ℝ))
    (i j : Fin 2) {B : ℝ}
    (hB : ∀ k z, ‖pd k (pd j (pd i (heatOp v f))) z‖ ≤ B) (x y : Pt 2) :
    ‖pd j (pd i (heatOp v f)) x - pd j (pd i (heatOp v f)) y‖ ≤
      (2 * B) * ‖x - y‖ := by
  have hc := contDiff_three_heatOp_continuous_periodic hf hp hv
  have hC1 : ContDiff ℝ 1 (pd j (pd i (heatOp v f))) :=
    contDiff_pd (contDiff_pd (n := 2) hc i) j
  have hfd : ∀ z, ‖fderiv ℝ (pd j (pd i (heatOp v f))) z‖ ≤ 2 * B := by
    intro z
    have h := norm_clm_pt2_le (fderiv ℝ (pd j (pd i (heatOp v f))) z)
    change ‖fderiv ℝ (pd j (pd i (heatOp v f))) z‖ ≤
      ‖pd 0 (pd j (pd i (heatOp v f))) z‖ +
      ‖pd 1 (pd j (pd i (heatOp v f))) z‖ at h
    exact (h.trans (add_le_add (hB 0 z) (hB 1 z))).trans_eq (by ring)
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hC1.differentiable one_ne_zero z) (fun z _ => hfd z)
    (mem_univ y) (mem_univ x)

def duhamelThirdDerivativeScale (ν H β : ℝ) : ℝ :=
  8 * H * gmom (β + 1) * (gmom 1) ^ 2 * (2 * ν / 3) ^ ((β - 3) / 2)

lemma duhamelThirdDerivativeScale_nonneg {ν H β : ℝ} (hν : 0 ≤ ν) (hH : 0 ≤ H) :
    0 ≤ duhamelThirdDerivativeScale ν H β := by
  have hg := gmom_nonneg (β + 1)
  unfold duhamelThirdDerivativeScale
  positivity

/-- The long-time estimate uses the third genuine spatial heat derivative. -/
theorem laggedDuhamelSpaceDerivative_lipschitz_distance {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i : Fin 2) (t : ℝ) (x y : Pt 2) {r : ℝ} (hr : 0 < r) :
    ‖laggedDuhamelSpaceDerivative ν F i t x r - laggedDuhamelSpaceDerivative ν F i t y r‖ ≤
      duhamelThirdDerivativeScale ν H β * ‖x - y‖ * r ^ ((β - 3) / 2) := by
  let v := Real.toNNReal (2 * ν * r)
  have hv : 0 < (v : ℝ) := by
    change 0 < (Real.toNNReal (2 * ν * r) : ℝ)
    rw [Real.coe_toNNReal _ (by positivity)]
    positivity
  have hfc : Continuous (F (t - r)) := hF.comp (continuous_const.prodMk continuous_id)
  have he : heatGradientKernel v (F (t - r)) i = pd i (heatOp v (F (t - r))) :=
    funext fun z => (pd_heatOp_continuous_periodic hfc (hFp (t - r)) hv i z).symm
  let B : ℝ := 2 * H * gmom (β + 1) * (gmom 1) ^ 2 *
    ((v : ℝ) / 3) ^ ((β - 3) / 2)
  have hthird : ∀ j k z, ‖pd k (pd j (pd i (heatOp v (F (t - r))))) z‖ ≤ B := by
    intro j k z
    exact norm_pd3_heatOp_holder_le hfc (hFp (t - r)) (hC (t - r)) hH hβ
      (hholder (t - r)) hv k j i z
  unfold laggedDuhamelSpaceDerivative laggedDuhamelKernel
  change ‖fderiv ℝ (heatGradientKernel v (F (t - r)) i) x -
    fderiv ℝ (heatGradientKernel v (F (t - r)) i) y‖ ≤ _
  rw [he]
  have h := norm_clm_pt2_le (fderiv ℝ (pd i (heatOp v (F (t - r)))) x -
    fderiv ℝ (pd i (heatOp v (F (t - r)))) y)
  change ‖fderiv ℝ (pd i (heatOp v (F (t - r)))) x -
    fderiv ℝ (pd i (heatOp v (F (t - r)))) y‖ ≤
      ‖pd 0 (pd i (heatOp v (F (t - r)))) x - pd 0 (pd i (heatOp v (F (t - r)))) y‖ +
      ‖pd 1 (pd i (heatOp v (F (t - r)))) x - pd 1 (pd i (heatOp v (F (t - r)))) y‖ at h
  have h0 := pd2_heatOp_lipschitz_of_pd3_bound hfc (hFp (t - r)) hv i 0 (hthird 0) x y
  have h1 := pd2_heatOp_lipschitz_of_pd3_bound hfc (hFp (t - r)) hv i 1 (hthird 1) x y
  apply (h.trans (add_le_add h0 h1)).trans_eq
  have hvar : (v : ℝ) / 3 = (2 * ν / 3) * r := by
    change (Real.toNNReal (2 * ν * r) : ℝ) / 3 = (2 * ν / 3) * r
    rw [Real.coe_toNNReal _ (by positivity)]
    ring
  dsimp [B]
  rw [hvar, Real.mul_rpow (by positivity : 0 ≤ 2 * ν / 3) hr.le]
  unfold duhamelThirdDerivativeScale
  ring

/-- The full Duhamel spatial derivative is Hölder with the original source
exponent, uniformly over the entire finite time slab. -/
theorem fderiv_duhamelComponent_spatial_schauder {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) (x y : Pt 2) :
    ‖fderiv ℝ (duhamelComponent ν F i t) x - fderiv ℝ (duhamelComponent ν F i t) y‖ ≤
      (4 * duhamelSpaceDerivativeScale ν H β / β +
        2 * duhamelThirdDerivativeScale ν H β / (1 - β)) * ‖x - y‖ ^ β := by
  have hA : 0 ≤ duhamelSpaceDerivativeScale ν H β := by
    have hg := gmom_nonneg (β + 1)
    have hg1 := gmom_nonneg 1
    unfold duhamelSpaceDerivativeScale
    positivity
  have hB := duhamelThirdDerivativeScale_nonneg hν.le hH (β := β)
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, Real.zero_rpow hβ0.ne', mul_zero, le_rfl]
  have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [(hasFDerivAt_duhamelComponent_holder hν hF hFp hC hH hβ0 hholder i ht x).fderiv,
    (hasFDerivAt_duhamelComponent_holder hν hF hFp hC hH hβ0 hholder i ht y).fderiv,
    ← intervalIntegral.integral_sub
      (intervalIntegrable_laggedDuhamelSpaceDerivative_holder hν hF hFp hC hH hβ0 hholder i t x ht)
      (intervalIntegrable_laggedDuhamelSpaceDerivative_holder hν hF hFp hC hH hβ0 hholder i t y ht)]
  apply (norm_integral_schauder_split (A := 2 * duhamelSpaceDerivativeScale ν H β)
    (B := duhamelThirdDerivativeScale ν H β) (by positivity) hB hβ0 hβ1 hd ht
    ((intervalIntegrable_laggedDuhamelSpaceDerivative_holder hν hF hFp hC hH hβ0 hholder i t x ht).sub
      (intervalIntegrable_laggedDuhamelSpaceDerivative_holder hν hF hFp hC hH hβ0 hholder i t y ht))
    (fun r hr => (norm_sub_le _ _).trans
      ((add_le_add
        (norm_laggedDuhamelSpaceDerivative_holder_le hν hF hFp hC hH hβ0 hholder i t x hr)
        (norm_laggedDuhamelSpaceDerivative_holder_le hν hF hFp hC hH hβ0 hholder i t y hr)).trans_eq
        (by ring)))
    (fun r hr => laggedDuhamelSpaceDerivative_lipschitz_distance hν hF hFp hC hH hβ0
      hholder i t x y hr)).trans_eq
  ring

/-- In particular the actual Hessian of ordinary-source heat Duhamel
integration has the source spatial Hölder exponent. -/
theorem pd2_heatDuhamel_spatial_schauder {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hFp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i j : Fin 2) {t : ℝ} (ht : 0 ≤ t) (x y : Pt 2) :
    ‖pd i (pd j (heatDuhamel ν F t)) x - pd i (pd j (heatDuhamel ν F t)) y‖ ≤
      (4 * duhamelSpaceDerivativeScale ν H β / β +
        2 * duhamelThirdDerivativeScale ν H β / (1 - β)) * ‖x - y‖ ^ β := by
  have he : pd j (heatDuhamel ν F t) = duhamelComponent ν F j t :=
    funext (pd_heatDuhamel_eq_duhamelComponent hν hF hFp hC ht j)
  rw [he]
  have hc := fderiv_duhamelComponent_spatial_schauder hν hF hFp hC hH hβ0 hβ1 hholder j ht x y
  calc
    ‖pd i (duhamelComponent ν F j t) x - pd i (duhamelComponent ν F j t) y‖ =
        ‖(fderiv ℝ (duhamelComponent ν F j t) x -
          fderiv ℝ (duhamelComponent ν F j t) y) (Pi.single i 1)‖ := by rfl
    _ ≤ ‖fderiv ℝ (duhamelComponent ν F j t) x -
        fderiv ℝ (duhamelComponent ν F j t) y‖ * ‖(Pi.single i 1 : Pt 2)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (duhamelComponent ν F j t) x -
        fderiv ℝ (duhamelComponent ν F j t) y‖ := by simp [Pi.norm_single]
    _ ≤ _ := hc

end AnomDiss

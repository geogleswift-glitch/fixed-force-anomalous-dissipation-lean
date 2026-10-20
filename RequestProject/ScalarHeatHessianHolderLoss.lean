module

public import RequestProject.ScalarHeatFractionalSmoothing
public import RequestProject.HeatSecondKernel

/-! # A spatial Hölder estimate for the true Hessian, with an explicit exponent loss -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

lemma gaussianFirstMomentAverage_holder_distance {f : Pt 2 → ℂ} (hf : Continuous f)
    {C H β : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β)
    (v : ℝ≥0) (i : Fin 2) (x y : Pt 2) :
    ‖gaussianFirstMomentAverage v f i x - gaussianFirstMomentAverage v f i y‖ ≤
      H * gmom 1 * ‖x - y‖ ^ β := by
  have hi : Integrable (fun ζ : Pt 2 => |ζ i|) (gauss2 1) :=
    integrable_gauss2_coord 1 i continuous_abs.aestronglyMeasurable integrable_abs_gaussianReal_std
  have hm : (∫ ζ : Pt 2, |ζ i| ∂(gauss2 1)) = gmom 1 := by
    rw [integral_gauss2_coord 1 i continuous_abs.aestronglyMeasurable]
    simp [gmom]
  unfold gaussianFirstMomentAverage
  rw [← integral_sub (integrable_heatGradientKernel_integrand hf hC v i x)
    (integrable_heatGradientKernel_integrand hf hC v i y)]
  calc
    ‖∫ ζ : Pt 2, ((ζ i : ℂ) * f (x + Real.sqrt v • ζ) -
        (ζ i : ℂ) * f (y + Real.sqrt v • ζ)) ∂(gauss2 1)‖
        ≤ ∫ ζ : Pt 2, (H * ‖x - y‖ ^ β) * |ζ i| ∂(gauss2 1) := by
      refine norm_integral_le_of_norm_le (hi.const_mul _) (Eventually.of_forall fun ζ => ?_)
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hh := hholder (x + Real.sqrt v • ζ) (y + Real.sqrt v • ζ)
      simp only [add_sub_add_right_eq_sub] at hh
      exact (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := by
      rw [integral_const_mul, hm]
      ring

lemma gaussianSecondMomentAverage_holder_distance {f : Pt 2 → ℂ} (hf : Continuous f)
    {C H β : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β)
    (v : ℝ≥0) (i j : Fin 2) (x y : Pt 2) :
    ‖gaussianSecondMomentAverage v f i j x - gaussianSecondMomentAverage v f i j y‖ ≤
      H * (gmom 1) ^ 2 * ‖x - y‖ ^ β := by
  have hg : Continuous (gaussianFirstMomentAverage v f j) :=
    (continuous_heatGradientMoment hf hC j).comp (continuous_const.prodMk continuous_id)
  have hgb : ∀ z, ‖gaussianFirstMomentAverage v f j z‖ ≤ C * gmom 1 :=
    norm_gaussianFirstMomentAverage_le hf hC v j
  have hgh : ∀ a b, ‖gaussianFirstMomentAverage v f j a - gaussianFirstMomentAverage v f j b‖ ≤
      (H * gmom 1) * ‖a - b‖ ^ β :=
    gaussianFirstMomentAverage_holder_distance hf hC hholder v j
  exact (gaussianFirstMomentAverage_holder_distance hg hgb hgh v i x y).trans_eq (by
    ring)

/-- The genuine Hessian inherits a Hölder input difference with a `1/v` cost. -/
theorem pd2_heatOp_holder_distance {f : Pt 2 → ℂ} (hf : Continuous f) (hp : IsPeriodic f)
    {C H β : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β)
    {v : ℝ≥0} (hv : 0 < (v : ℝ)) (i j : Fin 2) (x y : Pt 2) :
    ‖pd i (pd j (heatOp v f)) x - pd i (pd j (heatOp v f)) y‖ ≤
      H * (gmom 1) ^ 2 / ((v : ℝ) / 2) * ‖x - y‖ ^ β := by
  rw [pd2_heatOp_eq_secondMoment hf hp hv i j x, pd2_heatOp_eq_secondMoment hf hp hv i j y,
    ← smul_sub, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  apply (mul_le_mul_of_nonneg_left
    (gaussianSecondMomentAverage_holder_distance hf hC hholder (v / 2) i j x y)
    (sq_nonneg _)).trans_eq
  rw [inv_pow, Real.sq_sqrt (by positivity)]
  ring

def heatHessianHolderLossConstant (H β α : ℝ) : ℝ :=
  (4 * H * gmom (β + 1) * gmom 1) ^ (1 - α / β) *
    (H * (gmom 1) ^ 2) ^ (α / β)

lemma heatHessianHolderLossConstant_nonneg {H β α : ℝ} (hH : 0 ≤ H) :
    0 ≤ heatHessianHolderLossConstant H β α := by
  unfold heatHessianHolderLossConstant
  have hg₀ := gmom_nonneg (β + 1)
  have hg₁ := gmom_nonneg 1
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)

/-- Cancellation and the double-moment difference interpolate to an integrable
time singularity whenever the output exponent is strictly smaller than the input exponent. -/
theorem pd2_heatOp_holder_loss_distance {f : Pt 2 → ℂ} (hf : Continuous f) (hp : IsPeriodic f)
    {C H β α : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (hH : 0 ≤ H) (hβ : 0 < β)
    (hα₀ : 0 ≤ α) (hαβ : α < β)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β)
    {v : ℝ≥0} (hv : 0 < (v : ℝ)) (i j : Fin 2) (x y : Pt 2) :
    ‖pd i (pd j (heatOp v f)) x - pd i (pd j (heatOp v f)) y‖ ≤
      heatHessianHolderLossConstant H β α * ((v : ℝ) / 2) ^ ((β - α - 2) / 2) * ‖x - y‖ ^ α := by
  let w := (v : ℝ) / 2
  have hw : 0 < w := half_pos hv
  let η := α / β
  have hη₀ : 0 ≤ η := div_nonneg hα₀ hβ.le
  have hη₁ : η ≤ 1 := (div_le_one hβ).2 hαβ.le
  have hg₀ := gmom_nonneg (β + 1)
  have hg₁ := gmom_nonneg 1
  have hA : ‖pd i (pd j (heatOp v f)) x - pd i (pd j (heatOp v f)) y‖ ≤
      (4 * H * gmom (β + 1) * gmom 1) * w ^ ((β - 2) / 2) := by
    apply (norm_sub_le _ _).trans
    apply (add_le_add (norm_pd2_heatOp_holder_le hf hp hC hH hβ hholder hv i j x)
      (norm_pd2_heatOp_holder_le hf hp hC hH hβ hholder hv i j y)).trans_eq
    ring
  have hB := pd2_heatOp_holder_distance hf hp hC hholder hv i j x y
  have h := le_rpow_interpolation (norm_nonneg _) hA hB hη₀ hη₁
  have hηβ : β * η = α := by dsimp [η]; field_simp
  have hexp : (β - 2) / 2 * (1 - η) + -η = (β - α - 2) / 2 := by
    dsimp [η]
    field_simp
    ring
  apply h.trans_eq
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hw.le _),
    ← Real.rpow_mul hw.le,
    Real.mul_rpow (by positivity) (Real.rpow_nonneg (norm_nonneg _) _),
    Real.div_rpow (by positivity) hw.le _, ← Real.rpow_mul (norm_nonneg _)]
  calc
    ((4 * H * gmom (β + 1) * gmom 1) ^ (1 - η) * w ^ (((β - 2) / 2) * (1 - η))) *
        ((H * (gmom 1) ^ 2) ^ η / w ^ η * ‖x - y‖ ^ (β * η))
        = heatHessianHolderLossConstant H β α *
            (w ^ (((β - 2) / 2) * (1 - η)) * w ^ (-η)) * ‖x - y‖ ^ (β * η) := by
      rw [Real.rpow_neg hw.le]
      unfold heatHessianHolderLossConstant
      dsimp [η]
      ring
    _ = _ := by
      rw [← Real.rpow_add hw, hexp, hηβ]

end AnomDiss

module

public import RequestProject.ScalarHeatHolderSmoothing

/-! # Fractional spatial smoothing of the genuine heat derivative kernel -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

lemma le_rpow_interpolation {z A B α : ℝ} (hz : 0 ≤ z) (hzA : z ≤ A)
    (hzB : z ≤ B) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    z ≤ A ^ (1 - α) * B ^ α := by
  calc
    z = z ^ (1 - α) * z ^ α := by
      rw [← Real.rpow_add_of_nonneg hz (sub_nonneg.2 hα₁) hα₀]
      simp
    _ ≤ A ^ (1 - α) * B ^ α :=
      mul_le_mul (Real.rpow_le_rpow hz hzA (sub_nonneg.2 hα₁))
        (Real.rpow_le_rpow hz hzB hα₀) (Real.rpow_nonneg hz _)
        (Real.rpow_nonneg (hz.trans hzA) _)

def heatGradientFractionalConstant (C α : ℝ) : ℝ :=
  (2 * C * gmom 1) ^ (1 - α) * (4 * C * (gmom 1) ^ 2) ^ α

lemma heatGradientFractionalConstant_nonneg {C α : ℝ} (hC : 0 ≤ C) :
    0 ≤ heatGradientFractionalConstant C α := by
  have hg := gmom_nonneg 1
  unfold heatGradientFractionalConstant
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)

/-- The true first derivative kernel is globally Lipschitz in space at positive variance. -/
theorem heatGradientKernel_lipschitz_distance {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {v : ℝ≥0}
    (hv : 0 < (v : ℝ)) (j : Fin 2) (x y : Pt 2) :
    ‖heatGradientKernel v f j x - heatGradientKernel v f j y‖ ≤
      (4 * C * (gmom 1) ^ 2 / (v : ℝ)) * ‖x - y‖ := by
  have hc := contDiff_one_heatGradientKernel_continuous_periodic hf hp hv j
  have hfd : ∀ z, ‖fderiv ℝ (heatGradientKernel v f j) z‖ ≤
      4 * C * (gmom 1) ^ 2 / (v : ℝ) := by
    intro z
    have h := norm_clm_pt2_le (fderiv ℝ (heatGradientKernel v f j) z)
    change ‖fderiv ℝ (heatGradientKernel v f j) z‖ ≤
      ‖pd 0 (heatGradientKernel v f j) z‖ + ‖pd 1 (heatGradientKernel v f j) z‖ at h
    have h₀ := norm_pd_heatGradientKernel_continuous_periodic_le hf hp hC hv 0 j z
    have h₁ := norm_pd_heatGradientKernel_continuous_periodic_le hf hp hC hv 1 j z
    exact (h.trans (add_le_add h₀ h₁)).trans_eq (by ring_nf)
  exact (convex_univ : Convex ℝ (univ : Set (Pt 2))).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hc.differentiable one_ne_zero) z) (fun z _ => hfd z) (mem_univ y) (mem_univ x)

/-- Interpolating the sup bound and the actual spatial Lipschitz bound gives
an integrable heat-time singularity for every fractional exponent below one. -/
theorem heatGradientKernel_fractional_distance {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {C α : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) {v : ℝ≥0} (hv : 0 < (v : ℝ))
    (j : Fin 2) (x y : Pt 2) :
    ‖heatGradientKernel v f j x - heatGradientKernel v f j y‖ ≤
      heatGradientFractionalConstant C α * (v : ℝ) ^ (-(1 + α) / 2) * ‖x - y‖ ^ α := by
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hg : 0 ≤ gmom 1 := gmom_nonneg 1
  have hA : ‖heatGradientKernel v f j x - heatGradientKernel v f j y‖ ≤
      2 * C * gmom 1 / Real.sqrt (v : ℝ) := by
    calc
      ‖heatGradientKernel v f j x - heatGradientKernel v f j y‖
          ≤ ‖heatGradientKernel v f j x‖ + ‖heatGradientKernel v f j y‖ := norm_sub_le _ _
      _ ≤ C * gmom 1 / Real.sqrt (v : ℝ) + C * gmom 1 / Real.sqrt (v : ℝ) :=
        add_le_add (norm_heatGradientKernel_le hf hC v j x) (norm_heatGradientKernel_le hf hC v j y)
      _ = _ := by ring_nf
  have hL := heatGradientKernel_lipschitz_distance hf hp hC hv j x y
  have h := le_rpow_interpolation (norm_nonneg _) hA hL hα₀ hα₁
  have hden : (Real.sqrt (v : ℝ)) ^ (1 - α) * (v : ℝ) ^ α =
      (v : ℝ) ^ ((1 + α) / 2) := by
    rw [← Real.rpow_div_two_eq_sqrt (1 - α) hv.le, ← Real.rpow_add hv]
    congr 1
    ring_nf
  apply h.trans_eq
  rw [Real.mul_rpow (by positivity) (norm_nonneg _),
    Real.div_rpow (by positivity) (Real.sqrt_nonneg _) _, Real.div_rpow (by positivity) hv.le _]
  calc
    ((2 * C * gmom 1) ^ (1 - α) / (Real.sqrt (v : ℝ)) ^ (1 - α)) *
        ((4 * C * (gmom 1) ^ 2) ^ α / (v : ℝ) ^ α * ‖x - y‖ ^ α)
        = heatGradientFractionalConstant C α /
            ((Real.sqrt (v : ℝ)) ^ (1 - α) * (v : ℝ) ^ α) * ‖x - y‖ ^ α := by
      unfold heatGradientFractionalConstant
      ring_nf
    _ = _ := by
      rw [hden, div_eq_mul_inv, ← Real.rpow_neg hv.le]
      congr 2
      ring_nf

end AnomDiss

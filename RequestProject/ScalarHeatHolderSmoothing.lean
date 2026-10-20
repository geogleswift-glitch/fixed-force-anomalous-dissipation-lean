module

public import RequestProject.ScalarHeatHigherSmoothing

/-! # Cancellation estimates for heat derivatives of Hölder data -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-- The first Gaussian derivative moment cancels constant input. -/
lemma heatGradientKernel_eq_cancelled {f : Pt 2 → ℂ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (v : ℝ≥0) (i : Fin 2) (x : Pt 2) :
    heatGradientKernel v f i x = (Real.sqrt v)⁻¹ •
      ∫ ζ : Pt 2, (ζ i : ℂ) * (f (x + Real.sqrt v • ζ) - f x) ∂(gauss2 1) := by
  have hi := integrable_heatGradientKernel_integrand hf hC v i x
  have hi₀ : Integrable (fun ζ : Pt 2 => (ζ i : ℂ) * f x) (gauss2 1) := by
    exact ((integrable_gauss2_coord_id 1 i).ofReal).mul_const (f x)
  have hz : (∫ ζ : Pt 2, (ζ i : ℂ) * f x ∂(gauss2 1)) = 0 := by
    simp only [← Complex.real_smul]
    rw [integral_smul_const, integral_gauss2_coord_id, zero_smul]
  unfold heatGradientKernel
  simp_rw [mul_sub]
  rw [integral_sub hi hi₀, hz, sub_zero]

/-- The cancelled first derivative gains the Hölder power of the heat length scale. -/
theorem norm_heatGradientKernel_holder_le {f : Pt 2 → ℂ} (hf : Continuous f)
    {C H β : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β)
    {v : ℝ≥0} (hv : 0 < (v : ℝ)) (i : Fin 2) (x : Pt 2) :
    ‖heatGradientKernel v f i x‖ ≤
      2 * H * gmom (β + 1) * (v : ℝ) ^ ((β - 1) / 2) := by
  have hσ : 0 ≤ Real.sqrt (v : ℝ) := Real.sqrt_nonneg _
  have hpower : ∀ ζ : Pt 2, ‖ζ‖ * ‖ζ‖ ^ β = ‖ζ‖ ^ (β + 1) := by
    intro ζ
    rw [Real.rpow_add_of_nonneg (norm_nonneg _) hβ.le zero_le_one, Real.rpow_one, mul_comm]
  have hbound : ∀ ζ : Pt 2,
      ‖(ζ i : ℂ) * (f (x + Real.sqrt v • ζ) - f x)‖ ≤
        H * (Real.sqrt (v : ℝ)) ^ β * ‖ζ‖ ^ (β + 1) := by
    intro ζ
    rw [norm_mul, Complex.norm_real]
    have hh := hholder (x + Real.sqrt v • ζ) x
    rw [show x + Real.sqrt v • ζ - x = Real.sqrt v • ζ by abel,
      norm_smul, Real.norm_of_nonneg hσ, Real.mul_rpow hσ (norm_nonneg _)] at hh
    calc
      ‖ζ i‖ * ‖f (x + Real.sqrt v • ζ) - f x‖
          ≤ ‖ζ‖ * (H * ((Real.sqrt (v : ℝ)) ^ β * ‖ζ‖ ^ β)) :=
        mul_le_mul (norm_le_pi_norm ζ i) hh (norm_nonneg _) (norm_nonneg _)
      _ = H * (Real.sqrt (v : ℝ)) ^ β * (‖ζ‖ * ‖ζ‖ ^ β) := by ring
      _ = _ := by rw [hpower]
  have him := (integrable_gauss2_norm_rpow 1 (show 0 < β + 1 by linarith)).const_mul
    (H * (Real.sqrt (v : ℝ)) ^ β)
  have hb : ‖∫ ζ : Pt 2, (ζ i : ℂ) * (f (x + Real.sqrt v • ζ) - f x) ∂(gauss2 1)‖ ≤
      H * (Real.sqrt (v : ℝ)) ^ β * (2 * gmom (β + 1)) := by
    calc
      ‖∫ ζ : Pt 2, (ζ i : ℂ) * (f (x + Real.sqrt v • ζ) - f x) ∂(gauss2 1)‖
          ≤ ∫ ζ : Pt 2, H * (Real.sqrt (v : ℝ)) ^ β * ‖ζ‖ ^ (β + 1) ∂(gauss2 1) :=
        norm_integral_le_of_norm_le him (Eventually.of_forall hbound)
      _ = H * (Real.sqrt (v : ℝ)) ^ β * ∫ ζ : Pt 2, ‖ζ‖ ^ (β + 1) ∂(gauss2 1) :=
        integral_const_mul _ _
      _ ≤ H * (Real.sqrt (v : ℝ)) ^ β * (2 * gmom (β + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hH (Real.rpow_nonneg hσ _))
        simpa using integral_gauss2_norm_rpow_le 1 (show 0 < β + 1 by linarith)
  have hp : (Real.sqrt (v : ℝ)) ^ β / Real.sqrt (v : ℝ) = (v : ℝ) ^ ((β - 1) / 2) := by
    rw [← Real.rpow_div_two_eq_sqrt β hv.le, Real.sqrt_eq_rpow, ← Real.rpow_sub hv]
    congr 1
    ring
  rw [heatGradientKernel_eq_cancelled hf hC, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 hσ)]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hσ)).trans_eq
  calc
    (Real.sqrt (v : ℝ))⁻¹ * (H * (Real.sqrt (v : ℝ)) ^ β * (2 * gmom (β + 1)))
        = 2 * H * gmom (β + 1) * ((Real.sqrt (v : ℝ)) ^ β / Real.sqrt (v : ℝ)) := by ring
    _ = _ := by rw [hp]

theorem norm_pd_heatOp_holder_le {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {C H β : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β)
    {v : ℝ≥0} (hv : 0 < (v : ℝ)) (i : Fin 2) (x : Pt 2) :
    ‖pd i (heatOp v f) x‖ ≤ 2 * H * gmom (β + 1) * (v : ℝ) ^ ((β - 1) / 2) := by
  rw [pd_heatOp_continuous_periodic hf hp hv]
  exact norm_heatGradientKernel_holder_le hf hC hH hβ hholder hv i x

/-- Heat averaging preserves the spatial Hölder seminorm. -/
theorem heatOp_holder_distance {f : Pt 2 → ℂ} (hf : Continuous f)
    {C H β : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β)
    (v : ℝ≥0) (x y : Pt 2) :
    ‖heatOp v f x - heatOp v f y‖ ≤ H * ‖x - y‖ ^ β := by
  unfold heatOp
  rw [← integral_sub (integrable_gauss2_of_bdd hf hC v x)
    (integrable_gauss2_of_bdd hf hC v y)]
  simpa using norm_integral_le_of_norm_le_const (μ := gauss2 v)
    (f := fun ζ => f (x + ζ) - f (y + ζ))
    (C := H * ‖x - y‖ ^ β) (Eventually.of_forall fun ζ => by
      simpa only [add_sub_add_right_eq_sub] using hholder (x + ζ) (y + ζ))

/-- Second heat derivatives of Hölder input have the integrable parabolic singularity
`v^(β/2-1)`. The half-variance form becomes `(ν r)^(β/2-1)` at variance `2νr`. -/
theorem norm_pd2_heatOp_holder_le {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {C H β : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β)
    {v : ℝ≥0} (hv : 0 < (v : ℝ)) (i j : Fin 2) (x : Pt 2) :
    ‖pd i (pd j (heatOp v f)) x‖ ≤
      2 * H * gmom (β + 1) * gmom 1 * ((v : ℝ) / 2) ^ ((β - 2) / 2) := by
  let w : ℝ≥0 := v / 2
  have hw : 0 < (w : ℝ) := by dsimp [w]; simpa using half_pos hv
  have hs : w + w = v := by dsimp [w]; ring
  have he : heatOp v f = heatOp w (heatOp w f) := by
    rw [← hs]
    funext y
    exact heatOp_semigroup_periodic hf hp w w y
  rw [he]
  have hgrad : ∀ y, ‖pd j (heatOp w f) y‖ ≤
      2 * H * gmom (β + 1) * (w : ℝ) ^ ((β - 1) / 2) :=
    fun y => norm_pd_heatOp_holder_le hf hp hC hH hβ hholder hw j y
  have h := norm_pd2_heatOp_of_C1_le (contDiff_one_heatOp_continuous_periodic hf hp hw)
    (isQP_zero_iff.1 (heatOp_isQP (isQP_zero_iff.2 hp) w)) hgrad hw i x
  have hpower : (w : ℝ) ^ ((β - 1) / 2) / Real.sqrt (w : ℝ) =
      (w : ℝ) ^ ((β - 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hw]
    congr 1
    ring
  apply h.trans_eq
  calc
    (2 * H * gmom (β + 1) * (w : ℝ) ^ ((β - 1) / 2)) * gmom 1 / Real.sqrt (w : ℝ)
        = 2 * H * gmom (β + 1) * gmom 1 *
            ((w : ℝ) ^ ((β - 1) / 2) / Real.sqrt (w : ℝ)) := by ring
    _ = _ := by rw [hpower]; rfl

end AnomDiss

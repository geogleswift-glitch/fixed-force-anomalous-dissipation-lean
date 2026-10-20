module

public import RequestProject.ScalarHeatHolderSmoothing

/-!
# First-order Hölder cancellation for the genuine heat operator

The first-order Taylor remainder and the centered Gaussian first moment
give the heat increment rate `v^((1+β)/2)` for `C^{1+β}` input.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

theorem taylor1_holder {f : Pt 2 → ℂ} (hf : ContDiff ℝ 1 f)
    {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β)
    (hholder : ∀ i x y, ‖pd i f x - pd i f y‖ ≤ H * ‖x - y‖ ^ β)
    (z δ : Pt 2) :
    ‖f (z + δ) - f z - ∑ i, δ i • pd i f z‖ ≤
      2 * H * ‖δ‖ ^ (1 + β) := by
  let p : ℝ → ℂ := fun u =>
    f (z + u • δ) - f z - u • ∑ i, δ i • pd i f z
  have hd : ∀ u, HasDerivAt p
      (∑ i, δ i • (pd i f (z + u • δ) - pd i f z)) u := by
    intro u
    have he := ((hasDerivAt_dirLine (hf.differentiable one_ne_zero) z δ u).sub_const
      (f z)).fun_sub ((hasDerivAt_id u).smul_const (∑ i, δ i • pd i f z))
    simpa [p, smul_sub, Finset.sum_sub_distrib] using he
  have hb : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖∑ i, δ i • (pd i f (z + u • δ) - pd i f z)‖ ≤
        2 * H * ‖δ‖ ^ (1 + β) := by
    intro u hu
    have hdist : ‖z + u • δ - z‖ ≤ ‖δ‖ := by
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hu.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hu.2
    have hterm : ∀ i : Fin 2,
        ‖δ i • (pd i f (z + u • δ) - pd i f z)‖ ≤ H * ‖δ‖ ^ (1 + β) := by
      intro i
      rw [norm_smul]
      have hh := (hholder i (z + u • δ) z).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) hdist hβ) hH)
      calc
        ‖δ i‖ * ‖pd i f (z + u • δ) - pd i f z‖ ≤
            ‖δ‖ * (H * ‖δ‖ ^ β) :=
          mul_le_mul (norm_le_pi_norm δ i) hh (norm_nonneg _) (norm_nonneg _)
        _ = H * ‖δ‖ ^ (1 + β) := by
          rw [Real.rpow_add_of_nonneg (norm_nonneg _) zero_le_one hβ,
            Real.rpow_one]
          ring
    calc
      _ ≤ ∑ i : Fin 2, H * ‖δ‖ ^ (1 + β) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
      _ = _ := by simp; ring
  have he := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) hb
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  simpa [p] using he

theorem heatOp_C1_holder_initial_error {f : Pt 2 → ℂ} (hf : ContDiff ℝ 1 f)
    {C H β : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (hH : 0 ≤ H) (hβ : 0 ≤ β)
    (hholder : ∀ i x y, ‖pd i f x - pd i f y‖ ≤ H * ‖x - y‖ ^ β)
    (v : ℝ≥0) (x : Pt 2) :
    ‖heatOp v f x - f x‖ ≤
      4 * H * gmom (1 + β) * (v : ℝ) ^ ((1 + β) / 2) := by
  let L : Pt 2 → ℂ := fun ζ => ∑ i, ζ i • pd i f x
  have hLi : Integrable L (gauss2 v) :=
    integrable_finset_sum _ fun i _ => (integrable_gauss2_coord_id v i).smul_const _
  have hLzero : (∫ ζ, L ζ ∂(gauss2 v)) = 0 := by
    change (∫ ζ, ∑ i, ζ i • pd i f x ∂(gauss2 v)) = 0
    rw [integral_finset_sum _ fun i _ =>
      (integrable_gauss2_coord_id v i).smul_const _]
    apply Finset.sum_eq_zero
    intro i _
    rw [integral_smul_const, integral_gauss2_coord_id, zero_smul]
  have hi := integrable_gauss2_of_bdd hf.continuous hC v x
  have he : heatOp v f x - f x =
      ∫ ζ, f (x + ζ) - f x - L ζ ∂(gauss2 v) := by
    calc
      heatOp v f x - f x =
          (∫ ζ, f (x + ζ) - f x ∂(gauss2 v)) - ∫ ζ, L ζ ∂(gauss2 v) := by
        rw [integral_sub hi (integrable_const (f x)), hLzero]
        simp [heatOp]
      _ = _ := (integral_sub (hi.sub (integrable_const (f x))) hLi).symm
  rw [he]
  calc
    ‖∫ ζ, f (x + ζ) - f x - L ζ ∂(gauss2 v)‖ ≤
        ∫ ζ, 2 * H * ‖ζ‖ ^ (1 + β) ∂(gauss2 v) := by
      apply norm_integral_le_of_norm_le
        ((integrable_gauss2_norm_rpow v (show 0 < 1 + β by linarith)).const_mul (2 * H))
      exact Eventually.of_forall fun ζ => taylor1_holder hf hH hβ hholder x ζ
    _ = 2 * H * ∫ ζ, ‖ζ‖ ^ (1 + β) ∂(gauss2 v) := integral_const_mul _ _
    _ ≤ 2 * H * (2 * gmom (1 + β) * (v : ℝ) ^ ((1 + β) / 2)) :=
      mul_le_mul_of_nonneg_left
        (integral_gauss2_norm_rpow_le v (show 0 < 1 + β by linarith)) (by positivity)
    _ = _ := by ring

end AnomDiss

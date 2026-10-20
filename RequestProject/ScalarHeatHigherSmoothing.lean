module

public import RequestProject.HeatSemigroup

/-!
# Genuine second-order heat smoothing

The semigroup identity splits a positive heat step into two positive steps. Each
step supplies one spatial derivative, so only the bound of the original input
occurs in the second-derivative estimate. No PDE regularity is assumed.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-- On `ℝ²`, continuous differentiability of both coordinate derivatives gives `C²`. -/
lemma contDiff_two_of_contDiff_partials {f : Pt 2 → ℂ} (hf : Differentiable ℝ f)
    (hpd : ∀ i : Fin 2, ContDiff ℝ 1 (pd i f)) : ContDiff ℝ 2 f := by
  have he : fderiv ℝ f = fun x =>
      ∑ i : Fin 2, (ContinuousLinearMap.proj i).smulRight (pd i f x) := by
    funext x
    apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply]
    exact fderiv_apply_eq_sum_pd x z
  refine (contDiff_succ_iff_fderiv (n := 1)).2 ⟨hf, by simp, ?_⟩
  rw [he]
  exact ContDiff.sum fun i _ =>
    (ContinuousLinearMap.smulRightL ℝ (Pt 2) ℂ (ContinuousLinearMap.proj i)).contDiff.comp (hpd i)

/-- One positive heat step adds a derivative to `C¹` periodic data. -/
theorem contDiff_two_heatOp_of_C1 {f : Pt 2 → ℂ} (hf : ContDiff ℝ 1 f)
    (hp : IsPeriodic f) {v : ℝ≥0} (hv : 0 < (v : ℝ)) : ContDiff ℝ 2 (heatOp v f) := by
  apply contDiff_two_of_contDiff_partials
  · exact (contDiff_one_heatOp_continuous_periodic hf.continuous hp hv).differentiable one_ne_zero
  · intro i
    rw [pd_heatOp_fun (isQP_zero_iff.2 hp) hf v i]
    exact contDiff_one_heatOp_continuous_periodic (continuous_pd_of_C1 f hf i)
      (isPeriodic_pd f hp i) hv

theorem norm_pd2_heatOp_of_C1_le {f : Pt 2 → ℂ} (hf : ContDiff ℝ 1 f)
    (hp : IsPeriodic f) {C : ℝ} {j : Fin 2} (hC : ∀ x, ‖pd j f x‖ ≤ C) {v : ℝ≥0}
    (hv : 0 < (v : ℝ)) (i : Fin 2) (x : Pt 2) :
    ‖pd i (pd j (heatOp v f)) x‖ ≤ C * gmom 1 / Real.sqrt (v : ℝ) := by
  rw [pd_heatOp_fun (isQP_zero_iff.2 hp) hf v j]
  exact norm_pd_heatOp_continuous_periodic_le (continuous_pd_of_C1 f hf j)
    (isPeriodic_pd f hp j) hC hv i x

/-- Positive heat variance gives two genuine spatial derivatives for continuous periodic data. -/
theorem contDiff_two_heatOp_continuous_periodic {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {v : ℝ≥0} (hv : 0 < (v : ℝ)) : ContDiff ℝ 2 (heatOp v f) := by
  let w : ℝ≥0 := v / 2
  have hw : 0 < (w : ℝ) := by dsimp [w]; simpa using half_pos hv
  have hs : w + w = v := by dsimp [w]; ring
  have he : heatOp v f = heatOp w (heatOp w f) := by
    rw [← hs]
    funext x
    exact heatOp_semigroup_periodic hf hp w w x
  rw [he]
  exact contDiff_two_heatOp_of_C1 (contDiff_one_heatOp_continuous_periodic hf hp hw)
    (isQP_zero_iff.1 (heatOp_isQP (isQP_zero_iff.2 hp) w)) hw

/-- A concrete second-derivative bound proportional to the inverse heat variance. -/
theorem norm_pd2_heatOp_continuous_periodic_le {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {v : ℝ≥0}
    (hv : 0 < (v : ℝ)) (i j : Fin 2) (x : Pt 2) :
    ‖pd i (pd j (heatOp v f)) x‖ ≤ 2 * C * (gmom 1) ^ 2 / (v : ℝ) := by
  let w : ℝ≥0 := v / 2
  have hw : 0 < (w : ℝ) := by dsimp [w]; simpa using half_pos hv
  have hs : w + w = v := by dsimp [w]; ring
  have he : heatOp v f = heatOp w (heatOp w f) := by
    rw [← hs]
    funext y
    exact heatOp_semigroup_periodic hf hp w w y
  rw [he]
  have hgrad : ∀ y, ‖pd j (heatOp w f) y‖ ≤ C * gmom 1 / Real.sqrt (w : ℝ) :=
    fun y => norm_pd_heatOp_continuous_periodic_le hf hp hC hw j y
  have h := norm_pd2_heatOp_of_C1_le (contDiff_one_heatOp_continuous_periodic hf hp hw)
    (isQP_zero_iff.1 (heatOp_isQP (isQP_zero_iff.2 hp) w)) hgrad hw i x
  apply h.trans_eq
  rw [div_mul_eq_mul_div, div_div, ← pow_two, Real.sq_sqrt hw.le]
  dsimp [w]
  ring

/-- The first derivative kernel is now genuinely `C¹` in space for continuous periodic input. -/
theorem contDiff_one_heatGradientKernel_continuous_periodic {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {v : ℝ≥0} (hv : 0 < (v : ℝ)) (j : Fin 2) :
    ContDiff ℝ 1 (heatGradientKernel v f j) := by
  have he : heatGradientKernel v f j = pd j (heatOp v f) :=
    funext fun x => (pd_heatOp_continuous_periodic hf hp hv j x).symm
  rw [he]
  exact contDiff_pd_of_C2 _ (contDiff_two_heatOp_continuous_periodic hf hp hv) j

theorem norm_pd_heatGradientKernel_continuous_periodic_le {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {v : ℝ≥0}
    (hv : 0 < (v : ℝ)) (i j : Fin 2) (x : Pt 2) :
    ‖pd i (heatGradientKernel v f j) x‖ ≤ 2 * C * (gmom 1) ^ 2 / (v : ℝ) := by
  have he : heatGradientKernel v f j = pd j (heatOp v f) :=
    funext fun y => (pd_heatOp_continuous_periodic hf hp hv j y).symm
  rw [he]
  exact norm_pd2_heatOp_continuous_periodic_le hf hp hC hv i j x

end AnomDiss

module

public import RequestProject.ScalarHeatHolderSmoothing

/-!
# Genuine third heat derivatives and Hölder cancellation

A split into variances `v/3` and `2v/3` supplies the third derivative bound from
the already proved second-derivative cancellation. These are actual derivatives,
not formal kernel symbols or additional regularity hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

lemma contDiff_three_of_contDiff_partials {f : Pt 2 → ℂ} (hf : Differentiable ℝ f)
    (hpd : ∀ i : Fin 2, ContDiff ℝ 2 (pd i f)) : ContDiff ℝ 3 f := by
  have he : fderiv ℝ f = fun x =>
      ∑ i : Fin 2, (ContinuousLinearMap.proj i).smulRight (pd i f x) := by
    funext x
    apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply]
    exact fderiv_apply_eq_sum_pd x z
  refine (contDiff_succ_iff_fderiv (n := 2)).2 ⟨hf, by simp, ?_⟩
  rw [he]
  exact ContDiff.sum fun i _ =>
    (ContinuousLinearMap.smulRightL ℝ (Pt 2) ℂ (ContinuousLinearMap.proj i)).contDiff.comp (hpd i)

theorem contDiff_three_heatOp_of_C2 {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : IsPeriodic f) {v : ℝ≥0} (hv : 0 < (v : ℝ)) : ContDiff ℝ 3 (heatOp v f) := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  apply contDiff_three_of_contDiff_partials
  · exact (contDiff_one_heatOp_continuous_periodic hf.continuous hp hv).differentiable one_ne_zero
  · intro i
    rw [pd_heatOp_fun (isQP_zero_iff.2 hp) hf₁ v i]
    exact contDiff_two_heatOp_of_C1 (contDiff_pd_of_C2 f hf i) (isPeriodic_pd f hp i) hv

theorem contDiff_three_heatOp_continuous_periodic {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {v : ℝ≥0} (hv : 0 < (v : ℝ)) : ContDiff ℝ 3 (heatOp v f) := by
  let w : ℝ≥0 := v / 2
  have hw : 0 < (w : ℝ) := by dsimp [w]; simpa using half_pos hv
  have hs : w + w = v := by dsimp [w]; ring
  have he : heatOp v f = heatOp w (heatOp w f) := by
    rw [← hs]
    funext x
    exact heatOp_semigroup_periodic hf hp w w x
  rw [he]
  exact contDiff_three_heatOp_of_C2 (contDiff_two_heatOp_continuous_periodic hf hp hw)
    (isQP_zero_iff.1 (heatOp_isQP (isQP_zero_iff.2 hp) w)) hw

theorem norm_pd3_heatOp_of_C2_le {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : IsPeriodic f) {C : ℝ} {j k : Fin 2} (hC : ∀ x, ‖pd j (pd k f) x‖ ≤ C)
    {v : ℝ≥0} (hv : 0 < (v : ℝ)) (i : Fin 2) (x : Pt 2) :
    ‖pd i (pd j (pd k (heatOp v f))) x‖ ≤ C * gmom 1 / Real.sqrt (v : ℝ) := by
  have he : pd j (pd k (heatOp v f)) = heatOp v (pd j (pd k f)) :=
    funext fun y => pd2_heatOp (isQP_zero_iff.2 hp) hf v j k y
  rw [he]
  exact norm_pd_heatOp_continuous_periodic_le
    (continuous_pd_of_C1 _ (contDiff_pd_of_C2 f hf k) j)
    (isPeriodic_pd _ (isPeriodic_pd f hp k) j) hC hv i x

/-- A bound on the third actual derivative using only the sup norm of the input. -/
theorem norm_pd3_heatOp_continuous_periodic_le {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {v : ℝ≥0}
    (hv : 0 < (v : ℝ)) (i j k : Fin 2) (x : Pt 2) :
    ‖pd i (pd j (pd k (heatOp v f))) x‖ ≤
      C * (gmom 1) ^ 3 / (((v : ℝ) / 3) ^ (3 / 2 : ℝ)) := by
  let w : ℝ≥0 := v / 3
  have hw : 0 < (w : ℝ) := by dsimp [w]; simpa using div_pos hv (by norm_num : (0 : ℝ) < 3)
  have h₂w : 0 < ((2 * w : ℝ≥0) : ℝ) := by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hw
  have hs : w + 2 * w = v := by dsimp [w]; ring
  have he : heatOp v f = heatOp w (heatOp (2 * w) f) := by
    rw [← hs]
    funext y
    exact heatOp_semigroup_periodic hf hp w (2 * w) y
  rw [he]
  have hgrad : ∀ y, ‖pd j (pd k (heatOp (2 * w) f)) y‖ ≤
      2 * C * (gmom 1) ^ 2 / ((2 * w : ℝ≥0) : ℝ) :=
    fun y => norm_pd2_heatOp_continuous_periodic_le hf hp hC h₂w j k y
  have h := norm_pd3_heatOp_of_C2_le (contDiff_two_heatOp_continuous_periodic hf hp h₂w)
    (isQP_zero_iff.1 (heatOp_isQP (isQP_zero_iff.2 hp) (2 * w))) hgrad hw i x
  have hpow : (w : ℝ) * Real.sqrt (w : ℝ) = (w : ℝ) ^ (3 / 2 : ℝ) := by
    calc
      (w : ℝ) * Real.sqrt (w : ℝ) = (w : ℝ) ^ (1 : ℝ) * (w : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = (w : ℝ) ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hw 1 (1 / 2)).symm
      _ = _ := by congr 1; norm_num
  apply h.trans_eq
  calc
    (2 * C * (gmom 1) ^ 2 / ((2 * w : ℝ≥0) : ℝ)) * gmom 1 / Real.sqrt (w : ℝ)
        = C * (gmom 1) ^ 3 / ((w : ℝ) * Real.sqrt (w : ℝ)) := by
      simp only [NNReal.coe_mul, NNReal.coe_ofNat]
      ring
    _ = _ := by rw [hpow]; rfl

/-- Hölder cancellation for the third actual heat derivative. At physical variance
`2νr`, the exponent is precisely `r^((β-3)/2)`, needed for the spatial Schauder split. -/
theorem norm_pd3_heatOp_holder_le {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {C H β : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β)
    {v : ℝ≥0} (hv : 0 < (v : ℝ)) (i j k : Fin 2) (x : Pt 2) :
    ‖pd i (pd j (pd k (heatOp v f))) x‖ ≤
      2 * H * gmom (β + 1) * (gmom 1) ^ 2 * ((v : ℝ) / 3) ^ ((β - 3) / 2) := by
  let w : ℝ≥0 := v / 3
  have hw : 0 < (w : ℝ) := by dsimp [w]; simpa using div_pos hv (by norm_num : (0 : ℝ) < 3)
  have h₂w : 0 < ((2 * w : ℝ≥0) : ℝ) := by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hw
  have hs : w + 2 * w = v := by dsimp [w]; ring
  have he : heatOp v f = heatOp w (heatOp (2 * w) f) := by
    rw [← hs]
    funext y
    exact heatOp_semigroup_periodic hf hp w (2 * w) y
  rw [he]
  have hhalf : (((2 * w : ℝ≥0) : ℝ) / 2) = (w : ℝ) := by
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    ring
  have hgrad : ∀ y, ‖pd j (pd k (heatOp (2 * w) f)) y‖ ≤
      2 * H * gmom (β + 1) * gmom 1 * (w : ℝ) ^ ((β - 2) / 2) := by
    intro y
    have h := norm_pd2_heatOp_holder_le hf hp hC hH hβ hholder h₂w j k y
    rwa [hhalf] at h
  have h := norm_pd3_heatOp_of_C2_le (contDiff_two_heatOp_continuous_periodic hf hp h₂w)
    (isQP_zero_iff.1 (heatOp_isQP (isQP_zero_iff.2 hp) (2 * w))) hgrad hw i x
  have hpower : (w : ℝ) ^ ((β - 2) / 2) / Real.sqrt (w : ℝ) =
      (w : ℝ) ^ ((β - 3) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hw]
    congr 1
    ring
  apply h.trans_eq
  calc
    (2 * H * gmom (β + 1) * gmom 1 * (w : ℝ) ^ ((β - 2) / 2)) * gmom 1 / Real.sqrt (w : ℝ)
        = 2 * H * gmom (β + 1) * (gmom 1) ^ 2 *
            ((w : ℝ) ^ ((β - 2) / 2) / Real.sqrt (w : ℝ)) := by ring
    _ = _ := by rw [hpower]; rfl

end AnomDiss

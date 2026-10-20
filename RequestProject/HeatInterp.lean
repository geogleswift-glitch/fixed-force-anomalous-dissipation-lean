module

public import RequestProject.HeatCalc
public import RequestProject.FlowTime
public import RequestProject.SplitRegular

/-!
# Time derivative of the heat–transport interpolant

For a `C²` quasi-periodic `g`, the backward flow maps `Y_r = Φ_{r → t₀}` of a periodic field `V`
and `κ ≥ 0`, the interpolant `z(r) = H_{2κ(r - t₀)}(g ∘ Y_r)` satisfies, for `r > t₀`,
`∂ᵣ z = κ Δz - H(V · ∇(g ∘ Y_r))`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal InnerProductSpace

noncomputable section

namespace AnomDiss

variable {ξ : Pt 2}

lemma integrable_norm_gauss2_one : Integrable (fun ζ : Pt 2 => ‖ζ‖) (gauss2 1) := by
  have := integrable_gauss2_norm_rpow 1 (p := 1) one_pos
  simpa using this

lemma norm_fderiv_pd_le {F : Pt 2 → ℂ} (hF : ContDiff ℝ 2 F) {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ C) (i : Fin 2) (y : Pt 2) :
    ‖fderiv ℝ (pd i F) y‖ ≤ C := by
  have hd : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have e : fderiv ℝ (pd i F) y = (fderiv ℝ (fderiv ℝ F) y).flip (Pi.single i 1) := by
    unfold pd
    rw [fderiv_clm_apply (hd y) (differentiableAt_const _)]
    simp
  rw [e]
  refine ((fderiv ℝ (fderiv ℝ F) y).flip.le_opNorm _).trans ?_
  rw [ContinuousLinearMap.opNorm_flip]
  have : ‖(Pi.single i 1 : Pt 2)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  have h0 := norm_nonneg (fderiv ℝ (fderiv ℝ F) y)
  nlinarith [hC y]

/-- Gaussian integration by parts for `DF(x + σζ)ζ`. -/
lemma integral_fderiv_apply_gauss {F : Pt 2 → ℂ} (hF : ContDiff ℝ 2 F) (hqp : IsQP ξ F) (σ : ℝ)
    (x : Pt 2) :
    ∫ ζ, fderiv ℝ F (x + σ • ζ) ζ ∂(gauss2 1) =
      (σ : ℂ) * ∑ i, ∫ ζ, pd i (pd i F) (x + σ • ζ) ∂(gauss2 1) := by
  obtain ⟨C, hC⟩ := bdd_C2_of_isQP hqp hF
  have h1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hpd : ∀ i, ContDiff ℝ 1 (pd i F) := fun i => contDiff_pd_of_C2 F hF i
  have hpdb : ∀ i y, ‖pd i F y‖ ≤ C := fun i y => pd_bound_of_fderiv (fun y => (hC y).2.1) i y
  have hpdd : ∀ i y, ‖fderiv ℝ (pd i F) y‖ ≤ C := fun i y =>
    norm_fderiv_pd_le hF (fun y => (hC y).2.2) i y
  have hA : ContDiff ℝ 1 (fun ζ : Pt 2 => x + σ • ζ) := by fun_prop
  have hAd : ∀ ζ, HasFDerivAt (fun ζ : Pt 2 => x + σ • ζ) (σ • ContinuousLinearMap.id ℝ (Pt 2)) ζ :=
    fun ζ => ((hasFDerivAt_id ζ).const_smul σ).const_add x
  have haff : ∀ i, ContDiff ℝ 1 (fun ζ : Pt 2 => pd i F (x + σ • ζ)) := fun i => (hpd i).comp hA
  have hfd : ∀ i ζ, fderiv ℝ (fun ζ : Pt 2 => pd i F (x + σ • ζ)) ζ =
      (fderiv ℝ (pd i F) (x + σ • ζ)).comp (σ • ContinuousLinearMap.id ℝ (Pt 2)) := fun i ζ =>
    (((hpd i).differentiable one_ne_zero _).hasFDerivAt.comp ζ (hAd ζ)).fderiv
  have hfdb : ∀ i ζ, ‖fderiv ℝ (fun ζ : Pt 2 => pd i F (x + σ • ζ)) ζ‖ ≤ |σ| * C := fun i ζ => by
    rw [hfd]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have hid : ‖ContinuousLinearMap.id ℝ (Pt 2)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h0 : 0 ≤ ‖fderiv ℝ (pd i F) (x + σ • ζ)‖ := norm_nonneg _
    have hb := hpdd i (x + σ • ζ)
    calc ‖fderiv ℝ (pd i F) (x + σ • ζ)‖ * (|σ| * ‖ContinuousLinearMap.id ℝ (Pt 2)‖)
        ≤ C * (|σ| * 1) := mul_le_mul hb (mul_le_mul_of_nonneg_left hid (abs_nonneg σ))
          (by positivity) (h0.trans hb)
      _ = |σ| * C := by ring
  have hint : ∀ i, Integrable (fun ζ : Pt 2 => ((ζ i : ℝ) : ℂ) * pd i F (x + σ • ζ)) (gauss2 1) :=
    fun i => by
      refine (integrable_norm_gauss2_one.mul_const C).mono'
        ((Complex.continuous_ofReal.comp (continuous_apply i)).mul
          (haff i).continuous).aestronglyMeasurable (Eventually.of_forall fun ζ => ?_)
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul (norm_le_pi_norm ζ i) (hpdb i _) (norm_nonneg _) (norm_nonneg _)
  simp only [fderiv_apply_eq_sum_pd, Complex.real_smul]
  rw [integral_finset_sum _ fun i _ => hint i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [stein_2d (haff i) (fun ζ => hpdb i _) (hfdb i) i, ← integral_const_mul]
  congr 1; funext ζ
  show fderiv ℝ (fun ζ => pd i F (x + σ • ζ)) ζ (Pi.single i 1) = _
  rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, Complex.real_smul]
  rfl

end AnomDiss

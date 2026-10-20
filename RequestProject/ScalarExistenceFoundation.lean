module

public import RequestProject.H2Dens

/-!
# Heat estimates for a future scalar existence construction

These estimates have no Navier–Stokes or scalar existence hypothesis.  In particular,
the derivative estimate is independent of the size of the derivative of the input.
It provides the integrable `t⁻¹/²` singularity needed by a Duhamel fixed-point construction.
This file does not assert existence of a classical advection–diffusion solution.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-- Heat averaging is a contraction for a uniform distance between bounded continuous inputs. -/
theorem heatOp_uniform_distance {f g : Pt 2 → ℂ} (hf : Continuous f) (hg : Continuous g)
    {Cf Cg D : ℝ} (hCf : ∀ x, ‖f x‖ ≤ Cf) (hCg : ∀ x, ‖g x‖ ≤ Cg)
    (hD : ∀ x, ‖f x - g x‖ ≤ D) (v : ℝ≥0) (x : Pt 2) :
    ‖heatOp v f x - heatOp v g x‖ ≤ D := by
  have hiF := integrable_gauss2_of_bdd hf hCf v x
  have hiG := integrable_gauss2_of_bdd hg hCg v x
  unfold heatOp
  rw [← integral_sub hiF hiG]
  simpa using norm_integral_le_of_norm_le_const (μ := gauss2 v)
    (f := fun ζ => f (x + ζ) - g (x + ζ))
    (C := D) (Eventually.of_forall fun ζ => hD (x + ζ))

/-- The Gaussian heat step approaches a Hölder input uniformly with rate `v^(β/2)`. -/
theorem heatOp_holder_initial_error {f : Pt 2 → ℂ} (hf : Continuous f) {C H β : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (hβ : 0 < β) (hH0 : 0 ≤ H)
    (hH : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β) (v : ℝ≥0) (x : Pt 2) :
    ‖heatOp v f x - f x‖ ≤ 2 * H * gmom β * (v : ℝ) ^ (β / 2) := by
  have hi := integrable_gauss2_of_bdd hf hC v x
  have hc : (∫ ζ, f x ∂(gauss2 v)) = f x := by simp
  unfold heatOp
  rw [← hc, ← integral_sub hi (integrable_const _)]
  calc
    ‖∫ ζ, f (x + ζ) - f x ∂(gauss2 v)‖
        ≤ ∫ ζ, H * ‖ζ‖ ^ β ∂(gauss2 v) := by
      refine norm_integral_le_of_norm_le ((integrable_gauss2_norm_rpow v hβ).const_mul H) ?_
      exact Eventually.of_forall fun ζ => by simpa using hH (x + ζ) x
    _ = H * ∫ ζ, ‖ζ‖ ^ β ∂(gauss2 v) := integral_const_mul _ _
    _ ≤ H * (2 * gmom β * (v : ℝ) ^ (β / 2)) :=
      mul_le_mul_of_nonneg_left (integral_gauss2_norm_rpow_le v hβ) hH0
    _ = 2 * H * gmom β * (v : ℝ) ^ (β / 2) := by ring

/-- The heat gradient written as a first Gaussian moment of the input. -/
def heatGradientKernel (v : ℝ≥0) (f : Pt 2 → ℂ) (i : Fin 2) (x : Pt 2) : ℂ :=
  (Real.sqrt v)⁻¹ • ∫ ζ, (ζ i : ℂ) * f (x + Real.sqrt v • ζ) ∂(gauss2 1)

/-- The Gaussian first-moment formula for the derivative of a heat average. -/
theorem sqrt_mul_pd_heatOp {ξ : Pt 2} {f : Pt 2 → ℂ} (hqp : IsQP ξ f)
    (hf : ContDiff ℝ 1 f) (v : ℝ≥0) (i : Fin 2) (x : Pt 2) :
    Real.sqrt v • pd i (heatOp v f) x =
      ∫ ζ, (ζ i : ℂ) * f (x + Real.sqrt v • ζ) ∂(gauss2 1) := by
  obtain ⟨C, hC⟩ := bdd_C1_of_isQP hqp hf
  let σ : ℝ := Real.sqrt v
  let A : Pt 2 → Pt 2 := fun ζ => x + σ • ζ
  let G : Pt 2 → ℂ := f ∘ A
  have hσ : 0 ≤ σ := Real.sqrt_nonneg _
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0).1
  have hA : ∀ ζ, HasFDerivAt A (σ • ContinuousLinearMap.id ℝ (Pt 2)) ζ := fun ζ => by
    exact ((hasFDerivAt_id ζ).const_smul σ).const_add x
  have hG : ContDiff ℝ 1 G := hf.comp (by unfold A; fun_prop)
  have hGD : ∀ ζ, fderiv ℝ G ζ =
      (fderiv ℝ f (A ζ)).comp (σ • ContinuousLinearMap.id ℝ (Pt 2)) := fun ζ =>
    (((hf.differentiable one_ne_zero) (A ζ)).hasFDerivAt.comp ζ (hA ζ)).fderiv
  have hGB : ∀ ζ, ‖G ζ‖ ≤ C := fun ζ => (hC (A ζ)).1
  have hGDB : ∀ ζ, ‖fderiv ℝ G ζ‖ ≤ C * σ := by
    intro ζ
    rw [hGD]
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC0 hσ) fun z => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, norm_smul, Real.norm_of_nonneg hσ]
    calc σ * ‖fderiv ℝ f (A ζ) z‖ ≤ σ * (C * ‖z‖) :=
        mul_le_mul_of_nonneg_left
          (((fderiv ℝ f (A ζ)).le_opNorm z).trans
            (mul_le_mul_of_nonneg_right (hC (A ζ)).2 (norm_nonneg z))) hσ
      _ = C * σ * ‖z‖ := by ring
  have hPD : ∀ ζ, pd i G ζ = σ • pd i f (A ζ) := by
    intro ζ
    unfold pd
    rw [hGD]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul]
  have hs := stein_2d hG hGB hGDB i
  simp only [hPD] at hs
  rw [integral_smul] at hs
  rw [pd_heatOp_C1 hqp hf, heatOp_eq_scaled (continuous_pd_of_C1 f hf i)]
  exact hs.symm

/-- For positive variance the kernel formula equals the actual partial derivative. -/
theorem pd_heatOp_eq_heatGradientKernel {ξ : Pt 2} {f : Pt 2 → ℂ} (hqp : IsQP ξ f)
    (hf : ContDiff ℝ 1 f) {v : ℝ≥0} (hv : 0 < (v : ℝ)) (i : Fin 2) (x : Pt 2) :
    pd i (heatOp v f) x = heatGradientKernel v f i x := by
  have hσ : Real.sqrt (v : ℝ) ≠ 0 := (Real.sqrt_pos.2 hv).ne'
  unfold heatGradientKernel
  rw [← sqrt_mul_pd_heatOp hqp hf]
  simp [hσ]

/-- The first-moment kernel of bounded continuous data is Bochner integrable. -/
theorem integrable_heatGradientKernel_integrand {f : Pt 2 → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (v : ℝ≥0) (i : Fin 2) (x : Pt 2) :
    Integrable (fun ζ : Pt 2 => (ζ i : ℂ) * f (x + Real.sqrt v • ζ)) (gauss2 1) := by
  have hi : Integrable (fun ζ : Pt 2 => |ζ i|) (gauss2 1) :=
    integrable_gauss2_coord 1 i continuous_abs.aestronglyMeasurable integrable_abs_gaussianReal_std
  refine (hi.const_mul C).mono' ?_ (Eventually.of_forall fun ζ => ?_)
  · exact ((Complex.continuous_ofReal.comp (continuous_apply i)).fun_mul
      (hf.comp (by fun_prop : Continuous
        fun ζ : Pt 2 => x + Real.sqrt (v : ℝ) • ζ))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)).trans_eq (mul_comm _ _)

/-- Uniform gradient smoothing bound; only the bound of the input occurs in the constant. -/
theorem norm_heatGradientKernel_le {f : Pt 2 → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (v : ℝ≥0) (i : Fin 2) (x : Pt 2) :
    ‖heatGradientKernel v f i x‖ ≤ C * gmom 1 / Real.sqrt (v : ℝ) := by
  have hi : Integrable (fun ζ : Pt 2 => |ζ i|) (gauss2 1) :=
    integrable_gauss2_coord 1 i continuous_abs.aestronglyMeasurable integrable_abs_gaussianReal_std
  have hmoment : (∫ ζ : Pt 2, |ζ i| ∂(gauss2 1)) = gmom 1 := by
    rw [integral_gauss2_coord 1 i continuous_abs.aestronglyMeasurable]
    simp [gmom]
  unfold heatGradientKernel
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  have hbound : ‖∫ ζ, (ζ i : ℂ) * f (x + Real.sqrt v • ζ) ∂(gauss2 1)‖ ≤ C * gmom 1 := by
    calc
      ‖∫ ζ, (ζ i : ℂ) * f (x + Real.sqrt v • ζ) ∂(gauss2 1)‖
          ≤ ∫ ζ, ‖(ζ i : ℂ) * f (x + Real.sqrt v • ζ)‖ ∂(gauss2 1) :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ ζ, C * |ζ i| ∂(gauss2 1) := by
        refine integral_mono (integrable_heatGradientKernel_integrand hf hC v i x).norm
          (hi.const_mul C) fun ζ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)).trans_eq (mul_comm _ _)
      _ = C * gmom 1 := by rw [integral_const_mul, hmoment]
  calc (Real.sqrt (v : ℝ))⁻¹ * ‖∫ ζ, (ζ i : ℂ) * f (x + Real.sqrt v • ζ) ∂(gauss2 1)‖
      ≤ (Real.sqrt (v : ℝ))⁻¹ * (C * gmom 1) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 (Real.sqrt_nonneg _))
    _ = C * gmom 1 / Real.sqrt (v : ℝ) := by ring

/-- A positive heat step improves the first derivative bound by a factor `1/√v`. -/
theorem norm_pd_heatOp_le {ξ : Pt 2} {f : Pt 2 → ℂ} (hqp : IsQP ξ f)
    (hf : ContDiff ℝ 1 f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {v : ℝ≥0}
    (hv : 0 < (v : ℝ)) (i : Fin 2) (x : Pt 2) :
    ‖pd i (heatOp v f) x‖ ≤ C * gmom 1 / Real.sqrt (v : ℝ) := by
  rw [pd_heatOp_eq_heatGradientKernel hqp hf hv]
  exact norm_heatGradientKernel_le hf.continuous hC v i x

/-- The first-moment kernel is continuous in the spatial point for continuous bounded data. -/
theorem continuous_heatGradientKernel {f : Pt 2 → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (v : ℝ≥0) (i : Fin 2) :
    Continuous (heatGradientKernel v f i) := by
  have hi : Integrable (fun ζ : Pt 2 => |ζ i|) (gauss2 1) :=
    integrable_gauss2_coord 1 i continuous_abs.aestronglyMeasurable integrable_abs_gaussianReal_std
  unfold heatGradientKernel
  refine (continuous_const : Continuous
    fun _ : Pt 2 => (Real.sqrt (v : ℝ))⁻¹).fun_smul ?_
  refine continuous_of_dominated (bound := fun ζ : Pt 2 => C * |ζ i|)
    (fun x => (integrable_heatGradientKernel_integrand hf hC v i x).aestronglyMeasurable)
    (fun x => Eventually.of_forall fun ζ => ?_) (hi.const_mul C)
    (Eventually.of_forall fun ζ => ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)).trans_eq (mul_comm _ _)
  · exact (continuous_const : Continuous fun _ : Pt 2 => (ζ i : ℂ)).fun_mul
      (hf.comp (by fun_prop : Continuous fun x : Pt 2 => x + Real.sqrt (v : ℝ) • ζ))

/-- Uniform-distance stability of the Gaussian derivative kernel. -/
theorem heatGradientKernel_uniform_distance {f g : Pt 2 → ℂ} (hf : Continuous f)
    (hg : Continuous g) {Cf Cg D : ℝ} (hCf : ∀ x, ‖f x‖ ≤ Cf)
    (hCg : ∀ x, ‖g x‖ ≤ Cg) (hD : ∀ x, ‖f x - g x‖ ≤ D)
    (v : ℝ≥0) (i : Fin 2) (x : Pt 2) :
    ‖heatGradientKernel v f i x - heatGradientKernel v g i x‖ ≤
      D * gmom 1 / Real.sqrt (v : ℝ) := by
  have he : heatGradientKernel v f i x - heatGradientKernel v g i x =
      heatGradientKernel v (fun y => f y - g y) i x := by
    unfold heatGradientKernel
    rw [← smul_sub, ← integral_sub
      (integrable_heatGradientKernel_integrand hf hCf v i x)
      (integrable_heatGradientKernel_integrand hg hCg v i x)]
    congr 2
    funext ζ
    rw [mul_sub]
  rw [he]
  exact norm_heatGradientKernel_le (hf.sub hg) hD v i x

end AnomDiss

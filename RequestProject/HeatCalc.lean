module

public import RequestProject.HeatStep
public import RequestProject.QPBasic

/-!
# Calculus for the heat operator

Gaussian averages `x ↦ 𝔼 F(x + ζ)` of `C¹` functions with bounded derivatives are differentiable
with derivative `𝔼 DF(x + ζ)`; hence the heat operator commutes with partial derivatives and
preserves `C²` regularity and quasi-periodicity.  We also record the scaled representation
`H_v f(x) = 𝔼 f(x + √v ζ)` with `ζ` standard, and Gaussian integration by parts (Stein's lemma).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal InnerProductSpace

noncomputable section

namespace AnomDiss

section Gavg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma integrable_gauss2_of_bdd {F : Pt 2 → E} (hF : Continuous F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    (v : ℝ≥0) (x : Pt 2) : Integrable (fun ζ => F (x + ζ)) (gauss2 v) :=
  Integrable.of_bound (hF.comp (continuous_const.add continuous_id)).aestronglyMeasurable C
    (Eventually.of_forall fun _ => hC _)

lemma continuous_gavg {F : Pt 2 → E} (hF : Continuous F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    (v : ℝ≥0) : Continuous fun x => ∫ ζ, F (x + ζ) ∂(gauss2 v) :=
  continuous_of_dominated (bound := fun _ => C)
    (fun _ => (hF.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    (fun _ => Eventually.of_forall fun _ => hC _) (integrable_const C)
    (Eventually.of_forall fun _ => hF.comp (continuous_id.add continuous_const))

lemma hasFDerivAt_gavg {F : Pt 2 → E} (hF : ContDiff ℝ 1 F) {C₀ C₁ : ℝ}
    (h₀ : ∀ x, ‖F x‖ ≤ C₀) (h₁ : ∀ x, ‖fderiv ℝ F x‖ ≤ C₁) (v : ℝ≥0) (x : Pt 2) :
    HasFDerivAt (fun x => ∫ ζ, F (x + ζ) ∂(gauss2 v)) (∫ ζ, fderiv ℝ F (x + ζ) ∂(gauss2 v)) x := by
  have hd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hc : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C₁) (s := univ)
    (F := fun y ζ => F (y + ζ)) (F' := fun y ζ => fderiv ℝ F (y + ζ))
    univ_mem (Eventually.of_forall fun y => ?_) (integrable_gauss2_of_bdd hF.continuous h₀ v x)
    (hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun ζ y _ => h₁ _) (integrable_const C₁)
    (Eventually.of_forall fun ζ y _ => ?_)
  · exact (hF.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  · have := (hd (y + ζ)).hasFDerivAt.comp y ((hasFDerivAt_id y).add_const ζ)
    simpa [Function.comp_def] using this

lemma fderiv_gavg {F : Pt 2 → E} (hF : ContDiff ℝ 1 F) {C₀ C₁ : ℝ}
    (h₀ : ∀ x, ‖F x‖ ≤ C₀) (h₁ : ∀ x, ‖fderiv ℝ F x‖ ≤ C₁) (v : ℝ≥0) :
    fderiv ℝ (fun x => ∫ ζ, F (x + ζ) ∂(gauss2 v)) =
      fun x => ∫ ζ, fderiv ℝ F (x + ζ) ∂(gauss2 v) :=
  funext fun x => (hasFDerivAt_gavg hF h₀ h₁ v x).fderiv

end Gavg

/-! ### Bounds for `C²` quasi-periodic functions -/

lemma norm_clm_pt2_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : Pt 2 →L[ℝ] E) :
    ‖L‖ ≤ ‖L (Pi.single 0 1)‖ + ‖L (Pi.single 1 1)‖ := by
  refine L.opNorm_le_bound (by positivity) fun v => ?_
  have hv : v = v 0 • (Pi.single 0 1 : Pt 2) + v 1 • (Pi.single 1 1 : Pt 2) := by
    ext i; fin_cases i <;> simp
  have h0 : |v 0| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v 0
  have h1 : |v 1| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v 1
  calc ‖L v‖ = ‖v 0 • L (Pi.single 0 1) + v 1 • L (Pi.single 1 1)‖ := by
        conv_lhs => rw [hv]
        rw [map_add, map_smul, map_smul]
    _ ≤ |v 0| * ‖L (Pi.single 0 1)‖ + |v 1| * ‖L (Pi.single 1 1)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖v‖ * ‖L (Pi.single 0 1)‖ + ‖v‖ * ‖L (Pi.single 1 1)‖ := by gcongr
    _ = _ := by ring

lemma fderiv_fderiv_apply_eq_pd {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f) (i j : Fin 2) (x : Pt 2) :
    fderiv ℝ (fderiv ℝ f) x (Pi.single j 1) (Pi.single i 1) = pd j (pd i f) x := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  unfold pd
  rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simp

/-- A `C²` quasi-periodic function is bounded together with its first two derivatives. -/
lemma bdd_C2_of_isQP {ξ : Pt 2} {f : Pt 2 → ℂ} (hqp : IsQP ξ f) (hf : ContDiff ℝ 2 f) :
    ∃ C, ∀ x, ‖f x‖ ≤ C ∧ ‖fderiv ℝ f x‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C := by
  have h1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hd : Differentiable ℝ f := h1.differentiable one_ne_zero
  have hpd : ∀ i, ContDiff ℝ 1 (pd i f) := fun i => contDiff_pd_of_C2 f hf i
  obtain ⟨C₀, hC₀⟩ := hqp.bdd hf.continuous
  have hb1 : ∀ i, ∃ C, ∀ x, ‖pd i f x‖ ≤ C := fun i => (hqp.pd hd i).bdd (hpd i).continuous
  have hb2 : ∀ i j, ∃ C, ∀ x, ‖pd j (pd i f) x‖ ≤ C := fun i j =>
    ((hqp.pd hd i).pd ((hpd i).differentiable one_ne_zero) j).bdd
      (continuous_pd_of_C1 _ (hpd i) j)
  choose C₁ hC₁ using hb1
  choose C₂ hC₂ using hb2
  refine ⟨C₀ + (C₁ 0 + C₁ 1) + ((C₂ 0 0 + C₂ 1 0) + (C₂ 0 1 + C₂ 1 1)), fun x => ⟨?_, ?_, ?_⟩⟩
  · have := hC₁ 0 x; have := hC₁ 1 x; have := hC₂ 0 0 x; have := hC₂ 1 0 x
    have := hC₂ 0 1 x; have := hC₂ 1 1 x
    have := norm_nonneg (pd 0 f x); have := norm_nonneg (pd 1 f x)
    have := norm_nonneg (pd 0 (pd 0 f) x); have := norm_nonneg (pd 1 (pd 0 f) x)
    have := norm_nonneg (pd 0 (pd 1 f) x); have := norm_nonneg (pd 1 (pd 1 f) x)
    linarith [hC₀ x]
  · have h := norm_clm_pt2_le (fderiv ℝ f x)
    have e0 : fderiv ℝ f x (Pi.single 0 1) = pd 0 f x := rfl
    have e1 : fderiv ℝ f x (Pi.single 1 1) = pd 1 f x := rfl
    rw [e0, e1] at h
    have := hC₁ 0 x; have := hC₁ 1 x
    have := (norm_nonneg (f x)).trans (hC₀ x)
    have := hC₂ 0 0 x; have := hC₂ 1 0 x; have := hC₂ 0 1 x; have := hC₂ 1 1 x
    have := norm_nonneg (pd 0 (pd 0 f) x); have := norm_nonneg (pd 1 (pd 0 f) x)
    have := norm_nonneg (pd 0 (pd 1 f) x); have := norm_nonneg (pd 1 (pd 1 f) x)
    linarith
  · have h := norm_clm_pt2_le (fderiv ℝ (fderiv ℝ f) x)
    have hj : ∀ j : Fin 2, ‖fderiv ℝ (fderiv ℝ f) x (Pi.single j 1)‖ ≤
        ‖pd j (pd 0 f) x‖ + ‖pd j (pd 1 f) x‖ := fun j => by
      have := norm_clm_pt2_le (fderiv ℝ (fderiv ℝ f) x (Pi.single j 1))
      rwa [fderiv_fderiv_apply_eq_pd hf, fderiv_fderiv_apply_eq_pd hf] at this
    have := hj 0; have := hj 1
    have := hC₂ 0 0 x; have := hC₂ 1 0 x; have := hC₂ 0 1 x; have := hC₂ 1 1 x
    have := (norm_nonneg (f x)).trans (hC₀ x)
    have := (norm_nonneg (pd 0 f x)).trans (hC₁ 0 x)
    have := (norm_nonneg (pd 1 f x)).trans (hC₁ 1 x)
    linarith

/-! ### The heat operator on `C²` quasi-periodic functions -/

section HeatQP

variable {ξ : Pt 2} {f : Pt 2 → ℂ}

lemma heatOp_isQP (hqp : IsQP ξ f) (v : ℝ≥0) : IsQP ξ (heatOp v f) := by
  intro x m
  unfold heatOp
  rw [← integral_const_mul]
  congr 1; funext ζ
  rw [show x + intVec m + ζ = x + ζ + intVec m by abel, hqp]

lemma pd_heatOp (hqp : IsQP ξ f) (hf : ContDiff ℝ 2 f) (v : ℝ≥0) (i : Fin 2) (x : Pt 2) :
    pd i (heatOp v f) x = heatOp v (pd i f) x := by
  obtain ⟨C, hC⟩ := bdd_C2_of_isQP hqp hf
  have h1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hfd : fderiv ℝ (heatOp v f) = fun x => ∫ ζ, fderiv ℝ f (x + ζ) ∂(gauss2 v) :=
    fderiv_gavg h1 (fun x => (hC x).1) (fun x => (hC x).2.1) v
  unfold pd heatOp
  rw [show (fun x => ∫ ζ, f (x + ζ) ∂(gauss2 v)) = heatOp v f from rfl, hfd]
  simp only
  rw [ContinuousLinearMap.integral_apply (integrable_gauss2_of_bdd
    (h1.continuous_fderiv one_ne_zero) (fun x => (hC x).2.1) v x)]

lemma contDiff_heatOp (hqp : IsQP ξ f) (hf : ContDiff ℝ 2 f) (v : ℝ≥0) :
    ContDiff ℝ 2 (heatOp v f) := by
  obtain ⟨C, hC⟩ := bdd_C2_of_isQP hqp hf
  have h1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have h1' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hfd : fderiv ℝ (heatOp v f) = fun x => ∫ ζ, fderiv ℝ f (x + ζ) ∂(gauss2 v) :=
    fderiv_gavg h1 (fun x => (hC x).1) (fun x => (hC x).2.1) v
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt_gavg h1 (fun x => (hC x).1) (fun x => (hC x).2.1) v x).differentiableAt,
    by simp, ?_⟩
  rw [hfd, contDiff_one_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt_gavg h1' (fun x => (hC x).2.1) (fun x => (hC x).2.2) v
    x).differentiableAt, ?_⟩
  rw [fderiv_gavg h1' (fun x => (hC x).2.1) (fun x => (hC x).2.2) v]
  exact continuous_gavg (h1'.continuous_fderiv one_ne_zero) (fun x => (hC x).2.2) v

end HeatQP

/-! ### Scaled representation -/

lemma gauss2_eq_map (v : ℝ≥0) : gauss2 v = (gauss2 1).map (fun ζ => Real.sqrt v • ζ) := by
  unfold gauss2
  have e : (fun ζ : Pt 2 => Real.sqrt v • ζ) = fun ζ i => (fun x => Real.sqrt v * x) (ζ i) :=
    funext fun ζ => by ext i; simp
  rw [e, Measure.pi_map_pi (fun i => by fun_prop)]
  congr 1; funext i
  rw [gaussianReal_eq_map v]

lemma heatOp_eq_scaled {f : Pt 2 → ℂ} (hf : Continuous f) (v : ℝ≥0) (x : Pt 2) :
    heatOp v f x = ∫ ζ, f (x + Real.sqrt v • ζ) ∂(gauss2 1) := by
  unfold heatOp
  rw [gauss2_eq_map v]
  exact integral_map (f := fun ζ => f (x + ζ)) (by fun_prop)
    (hf.comp (continuous_const.add continuous_id)).aestronglyMeasurable

lemma heatOp_zero {f : Pt 2 → ℂ} (hf : Continuous f) (x : Pt 2) : heatOp 0 f x = f x := by
  rw [heatOp_eq_scaled hf]
  simp

/-! ### Gaussian integration by parts -/

lemma hasDerivAt_gaussianPDFReal_std (t : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-t * gaussianPDFReal 0 1 t) t := by
  have e : gaussianPDFReal 0 1 = fun t => (Real.sqrt (2 * π))⁻¹ * Real.exp (-t ^ 2 / 2) := by
    rw [gaussianPDFReal_def]; funext t; simp
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => -t ^ 2 / 2) (-t) t := by
    have := ((hasDerivAt_pow 2 t).neg).div_const 2
    convert this using 1; push_cast; ring
  have := (h1.exp).const_mul (Real.sqrt (2 * π))⁻¹
  convert this using 1; ring

lemma continuous_gaussianPDFReal_std : Continuous (gaussianPDFReal 0 1) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_gaussianPDFReal_std t).continuousAt

lemma integrable_mul_gaussianPDFReal_std : Integrable fun t : ℝ => t * gaussianPDFReal 0 1 t := by
  have e : (fun t : ℝ => t * gaussianPDFReal 0 1 t) =
      fun t => (Real.sqrt (2 * π))⁻¹ * (t * Real.exp (-(1 / 2) * t ^ 2)) := by
    rw [gaussianPDFReal_def]; funext t; simp; ring_nf
  rw [e]
  exact (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul _

/-- **Stein's lemma** in one dimension. -/
lemma stein_1d {g g' : ℝ → ℂ} (hg : ∀ t, HasDerivAt g (g' t) t) (hgc : Continuous g')
    {C₀ C₁ : ℝ} (h₀ : ∀ t, ‖g t‖ ≤ C₀) (h₁ : ∀ t, ‖g' t‖ ≤ C₁) :
    ∫ t, (t : ℂ) * g t ∂(gaussianReal 0 1) = ∫ t, g' t ∂(gaussianReal 0 1) := by
  have hgcont : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  set φ := gaussianPDFReal 0 1 with hφ
  have hφc : Continuous φ := continuous_gaussianPDFReal_std
  have hφi : Integrable φ := integrable_gaussianPDFReal 0 1
  have hφ0 : ∀ t, 0 ≤ φ t := fun t => gaussianPDFReal_nonneg 0 1 t
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [Complex.real_smul]
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (A := ℂ)
    (u := fun t => ((φ t : ℝ) : ℂ)) (u' := fun t => ((-t * φ t : ℝ) : ℂ)) (v := g) (v' := g')
    (fun t _ => (hasDerivAt_gaussianPDFReal_std t).ofReal_comp) (fun t _ => hg t) ?_ ?_ ?_
  · rw [key, ← integral_neg]
    congr 1; funext t; push_cast; ring
  · refine (hφi.mul_const C₁).mono' ((Complex.continuous_ofReal.comp hφc).mul hgc).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ0 t)]
    exact mul_le_mul_of_nonneg_left (h₁ t) (hφ0 t)
  · refine (integrable_mul_gaussianPDFReal_std.norm.mul_const C₀).mono'
      ((Complex.continuous_ofReal.comp (continuous_id.neg.mul hφc)).mul hgcont).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    exact mul_le_mul_of_nonneg_left (h₀ t) (by positivity)
  · refine (hφi.mul_const C₀).mono' ((Complex.continuous_ofReal.comp hφc).mul hgcont).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ0 t)]
    exact mul_le_mul_of_nonneg_left (h₀ t) (hφ0 t)

lemma integral_gauss2_one_eq_prod (F : Pt 2 → ℂ) :
    ∫ ζ, F ζ ∂(gauss2 1) =
      ∫ p, F ![p.1, p.2] ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hmp := measurePreserving_piFinTwo (fun _ : Fin 2 => gaussianReal 0 1)
  have e : ∀ p : ℝ × ℝ, (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm p = ![p.1, p.2] :=
    fun p => by ext i; fin_cases i <;> rfl
  show ∫ ζ, F ζ ∂(Measure.pi fun _ => gaussianReal 0 1) = _
  rw [← hmp.symm.integral_comp' F]
  simp only [e]

lemma integrable_abs_gaussianReal_std : Integrable (fun t : ℝ => |t|) (gaussianReal 0 1) :=
  ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).abs

lemma pd_bound_of_fderiv {G : Pt 2 → ℂ} {C₁ : ℝ} (h₁ : ∀ x, ‖fderiv ℝ G x‖ ≤ C₁) (i : Fin 2)
    (x : Pt 2) : ‖pd i G x‖ ≤ C₁ := by
  unfold pd
  refine ((fderiv ℝ G x).le_opNorm _).trans ?_
  have : ‖(Pi.single i 1 : Pt 2)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  have h0 : 0 ≤ ‖fderiv ℝ G x‖ := norm_nonneg _
  nlinarith [h₁ x]

/-- **Stein's lemma** for the standard Gaussian on `ℝ²`: `𝔼[ζᵢ G(ζ)] = 𝔼[∂ᵢG(ζ)]`. -/
lemma stein_2d {G : Pt 2 → ℂ} (hG : ContDiff ℝ 1 G) {C₀ C₁ : ℝ} (h₀ : ∀ x, ‖G x‖ ≤ C₀)
    (h₁ : ∀ x, ‖fderiv ℝ G x‖ ≤ C₁) (i : Fin 2) :
    ∫ ζ, (ζ i : ℂ) * G ζ ∂(gauss2 1) = ∫ ζ, pd i G ζ ∂(gauss2 1) := by
  have hd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hpc : ∀ i, Continuous (pd i G) := fun i => continuous_pd_of_C1 G hG i
  have hpb : ∀ i x, ‖pd i G x‖ ≤ C₁ := fun i x => pd_bound_of_fderiv h₁ i x
  have hv : Continuous fun p : ℝ × ℝ => (![p.1, p.2] : Pt 2) := continuous_vec2
  have hab := integrable_abs_gaussianReal_std
  rw [integral_gauss2_one_eq_prod, integral_gauss2_one_eq_prod]
  have hI2 : ∀ i, Integrable (fun p : ℝ × ℝ => pd i G ![p.1, p.2])
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := fun i =>
    Integrable.of_bound ((hpc i).comp hv).aestronglyMeasurable C₁
      (Eventually.of_forall fun p => hpb i _)
  fin_cases i
  · have hI1 : Integrable (fun p : ℝ × ℝ => (p.1 : ℂ) * G ![p.1, p.2])
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      refine ((hab.comp_fst _).mul_const C₀).mono' ?_ (Eventually.of_forall fun p => ?_)
      · exact ((Complex.continuous_ofReal.comp continuous_fst).mul
          (hG.continuous.comp hv)).aestronglyMeasurable
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (h₀ _) (abs_nonneg _)
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [integral_prod_symm _ hI1, integral_prod_symm _ (hI2 0)]
    congr 1; funext b
    have e : ∀ a : ℝ, (![a, b] : Pt 2) = ![0, b] + a • eb 0 := by
      intro a; funext j; fin_cases j <;> simp [eb]
    show ∫ a, (a : ℂ) * G ![a, b] ∂(gaussianReal 0 1) = ∫ a, pd 0 G ![a, b] ∂(gaussianReal 0 1)
    rw [show (fun a : ℝ => (a : ℂ) * G ![a, b]) = fun a : ℝ => (a : ℂ) * G (![0, b] + a • eb 0) from
      funext fun a => by rw [← e a], show (fun a : ℝ => pd 0 G ![a, b]) =
        fun a : ℝ => pd 0 G (![0, b] + a • eb 0) from funext fun a => by rw [← e a]]
    exact stein_1d (fun a => hasDerivAt_line G ![0, b] 0 a (hd _))
      ((hpc 0).comp (continuous_const.add (continuous_id.smul continuous_const)))
      (fun a => h₀ _) (fun a => hpb 0 _)
  · have hI1 : Integrable (fun p : ℝ × ℝ => (p.2 : ℂ) * G ![p.1, p.2])
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      refine ((hab.comp_snd _).mul_const C₀).mono' ?_ (Eventually.of_forall fun p => ?_)
      · exact ((Complex.continuous_ofReal.comp continuous_snd).mul
          (hG.continuous.comp hv)).aestronglyMeasurable
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (h₀ _) (abs_nonneg _)
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [integral_prod _ hI1, integral_prod _ (hI2 1)]
    congr 1; funext a
    have e : ∀ b : ℝ, (![a, b] : Pt 2) = ![a, 0] + b • eb 1 := by
      intro b; funext j; fin_cases j <;> simp [eb]
    show ∫ b, (b : ℂ) * G ![a, b] ∂(gaussianReal 0 1) = ∫ b, pd 1 G ![a, b] ∂(gaussianReal 0 1)
    rw [show (fun b : ℝ => (b : ℂ) * G ![a, b]) = fun b : ℝ => (b : ℂ) * G (![a, 0] + b • eb 1) from
      funext fun b => by rw [← e b], show (fun b : ℝ => pd 1 G ![a, b]) =
        fun b : ℝ => pd 1 G (![a, 0] + b • eb 1) from funext fun b => by rw [← e b]]
    exact stein_1d (fun b => hasDerivAt_line G ![a, 0] 1 b (hd _))
      ((hpc 1).comp (continuous_const.add (continuous_id.smul continuous_const)))
      (fun b => h₀ _) (fun b => hpb 1 _)

end AnomDiss

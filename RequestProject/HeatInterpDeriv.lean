module

public import RequestProject.H2Dens

/-!
# Time derivative of the heat–transport interpolant

For a `C²` quasi-periodic `g`, the backward flow maps `Y_r = Φ_{r → t₀}` of a periodic field `V`
and `κ ≥ 0`, the interpolant `z(r) = H_{2κ(r - t₀)}(g ∘ Y_r)` is continuous in `r` and satisfies,
for `r > t₀`, `∂ᵣ z = κ Δz - H(V · ∇(g ∘ Y_r))`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

variable {ξ : Pt 2} {V : ℝ → Pt 2 → Pt 2} {M K : ℝ≥0} {K2 K3 : ℝ}

/-- The backward map `s ↦ Φ_{s → t₀}(y s)` is continuous along continuous curves. -/
lemma continuousAt_gflow_back (hV : GoodField V M K) (t₀ : ℝ) {y : ℝ → Pt 2} {s₀ : ℝ}
    (hy : ContinuousAt y s₀) : ContinuousAt (fun s => gflow V s t₀ (y s)) s₀ := by
  have e : (fun s => gflow V s t₀ (y s)) = fun s => gflow V s₀ t₀ (gflow V s s₀ (y s)) := by
    funext s; rw [hV.gflow_gflow]
  rw [e]
  refine (hV.continuous_gflow s₀ t₀).continuousAt.comp (f := fun s => gflow V s s₀ (y s)) ?_
  have h1 : Tendsto (fun s => gflow V s s₀ (y s) - y s) (𝓝 s₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun s => norm_nonneg _) (fun s => hV.norm_gflow_sub_le s s₀ (y s)) ?_
    have : Tendsto (fun s => (M : ℝ) * |s₀ - s|) (𝓝 s₀) (𝓝 ((M : ℝ) * |s₀ - s₀|)) :=
      (continuous_const.mul (continuous_const.sub continuous_id).abs).tendsto s₀
    simpa using this
  have h2 := h1.add hy
  show Tendsto _ _ (𝓝 (gflow V s₀ s₀ (y s₀)))
  rw [hV.gflow_self]
  simpa using h2

/-- Bound on the derivative of the transported function `g ∘ Φ_{s → t₀}`. -/
lemma norm_fderiv_comp_gflow_le (hV : GoodField V M K) {g : Pt 2 → ℂ} (hgd : Differentiable ℝ g)
    {C : ℝ} (hC : ∀ y, ‖fderiv ℝ g y‖ ≤ C) (s t₀ : ℝ) (y : Pt 2) :
    ‖fderiv ℝ (g ∘ gflow V s t₀) y‖ ≤ C * Real.exp (K * |t₀ - s|) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hgl : LipschitzWith (Real.toNNReal C) g := lipschitzWith_of_nnnorm_fderiv_le hgd fun y => by
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hC0]; exact hC y
  have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := y) (hgl.comp (hV.lipschitz_gflow s t₀))
  change ‖fderiv ℝ (g ∘ gflow V s t₀) y‖ ≤
    (Real.toNNReal C : ℝ) * Real.exp (K * |t₀ - s|) at h
  rw [Real.coe_toNNReal _ hC0] at h
  exact h

/-- The Gaussian average of the derivative of the interpolant. -/
lemma integral_fderiv_interp {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f) (hqp : IsQP ξ f)
    {W : Pt 2 → Pt 2} (hW : Continuous W) {MW : ℝ} (hWb : ∀ y, ‖W y‖ ≤ MW) (v : ℝ≥0) (c : ℝ)
    (x : Pt 2) :
    ∫ ζ, fderiv ℝ f (x + Real.sqrt v • ζ) (c • ζ - W (x + Real.sqrt v • ζ)) ∂(gauss2 1) =
      (c * Real.sqrt v) • lap (heatOp v f) x - heatOp v (conv W f) x := by
  obtain ⟨C, hC⟩ := bdd_C2_of_isQP hqp hf
  have h1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hfc : Continuous (fderiv ℝ f) := h1.continuous_fderiv one_ne_zero
  have hA : Continuous fun ζ : Pt 2 => x + Real.sqrt v • ζ :=
    continuous_const.fun_add (continuous_const_smul (Real.sqrt (v : ℝ)))
  have hI1 : Integrable (fun ζ : Pt 2 => fderiv ℝ f (x + Real.sqrt v • ζ) ζ) (gauss2 1) := by
    refine (integrable_norm_gauss2_one.const_mul C).mono'
      ((hfc.comp hA).clm_apply continuous_id).aestronglyMeasurable
      (Eventually.of_forall fun ζ => ?_)
    exact ((fderiv ℝ f _).le_opNorm ζ).trans
      (mul_le_mul_of_nonneg_right (hC _).2.1 (norm_nonneg _))
  have hconv : Continuous (conv W f) := continuous_conv hW h1
  have hI2 : Integrable (fun ζ : Pt 2 => fderiv ℝ f (x + Real.sqrt v • ζ)
      (W (x + Real.sqrt v • ζ))) (gauss2 1) := by
    refine Integrable.of_bound ((hfc.comp hA).clm_apply (hW.comp hA)).aestronglyMeasurable
      (C * MW) (Eventually.of_forall fun ζ => ?_)
    exact ((fderiv ℝ f _).le_opNorm _).trans (mul_le_mul (hC _).2.1 (hWb _) (norm_nonneg _)
      ((norm_nonneg _).trans (hC 0).1))
  simp only [map_sub, map_smul]
  have hI1' : Integrable (fun ζ : Pt 2 => c • fderiv ℝ f (x + Real.sqrt v • ζ) ζ) (gauss2 1) :=
    hI1.smul c
  rw [integral_sub hI1' hI2, integral_smul, integral_fderiv_apply_gauss hf hqp]
  have e1 : ∀ i, ∫ ζ, pd i (pd i f) (x + Real.sqrt v • ζ) ∂(gauss2 1) =
      pd i (pd i (heatOp v f)) x := fun i => by
    rw [pd2_heatOp hqp hf, heatOp_eq_scaled
      (continuous_pd_of_C1 _ (contDiff_pd_of_C2 f hf i) i)]
  have e2 : ∫ ζ, fderiv ℝ f (x + Real.sqrt v • ζ) (W (x + Real.sqrt v • ζ)) ∂(gauss2 1) =
      heatOp v (conv W f) x := by
    rw [heatOp_eq_scaled hconv]
    congr 1; funext ζ
    rw [fderiv_apply_eq_sum_pd]; rfl
  simp only [e1, e2]
  congr 1
  rw [lap, Complex.real_smul, Complex.real_smul, Complex.ofReal_mul]
  ring

/-- The standard deviation `σ(s) = √(2κ(s - t₀))₊` of the interpolant. -/
lemma continuous_sqrt_var (κ t₀ : ℝ) :
    Continuous fun s : ℝ => Real.sqrt (Real.toNNReal (2 * κ * (s - t₀))) :=
  Real.continuous_sqrt.comp (NNReal.continuous_coe.comp (continuous_real_toNNReal.comp
    (continuous_const.mul (continuous_id.sub continuous_const))))

lemma hasDerivAt_sqrt_var {κ t₀ s : ℝ} (hκ : 0 < κ) (hs : t₀ < s) :
    HasDerivAt (fun s : ℝ => Real.sqrt (Real.toNNReal (2 * κ * (s - t₀))))
      (2 * κ / (2 * Real.sqrt (2 * κ * (s - t₀)))) s := by
  have hf : HasDerivAt (fun s : ℝ => 2 * κ * (s - t₀)) (2 * κ) s := by
    simpa using ((hasDerivAt_id s).sub_const t₀).const_mul (2 * κ)
  have hpos : 0 < 2 * κ * (s - t₀) := by have : 0 < s - t₀ := by linarith
                                         positivity
  have h := hf.sqrt hpos.ne'
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with s' hs'
  have : 0 ≤ 2 * κ * (s' - t₀) := by
    have : 0 < s' - t₀ := by linarith [mem_Ioi.1 hs']
    positivity
  simp only [Real.coe_toNNReal _ this]

theorem continuous_heat_interp (hV : GoodField V M K) {g : Pt 2 → ℂ}
    (hg : ContDiff ℝ 2 g) (hqp : IsQP ξ g) (κ t₀ : ℝ) (x : Pt 2) :
    Continuous fun s => heatOp (Real.toNNReal (2 * κ * (s - t₀))) (g ∘ gflow V s t₀) x := by
  obtain ⟨C, hC⟩ := hqp.bdd hg.continuous
  have e : (fun s => heatOp (Real.toNNReal (2 * κ * (s - t₀))) (g ∘ gflow V s t₀) x) =
      fun s => ∫ ζ, g (gflow V s t₀ (x + Real.sqrt (Real.toNNReal (2 * κ * (s - t₀))) • ζ))
        ∂(gauss2 1) := by
    funext s
    exact heatOp_eq_scaled (hg.continuous.comp (hV.continuous_gflow s t₀)) _ x
  rw [e]
  refine continuous_of_dominated (bound := fun _ => C) (fun s => ?_)
    (fun s => Eventually.of_forall fun ζ => hC _) (integrable_const C)
    (Eventually.of_forall fun ζ => ?_)
  · have hA : Continuous (fun ζ : Pt 2 =>
        x + Real.sqrt (Real.toNNReal (2 * κ * (s - t₀))) • ζ) :=
      continuous_const.fun_add (continuous_const_smul _)
    simpa only [Function.comp_def] using
      (hg.continuous.comp ((hV.continuous_gflow s t₀).comp hA)).aestronglyMeasurable
  · refine continuous_iff_continuousAt.2 fun s₀ => ?_
    exact hg.continuous.continuousAt.comp (continuousAt_gflow_back hV t₀
      (continuous_const.fun_add ((continuous_sqrt_var κ t₀).fun_smul continuous_const)).continuousAt)

theorem hasDerivAt_heat_interp (hV : GoodField V M K) (hV2 : C2Field V K2 K3) {Lt : ℝ}
    (hLt : ∀ s s' x, ‖V s x - V s' x‖ ≤ Lt * |s - s'|)
    (hper : ∀ s x (m : Fin 2 → ℤ), V s (x + intVec m) = V s x) {g : Pt 2 → ℂ}
    (hg : ContDiff ℝ 2 g) (hqp : IsQP ξ g) {κ t₀ r : ℝ} (hκ : 0 ≤ κ) (hr : t₀ < r) (x : Pt 2) :
    HasDerivAt (fun s => heatOp (Real.toNNReal (2 * κ * (s - t₀))) (g ∘ gflow V s t₀) x)
      (κ • lap (heatOp (Real.toNNReal (2 * κ * (r - t₀))) (g ∘ gflow V r t₀)) x -
        heatOp (Real.toNNReal (2 * κ * (r - t₀))) (conv (V r) (g ∘ gflow V r t₀)) x) r := by
  obtain ⟨Cg, hCg⟩ := bdd_C2_of_isQP hqp hg
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hYC : ∀ s, ContDiff ℝ 2 (g ∘ gflow V s t₀) := fun s => hg.comp (gflow_C2 hV hV2 s t₀).1
  have hYq : ∀ s, IsQP ξ (g ∘ gflow V s t₀) := fun s => hqp.comp_lift (gflow_isLift hV hper s t₀)
  have hYcont : ∀ s, Continuous (g ∘ gflow V s t₀) := fun s => (hYC s).continuous
  have hVc : ∀ s, Continuous (V s) := fun s => (hV.lip s).continuous
  set σ : ℝ → ℝ := fun s => Real.sqrt (Real.toNNReal (2 * κ * (s - t₀))) with hσ
  have e : (fun s => heatOp (Real.toNNReal (2 * κ * (s - t₀))) (g ∘ gflow V s t₀) x) =
      fun s => ∫ ζ, g (gflow V s t₀ (x + σ s • ζ)) ∂(gauss2 1) := by
    funext s
    exact heatOp_eq_scaled (hYcont s) _ x
  rw [e]
  rcases hκ.lt_or_eq with hκ0 | hκ0
  · -- positive diffusivity: differentiate under the integral
    set σ' : ℝ → ℝ := fun s => 2 * κ / (2 * Real.sqrt (2 * κ * (s - t₀))) with hσ'
    have hrt : 0 < r - t₀ := by linarith
    set ε := (r - t₀) / 2 with hε
    have hε0 : 0 < ε := by positivity
    set m := Real.sqrt (κ * (r - t₀)) with hm
    have hm0 : 0 < m := Real.sqrt_pos.2 (by positivity)
    have hball : ∀ s ∈ Metric.ball r ε, t₀ < s ∧ |t₀ - s| ≤ 2 * (r - t₀) ∧ σ' s ≤ 2 * κ / (2 * m) := by
      intro s hs
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
      have h1 : t₀ < s := by linarith
      refine ⟨h1, ?_, ?_⟩
      · rw [abs_of_neg (by linarith)]; linarith
      · refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        have : m ≤ Real.sqrt (2 * κ * (s - t₀)) := Real.sqrt_le_sqrt (by nlinarith)
        linarith
    set L := Cg * Real.exp (K * (2 * (r - t₀))) with hL
    have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg 0).1
    have hDb : ∀ s ∈ Metric.ball r ε, ∀ y, ‖fderiv ℝ (g ∘ gflow V s t₀) y‖ ≤ L := by
      intro s hs y
      refine (norm_fderiv_comp_gflow_le hV hgd (fun y => (hCg y).2.1) s t₀ y).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCg0
      exact mul_le_mul_of_nonneg_left (hball s hs).2.1 K.2
    set F' : ℝ → Pt 2 → ℂ := fun s ζ =>
      fderiv ℝ (g ∘ gflow V s t₀) (x + σ s • ζ) (σ' s • ζ - V s (x + σ s • ζ)) with hF'
    have hAff (s : ℝ) : Continuous (fun ζ : Pt 2 => x + σ s • ζ) :=
      continuous_const.fun_add (continuous_const_smul _)
    have hIntc (s : ℝ) : Continuous (fun ζ : Pt 2 => g (gflow V s t₀ (x + σ s • ζ))) := by
      simpa only [Function.comp_def] using (hYcont s).comp (hAff s)
    have hFpc : Continuous (F' r) := by
      simpa only [hF', Function.comp_def] using
        ((((hYC r).continuous_fderiv (by norm_num)).comp (hAff r)).clm_apply
          ((continuous_const_smul (σ' r)).fun_sub ((hVc r).comp (hAff r))))
    have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gauss2 1) (x₀ := r)
      (F := fun s ζ => g (gflow V s t₀ (x + σ s • ζ))) (F' := F')
      (bound := fun ζ => L * (2 * κ / (2 * m) * ‖ζ‖ + M))
      (Metric.ball_mem_nhds r hε0)
      (Eventually.of_forall fun s => (hIntc s).aestronglyMeasurable)
      (Integrable.of_bound (hIntc r).aestronglyMeasurable Cg
        (Eventually.of_forall fun ζ => (hCg _).1))
      hFpc.aestronglyMeasurable
      (Eventually.of_forall fun ζ s hs => by
        refine ((fderiv ℝ (g ∘ gflow V s t₀) _).le_opNorm _).trans ?_
        refine mul_le_mul (hDb s hs _) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hDb s hs 0))
        refine (norm_sub_le _ _).trans (add_le_add ?_ (hV.bound s _))
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by simp only [hσ']; positivity)]
        exact mul_le_mul_of_nonneg_right (hball s hs).2.2 (norm_nonneg _))
      ((((integrable_norm_gauss2_one.const_mul (2 * κ / (2 * m))).add
        (integrable_const (M : ℝ))).const_mul L))
      (Eventually.of_forall fun ζ s hs => by
        have hy : HasDerivAt (fun s => x + σ s • ζ) (σ' s • ζ) s :=
          ((hasDerivAt_sqrt_var hκ0 (hball s hs).1).smul_const ζ).const_add x
        exact hV.hasDerivAt_comp_gflow_back hLt t₀ (((hYC s).differentiable (by norm_num)) _) hy)
    refine hmain.2.congr_deriv ?_
    have hvr : (Real.toNNReal (2 * κ * (r - t₀)) : ℝ) = 2 * κ * (r - t₀) :=
      Real.coe_toNNReal _ (by positivity)
    have hsq : 0 < Real.sqrt (2 * κ * (r - t₀)) := Real.sqrt_pos.2 (by positivity)
    have hkey := integral_fderiv_interp (hYC r) (hYq r) (hVc r) (hV.bound r)
      (Real.toNNReal (2 * κ * (r - t₀))) (σ' r) x
    simp only [hF', hσ]
    rw [hkey]
    congr 2
    rw [hσ', hvr]
    field_simp
  · -- zero diffusivity: pure transport
    subst hκ0
    have hσ0 : σ = fun _ => 0 := by funext s; simp [hσ]
    rw [hσ0]
    simp only [zero_smul, add_zero, mul_zero, zero_mul, Real.toNNReal_zero]
    have h := hV.hasDerivAt_comp_gflow_back hLt t₀ (g := g) (y := fun _ => x) (y' := 0) (s := r)
      (((hYC r).differentiable (by norm_num)) _) (hasDerivAt_const r x)
    have hint : ∀ s, ∫ _ζ : Pt 2, g (gflow V s t₀ x) ∂(gauss2 1) = g (gflow V s t₀ x) := fun s => by
      simp
    simp only [hint]
    refine h.congr_deriv ?_
    rw [heatOp_zero (continuous_conv (hVc r) ((hYC r).of_le (by norm_num))), zero_sub,
      map_neg, fderiv_apply_eq_sum_pd]
    rw [zero_sub]; rfl

end AnomDiss

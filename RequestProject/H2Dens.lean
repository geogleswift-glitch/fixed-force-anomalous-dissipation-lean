module

public import RequestProject.HeatInterp
public import RequestProject.Interpolation
public import RequestProject.EnergyStep

/-!
# The `H²` density

`h2Dens f = |f|² + ∑ᵢ |∂ᵢf|² + ∑ᵢⱼ |∂ᵢ∂ⱼf|²`, whose integral over the unit cell is `‖f‖²_{H²}`.
We also record the commutation of the heat operator with derivatives for `C¹` quasi-periodic
functions and the averaging identity `∫_{𝕋²} 𝔼[w(ζ) φ(x + ζ)] dx = 𝔼[w] ∫_{𝕋²} φ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal InnerProductSpace

noncomputable section

namespace AnomDiss

variable {ξ : Pt 2}

/-- The pointwise `H²` density of a function. -/
def h2Dens (f : Pt 2 → ℂ) (y : Pt 2) : ℝ :=
  ‖f y‖ ^ 2 + ∑ i, ‖pd i f y‖ ^ 2 + ∑ i, ∑ j, ‖pd i (pd j f) y‖ ^ 2

lemma h2Norm_eq (f : Pt 2 → ℂ) : h2Norm f = Real.sqrt (∫ y in cell 2, h2Dens f y) := rfl

lemma h2Dens_nonneg (f : Pt 2 → ℂ) (y : Pt 2) : 0 ≤ h2Dens f y := by
  unfold h2Dens; positivity

lemma isQP_pd2 {f : Pt 2 → ℂ} (hqp : IsQP ξ f) (hf : ContDiff ℝ 2 f) (i j : Fin 2) :
    IsQP ξ (pd i (pd j f)) :=
  (hqp.pd (hf.differentiable (by norm_num)) j).pd
    ((contDiff_pd_of_C2 f hf j).differentiable one_ne_zero) i

lemma continuous_h2Dens {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f) : Continuous (h2Dens f) := by
  unfold h2Dens
  refine ((hf.continuous.norm.pow 2).add (continuous_finset_sum _ fun i _ =>
    ((continuous_pd_of_C1 _ (hf.of_le (by norm_num)) i).norm.pow 2))).add
    (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      ((continuous_pd_of_C1 _ (contDiff_pd_of_C2 f hf j) i).norm.pow 2))

lemma periodic_h2Dens {f : Pt 2 → ℂ} (hqp : IsQP ξ f) (hf : ContDiff ℝ 2 f) :
    IsPeriodic (h2Dens f) := by
  intro x m
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  unfold h2Dens
  have h0 := hqp.periodic_norm_sq x m
  have h1 := fun i => (hqp.pd hd i).periodic_norm_sq x m
  have h2 := fun i j => (isQP_pd2 hqp hf i j).periodic_norm_sq x m
  simp only at h0 h1 h2
  simp only [h0, h1, h2]

lemma bdd_h2Dens {f : Pt 2 → ℂ} (hqp : IsQP ξ f) (hf : ContDiff ℝ 2 f) :
    ∃ C, ∀ x, h2Dens f x ≤ C := by
  have hq : IsQP 0 (fun x => (h2Dens f x : ℂ)) :=
    isQP_zero_iff.2 fun x m => by simp only [periodic_h2Dens hqp hf x m]
  obtain ⟨C, hC⟩ := hq.bdd (Complex.continuous_ofReal.comp (continuous_h2Dens hf))
  refine ⟨C, fun x => ?_⟩
  have := hC x
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

/-- A `C¹` quasi-periodic function is bounded together with its derivative. -/
lemma bdd_C1_of_isQP {f : Pt 2 → ℂ} (hqp : IsQP ξ f) (hf : ContDiff ℝ 1 f) :
    ∃ C, ∀ x, ‖f x‖ ≤ C ∧ ‖fderiv ℝ f x‖ ≤ C := by
  have hd : Differentiable ℝ f := hf.differentiable one_ne_zero
  obtain ⟨C₀, hC₀⟩ := hqp.bdd hf.continuous
  have hb1 : ∀ i, ∃ C, ∀ x, ‖pd i f x‖ ≤ C := fun i =>
    (hqp.pd hd i).bdd (continuous_pd_of_C1 _ hf i)
  choose C₁ hC₁ using hb1
  refine ⟨C₀ + (C₁ 0 + C₁ 1), fun x => ⟨?_, ?_⟩⟩
  · have := (norm_nonneg _).trans (hC₁ 0 x); have := (norm_nonneg _).trans (hC₁ 1 x)
    linarith [hC₀ x]
  · have h := norm_clm_pt2_le (fderiv ℝ f x)
    have e0 : fderiv ℝ f x (Pi.single 0 1) = pd 0 f x := rfl
    have e1 : fderiv ℝ f x (Pi.single 1 1) = pd 1 f x := rfl
    rw [e0, e1] at h
    have := hC₁ 0 x; have := hC₁ 1 x
    have := (norm_nonneg (f x)).trans (hC₀ x)
    linarith

/-- The heat operator commutes with partial derivatives on `C¹` quasi-periodic functions. -/
lemma pd_heatOp_C1 {f : Pt 2 → ℂ} (hqp : IsQP ξ f) (hf : ContDiff ℝ 1 f) (v : ℝ≥0) (i : Fin 2)
    (x : Pt 2) : pd i (heatOp v f) x = heatOp v (pd i f) x := by
  obtain ⟨C, hC⟩ := bdd_C1_of_isQP hqp hf
  have hfd : fderiv ℝ (heatOp v f) = fun x => ∫ ζ, fderiv ℝ f (x + ζ) ∂(gauss2 v) :=
    fderiv_gavg hf (fun x => (hC x).1) (fun x => (hC x).2) v
  unfold pd heatOp
  rw [show (fun x => ∫ ζ, f (x + ζ) ∂(gauss2 v)) = heatOp v f from rfl, hfd]
  simp only
  rw [ContinuousLinearMap.integral_apply (integrable_gauss2_of_bdd
    (hf.continuous_fderiv one_ne_zero) (fun x => (hC x).2) v x)]

/-- Averaging identity on the torus: `∫_{𝕋²} 𝔼[w(ζ) φ(x + ζ)] dx = 𝔼[w] ∫_{𝕋²} φ`. -/
lemma integral_cell_integral_translate {P : Measure (Pt 2)} [IsFiniteMeasure P] {w : Pt 2 → ℝ}
    (hw : Integrable w P) {φ : Pt 2 → ℝ} (hφ : Continuous φ) (hφp : IsPeriodic φ) :
    ∫ x in cell 2, ∫ ζ, w ζ * φ (x + ζ) ∂P = (∫ ζ, w ζ ∂P) * ∫ x in cell 2, φ x := by
  have hq : IsQP 0 (fun x => (φ x : ℂ)) := isQP_zero_iff.2 fun x m => by simp only [hφp x m]
  obtain ⟨C, hC⟩ := hq.bdd (Complex.continuous_ofReal.comp hφ)
  have hC' : ∀ x, ‖φ x‖ ≤ C := fun x => by simpa using hC x
  haveI : IsFiniteMeasure (volume.restrict (cell 2)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_cell_ne_top.lt_top⟩
  have hint : Integrable (Function.uncurry fun x ζ => w ζ * φ (x + ζ))
      ((volume.restrict (cell 2)).prod P) := by
    have hb : Integrable (fun p : Pt 2 × Pt 2 => w p.2 * C) ((volume.restrict (cell 2)).prod P) :=
      ((integrable_const (1 : ℝ)).mul_prod hw).mul_const C |>.congr
        (Eventually.of_forall fun p => by simp)
    refine Integrable.mono' (hb.norm.congr (Eventually.of_forall fun p => rfl)) ?_
      (Eventually.of_forall fun p => ?_)
    · exact (hw.aestronglyMeasurable.comp_snd).mul
        (hφ.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
    · show ‖w p.2 * φ (p.1 + p.2)‖ ≤ _
      rw [norm_mul]
      have h0 : 0 ≤ C := (norm_nonneg _).trans (hC' 0)
      rw [norm_mul, Real.norm_of_nonneg h0]
      exact mul_le_mul_of_nonneg_left (hC' _) (norm_nonneg _)
  rw [integral_integral_swap hint, ← integral_mul_const]
  congr 1; funext ζ
  rw [integral_const_mul, integral_cell_add_right_real φ hφ hφp ζ]

lemma norm_le_sqrt_h2Dens (f : Pt 2 → ℂ) (y : Pt 2) : ‖f y‖ ≤ Real.sqrt (h2Dens f y) := by
  refine Real.le_sqrt_of_sq_le ?_
  unfold h2Dens
  have h1 : 0 ≤ ∑ i, ‖pd i f y‖ ^ 2 := by positivity
  have h2 : 0 ≤ ∑ i, ∑ j, ‖pd i (pd j f) y‖ ^ 2 := by positivity
  linarith

lemma norm_pd_le_sqrt_h2Dens (f : Pt 2 → ℂ) (j : Fin 2) (y : Pt 2) :
    ‖pd j f y‖ ≤ Real.sqrt (h2Dens f y) := by
  refine Real.le_sqrt_of_sq_le ?_
  unfold h2Dens
  have h1 : ‖pd j f y‖ ^ 2 ≤ ∑ i, ‖pd i f y‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖pd i f y‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ j)
  have h2 : 0 ≤ ∑ i, ∑ j, ‖pd i (pd j f) y‖ ^ 2 := by positivity
  have h3 : 0 ≤ ‖f y‖ ^ 2 := by positivity
  linarith

lemma norm_pd2_le_sqrt_h2Dens (f : Pt 2 → ℂ) (i j : Fin 2) (y : Pt 2) :
    ‖pd i (pd j f) y‖ ≤ Real.sqrt (h2Dens f y) := by
  refine Real.le_sqrt_of_sq_le ?_
  unfold h2Dens
  have h1 : ‖pd i (pd j f) y‖ ^ 2 ≤ ∑ j', ‖pd i (pd j' f) y‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖pd i (pd j' f) y‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ j)
  have h2 : ∑ j', ‖pd i (pd j' f) y‖ ^ 2 ≤ ∑ i', ∑ j', ‖pd i' (pd j' f) y‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖pd i' (pd j' f) y‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i)
  have h3 : 0 ≤ ∑ i, ‖pd i f y‖ ^ 2 := by positivity
  have h4 : 0 ≤ ‖f y‖ ^ 2 := by positivity
  linarith

lemma pd_heatOp_fun {f : Pt 2 → ℂ} (hqp : IsQP ξ f) (hf : ContDiff ℝ 1 f) (v : ℝ≥0) (i : Fin 2) :
    pd i (heatOp v f) = heatOp v (pd i f) :=
  funext fun x => pd_heatOp_C1 hqp hf v i x

lemma pd2_heatOp {f : Pt 2 → ℂ} (hqp : IsQP ξ f) (hf : ContDiff ℝ 2 f) (v : ℝ≥0) (i j : Fin 2)
    (x : Pt 2) : pd i (pd j (heatOp v f)) x = heatOp v (pd i (pd j f)) x := by
  rw [pd_heatOp_fun hqp (hf.of_le (by norm_num)) v j]
  exact pd_heatOp_C1 (hqp.pd (hf.differentiable (by norm_num)) j) (contDiff_pd_of_C2 f hf j) v i x

lemma continuous_conv {u : Pt 2 → Pt 2} (hu : Continuous u) {f : Pt 2 → ℂ} (hf : ContDiff ℝ 1 f) :
    Continuous (conv u f) := by
  unfold conv
  exact continuous_finset_sum _ fun j _ => ((continuous_apply j).comp hu).smul
    (continuous_pd_of_C1 _ hf j)

lemma norm_conv_le {u : Pt 2 → Pt 2} {f : Pt 2 → ℂ} {M D : ℝ} (hu : ∀ y, ‖u y‖ ≤ M)
    (hf : ∀ j y, ‖pd j f y‖ ≤ D) (y : Pt 2) : ‖conv u f y‖ ≤ 2 * (M * D) := by
  unfold conv
  refine (norm_sum_le _ _).trans ?_
  have : ∀ j, ‖u y j • pd j f y‖ ≤ M * D := fun j => by
    rw [norm_smul]
    exact mul_le_mul ((norm_le_pi_norm (u y) j).trans (hu y)) (hf j y) (norm_nonneg _)
      ((norm_nonneg _).trans (hu y))
  simp only [Fin.sum_univ_two]
  linarith [this 0, this 1]

end AnomDiss

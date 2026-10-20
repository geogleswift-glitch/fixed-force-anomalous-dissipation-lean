module

public import RequestProject.ScalarExistenceFoundation

/-!
# Actual first-derivative smoothing of continuous periodic data

The proof uses smooth periodic convolution approximations and uniform convergence of
their heat gradients.  No PDE existence or regularity assumption is used.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal Convolution

noncomputable section

namespace AnomDiss

/-- Continuity and integer periodicity imply uniform continuity on the lifted torus. -/
theorem uniformContinuous_of_continuous_periodic {E : Type*} [PseudoMetricSpace E]
    {f : Pt 2 → E} (hf : Continuous f) (hp : IsPeriodic f) : UniformContinuous f := by
  let K : Set (Pt 2) := Icc (-1) 2
  have hu : UniformContinuousOn f K := isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  refine Metric.uniformContinuous_iff.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, ?_⟩
  intro x y hxy
  obtain ⟨a, ha, n, hx⟩ := exists_cell_rep x
  let b : Pt 2 := y - intVec n
  have hab : a - b = x - y := by dsimp [b]; rw [hx]; abel
  have hn : ‖b - a‖ < 1 := by
    rw [norm_sub_rev, hab]
    exact lt_of_lt_of_le hxy (min_le_right δ 1)
  have haK : a ∈ K := by
    exact ⟨fun i => by have := ha.1 i; simp at this ⊢; linarith,
      fun i => by have := ha.2 i; simp at this ⊢; linarith⟩
  have hbK : b ∈ K := by
    refine ⟨fun i => ?_, fun i => ?_⟩ <;>
      have hi : |b i - a i| < 1 := by
        rw [← Real.norm_eq_abs]
        exact lt_of_le_of_lt (norm_le_pi_norm (b - a) i) hn
    · have hai := ha.1 i
      have := (abs_lt.1 hi).1
      simp at hai ⊢
      linarith
    · have hai := ha.2 i
      have := (abs_lt.1 hi).2
      simp at hai ⊢
      linarith
  have hdist : dist a b < δ := by
    rw [dist_eq_norm, hab]
    exact lt_of_lt_of_le hxy (min_le_left δ 1)
  have hy : y = b + intVec n := by dsimp [b]; abel
  rw [hx, hy, hp a n, hp b n]
  exact hosc a haK b hbK hdist

/-- A uniformly continuous periodic input admits uniformly close smooth periodic inputs. -/
theorem exists_smooth_periodic_uniform_approx {f : Pt 2 → ℂ} (hf : UniformContinuous f)
    (hp : IsPeriodic f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Pt 2 → ℂ, ContDiff ℝ ∞ g ∧ IsPeriodic g ∧ ∀ x, ‖g x - f x‖ ≤ ε := by
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuous_iff.mp hf ε hε
  let φ : ContDiffBump (0 : Pt 2) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let g : Pt 2 → ℂ := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
  have hg : ContDiff ℝ ∞ g := φ.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed hf.continuous.locallyIntegrable
  refine ⟨g, hg, ?_, fun x => ?_⟩
  · intro x n
    unfold g convolution
    congr 1
    funext y
    rw [show x + intVec n - y = (x - y) + intVec n by abel, hp]
  · have ha := φ.dist_normed_convolution_le (μ := volume) hf.continuous.aestronglyMeasurable
      (x₀ := x) (ε := ε) (fun y hy => (hosc (Metric.mem_ball.1 hy)).le)
    simpa only [dist_eq_norm] using ha

/-- The two first-moment kernels assembled as a continuous real-linear derivative. -/
def heatGradientLinear (v : ℝ≥0) (f : Pt 2 → ℂ) (x : Pt 2) : Pt 2 →L[ℝ] ℂ :=
  ∑ i : Fin 2, (ContinuousLinearMap.proj i).smulRight (heatGradientKernel v f i x)

lemma heatGradientLinear_apply (v : ℝ≥0) (f : Pt 2 → ℂ) (x z : Pt 2) :
    heatGradientLinear v f x z = ∑ i : Fin 2, z i • heatGradientKernel v f i x := by
  simp [heatGradientLinear]

lemma heatGradientLinear_basis (v : ℝ≥0) (f : Pt 2 → ℂ) (x : Pt 2) (i : Fin 2) :
    heatGradientLinear v f x (Pi.single i 1) = heatGradientKernel v f i x := by
  rw [heatGradientLinear_apply]
  fin_cases i <;> simp [Fin.sum_univ_two]

/-- Uniform distance controls the full Gaussian derivative, in operator norm. -/
theorem heatGradientLinear_uniform_distance {f g : Pt 2 → ℂ} (hf : Continuous f)
    (hg : Continuous g) {Cf Cg D : ℝ} (hCf : ∀ x, ‖f x‖ ≤ Cf)
    (hCg : ∀ x, ‖g x‖ ≤ Cg) (hD : ∀ x, ‖f x - g x‖ ≤ D)
    (v : ℝ≥0) (x : Pt 2) :
    ‖heatGradientLinear v f x - heatGradientLinear v g x‖ ≤
      2 * (D * gmom 1 / Real.sqrt (v : ℝ)) := by
  have h := norm_clm_pt2_le (heatGradientLinear v f x - heatGradientLinear v g x)
  simp only [ContinuousLinearMap.sub_apply, heatGradientLinear_basis] at h
  have h0 := heatGradientKernel_uniform_distance hf hg hCf hCg hD v 0 x
  have h1 := heatGradientKernel_uniform_distance hf hg hCf hCg hD v 1 x
  linarith

/-- For smooth periodic data the heat derivative is the Gaussian kernel linear map. -/
theorem hasFDerivAt_heatOp_gradient_C1 {f : Pt 2 → ℂ} (hf : ContDiff ℝ 1 f)
    (hp : IsPeriodic f) {v : ℝ≥0} (hv : 0 < (v : ℝ)) (x : Pt 2) :
    HasFDerivAt (heatOp v f) (heatGradientLinear v f x) x := by
  have hqp : IsQP 0 f := isQP_zero_iff.2 hp
  obtain ⟨C, hC⟩ := bdd_C1_of_isQP hqp hf
  have hdiff : HasFDerivAt (heatOp v f) (fderiv ℝ (heatOp v f) x) x :=
    (hasFDerivAt_gavg hf (fun y => (hC y).1) (fun y => (hC y).2) v x).differentiableAt.hasFDerivAt
  have he : fderiv ℝ (heatOp v f) x = heatGradientLinear v f x := by
    apply ContinuousLinearMap.ext
    intro z
    have hz : z = z 0 • (Pi.single 0 1 : Pt 2) + z 1 • (Pi.single 1 1 : Pt 2) := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul, heatGradientLinear_apply, Fin.sum_univ_two]
    change z 0 • pd 0 (heatOp v f) x + z 1 • pd 1 (heatOp v f) x = _
    rw [pd_heatOp_eq_heatGradientKernel hqp hf hv, pd_heatOp_eq_heatGradientKernel hqp hf hv]
  rwa [he] at hdiff

/-- A positive heat step has the displayed Fréchet derivative even for continuous data.
Uniform continuity is enough; neither first derivatives nor Hölder derivatives of the
input are required. -/
theorem hasFDerivAt_heatOp_gradient {f : Pt 2 → ℂ} (hf : UniformContinuous f)
    (hp : IsPeriodic f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {v : ℝ≥0}
    (hv : 0 < (v : ℝ)) (x : Pt 2) :
    HasFDerivAt (heatOp v f) (heatGradientLinear v f x) x := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε0 : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    dsimp [ε]
    rw [div_le_iff₀ (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa [ε, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp h
  choose g hgs hgp hge using fun n => exists_smooth_periodic_uniform_approx hf hp (hε0 n)
  have hgC : ∀ n y, ‖g n y‖ ≤ C + 1 := by
    intro n y
    calc ‖g n y‖ = ‖(g n y - f y) + f y‖ := by rw [sub_add_cancel]
      _ ≤ ‖g n y - f y‖ + ‖f y‖ := norm_add_le _ _
      _ ≤ ε n + C := add_le_add (hge n y) (hC y)
      _ ≤ C + 1 := by linarith [hε1 n]
  have hH : ∀ n y, ‖heatOp v (g n) y - heatOp v f y‖ ≤ ε n := fun n y =>
    heatOp_uniform_distance (hgs n).continuous hf.continuous (hgC n) hC (hge n) v y
  have hHlim : ∀ y, Tendsto (fun n => heatOp v (g n) y) atTop (𝓝 (heatOp v f y)) := by
    intro y
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => hH n y) hεlim
  have hD : ∀ n y, ‖heatGradientLinear v (g n) y - heatGradientLinear v f y‖ ≤
      2 * (ε n * gmom 1 / Real.sqrt (v : ℝ)) := fun n y =>
    heatGradientLinear_uniform_distance (hgs n).continuous hf.continuous (hgC n) hC (hge n) v y
  have hDlim : Tendsto (fun n => 2 * (ε n * gmom 1 / Real.sqrt (v : ℝ))) atTop (𝓝 0) := by
    simpa only [zero_mul, zero_div, mul_zero] using
      ((hεlim.mul_const (gmom 1)).div_const (Real.sqrt (v : ℝ))).const_mul 2
  have hDu : TendstoUniformly (fun n y => heatGradientLinear v (g n) y)
      (heatGradientLinear v f) atTop := by
    refine Metric.tendstoUniformly_iff.2 fun η hη => ?_
    filter_upwards [hDlim.eventually (gt_mem_nhds hη)] with n hn
    intro y
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt (hD n y) hn
  exact hasFDerivAt_of_tendstoUniformly hDu
    (fun n y => hasFDerivAt_heatOp_gradient_C1 ((hgs n).of_le (by norm_num)) (hgp n) hv y)
    hHlim x

/-- The unnormalized first Gaussian moment is jointly continuous in variance and space. -/
theorem continuous_heatGradientMoment {f : Pt 2 → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (i : Fin 2) :
    Continuous fun p : ℝ≥0 × Pt 2 =>
      ∫ ζ, (ζ i : ℂ) * f (p.2 + Real.sqrt p.1 • ζ) ∂(gauss2 1) := by
  have hi : Integrable (fun ζ : Pt 2 => |ζ i|) (gauss2 1) :=
    integrable_gauss2_coord 1 i continuous_abs.aestronglyMeasurable integrable_abs_gaussianReal_std
  refine continuous_of_dominated (bound := fun ζ : Pt 2 => C * |ζ i|)
    (fun p => (integrable_heatGradientKernel_integrand hf hC p.1 i p.2).aestronglyMeasurable)
    (fun _ => Eventually.of_forall fun ζ => ?_) (hi.const_mul C)
    (Eventually.of_forall fun ζ => ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)).trans_eq (mul_comm _ _)
  · exact continuous_const.mul (hf.comp (continuous_snd.add
      ((Real.continuous_sqrt.comp (NNReal.continuous_coe.comp continuous_fst)).smul continuous_const)))

/-- The Gaussian heat derivative kernel is jointly continuous at positive variance. -/
theorem continuousAt_heatGradientKernel {f : Pt 2 → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (i : Fin 2) {p : ℝ≥0 × Pt 2} (hp : 0 < (p.1 : ℝ)) :
    ContinuousAt (fun q : ℝ≥0 × Pt 2 => heatGradientKernel q.1 f i q.2) p := by
  unfold heatGradientKernel
  have hsqrt : ContinuousAt (fun q : ℝ≥0 × Pt 2 => Real.sqrt (q.1 : ℝ)) p := by
    fun_prop
  exact (hsqrt.fun_inv₀ (Real.sqrt_pos.2 hp).ne').fun_smul
    (continuous_heatGradientMoment hf hC i).continuousAt

/-- Joint continuity of the kernel on the full open set of positive variances. -/
theorem continuousOn_heatGradientKernel {f : Pt 2 → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (i : Fin 2) :
    ContinuousOn (fun p : ℝ≥0 × Pt 2 => heatGradientKernel p.1 f i p.2)
      {p | 0 < (p.1 : ℝ)} := fun _ hp =>
  (continuousAt_heatGradientKernel hf hC i hp).continuousWithinAt

/-- The displayed derivative is continuous in space, so the positive heat step is `C¹`. -/
theorem contDiff_one_heatOp {f : Pt 2 → ℂ} (hf : UniformContinuous f)
    (hp : IsPeriodic f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {v : ℝ≥0}
    (hv : 0 < (v : ℝ)) : ContDiff ℝ 1 (heatOp v f) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt_heatOp_gradient hf hp hC hv x).differentiableAt, ?_⟩
  have he : fderiv ℝ (heatOp v f) = heatGradientLinear v f :=
    funext fun x => (hasFDerivAt_heatOp_gradient hf hp hC hv x).fderiv
  rw [he]
  unfold heatGradientLinear
  refine continuous_finset_sum _ fun i _ => ?_
  exact (ContinuousLinearMap.smulRightL ℝ (Pt 2) ℂ (ContinuousLinearMap.proj i)).continuous.comp
    (continuous_heatGradientKernel hf.continuous hC v i)

/-- Positive-time first-derivative smoothing for arbitrary continuous periodic input. -/
theorem hasFDerivAt_heatOp_continuous_periodic {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {v : ℝ≥0} (hv : 0 < (v : ℝ)) (x : Pt 2) :
    HasFDerivAt (heatOp v f) (heatGradientLinear v f x) x := by
  obtain ⟨C, hC⟩ := (isQP_zero_iff.2 hp).bdd hf
  exact hasFDerivAt_heatOp_gradient (uniformContinuous_of_continuous_periodic hf hp) hp hC hv x

/-- The positive heat step of a continuous torus function belongs to `C¹`. -/
theorem contDiff_one_heatOp_continuous_periodic {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {v : ℝ≥0} (hv : 0 < (v : ℝ)) : ContDiff ℝ 1 (heatOp v f) := by
  obtain ⟨C, hC⟩ := (isQP_zero_iff.2 hp).bdd hf
  exact contDiff_one_heatOp (uniformContinuous_of_continuous_periodic hf hp) hp hC hv

/-- The kernel formula is the actual partial derivative for continuous periodic data. -/
theorem pd_heatOp_continuous_periodic {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {v : ℝ≥0} (hv : 0 < (v : ℝ)) (i : Fin 2) (x : Pt 2) :
    pd i (heatOp v f) x = heatGradientKernel v f i x := by
  unfold pd
  rw [(hasFDerivAt_heatOp_continuous_periodic hf hp hv x).fderiv]
  exact heatGradientLinear_basis v f x i

/-- The genuine derivative smoothing bound now only needs continuity of the periodic input. -/
theorem norm_pd_heatOp_continuous_periodic_le {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {v : ℝ≥0}
    (hv : 0 < (v : ℝ)) (i : Fin 2) (x : Pt 2) :
    ‖pd i (heatOp v f) x‖ ≤ C * gmom 1 / Real.sqrt (v : ℝ) := by
  rw [pd_heatOp_continuous_periodic hf hp hv]
  exact norm_heatGradientKernel_le hf hC v i x

/-- Gaussian first moments are jointly continuous also for a continuous family of inputs. -/
theorem continuous_heatGradientMoment_with_param {A : Type*} [TopologicalSpace A]
    [FirstCountableTopology A]
    {F : A → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F)) {C : ℝ}
    (hC : ∀ a x, ‖F a x‖ ≤ C) (i : Fin 2) :
    Continuous fun p : A × ℝ≥0 × Pt 2 =>
      ∫ ζ, (ζ i : ℂ) * F p.1 (p.2.2 + Real.sqrt p.2.1 • ζ) ∂(gauss2 1) := by
  have hi : Integrable (fun ζ : Pt 2 => |ζ i|) (gauss2 1) :=
    integrable_gauss2_coord 1 i continuous_abs.aestronglyMeasurable integrable_abs_gaussianReal_std
  have hFa : ∀ a, Continuous (F a) := fun a =>
    hF.comp (continuous_const.prodMk continuous_id)
  refine continuous_of_dominated (bound := fun ζ : Pt 2 => C * |ζ i|)
    (fun p => (integrable_heatGradientKernel_integrand (hFa p.1) (hC p.1) p.2.1 i p.2.2).aestronglyMeasurable)
    (fun _ => Eventually.of_forall fun ζ => ?_) (hi.const_mul C)
    (Eventually.of_forall fun ζ => ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hC _ _) (abs_nonneg _)).trans_eq (mul_comm _ _)
  · exact continuous_const.mul (hF.comp (continuous_fst.prodMk
      ((continuous_snd.comp continuous_snd).add
        ((Real.continuous_sqrt.comp (NNReal.continuous_coe.comp
          (continuous_fst.comp continuous_snd))).smul continuous_const))))

/-- Joint continuity of the derivative kernel for a time-dependent continuous bounded source. -/
theorem continuousAt_heatGradientKernel_with_param {A : Type*} [TopologicalSpace A]
    [FirstCountableTopology A]
    {F : A → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F)) {C : ℝ}
    (hC : ∀ a x, ‖F a x‖ ≤ C) (i : Fin 2) {p : A × ℝ≥0 × Pt 2}
    (hp : 0 < (p.2.1 : ℝ)) :
    ContinuousAt (fun q : A × ℝ≥0 × Pt 2 => heatGradientKernel q.2.1 (F q.1) i q.2.2) p := by
  unfold heatGradientKernel
  have hsqrt : ContinuousAt (fun q : A × ℝ≥0 × Pt 2 => Real.sqrt (q.2.1 : ℝ)) p := by
    fun_prop
  exact (hsqrt.fun_inv₀ (Real.sqrt_pos.2 hp).ne').fun_smul
    (continuous_heatGradientMoment_with_param hF hC i).continuousAt

end AnomDiss

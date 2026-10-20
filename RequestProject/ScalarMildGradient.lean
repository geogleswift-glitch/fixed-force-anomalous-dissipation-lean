module

public import RequestProject.ScalarMildC1
public import RequestProject.ScalarDuhamelGradientContinuity
public import RequestProject.HeatEvolutionEndpoint

/-! # Reusable source bounds and joint spatial-gradient continuity for the mild solution -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

/-- The actual product sources appearing in the constructed mild equation are
uniformly spatially Hölder, with nonnegative constants and genuine periodicity. -/
theorem scalar_mild_product_sources_holder {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ)
    (hbper : ∀ i t, IsPeriodic (fun x => b i (t, x))) (hfper : IsPeriodic f)
    (hfc : ContDiff ℝ 1 (f : Pt 2 → ℂ))
    (hbholder : ∀ i, ∃ H, ∀ t : Icc (0 : ℝ) T, ∀ x y,
      ‖b i (t, x) - b i (t, y)‖ ≤ H * ‖x - y‖ ^ β)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u) :
    ∀ i, ∃ H, 0 ≤ H ∧
      (∀ s, IsPeriodic (extendSlabScalar hT (b i * u) s)) ∧
      ∀ s x y, ‖extendSlabScalar hT (b i * u) s x - extendSlabScalar hT (b i * u) s y‖ ≤
        H * ‖x - y‖ ^ β := by
  obtain ⟨Hf, _, hHf⟩ := periodic_C1_holder hfc hfper hβ₀.le hβ₁.le
  obtain ⟨Hu, hHu⟩ := scalar_mild_fixedPoint_spatial_holder hν hT hβ₀.le hβ₁ b f hbper hfper hHf hu
  have hHu' : ∀ t : Icc (0 : ℝ) T, ∀ x y,
      ‖u (t, x) - u (t, y)‖ ≤ max Hu 0 * ‖x - y‖ ^ β := by
    intro t x y
    exact (hHu t x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left Hu 0) (Real.rpow_nonneg (norm_nonneg _) _))
  have huper := global_scalar_mild_fixedPoint_periodic hν hT b f hbper hfper hu
  intro i
  obtain ⟨Hb, hHb⟩ := hbholder i
  have hHb' : ∀ (t : Icc (0 : ℝ) T) x y,
      ‖b i (t, x) - b i (t, y)‖ ≤ max Hb 0 * ‖x - y‖ ^ β := by
    intro t x y
    exact (hHb t x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
  let H := ‖b i‖ * max Hu 0 + ‖u‖ * max Hb 0
  refine ⟨H, add_nonneg (mul_nonneg (norm_nonneg _) (le_max_right _ _))
    (mul_nonneg (norm_nonneg _) (le_max_right _ _)), ?_, ?_⟩
  · intro s x m
    simp only [extendSlabScalar, BoundedContinuousFunction.mul_apply]
    have hb' : b i (projIcc 0 T hT s, x + intVec m) = b i (projIcc 0 T hT s, x) :=
      hbper i (projIcc 0 T hT s) x m
    have hu' : u (projIcc 0 T hT s, x + intVec m) = u (projIcc 0 T hT s, x) :=
      huper (projIcc 0 T hT s) x m
    rw [hb', hu']
  · intro s x y
    let τ := projIcc 0 T hT s
    change ‖b i (τ, x) * u (τ, x) - b i (τ, y) * u (τ, y)‖ ≤ _
    calc
      ‖b i (τ, x) * u (τ, x) - b i (τ, y) * u (τ, y)‖
          = ‖b i (τ, x) * (u (τ, x) - u (τ, y)) +
              (b i (τ, x) - b i (τ, y)) * u (τ, y)‖ := by congr 1; ring
      _ ≤ ‖b i (τ, x) * (u (τ, x) - u (τ, y))‖ +
            ‖(b i (τ, x) - b i (τ, y)) * u (τ, y)‖ := norm_add_le _ _
      _ ≤ H * ‖x - y‖ ^ β := by
        rw [norm_mul, norm_mul]
        have h₁ := mul_le_mul ((b i).norm_coe_le_norm (τ, x)) (hHu' τ x y)
          (norm_nonneg _) (norm_nonneg _)
        have h₂ := mul_le_mul (hHb' τ x y) (u.norm_coe_le_norm (τ, y))
          (norm_nonneg _) (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _))
        exact (add_le_add h₁ h₂).trans_eq (by dsimp [H]; ring)

lemma continuous_fderiv_heat_initial_C1 (ν : ℝ) {f : Pt 2 → ℂ} (hf : ContDiff ℝ 1 f)
    (hp : IsPeriodic f) :
    Continuous fun p : ℝ × Pt 2 => fderiv ℝ (heatOp (Real.toNNReal (2 * ν * p.1)) f) p.2 := by
  have hqp : IsQP 0 f := isQP_zero_iff.2 hp
  obtain ⟨C, hC⟩ := bdd_C1_of_isQP hqp hf
  have he : (fun p : ℝ × Pt 2 => fderiv ℝ (heatOp (Real.toNNReal (2 * ν * p.1)) f) p.2) =
      fun p => ∑ i : Fin 2, (ContinuousLinearMap.proj i).smulRight
        (heatOp (Real.toNNReal (2 * ν * p.1)) (pd i f) p.2) := by
    funext p
    apply ContinuousLinearMap.ext
    intro z
    rw [fderiv_apply_eq_sum_pd]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply]
    congr 1
    funext i
    rw [pd_heatOp_C1 hqp hf]
  rw [he]
  refine continuous_finset_sum _ fun i _ => ?_
  apply (ContinuousLinearMap.smulRightL ℝ (Pt 2) ℂ (ContinuousLinearMap.proj i)).continuous.comp
  have hpd : ∀ x, ‖pd i f x‖ ≤ C := fun x => pd_bound_of_fderiv (fun y => (hC y).2) i x
  exact (continuous_heatOp_variance_space (continuous_pd_of_C1 f hf i) hpd).comp
    (by fun_prop : Continuous (fun p : ℝ × Pt 2 => (Real.toNNReal (2 * ν * p.1), p.2)))

/-- The full Fréchet derivative of the constructed mild solution is jointly continuous on the slab. -/
theorem scalar_mild_fixedPoint_fderiv_continuous {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ)
    (hbper : ∀ i t, IsPeriodic (fun x => b i (t, x))) (hfper : IsPeriodic f)
    (hfc : ContDiff ℝ 1 (f : Pt 2 → ℂ))
    (hbholder : ∀ i, ∃ H, ∀ t : Icc (0 : ℝ) T, ∀ x y,
      ‖b i (t, x) - b i (t, y)‖ ≤ H * ‖x - y‖ ^ β)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u) :
    Continuous (fun p : ScalarTimeSlab T => fderiv ℝ (fun x => u (p.1, x)) p.2) := by
  choose H hH hper hholder using scalar_mild_product_sources_holder hν hT hβ₀ hβ₁ b f
    hbper hfper hfc hbholder hu
  have hD : ∀ i (t : Icc (0 : ℝ) T),
      ContDiff ℝ 1 (duhamelComponent ν (extendSlabScalar hT (b i * u)) i t) := by
    intro i t
    exact contDiff_one_duhamelComponent_holder hν (continuous_extendSlabScalar hT (b i * u))
      (hper i) (norm_extendSlabScalar_le hT (b i * u)) (hH i) hβ₀ (hholder i) i t.property.1
  have hcD : ∀ i, Continuous (fun p : ScalarTimeSlab T =>
      fderiv ℝ (duhamelComponent ν (extendSlabScalar hT (b i * u)) i p.1) p.2) := by
    intro i
    exact (continuousOn_fderiv_duhamelComponent_holder hν (continuous_extendSlabScalar hT (b i * u))
      (hper i) (norm_extendSlabScalar_le hT (b i * u)) (hH i) hβ₀ (hholder i) i hT).comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd) (fun p => p.1.property)
  have hheat : ∀ t : Icc (0 : ℝ) T,
      ContDiff ℝ 1 (heatOp (Real.toNNReal (2 * ν * (t : ℝ))) f) := by
    intro t
    obtain ⟨C, hC⟩ := bdd_C1_of_isQP (isQP_zero_iff.2 hfper) hfc
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_gavg hfc (fun y => (hC y).1) (fun y => (hC y).2) _ x).differentiableAt, ?_⟩
    exact (continuous_fderiv_heat_initial_C1 ν hfc hfper).comp (continuous_const.prodMk continuous_id)
  have he : (fun p : ScalarTimeSlab T => fderiv ℝ (fun x => u (p.1, x)) p.2) =
      fun p => fderiv ℝ (heatOp (Real.toNNReal (2 * ν * (p.1 : ℝ))) f) p.2 -
        ∑ i : Fin 2, fderiv ℝ (duhamelComponent ν (extendSlabScalar hT (b i * u)) i p.1) p.2 := by
    funext p
    have hu' : (fun x => u (p.1, x)) = fun x =>
        heatOp (Real.toNNReal (2 * ν * (p.1 : ℝ))) f x -
          ∑ i : Fin 2, duhamelComponent ν (extendSlabScalar hT (b i * u)) i p.1 x := by
      funext x
      have hh := congrArg (fun w : SlabScalar T => w (p.1, x)) hu
      simpa [scalarMildMap] using hh.symm
    rw [hu', fderiv_fun_sub ((hheat p.1).differentiable one_ne_zero p.2)
      ((ContDiff.sum fun i _ => hD i p.1).differentiable one_ne_zero p.2)]
    congr 1
    exact fderiv_fun_sum fun i _ => (hD i p.1).differentiable one_ne_zero p.2
  rw [he]
  exact ((continuous_fderiv_heat_initial_C1 ν hfc hfper).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).sub
      (continuous_finset_sum _ fun i _ => hcD i)

lemma bdd_fderiv_heat_initial_C1 (ν : ℝ) {f : Pt 2 → ℂ} (hf : ContDiff ℝ 1 f)
    (hp : IsPeriodic f) :
    ∃ C, 0 ≤ C ∧ ∀ t x,
      ‖fderiv ℝ (heatOp (Real.toNNReal (2 * ν * t)) f) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := bdd_C1_of_isQP (isQP_zero_iff.2 hp) hf
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0).1
  refine ⟨C, hC₀, fun t x => ?_⟩
  unfold heatOp
  rw [fderiv_gavg hf (fun y => (hC y).1) (fun y => (hC y).2)]
  simpa using norm_integral_le_of_norm_le_const
    (μ := gauss2 (Real.toNNReal (2 * ν * t)))
    (f := fun ζ => fderiv ℝ f (x + ζ)) (C := C)
    (Eventually.of_forall fun ζ => (hC (x + ζ)).2)

theorem scalar_mild_fixedPoint_fderiv_eq {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ)
    (hbper : ∀ i t, IsPeriodic (fun x => b i (t, x))) (hfper : IsPeriodic f)
    (hfc : ContDiff ℝ 1 (f : Pt 2 → ℂ))
    (hbholder : ∀ i, ∃ H, ∀ t : Icc (0 : ℝ) T, ∀ x y,
      ‖b i (t, x) - b i (t, y)‖ ≤ H * ‖x - y‖ ^ β)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u)
    (t : Icc (0 : ℝ) T) (x : Pt 2) :
    fderiv ℝ (fun y => u (t, y)) x =
      fderiv ℝ (heatOp (Real.toNNReal (2 * ν * (t : ℝ))) f) x -
        ∑ i : Fin 2, fderiv ℝ (duhamelComponent ν (extendSlabScalar hT (b i * u)) i t) x := by
  choose H hH hper hholder using scalar_mild_product_sources_holder hν hT hβ₀ hβ₁ b f
    hbper hfper hfc hbholder hu
  have hD : ∀ i, ContDiff ℝ 1 (duhamelComponent ν (extendSlabScalar hT (b i * u)) i t) := by
    intro i
    exact contDiff_one_duhamelComponent_holder hν (continuous_extendSlabScalar hT (b i * u))
      (hper i) (norm_extendSlabScalar_le hT (b i * u)) (hH i) hβ₀ (hholder i) i t.property.1
  obtain ⟨C, hC⟩ := bdd_C1_of_isQP (isQP_zero_iff.2 hfper) hfc
  have hd : DifferentiableAt ℝ (heatOp (Real.toNNReal (2 * ν * (t : ℝ))) f) x :=
    (hasFDerivAt_gavg hfc (fun y => (hC y).1) (fun y => (hC y).2) _ x).differentiableAt
  have he : (fun y => u (t, y)) = fun y =>
      heatOp (Real.toNNReal (2 * ν * (t : ℝ))) f y -
        ∑ i : Fin 2, duhamelComponent ν (extendSlabScalar hT (b i * u)) i t y := by
    funext y
    have hh := congrArg (fun w : SlabScalar T => w (t, y)) hu
    simpa [scalarMildMap] using hh.symm
  rw [he, fderiv_fun_sub hd ((ContDiff.sum fun i _ => hD i).differentiable one_ne_zero x)]
  congr 1
  exact fderiv_fun_sum fun i _ => (hD i).differentiable one_ne_zero x

/-- The actual spatial derivative is uniformly bounded throughout the finite slab. -/
theorem scalar_mild_fixedPoint_fderiv_bdd {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ)
    (hbper : ∀ i t, IsPeriodic (fun x => b i (t, x))) (hfper : IsPeriodic f)
    (hfc : ContDiff ℝ 1 (f : Pt 2 → ℂ))
    (hbholder : ∀ i, ∃ H, ∀ t : Icc (0 : ℝ) T, ∀ x y,
      ‖b i (t, x) - b i (t, y)‖ ≤ H * ‖x - y‖ ^ β)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u) :
    ∃ C, ∀ (t : Icc (0 : ℝ) T) x, ‖fderiv ℝ (fun y => u (t, y)) x‖ ≤ C := by
  choose H hH hper hholder using scalar_mild_product_sources_holder hν hT hβ₀ hβ₁ b f
    hbper hfper hfc hbholder hu
  obtain ⟨C₀, _, hC₀⟩ := bdd_fderiv_heat_initial_C1 ν hfc hfper
  let D : Fin 2 → ℝ := fun i => 2 * duhamelSpaceDerivativeScale ν (H i) β / β * T ^ (β / 2)
  have hD : ∀ i (t : Icc (0 : ℝ) T) x,
      ‖fderiv ℝ (duhamelComponent ν (extendSlabScalar hT (b i * u)) i t) x‖ ≤ D i := by
    intro i t x
    have h := norm_fderiv_duhamelComponent_holder_le hν (continuous_extendSlabScalar hT (b i * u))
      (hper i) (norm_extendSlabScalar_le hT (b i * u)) (hH i) hβ₀ (hholder i) i t.property.1 x
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow t.property.1 t.property.2 (by positivity))
      (div_nonneg (mul_nonneg (by norm_num)
        (duhamelSpaceDerivativeScale_nonneg hν.le (hH i))) hβ₀.le))
  refine ⟨C₀ + ∑ i : Fin 2, D i, fun t x => ?_⟩
  rw [scalar_mild_fixedPoint_fderiv_eq hν hT hβ₀ hβ₁ b f hbper hfper hfc hbholder hu t x]
  exact (norm_sub_le _ _).trans (add_le_add (hC₀ t x)
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hD i t x)))

end AnomDiss

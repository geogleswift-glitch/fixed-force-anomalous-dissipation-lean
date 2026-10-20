module

public import RequestProject.ScalarMildHolder
public import RequestProject.ScalarDuhamelDifferentiability

/-! # Actual first spatial derivatives of the constructed scalar mild solution -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

lemma bounded_C1_holder {f : Pt 2 → ℂ} (hf : ContDiff ℝ 1 f)
    {C₀ C₁ α : ℝ} (hC₁ : 0 ≤ C₁)
    (hbound : ∀ x, ‖f x‖ ≤ C₀) (hderiv : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (x y : Pt 2) :
    ‖f x - f y‖ ≤ ((2 * C₀) ^ (1 - α) * C₁ ^ α) * ‖x - y‖ ^ α := by
  have hA : ‖f x - f y‖ ≤ 2 * C₀ :=
    (norm_sub_le _ _).trans ((add_le_add (hbound x) (hbound y)).trans_eq (by ring))
  have hB : ‖f x - f y‖ ≤ C₁ * ‖x - y‖ :=
    (convex_univ : Convex ℝ (univ : Set (Pt 2))).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hf.differentiable one_ne_zero) z) (fun z _ => hderiv z) (mem_univ y) (mem_univ x)
  apply (le_rpow_interpolation (norm_nonneg _) hA hB hα₀ hα₁).trans_eq
  rw [Real.mul_rpow hC₁ (norm_nonneg _)]
  ring

/-- Periodic `C¹` data satisfy every global spatial Hölder exponent at most one. -/
lemma periodic_C1_holder {f : Pt 2 → ℂ} (hf : ContDiff ℝ 1 f) (hp : IsPeriodic f)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    ∃ H, 0 ≤ H ∧ ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ α := by
  obtain ⟨C, hC⟩ := bdd_C1_of_isQP (isQP_zero_iff.2 hp) hf
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0).1
  refine ⟨(2 * C) ^ (1 - α) * C ^ α,
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hC₀ _), ?_⟩
  exact bounded_C1_holder hf hC₀ (fun x => (hC x).1) (fun x => (hC x).2) hα₀ hα₁

/-- Spatial Hölder drift coefficients and `C¹` initial data give actual `C¹`
spatial slices of the unique constructed bounded mild solution. -/
theorem scalar_mild_fixedPoint_contDiff_one {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ)
    (hbper : ∀ i t, IsPeriodic (fun x => b i (t, x))) (hfper : IsPeriodic f)
    (hfc : ContDiff ℝ 1 (f : Pt 2 → ℂ))
    (hbholder : ∀ i, ∃ H, ∀ t : Icc (0 : ℝ) T, ∀ x y,
      ‖b i (t, x) - b i (t, y)‖ ≤ H * ‖x - y‖ ^ β)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u) :
    ∀ t : Icc (0 : ℝ) T, ContDiff ℝ 1 (fun x => u (t, x)) := by
  obtain ⟨Hf, _, hHf⟩ := periodic_C1_holder hfc hfper hβ₀.le hβ₁.le
  obtain ⟨Hu, hHu⟩ := scalar_mild_fixedPoint_spatial_holder hν hT hβ₀.le hβ₁ b f hbper hfper hHf hu
  have hHu' : ∀ t : Icc (0 : ℝ) T, ∀ x y,
      ‖u (t, x) - u (t, y)‖ ≤ max Hu 0 * ‖x - y‖ ^ β := by
    intro t x y
    exact (hHu t x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left Hu 0) (Real.rpow_nonneg (norm_nonneg _) _))
  choose Hb hHb using hbholder
  have hHb' : ∀ i (t : Icc (0 : ℝ) T) x y,
      ‖b i (t, x) - b i (t, y)‖ ≤ max (Hb i) 0 * ‖x - y‖ ^ β := by
    intro i t x y
    exact (hHb i t x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
  have huper := global_scalar_mild_fixedPoint_periodic hν hT b f hbper hfper hu
  have hper : ∀ i s, IsPeriodic (extendSlabScalar hT (b i * u) s) := by
    intro i s x m
    simp only [extendSlabScalar, BoundedContinuousFunction.mul_apply]
    have hb' : b i (projIcc 0 T hT s, x + intVec m) = b i (projIcc 0 T hT s, x) :=
      hbper i (projIcc 0 T hT s) x m
    have hu' : u (projIcc 0 T hT s, x + intVec m) = u (projIcc 0 T hT s, x) :=
      huper (projIcc 0 T hT s) x m
    rw [hb', hu']
  let H : Fin 2 → ℝ := fun i => ‖b i‖ * max Hu 0 + ‖u‖ * max (Hb i) 0
  have hH₀ : ∀ i, 0 ≤ H i := fun i =>
    add_nonneg (mul_nonneg (norm_nonneg _) (le_max_right _ _))
      (mul_nonneg (norm_nonneg _) (le_max_right _ _))
  have hholder : ∀ i s x y,
      ‖extendSlabScalar hT (b i * u) s x - extendSlabScalar hT (b i * u) s y‖ ≤
        H i * ‖x - y‖ ^ β := by
    intro i s x y
    let τ := projIcc 0 T hT s
    change ‖b i (τ, x) * u (τ, x) - b i (τ, y) * u (τ, y)‖ ≤ _
    calc
      ‖b i (τ, x) * u (τ, x) - b i (τ, y) * u (τ, y)‖
          = ‖b i (τ, x) * (u (τ, x) - u (τ, y)) +
              (b i (τ, x) - b i (τ, y)) * u (τ, y)‖ := by congr 1; ring
      _ ≤ ‖b i (τ, x) * (u (τ, x) - u (τ, y))‖ +
            ‖(b i (τ, x) - b i (τ, y)) * u (τ, y)‖ := norm_add_le _ _
      _ ≤ (‖b i‖ * max Hu 0 + ‖u‖ * max (Hb i) 0) * ‖x - y‖ ^ β := by
        rw [norm_mul, norm_mul]
        have h₁ := mul_le_mul ((b i).norm_coe_le_norm (τ, x)) (hHu' τ x y)
          (norm_nonneg _) (norm_nonneg _)
        have h₂ := mul_le_mul (hHb' i τ x y) (u.norm_coe_le_norm (τ, y))
          (norm_nonneg _) (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _))
        exact (add_le_add h₁ h₂).trans_eq (by ring)
  have hD : ∀ i (t : Icc (0 : ℝ) T),
      ContDiff ℝ 1 (duhamelComponent ν (extendSlabScalar hT (b i * u)) i t) := by
    intro i t
    exact contDiff_one_duhamelComponent_holder hν (continuous_extendSlabScalar hT (b i * u))
      (hper i) (norm_extendSlabScalar_le hT (b i * u)) (hH₀ i) hβ₀ (hholder i) i t.property.1
  intro t
  have he : (fun x => u (t, x)) =
      fun x => heatOp (Real.toNNReal (2 * ν * (t : ℝ))) f x -
        ∑ i : Fin 2, duhamelComponent ν (extendSlabScalar hT (b i * u)) i t x := by
    funext x
    have hh := congrArg (fun w : SlabScalar T => w (t, x)) hu
    simpa [scalarMildMap] using hh.symm
  rw [he]
  have hheat : ContDiff ℝ 1 (heatOp (Real.toNNReal (2 * ν * (t : ℝ))) f) := by
    rcases eq_or_lt_of_le t.property.1 with ht | ht
    · have he : heatOp (Real.toNNReal (2 * ν * (t : ℝ))) f = f := by
        rw [← ht]
        simp only [mul_zero, Real.toNNReal_zero]
        funext x
        exact heatOp_zero f.continuous x
      rw [he]
      exact hfc
    · have hv : 0 < (Real.toNNReal (2 * ν * (t : ℝ)) : ℝ) := by
        rw [Real.coe_toNNReal _ (by positivity)]
        positivity
      exact contDiff_one_heatOp_continuous_periodic f.continuous hfper hv
  exact hheat.sub (ContDiff.sum fun i _ => hD i t)

end AnomDiss

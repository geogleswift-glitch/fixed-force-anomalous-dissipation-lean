module

public import RequestProject.ScalarMildGradient
public import RequestProject.ScalarDuhamelGradientHolderLoss

/-! # Positive spatial Hölder regularity of the constructed mild solution's gradient -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

lemma fderiv_heatOp_C2_uniform_holder {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : IsPeriodic f) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    ∃ H, 0 ≤ H ∧ ∀ (v : ℝ≥0) x y,
      ‖fderiv ℝ (heatOp v f) x - fderiv ℝ (heatOp v f) y‖ ≤ H * ‖x - y‖ ^ α := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  choose H hH hHolder using fun i : Fin 2 => periodic_C1_holder
    (contDiff_pd_of_C2 f hf i) (isPeriodic_pd f hp i) hα₀ hα₁
  have hqp := isQP_zero_iff.2 hp
  obtain ⟨C, hC⟩ := bdd_C1_of_isQP hqp hf₁
  have hpd : ∀ i x, ‖pd i f x‖ ≤ C := fun i x => pd_bound_of_fderiv (fun y => (hC y).2) i x
  refine ⟨H 0 + H 1, add_nonneg (hH 0) (hH 1), fun v x y => ?_⟩
  have h := norm_clm_pt2_le (fderiv ℝ (heatOp v f) x - fderiv ℝ (heatOp v f) y)
  change ‖fderiv ℝ (heatOp v f) x - fderiv ℝ (heatOp v f) y‖ ≤
    ‖pd 0 (heatOp v f) x - pd 0 (heatOp v f) y‖ +
    ‖pd 1 (heatOp v f) x - pd 1 (heatOp v f) y‖ at h
  simp_rw [pd_heatOp_C1 hqp hf₁] at h
  have h₀ := heatOp_holder_distance (continuous_pd_of_C1 f hf₁ 0) (hpd 0) (hHolder 0) v x y
  have h₁ := heatOp_holder_distance (continuous_pd_of_C1 f hf₁ 1) (hpd 1) (hHolder 1) v x y
  exact (h.trans (add_le_add h₀ h₁)).trans_eq (by ring)

/-- The actual full spatial derivative of the constructed mild solution is uniformly
Hölder on the whole slab, at every positive exponent smaller than that of the drift. -/
theorem scalar_mild_fixedPoint_fderiv_spatial_holder_loss {ν T β α : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hα₀ : 0 ≤ α) (hαβ : α < β) (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ)
    (hbper : ∀ i t, IsPeriodic (fun x => b i (t, x))) (hfper : IsPeriodic f)
    (hfc : ContDiff ℝ 2 (f : Pt 2 → ℂ))
    (hbholder : ∀ i, ∃ H, ∀ t : Icc (0 : ℝ) T, ∀ x y,
      ‖b i (t, x) - b i (t, y)‖ ≤ H * ‖x - y‖ ^ β)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u) :
    ∃ H, 0 ≤ H ∧ ∀ (t : Icc (0 : ℝ) T) x y,
      ‖fderiv ℝ (fun z => u (t, z)) x - fderiv ℝ (fun z => u (t, z)) y‖ ≤ H * ‖x - y‖ ^ α := by
  have hf₁ : ContDiff ℝ 1 (f : Pt 2 → ℂ) := hfc.of_le (by norm_num)
  choose H hH hper hholder using scalar_mild_product_sources_holder hν hT hβ₀ hβ₁ b f
    hbper hfper hf₁ hbholder hu
  obtain ⟨C₀, hC₀, hheat⟩ := fderiv_heatOp_C2_uniform_holder hfc hfper hα₀ (hαβ.le.trans hβ₁.le)
  let D : Fin 2 → ℝ := fun i =>
    2 * duhamelGradientHolderLossScale ν (H i) β α / (β - α) * T ^ ((β - α) / 2)
  have hD₀ : ∀ i, 0 ≤ D i := by
    intro i
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num)
      (duhamelGradientHolderLossScale_nonneg hν.le (hH i))) (sub_pos.2 hαβ).le)
      (Real.rpow_nonneg hT _)
  have hD : ∀ i (t : Icc (0 : ℝ) T) x y,
      ‖fderiv ℝ (duhamelComponent ν (extendSlabScalar hT (b i * u)) i t) x -
        fderiv ℝ (duhamelComponent ν (extendSlabScalar hT (b i * u)) i t) y‖ ≤ D i * ‖x - y‖ ^ α := by
    intro i t x y
    have h := fderiv_duhamelComponent_holder_loss_distance hν
      (continuous_extendSlabScalar hT (b i * u)) (hper i) (norm_extendSlabScalar_le hT (b i * u))
      (hH i) hβ₀ hα₀ hαβ (hholder i) i t.property.1 x y
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow t.property.1 t.property.2 (by linarith))
      (div_nonneg (mul_nonneg (by norm_num)
        (duhamelGradientHolderLossScale_nonneg hν.le (hH i))) (sub_pos.2 hαβ).le)
  refine ⟨C₀ + ∑ i : Fin 2, D i, add_nonneg hC₀ (Finset.sum_nonneg fun i _ => hD₀ i), fun t x y => ?_⟩
  let v := Real.toNNReal (2 * ν * (t : ℝ))
  let A : Fin 2 → (Pt 2 →L[ℝ] ℂ) := fun i =>
    fderiv ℝ (duhamelComponent ν (extendSlabScalar hT (b i * u)) i t) x -
      fderiv ℝ (duhamelComponent ν (extendSlabScalar hT (b i * u)) i t) y
  calc
    ‖fderiv ℝ (fun z => u (t, z)) x - fderiv ℝ (fun z => u (t, z)) y‖
        = ‖(fderiv ℝ (heatOp v f) x - fderiv ℝ (heatOp v f) y) - ∑ i : Fin 2, A i‖ := by
      rw [scalar_mild_fixedPoint_fderiv_eq hν hT hβ₀ hβ₁ b f hbper hfper hf₁ hbholder hu t x,
        scalar_mild_fixedPoint_fderiv_eq hν hT hβ₀ hβ₁ b f hbper hfper hf₁ hbholder hu t y]
      unfold A v
      rw [Finset.sum_sub_distrib]
      congr 1
      abel
    _ ≤ ‖fderiv ℝ (heatOp v f) x - fderiv ℝ (heatOp v f) y‖ + ‖∑ i : Fin 2, A i‖ := norm_sub_le _ _
    _ ≤ C₀ * ‖x - y‖ ^ α + ∑ i : Fin 2, D i * ‖x - y‖ ^ α :=
      add_le_add (hheat v x y) ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hD i t x y))
    _ = _ := by
      rw [← Finset.sum_mul]
      ring

end AnomDiss

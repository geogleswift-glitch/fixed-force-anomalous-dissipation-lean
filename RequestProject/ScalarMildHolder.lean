module

public import RequestProject.ScalarGlobalMild
public import RequestProject.ScalarDuhamelHolder

/-! # The actual full-slab scalar mild solution is spatially Hölder -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

/-- The constructed bounded mild solution gains every spatial Hölder exponent
below one that is already satisfied by its initial data. -/
theorem scalar_mild_fixedPoint_spatial_holder {ν T α : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hα₀ : 0 ≤ α) (hα₁ : α < 1) (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ)
    (hbper : ∀ i t, IsPeriodic (fun x => b i (t, x))) (hfper : IsPeriodic f)
    {Hf : ℝ} (hHf : ∀ x y, ‖f x - f y‖ ≤ Hf * ‖x - y‖ ^ α)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u) :
    ∃ H, ∀ t : Icc (0 : ℝ) T, ∀ x y, ‖u (t, x) - u (t, y)‖ ≤ H * ‖x - y‖ ^ α := by
  have huper := global_scalar_mild_fixedPoint_periodic hν hT b f hbper hfper hu
  let D : Fin 2 → ℝ := fun i =>
    2 * duhamelFractionalScale ν ‖b i * u‖ α / (1 - α) * T ^ ((1 - α) / 2)
  have hDp : ∀ i s, IsPeriodic (extendSlabScalar hT (b i * u) s) := by
    intro i s x m
    simp only [extendSlabScalar, BoundedContinuousFunction.mul_apply]
    have hb' : b i (projIcc 0 T hT s, x + intVec m) = b i (projIcc 0 T hT s, x) :=
      hbper i (projIcc 0 T hT s) x m
    have hu' : u (projIcc 0 T hT s, x + intVec m) = u (projIcc 0 T hT s, x) :=
      huper (projIcc 0 T hT s) x m
    rw [hb', hu']
  have hD : ∀ i (t : Icc (0 : ℝ) T) x y,
      ‖duhamelComponent ν (extendSlabScalar hT (b i * u)) i t x -
        duhamelComponent ν (extendSlabScalar hT (b i * u)) i t y‖ ≤ D i * ‖x - y‖ ^ α := by
    intro i t x y
    have hh := duhamelComponent_fractional_distance hν (continuous_extendSlabScalar hT (b i * u))
      (hDp i) (norm_extendSlabScalar_le hT (b i * u)) hα₀ hα₁ i t.property.1 x y
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow t.property.1 t.property.2 (by linarith))
      (div_nonneg (mul_nonneg (by norm_num)
        (duhamelFractionalScale_nonneg hν.le (norm_nonneg _))) (by linarith))
  have he : ∀ t x, u (t, x) = heatOp (Real.toNNReal (2 * ν * (t : ℝ))) f x -
      ∑ i : Fin 2, duhamelComponent ν (extendSlabScalar hT (b i * u)) i t x := by
    intro t x
    have hp := congrArg (fun w : SlabScalar T => w (t, x)) hu
    simpa [scalarMildMap] using hp.symm
  refine ⟨Hf + ∑ i : Fin 2, D i, fun t x y => ?_⟩
  let v := Real.toNNReal (2 * ν * (t : ℝ))
  let A : Fin 2 → ℂ := fun i => duhamelComponent ν (extendSlabScalar hT (b i * u)) i t x -
    duhamelComponent ν (extendSlabScalar hT (b i * u)) i t y
  calc
    ‖u (t, x) - u (t, y)‖ = ‖(heatOp v f x - heatOp v f y) - ∑ i : Fin 2, A i‖ := by
      rw [he t x, he t y]
      unfold A v
      rw [Finset.sum_sub_distrib]
      congr 1
      abel
    _ ≤ ‖heatOp v f x - heatOp v f y‖ + ‖∑ i : Fin 2, A i‖ := norm_sub_le _ _
    _ ≤ Hf * ‖x - y‖ ^ α + ∑ i : Fin 2, D i * ‖x - y‖ ^ α := by
      apply add_le_add
      · exact heatOp_holder_distance f.continuous (fun z => f.norm_coe_le_norm z) hHf v x y
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hD i t x y)
    _ = _ := by
      rw [← Finset.sum_mul]
      ring

end AnomDiss

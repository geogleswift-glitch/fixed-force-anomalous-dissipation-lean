module

public import RequestProject.HeatDuhamelFoundation

/-!
# The actual Duhamel evolution law

Gaussian Fubini and the proved heat semigroup give the variation-of-constants
cocycle. This will identify time derivatives without requiring a time derivative
of the source.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

theorem heatOp_heatDuhamel {ν t h : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (hh : 0 ≤ h)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C) (x : Pt 2) :
    heatOp (Real.toNNReal (2 * ν * h)) (heatDuhamel ν F t) x =
      ∫ s in (0 : ℝ)..t, heatOp (Real.toNNReal (2 * ν * (t + h - s))) (F s) x := by
  let vh := Real.toNNReal (2 * ν * h)
  have hc : Continuous (fun p : Pt 2 × ℝ =>
      heatOp (Real.toNNReal (2 * ν * (t - p.2))) (F p.2) (x + p.1)) :=
    (continuous_heatOp_with_param hF hC).comp
      (by fun_prop : Continuous (fun p : Pt 2 × ℝ =>
        (p.2, Real.toNNReal (2 * ν * (t - p.2)), x + p.1)))
  have hi : Integrable (fun p : Pt 2 × ℝ =>
      heatOp (Real.toNNReal (2 * ν * (t - p.2))) (F p.2) (x + p.1))
      ((gauss2 vh).prod (volume.restrict (Ioc (0 : ℝ) t))) :=
    Integrable.of_bound hc.aestronglyMeasurable C
      (Eventually.of_forall fun p => norm_heatOp_le (hC p.2) _ _)
  change (∫ ζ, heatDuhamel ν F t (x + ζ) ∂(gauss2 vh)) = _
  simp only [heatDuhamel, intervalIntegral.integral_of_le ht]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
  change heatOp vh (heatOp (Real.toNNReal (2 * ν * (t - s))) (F s)) x = _
  have hFs : Continuous (F s) := hF.comp (continuous_const.prodMk continuous_id)
  rw [← heatOp_semigroup hFs (hC s)]
  congr 1
  have hts : 0 ≤ t - s := sub_nonneg.2 hs.2
  dsimp only [vh]
  rw [← Real.toNNReal_add (by positivity : 0 ≤ 2 * ν * h)
    (by positivity : 0 ≤ 2 * ν * (t - s))]
  congr 1
  ring

/-- The actual ordinary Duhamel integral advances by heat evolution plus the new source interval. -/
theorem heatDuhamel_cocycle {ν t h : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (hh : 0 ≤ h)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C) (x : Pt 2) :
    heatDuhamel ν F (t + h) x =
      heatOp (Real.toNNReal (2 * ν * h)) (heatDuhamel ν F t) x +
        ∫ s in t..(t + h), heatOp (Real.toNNReal (2 * ν * (t + h - s))) (F s) x := by
  have hc : Continuous (fun s : ℝ =>
      heatOp (Real.toNNReal (2 * ν * (t + h - s))) (F s) x) :=
    (continuous_heatOp_with_param hF hC).comp
      (by fun_prop : Continuous (fun s : ℝ =>
        (s, Real.toNNReal (2 * ν * (t + h - s)), x)))
  rw [heatOp_heatDuhamel hν ht hh hF hC]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 t) (hc.intervalIntegrable t (t + h))).symm

end AnomDiss

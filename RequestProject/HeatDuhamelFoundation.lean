module

public import RequestProject.HeatEvolutionEndpoint

/-!
# Heat Duhamel integration for ordinary sources

This operator uses the genuine Gaussian average of the source. It is the
nondivergence counterpart of `duhamelComponent`, and will be used after the mild
scalar solution has a continuous spatial gradient.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-- Joint continuity of actual heat averaging for a bounded continuous source family. -/
theorem continuous_heatOp_with_param {A : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] {F : A → Pt 2 → ℂ}
    (hF : Continuous (Function.uncurry F)) {C : ℝ} (hC : ∀ a x, ‖F a x‖ ≤ C) :
    Continuous (fun p : A × ℝ≥0 × Pt 2 => heatOp p.2.1 (F p.1) p.2.2) := by
  have hFa (a : A) : Continuous (F a) :=
    hF.comp (continuous_const.prodMk continuous_id)
  simp_rw [heatOp_eq_scaled (hFa _)]
  refine continuous_of_dominated (bound := fun _ => C)
    (fun p => by
      have hA : Continuous (fun ζ : Pt 2 => p.2.2 + Real.sqrt p.2.1 • ζ) :=
        continuous_const.fun_add (continuous_const_smul _)
      simpa only [Function.comp_def] using ((hFa p.1).comp hA).aestronglyMeasurable)
    (fun _ => Eventually.of_forall fun ζ => hC _ _)
    (integrable_const C) (Eventually.of_forall fun ζ => ?_)
  have hA : Continuous (fun p : A × ℝ≥0 × Pt 2 => p.2.2 + Real.sqrt p.2.1 • ζ) :=
    (continuous_snd.comp continuous_snd).fun_add
      ((Real.continuous_sqrt.comp (NNReal.continuous_coe.comp
        (continuous_fst.comp continuous_snd))).fun_smul (continuous_const (y := ζ)))
  simpa only [Function.comp_def, Function.uncurry] using hF.comp (continuous_fst.prodMk hA)

/-- The actual ordinary-source variation-of-constants integral. -/
def heatDuhamel (ν : ℝ) (F : ℝ → Pt 2 → ℂ) (t : ℝ) (x : Pt 2) : ℂ :=
  ∫ s in (0 : ℝ)..t, heatOp (Real.toNNReal (2 * ν * (t - s))) (F s) x

theorem continuous_heatDuhamel (ν : ℝ) {F : ℝ → Pt 2 → ℂ}
    (hF : Continuous (Function.uncurry F)) {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C) :
    Continuous (Function.uncurry (heatDuhamel ν F)) := by
  have hc : Continuous (fun p : (ℝ × Pt 2) × ℝ =>
      heatOp (Real.toNNReal (2 * ν * (p.1.1 - p.2))) (F p.2) p.1.2) :=
    (continuous_heatOp_with_param hF hC).comp
      (by fun_prop : Continuous (fun p : (ℝ × Pt 2) × ℝ =>
        (p.2, Real.toNNReal (2 * ν * (p.1.1 - p.2)), p.1.2)))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hc continuous_fst

theorem intervalIntegrable_heatDuhamel_kernel (ν : ℝ) {F : ℝ → Pt 2 → ℂ}
    (hF : Continuous (Function.uncurry F)) {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (t : ℝ) (x : Pt 2) :
    IntervalIntegrable (fun s =>
      heatOp (Real.toNNReal (2 * ν * (t - s))) (F s) x) volume 0 t := by
  have hc : Continuous (fun s =>
      heatOp (Real.toNNReal (2 * ν * (t - s))) (F s) x) :=
    (continuous_heatOp_with_param hF hC).comp
      (by fun_prop : Continuous (fun s : ℝ =>
        (s, Real.toNNReal (2 * ν * (t - s)), x)))
  exact hc.intervalIntegrable _ _

theorem norm_heatDuhamel_le (ν : ℝ) {F : ℝ → Pt 2 → ℂ} {C : ℝ}
    (hC : ∀ s x, ‖F s x‖ ≤ C) (t : ℝ) (x : Pt 2) :
    ‖heatDuhamel ν F t x‖ ≤ C * |t| := by
  simpa only [heatDuhamel, sub_zero] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (fun s _ => norm_heatOp_le (hC s) _ x))

@[simp] theorem heatDuhamel_zero (ν : ℝ) (F : ℝ → Pt 2 → ℂ) (x : Pt 2) :
    heatDuhamel ν F 0 x = 0 := by simp [heatDuhamel]

theorem heatDuhamel_periodic (ν : ℝ) {F : ℝ → Pt 2 → ℂ}
    (hp : ∀ s, IsPeriodic (F s)) (t : ℝ) : IsPeriodic (heatDuhamel ν F t) := by
  intro x m
  unfold heatDuhamel
  congr 1
  funext s
  exact (isQP_zero_iff.1 (heatOp_isQP (isQP_zero_iff.2 (hp s)) _)) x m

end AnomDiss

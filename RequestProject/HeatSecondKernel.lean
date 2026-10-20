module

public import RequestProject.HeatDuhamelFoundation

/-!
# Joint continuity of actual second heat derivatives

Two half-variance heat steps express the Hessian through two Gaussian first
moments. The moments are bounded and continuous even at zero variance; their
scalar prefactor is continuous at every positive variance.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

def gaussianFirstMomentAverage (v : ℝ≥0) (f : Pt 2 → ℂ) (i : Fin 2) (x : Pt 2) : ℂ :=
  ∫ ζ, (ζ i : ℂ) * f (x + Real.sqrt v • ζ) ∂(gauss2 1)

theorem norm_gaussianFirstMomentAverage_le {f : Pt 2 → ℂ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (v : ℝ≥0) (i : Fin 2) (x : Pt 2) :
    ‖gaussianFirstMomentAverage v f i x‖ ≤ C * gmom 1 := by
  have hi : Integrable (fun ζ : Pt 2 => |ζ i|) (gauss2 1) :=
    integrable_gauss2_coord 1 i continuous_abs.aestronglyMeasurable integrable_abs_gaussianReal_std
  have hm : (∫ ζ : Pt 2, |ζ i| ∂(gauss2 1)) = gmom 1 := by
    rw [integral_gauss2_coord 1 i continuous_abs.aestronglyMeasurable]
    simp [gmom]
  calc
    ‖gaussianFirstMomentAverage v f i x‖ ≤
        ∫ ζ, ‖(ζ i : ℂ) * f (x + Real.sqrt v • ζ)‖ ∂(gauss2 1) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ζ, C * |ζ i| ∂(gauss2 1) := by
      refine integral_mono (integrable_heatGradientKernel_integrand hf hC v i x).norm
        (hi.const_mul C) fun ζ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)).trans_eq (mul_comm _ _)
    _ = C * gmom 1 := by rw [integral_const_mul, hm]

theorem continuous_gaussianFirstMomentAverage_with_param {A : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] {F : A → Pt 2 → ℂ}
    (hF : Continuous (Function.uncurry F)) {C : ℝ} (hC : ∀ a x, ‖F a x‖ ≤ C)
    (i : Fin 2) :
    Continuous (fun p : A × ℝ≥0 × Pt 2 =>
      gaussianFirstMomentAverage p.2.1 (F p.1) i p.2.2) :=
  continuous_heatGradientMoment_with_param hF hC i

def gaussianSecondMomentAverage (v : ℝ≥0) (f : Pt 2 → ℂ)
    (i j : Fin 2) (x : Pt 2) : ℂ :=
  gaussianFirstMomentAverage v (gaussianFirstMomentAverage v f j) i x

theorem continuous_gaussianSecondMomentAverage_with_param {A : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] {F : A → Pt 2 → ℂ}
    (hF : Continuous (Function.uncurry F)) {C : ℝ} (hC : ∀ a x, ‖F a x‖ ≤ C)
    (i j : Fin 2) :
    Continuous (fun p : A × ℝ≥0 × Pt 2 =>
      gaussianSecondMomentAverage p.2.1 (F p.1) i j p.2.2) := by
  let G : (A × ℝ≥0) → Pt 2 → ℂ := fun p => gaussianFirstMomentAverage p.2 (F p.1) j
  have hG : Continuous (Function.uncurry G) :=
    (continuous_gaussianFirstMomentAverage_with_param hF hC j).comp
      (by fun_prop : Continuous (fun p : (A × ℝ≥0) × Pt 2 => (p.1.1, p.1.2, p.2)))
  have hGb (p : A × ℝ≥0) (x : Pt 2) : ‖G p x‖ ≤ C * gmom 1 :=
    norm_gaussianFirstMomentAverage_le
      (hF.comp (continuous_const.prodMk continuous_id)) (hC p.1) p.2 j x
  exact (continuous_gaussianFirstMomentAverage_with_param hG hGb i).comp
    (by fun_prop : Continuous (fun p : A × ℝ≥0 × Pt 2 => ((p.1, p.2.1), p.2.1, p.2.2)))

theorem heatGradientKernel_comp_eq_secondMoment (v : ℝ≥0) (f : Pt 2 → ℂ)
    (i j : Fin 2) (x : Pt 2) :
    heatGradientKernel v (heatGradientKernel v f j) i x =
      (Real.sqrt (v : ℝ))⁻¹ ^ 2 • gaussianSecondMomentAverage v f i j x := by
  unfold heatGradientKernel gaussianSecondMomentAverage gaussianFirstMomentAverage
  have he : (fun ζ : Pt 2 => (ζ i : ℂ) *
      ((Real.sqrt (v : ℝ))⁻¹ •
        ∫ η, (η j : ℂ) * f (x + Real.sqrt v • ζ + Real.sqrt v • η) ∂(gauss2 1))) =
      fun ζ : Pt 2 => (Real.sqrt (v : ℝ))⁻¹ •
        ((ζ i : ℂ) *
          ∫ η, (η j : ℂ) * f (x + Real.sqrt v • ζ + Real.sqrt v • η) ∂(gauss2 1)) := by
    funext ζ
    rw [mul_smul_comm]
  rw [he, integral_smul, smul_smul, pow_two]

/-- Both actual coordinate derivatives equal the two-moment formula at positive variance. -/
theorem pd2_heatOp_eq_secondMoment {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {v : ℝ≥0} (hv : 0 < (v : ℝ)) (i j : Fin 2) (x : Pt 2) :
    pd i (pd j (heatOp v f)) x =
      (Real.sqrt ((v : ℝ) / 2))⁻¹ ^ 2 • gaussianSecondMomentAverage (v / 2) f i j x := by
  let w : ℝ≥0 := v / 2
  have hw : 0 < (w : ℝ) := by dsimp [w]; simpa using half_pos hv
  have hs : w + w = v := by dsimp [w]; ring
  have hgp : IsQP 0 (heatOp w f) := heatOp_isQP (isQP_zero_iff.2 hp) w
  have hgc : ContDiff ℝ 1 (heatOp w f) := contDiff_one_heatOp_continuous_periodic hf hp hw
  have he : heatOp v f = heatOp w (heatOp w f) := by
    rw [← hs]
    funext y
    exact heatOp_semigroup_periodic hf hp w w y
  have hgj : IsPeriodic (pd j (heatOp w f)) :=
    isQP_zero_iff.1 (hgp.pd (hgc.differentiable one_ne_zero) j)
  have hder : pd j (heatOp w f) = heatGradientKernel w f j :=
    funext fun y => pd_heatOp_continuous_periodic hf hp hw j y
  rw [he, pd_heatOp_fun hgp hgc w j,
    pd_heatOp_continuous_periodic (continuous_pd_of_C1 _ hgc j) hgj hw i x,
    hder, heatGradientKernel_comp_eq_secondMoment]
  rfl

/-- The actual Hessian of a heat average is jointly continuous at positive variance. -/
theorem continuousAt_pd2_heatOp_with_param {A : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] {F : A → Pt 2 → ℂ}
    (hF : Continuous (Function.uncurry F)) {C : ℝ} (hC : ∀ a x, ‖F a x‖ ≤ C)
    (hp : ∀ a, IsPeriodic (F a)) (i j : Fin 2) {p : A × ℝ≥0 × Pt 2}
    (hv : 0 < (p.2.1 : ℝ)) :
    ContinuousAt (fun q : A × ℝ≥0 × Pt 2 =>
      pd i (pd j (heatOp q.2.1 (F q.1))) q.2.2) p := by
  have hw : 0 < (p.2.1 : ℝ) / 2 := half_pos hv
  have hc : ContinuousAt (fun q : A × ℝ≥0 × Pt 2 =>
      (Real.sqrt ((q.2.1 : ℝ) / 2))⁻¹ ^ 2) p :=
    ((by fun_prop : ContinuousAt
      (fun q : A × ℝ≥0 × Pt 2 => Real.sqrt ((q.2.1 : ℝ) / 2)) p).inv₀
      (Real.sqrt_pos.2 hw).ne').pow 2
  have hm : ContinuousAt (fun q : A × ℝ≥0 × Pt 2 =>
      gaussianSecondMomentAverage (q.2.1 / 2) (F q.1) i j q.2.2) p :=
    ((continuous_gaussianSecondMomentAverage_with_param hF hC i j).comp
      (by fun_prop : Continuous (fun q : A × ℝ≥0 × Pt 2 =>
        (q.1, q.2.1 / 2, q.2.2)))).continuousAt
  apply (hc.smul hm).congr_of_eventuallyEq
  have hpos : ∀ᶠ q : A × ℝ≥0 × Pt 2 in 𝓝 p, 0 < (q.2.1 : ℝ) :=
    (isOpen_lt continuous_const
      (NNReal.continuous_coe.comp (continuous_fst.comp continuous_snd))).mem_nhds hv
  filter_upwards [hpos] with q hq
  exact pd2_heatOp_eq_secondMoment
    (hF.comp (continuous_const.prodMk continuous_id)) (hp q.1) hq i j q.2.2

end AnomDiss

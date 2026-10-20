module

public import RequestProject.HeatInterpDeriv
public import RequestProject.ScalarHeatHigherSmoothing

/-!
# Time evolution of the genuine Gaussian heat average

The existing heat–transport differentiation theorem is specialized to the zero
field. A positive fixed heat step and the actual semigroup identity then remove
the differentiability requirement on the initial periodic input.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

lemma goodField_zero : GoodField (fun (_ : ℝ) (_ : Pt 2) => (0 : Pt 2)) 0 0 where
  cont _ := continuous_const
  bound _ _ := by simp
  lip _ := by intro x y; simp

lemma c2Field_zero : C2Field (fun (_ : ℝ) (_ : Pt 2) => (0 : Pt 2)) 0 0 where
  diff _ := contDiff_const
  d2 _ _ := by simp
  nonneg3 := le_rfl
  lip2 _ _ _ := by simp
  c1 _ := by simpa using (continuous_const : Continuous (fun _ : ℝ =>
    (0 : Pt 2 →L[ℝ] Pt 2)))
  c2 _ := by simpa using (continuous_const : Continuous (fun _ : ℝ =>
    (0 : Pt 2 →L[ℝ] Pt 2 →L[ℝ] Pt 2)))

lemma gflow_zero (s t : ℝ) (x : Pt 2) :
    gflow (fun (_ : ℝ) (_ : Pt 2) => (0 : Pt 2)) s t x = x := by
  have h := goodField_zero.norm_gflow_sub_le s t x
  simpa only [NNReal.coe_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] using h

/-- The actual heat average satisfies the heat equation at positive times for `C²` data. -/
theorem hasDerivAt_heatOp_C2 {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : IsPeriodic f) {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (x : Pt 2) :
    HasDerivAt (fun s => heatOp (Real.toNNReal (2 * ν * s)) f x)
      (ν • lap (heatOp (Real.toNNReal (2 * ν * t)) f) x) t := by
  have h := hasDerivAt_heat_interp goodField_zero c2Field_zero
    (Lt := 0) (by intro s s' y; simp) (by intro s y m; rfl)
    hf (isQP_zero_iff.2 hp) hν ht x
  simpa [gflow_zero, Function.comp_def, conv, heatOp] using h

/-- Positive-time heat evolution needs only continuous periodic initial data. -/
theorem hasDerivAt_heatOp_continuous_periodic {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (x : Pt 2) :
    HasDerivAt (fun s => heatOp (Real.toNNReal (2 * ν * s)) f x)
      (ν • lap (heatOp (Real.toNNReal (2 * ν * t)) f) x) t := by
  rcases hν.eq_or_lt with hν | hν
  · subst ν
    simpa [heatOp_zero hf] using (hasDerivAt_const t (f x))
  let a : ℝ := t / 2
  have ha : 0 < a := half_pos ht
  have hat : a < t := by dsimp [a]; linarith
  let v₀ : ℝ≥0 := Real.toNNReal (2 * ν * a)
  have hv₀ : 0 < (v₀ : ℝ) := by
    change 0 < ((Real.toNNReal (2 * ν * a) : ℝ≥0) : ℝ)
    rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 2 * ν * a)]
    positivity
  let g := heatOp v₀ f
  have hg : ContDiff ℝ 2 g := contDiff_two_heatOp_continuous_periodic hf hp hv₀
  have hgp : IsPeriodic g := isQP_zero_iff.1 (heatOp_isQP (isQP_zero_iff.2 hp) v₀)
  have he (s : ℝ) (hs : a < s) :
      heatOp (Real.toNNReal (2 * ν * s)) f =
        heatOp (Real.toNNReal (2 * ν * (s - a))) g := by
    have hsa : 0 < s - a := sub_pos.2 hs
    have hsv : 0 ≤ 2 * ν * (s - a) := by positivity
    have hav : 0 ≤ 2 * ν * a := by positivity
    have hsplit : Real.toNNReal (2 * ν * s) =
        Real.toNNReal (2 * ν * (s - a)) + v₀ := by
      dsimp [v₀]
      rw [← Real.toNNReal_add hsv hav]
      congr 1
      ring
    rw [hsplit]
    funext y
    exact heatOp_semigroup_periodic hf hp _ _ y
  have hd := (hasDerivAt_heatOp_C2 hg hgp hν.le (sub_pos.2 hat) x).scomp t
    ((hasDerivAt_id t).sub_const a)
  simp only [Function.comp_def, one_smul] at hd
  rw [he t hat]
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hat] with s hs
  exact congrFun (he s hs) x

end AnomDiss

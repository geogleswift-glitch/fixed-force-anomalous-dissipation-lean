module

public import Mathlib

/-! A shrinking interval contributes its integrand at the collapsed endpoint,
even when the integrand also depends continuously on the interval length. -/

@[expose] public section

open MeasureTheory Set Filter Topology

noncomputable section

namespace AnomDiss

theorem hasDerivAt_parametric_short_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {G : ℝ × ℝ → E} (hG : Continuous G) :
    HasDerivAt (fun h : ℝ => ∫ r in (0 : ℝ)..h, G (h, r)) (G (0, 0)) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨δ, hδ, hl⟩ := Metric.continuousAt_iff.1 (hG.continuousAt (x := (0, 0))) ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  have hh' : |h| < δ := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh
  have hsrc (r : ℝ) (hr : r ∈ Set.uIoc (0 : ℝ) h) : ‖G (h, r) - G (0, 0)‖ ≤ ε := by
    have hrabs : |r| ≤ |h| := by
      rcases le_total (0 : ℝ) h with hpos | hneg
      · rw [uIoc_of_le hpos] at hr
        rw [abs_of_nonneg hr.1.le, abs_of_nonneg hpos]
        exact hr.2
      · rw [uIoc_of_ge hneg] at hr
        rw [abs_of_nonpos hr.2, abs_of_nonpos hneg]
        linarith [hr.1]
    have hdist : dist (h, r) ((0, 0) : ℝ × ℝ) < δ := by
      simpa only [Prod.dist_eq, Real.dist_eq, sub_zero] using max_lt hh' (hrabs.trans_lt hh')
    exact (show ‖G (h, r) - G (0, 0)‖ < ε by
      simpa only [dist_eq_norm] using hl hdist).le
  have hi : IntervalIntegrable (fun r : ℝ => G (h, r)) volume 0 h :=
    (hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have he : (∫ r in (0 : ℝ)..h, G (h, r)) - h • G (0, 0) =
      ∫ r in (0 : ℝ)..h, G (h, r) - G (0, 0) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero]
  simpa only [intervalIntegral.integral_same, sub_zero, Real.norm_eq_abs, he] using
    (intervalIntegral.norm_integral_le_of_norm_le_const hsrc)

end AnomDiss

module

public import RequestProject.HeatDuhamelSpatial
public import RequestProject.HeatDuhamelSemigroup
public import RequestProject.ParametricShortIntegral

/-!
# Actual right time derivatives of heat Duhamel integration

The source is continuous in time; its time derivative is not assumed. The
genuine cocycle and the shrinking source interval identify the time derivative.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

def heatDuhamelShortSource (ν : ℝ) (F : ℝ → Pt 2 → ℂ)
    (t h : ℝ) (x : Pt 2) : ℂ :=
  ∫ r in (0 : ℝ)..h, heatOp (Real.toNNReal (2 * ν * (h - r))) (F (t + r)) x

theorem hasDerivAt_heatDuhamelShortSource (ν : ℝ) {F : ℝ → Pt 2 → ℂ}
    (hF : Continuous (Function.uncurry F)) {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (t : ℝ) (x : Pt 2) :
    HasDerivAt (fun h => heatDuhamelShortSource ν F t h x) (F t x) 0 := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      heatOp (Real.toNNReal (2 * ν * (p.1 - p.2))) (F (t + p.2)) x) :=
    (continuous_heatOp_with_param hF hC).comp
      (by fun_prop : Continuous (fun p : ℝ × ℝ =>
        (t + p.2, Real.toNNReal (2 * ν * (p.1 - p.2)), x)))
  have hFt : Continuous (F t) := hF.comp (continuous_const.prodMk continuous_id)
  simpa [heatDuhamelShortSource, heatOp_zero hFt] using
    hasDerivAt_parametric_short_integral hc

theorem heatDuhamel_short_interval_eq (ν : ℝ) (F : ℝ → Pt 2 → ℂ)
    (t h : ℝ) (x : Pt 2) :
    (∫ s in t..(t + h), heatOp (Real.toNNReal (2 * ν * (t + h - s))) (F s) x) =
      heatDuhamelShortSource ν F t h x := by
  have he := intervalIntegral.integral_comp_add_right
    (fun s => heatOp (Real.toNNReal (2 * ν * (t + h - s))) (F s) x) (a := 0) (b := h) t
  calc
    _ = ∫ r in (0 : ℝ)..h,
        heatOp (Real.toNNReal (2 * ν * (t + h - (r + t)))) (F (r + t)) x := by
      simpa only [zero_add, add_comm h t] using he.symm
    _ = _ := by
      unfold heatDuhamelShortSource
      congr 1
      funext r
      have hr : t + h - (r + t) = h - r := by ring
      rw [hr, add_comm r t]

/-- The genuine Duhamel term satisfies the inhomogeneous heat equation as a right derivative. -/
theorem hasDerivWithinAt_heatDuhamel_right {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    {t : ℝ} (ht : 0 ≤ t) (x : Pt 2) :
    HasDerivWithinAt (fun s => heatDuhamel ν F s x)
      (ν • lap (heatDuhamel ν F t) x + F t x) (Ici t) t := by
  have hu := contDiff_two_heatDuhamel_holder hν hF hp hC hH hβ hholder ht
  have hheat := hasDerivWithinAt_heatOp_zero hu (heatDuhamel_periodic ν hp t) hν.le x
  have hsrc := (hasDerivAt_heatDuhamelShortSource ν hF hC t x).hasDerivWithinAt (s := Ici 0)
  have he (h : ℝ) (hh : 0 ≤ h) : heatDuhamel ν F (t + h) x =
      heatOp (Real.toNNReal (2 * ν * h)) (heatDuhamel ν F t) x +
        heatDuhamelShortSource ν F t h x := by
    rw [heatDuhamel_cocycle hν.le ht hh hF hC, heatDuhamel_short_interval_eq]
  have hshift : HasDerivWithinAt (fun h => heatDuhamel ν F (t + h) x)
      (ν • lap (heatDuhamel ν F t) x + F t x) (Ici 0) 0 := by
    apply (hheat.add hsrc).congr_of_eventuallyEq ?_ (he 0 le_rfl)
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact he h hh
  have hsub : HasDerivWithinAt (fun s : ℝ => s - t) 1 (Ici t) t := by
    simpa using ((hasDerivAt_id t).sub_const t).hasDerivWithinAt (s := Ici t)
  have hmaps : MapsTo (fun s : ℝ => s - t) (Ici t) (Ici 0) := by
    intro s hs
    change t ≤ s at hs
    change 0 ≤ s - t
    exact sub_nonneg.2 hs
  have hcomp := hshift.scomp_of_eq t hsub hmaps (by simp)
  simpa [Function.comp_def, add_sub_assoc] using hcomp

end AnomDiss

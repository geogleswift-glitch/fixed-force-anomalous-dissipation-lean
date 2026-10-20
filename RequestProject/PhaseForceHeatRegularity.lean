module

public import RequestProject.HeatDuhamelParabolic
public import RequestProject.PhaseForceHolderBounds

/-! # Classical parabolic regularity of the actual linear force contribution -/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff
noncomputable section

namespace AnomDiss

/-- The genuine unprojected force heat contribution. The constructed force
is solenoidal, so its Fourier Leray projection fixes it. -/
def phaseForceHeatComponent (ν : ℝ) (w : Phase) (i : Fin 2) : ℝ → Pt 2 → ℂ :=
  heatDuhamel ν (fun t x => (gForce w t x i : ℂ))

theorem phaseForceHeatComponent_isParabolicC12 {ν T β : ℝ}
    (hν : 0 < ν) (hT : 0 < T) (hβ0 : 0 < β) (hβ1 : β < 1)
    (w : Phase) (i : Fin 2) : IsParabolicC12 T β (phaseForceHeatComponent ν w i) := by
  let L : Pt 2 →L[ℝ] ℂ := Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)
  let F : ℝ → Pt 2 → ℂ := fun t x => (gForce w t x i : ℂ)
  have hFc : Continuous (Function.uncurry F) :=
    L.continuous.comp (force_regularity.1 w).1.toIsTimeSmoothForce.continuous_uncurry
  have hFp : ∀ t, IsPeriodic (F t) := by
    intro t x n
    change ((gForce w t (x + intVec n) i : ℝ) : ℂ) = _
    rw [(gForce_slice_props w t).1 x n]
  obtain ⟨K, hK, hBd⟩ := forceD_uniform_holderBd hβ0.le hβ1 0
  have hC : ∀ t x, ‖F t x‖ ≤ K := by
    intro t x
    have hb : ‖gForce w t x‖ ≤ K := by
      simpa only [forceD_zero_eq] using (hBd w t).1 x
    have he : ‖F t x‖ ≤ ‖gForce w t x‖ := by
      simpa only [F, Complex.norm_real] using norm_le_pi_norm (gForce w t x) i
    exact he.trans hb
  have hH : ∀ t x y, ‖F t x - F t y‖ ≤ K * ‖x - y‖ ^ β := by
    intro t x y
    have hh : ‖gForce w t x - gForce w t y‖ ≤ K * ‖x - y‖ ^ β := by
      simpa only [forceD_zero_eq] using (hBd w t).2 x y
    have hi := norm_le_pi_norm (gForce w t x - gForce w t y) i
    have he : ‖F t x - F t y‖ ≤ ‖gForce w t x - gForce w t y‖ := by
      simpa only [F, ← Complex.ofReal_sub, Complex.norm_real, Pi.sub_apply] using hi
    exact he.trans hh
  have hFpar : ParHolder T β F := (gForce_parHolder w T hβ0.le hβ1).clm L
  exact heatDuhamel_isParabolicC12 hν hT hFc hFp hC hK hβ0 hβ1 hH hFpar

end AnomDiss

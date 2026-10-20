module

public import RequestProject.HeatDuhamelSpatial

/-! For differentiable periodic fluxes the divergence-form Duhamel term is
exactly the ordinary-source integral of the flux derivative. -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

theorem duhamelComponent_eq_heatDuhamel_pd {ν : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hFs : ∀ s, ContDiff ℝ 1 (F s))
    (hp : ∀ s, IsPeriodic (F s)) {t : ℝ} (ht : 0 ≤ t) (i : Fin 2) (x : Pt 2) :
    duhamelComponent ν F i t x = heatDuhamel ν (fun s => pd i (F s)) t x := by
  unfold duhamelComponent heatDuhamel
  apply intervalIntegral.integral_congr_ae
  rw [uIoc_of_le ht]
  filter_upwards [volume.ae_ne t] with s hne
  intro hs
  have hst : 0 < t - s := sub_pos.2 (lt_of_le_of_ne hs.2 hne)
  have hv : 0 < (Real.toNNReal (2 * ν * (t - s)) : ℝ) := by
    rw [Real.coe_toNNReal _ (by positivity)]
    positivity
  rw [← pd_heatOp_eq_heatGradientKernel (isQP_zero_iff.2 (hp s)) (hFs s) hv]
  exact pd_heatOp_C1 (isQP_zero_iff.2 (hp s)) (hFs s) _ i x

end AnomDiss

module

public import RequestProject.NSPhaseGalerkinVelocityTime
public import RequestProject.NSPhaseGalerkinPressureReal
public import RequestProject.FourierContinuousUniqueness
public import RequestProject.NSPhaseForceHeatFourier

/-!
# The genuine momentum source of the actual Galerkin limit

The true pointwise force minus advection minus pressure gradient has
exactly the original projected Fourier source coefficients. Continuous
bounded source data then identify its genuine heat Duhamel integral with
the same actual velocity, using pointwise Fourier uniqueness.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 1200000

/-- The actual real momentum source, using the reconstructed original
velocity and pressure. -/
def phaseL2MomentumSource (phase : Phase) (U : GalerkinTime →ᵇ TorusVelocityL2)
    (s : ℝ) (x : Pt 2) : Pt 2 :=
  gForce phase s x - conv (phaseL2VelocityExtension U s) (phaseL2VelocityExtension U s) x -
    grad (phaseL2PressureExtension U s) x

private lemma momentum_velocity_contDiff
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (s : ℝ) : ContDiff ℝ 1 (phaseL2VelocityExtension U s) :=
  phaseGalerkin_l2_limit_continuousVelocity_contDiff ν hν phase hφ hU _

private lemma momentum_pressure_contDiff
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (s : ℝ) : ContDiff ℝ 1 (phaseL2PressureExtension U s) :=
  contDiff_torusRealPressure_slice ν hν phase hφ hU _

private lemma momentum_velocity_periodic (U : GalerkinTime →ᵇ TorusVelocityL2) (s : ℝ) :
    IsPeriodic (phaseL2VelocityExtension U s) := isPeriodic_phaseL2ContinuousVelocity U _

private lemma momentum_pressure_periodic (U : GalerkinTime →ᵇ TorusVelocityL2) (s : ℝ) :
    IsPeriodic (phaseL2PressureExtension U s) := isPeriodic_torusRealPressure _

private lemma momentum_conv_periodic (U : GalerkinTime →ᵇ TorusVelocityL2) (s : ℝ) :
    IsPeriodic (conv (phaseL2VelocityExtension U s) (phaseL2VelocityExtension U s)) := by
  intro x m
  unfold conv
  apply Finset.sum_congr rfl
  intro j hj
  rw [momentum_velocity_periodic U s x m,
    isPeriodic_pd _ (momentum_velocity_periodic U s) j x m]

private lemma momentum_grad_periodic (U : GalerkinTime →ᵇ TorusVelocityL2) (s : ℝ) :
    IsPeriodic (grad (phaseL2PressureExtension U s)) := by
  intro x m
  funext i
  exact isPeriodic_pd _ (momentum_pressure_periodic U s) i x m

/-- The original pointwise momentum source is periodic at every time,
including the clamped extension outside the original slab. -/
theorem isPeriodic_phaseL2MomentumSource
    (phase : Phase) (U : GalerkinTime →ᵇ TorusVelocityL2) (s : ℝ) :
    IsPeriodic (phaseL2MomentumSource phase U s) := by
  intro x m
  change _ - _ - _ = _ - _ - _
  rw [(gForce_slice_props phase s).1 x m, momentum_conv_periodic U s x m,
    momentum_grad_periodic U s x m]

/-- The genuine pointwise momentum source has continuous spatial slices,
from the already earned spatial C¹ velocity and pressure. -/
theorem continuous_phaseL2MomentumSource_slice
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (s : ℝ) : Continuous (phaseL2MomentumSource phase U s) := by
  have hv := momentum_velocity_contDiff ν hν phase hφ hU s
  have hp := momentum_pressure_contDiff ν hν phase hφ hU s
  have hgrad : Continuous (grad (phaseL2PressureExtension U s)) := by
    apply continuous_pi
    intro i
    exact continuous_pd_of_C1 _ hp i
  exact (((gForce_slice_props phase s).2.1.continuous).sub
    (galerkin_continuous_conv hv.continuous hv)).sub hgrad

private theorem momentum_vectorFourierCoeff_sub (v w : Pt 2 → Pt 2)
    (hv : Continuous v) (hw : Continuous w) (k : Fin 2 → ℤ) (i : Fin 2) :
    vectorFourierCoeff (v-w) k i = vectorFourierCoeff v k i - vectorFourierCoeff w k i := by
  simpa only [vectorFourierCoeff_apply, Pi.sub_apply, Complex.ofReal_sub] using
    (fc_sub (fun x => (v x i : ℂ)) (fun x => (w x i : ℂ))
      (Complex.continuous_ofReal.comp ((continuous_apply i).comp hv))
      (Complex.continuous_ofReal.comp ((continuous_apply i).comp hw)) k).symm

/-- The original advective coefficient of the reconstructed real field is
exactly the genuine nonlinear Fourier flux of the same L² limit. -/
theorem phaseGalerkin_l2_limit_continuousVelocity_conv_fourier
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (k : Fin 2 → ℤ) (i : Fin 2) :
    vectorFourierCoeff (conv (phaseL2ContinuousVelocity U t) (phaseL2ContinuousVelocity U t)) k i =
      torusNonlinearFourierFlux k i (U t) := by
  rw [vectorFourierCoeff_conv_eq_flux _
    (phaseGalerkin_l2_limit_continuousVelocity_contDiff ν hν phase hφ hU t)
    (isPeriodic_phaseL2ContinuousVelocity U t)
    (phaseGalerkin_l2_limit_continuousVelocity_solenoidal ν hν phase hφ hU t)]
  rw [← torusNonlinearFourierFlux_of_field k i (phaseL2ContinuousVelocity U t)
    (continuous_phaseL2ContinuousVelocity_slice ν hν phase hφ hU t)
    (isPeriodic_phaseL2ContinuousVelocity U t),
    phaseGalerkin_l2_limit_continuousVelocity_identification ν hν phase hφ hU t]

/-- The true pointwise source, rather than a formal coefficient placeholder,
has exactly the projected source in the actual Galerkin-limit mild equation. -/
theorem phaseGalerkin_l2_limit_momentum_source_fourier
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (k : Fin 2 → ℤ) (i : Fin 2) :
    vectorFourierCoeff (phaseL2MomentumSource phase U t.1) k i =
      phaseL2FourierSourceCurve phase k i U t := by
  have hv := phaseGalerkin_l2_limit_continuousVelocity_contDiff ν hν phase hφ hU t
  have hp := contDiff_torusRealPressure_slice ν hν phase hφ hU t
  have hconv := galerkin_continuous_conv hv.continuous hv
  have hgrad : Continuous (grad (torusRealPressure (U t))) := by
    apply continuous_pi
    intro j
    exact continuous_pd_of_C1 _ hp j
  change vectorFourierCoeff (gForce phase t.1 -
    conv (phaseL2VelocityExtension U t.1) (phaseL2VelocityExtension U t.1) -
      grad (phaseL2PressureExtension U t.1)) k i = _
  rw [phaseL2VelocityExtension_of_mem U t.2, phaseL2PressureExtension_of_mem U t.2]
  change vectorFourierCoeff (gForce phase t.1 -
    conv (phaseL2ContinuousVelocity U t) (phaseL2ContinuousVelocity U t) -
      grad (torusRealPressure (U t))) k i = _
  have hgf : Continuous (gForce phase t.1 -
      conv (phaseL2ContinuousVelocity U t) (phaseL2ContinuousVelocity U t)) := by
    convert ((gForce_slice_props phase t.1).2.1.continuous).sub hconv using 1
  rw [momentum_vectorFourierCoeff_sub (gForce phase t.1 -
      conv (phaseL2ContinuousVelocity U t) (phaseL2ContinuousVelocity U t))
      (grad (torusRealPressure (U t))) hgf hgrad k i,
    momentum_vectorFourierCoeff_sub (gForce phase t.1)
      (conv (phaseL2ContinuousVelocity U t) (phaseL2ContinuousVelocity U t))
      (gForce_slice_props phase t.1).2.1.continuous hconv k i,
    phaseGalerkin_l2_limit_continuousVelocity_conv_fourier ν hν phase hφ hU t k i]
  have hpcoeff := phaseGalerkin_l2_limit_real_pressure_gradient_fourier ν hν phase hφ hU t k i
  change vectorFourierCoeff (gForce phase t.1) k i - torusNonlinearFourierFlux k i (U t) -
    fc (fun x => ((pd i (torusRealPressure (U t)) x : ℝ) : ℂ)) k = _
  rw [hpcoeff, phaseL2FourierSourceCurve_apply]
  have hforce := fourierLeray_vectorFourierCoeff (gForce phase t.1)
    ((gForce_slice_props phase t.1).2.1.of_le (natCast_le_infty 1))
    (gForce_slice_props phase t.1).1 (gForce_slice_props phase t.1).2.2.1 k
  rw [hforce]
  ring

/-- The actual velocity is the genuine heat Duhamel integral of its true
pointwise momentum source. Joint continuity and a global bound are explicit
analytic source hypotheses here; no differentiability or PDE conclusion is
assumed. The subsequent source regularity estimates discharge them. -/
theorem phaseGalerkin_l2_limit_continuousVelocity_eq_heatDuhamel
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (i : Fin 2)
    (hF : Continuous (Function.uncurry fun s x => (phaseL2MomentumSource phase U s x i : ℂ)))
    {C : ℝ} (hC : ∀ s x, ‖(phaseL2MomentumSource phase U s x i : ℂ)‖ ≤ C)
    (t : GalerkinTime) :
    (fun x => (phaseL2ContinuousVelocity U t x i : ℂ)) =
      heatDuhamel ν (fun s x => (phaseL2MomentumSource phase U s x i : ℂ)) t.1 := by
  have hpF : ∀ s, IsPeriodic (fun x => (phaseL2MomentumSource phase U s x i : ℂ)) := by
    intro s x m
    change (phaseL2MomentumSource phase U s (x + intVec m) i : ℂ) =
      (phaseL2MomentumSource phase U s x i : ℂ)
    rw [isPeriodic_phaseL2MomentumSource phase U s x m]
  have hvc := Complex.continuous_ofReal.comp
    ((continuous_apply i).comp (continuous_phaseL2ContinuousVelocity_slice ν hν phase hφ hU t))
  have hvp : IsPeriodic (fun x => (phaseL2ContinuousVelocity U t x i : ℂ)) := by
    intro x m
    change (phaseL2ContinuousVelocity U t (x + intVec m) i : ℂ) =
      (phaseL2ContinuousVelocity U t x i : ℂ)
    rw [isPeriodic_phaseL2ContinuousVelocity U t x m]
  have hdc : Continuous (heatDuhamel ν
      (fun s x => (phaseL2MomentumSource phase U s x i : ℂ)) t.1) :=
    (continuous_heatDuhamel ν hF hC).comp (continuous_const.prodMk continuous_id)
  apply continuous_periodic_eq_of_fc_eq hvc hvp hdc (heatDuhamel_periodic ν hpF t.1)
  intro k
  change vectorFourierCoeff (phaseL2ContinuousVelocity U t) k i = _
  rw [phaseGalerkin_l2_limit_continuousVelocity_fourier ν hν phase hφ hU t k i,
    phaseGalerkin_l2_limit_fourier_eq_heatDuhamelCoefficient ν hν phase hφ hU k i t,
    heatDuhamelCoefficient_eq_standard, fc_heatDuhamel hν.le hF hpF hC t.2.1]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) t.1 := by simpa only [uIcc_of_le t.2.1] using hs
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hs'.1, hs'.2.trans t.2.2⟩
  have hc := phaseGalerkin_l2_limit_momentum_source_fourier ν hν phase hφ hU ⟨s, hs01⟩ k i
  change fc (fun x => (phaseL2MomentumSource phase U s x i : ℂ)) k =
    phaseL2FourierSourceCurve phase k i U ⟨s, hs01⟩ at hc
  change Real.exp (-(ν * (t.1-s) * fourierEigenvalue k)) •
      phaseL2FourierSourceExtension phase i U s k =
    (Real.exp (-(ν * (t.1-s) * fourierEigenvalue k)) : ℂ) *
      fc (fun x => (phaseL2MomentumSource phase U s x i : ℂ)) k
  rw [hc]
  simp only [phaseL2FourierSourceExtension, extendGalerkinTimeCurve_of_mem _ hs01,
    Complex.real_smul]

/-- The same genuine heat representation in the original real-time
extension used by the parabolic regularity interface. -/
theorem phaseGalerkin_l2_limit_velocityExtension_component_eq_heatDuhamel
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (i : Fin 2)
    (hF : Continuous (Function.uncurry fun s x => (phaseL2MomentumSource phase U s x i : ℂ)))
    {C : ℝ} (hC : ∀ s x, ‖(phaseL2MomentumSource phase U s x i : ℂ)‖ ≤ C)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => (phaseL2VelocityExtension U t x i : ℂ)) =
      heatDuhamel ν (fun s x => (phaseL2MomentumSource phase U s x i : ℂ)) t := by
  rw [phaseL2VelocityExtension_of_mem U ht]
  exact phaseGalerkin_l2_limit_continuousVelocity_eq_heatDuhamel ν hν phase hφ hU i hF hC ⟨t, ht⟩

end AnomDiss

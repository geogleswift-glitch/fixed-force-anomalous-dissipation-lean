module

public import RequestProject.TorusL2Fourier
public import RequestProject.NSPhaseGalerkinL2Limit

/-!
# Fourier identification of the genuine L² velocity limit

Continuity of the true Fourier coefficient functionals identifies the
Arzelà--Ascoli coefficient limits with the coefficients of the actual
completed-space velocity curve. Thus the coefficient limit is not an
unrelated formal sequence.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

theorem l2FourierCoeff_phaseGalerkinL2Curve (ν : ℝ) (hν : 0 < ν) (phase : Phase)
    (N : ℕ) (t : GalerkinTime) (k : Fin 2 → ℤ) (i : Fin 2) :
    l2FourierCoeff k i (phaseGalerkinL2Curve ν hν phase N t) =
      vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N t) k i := by
  rw [phaseGalerkinL2Curve_eq]
  exact l2FourierCoeff_periodicVelocityToL2 k i _ _ _

theorem l2FourierCoeffCurve_phaseGalerkinL2Curve (ν : ℝ) (hν : 0 < ν) (phase : Phase)
    (N : ℕ) (k : Fin 2 → ℤ) (i : Fin 2) :
    (l2FourierCoeff k i).compLeftContinuousBounded GalerkinTime
        (phaseGalerkinL2Curve ν hν phase N) =
      phaseGalerkinCoefficientCurve ν hν phase N (k, i) := by
  apply BoundedContinuousFunction.ext
  intro t
  exact l2FourierCoeff_phaseGalerkinL2Curve ν hν phase N t k i

/-- Strong convergence in the completed velocity curve space implies
convergence of every actual coefficient curve in its sup norm. -/
theorem phaseGalerkin_l2_coefficient_curve_tendsto
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (k : Fin 2 → ℤ) (i : Fin 2) :
    Tendsto (fun n => phaseGalerkinCoefficientCurve ν hν phase (φ n) (k, i))
      atTop (𝓝 ((l2FourierCoeff k i).compLeftContinuousBounded GalerkinTime U)) := by
  simpa only [Function.comp_def, l2FourierCoeffCurve_phaseGalerkinL2Curve] using
    ((l2FourierCoeff k i).compLeftContinuousBounded GalerkinTime).continuous.tendsto U |>.comp hU

/-- The same actual `L²`-valued velocity limit has the coefficient family
obtained by simultaneous uniform-in-time extraction. -/
theorem exists_phaseGalerkin_l2_limit_with_fourier_identification
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) :
    ∃ a : GalerkinCoefficientIndex → (GalerkinTime →ᵇ ℂ), ∃ φ : ℕ → ℕ,
      ∃ U : GalerkinTime →ᵇ TorusVelocityL2,
        StrictMono φ ∧
        Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U) ∧
        U ⟨0, by norm_num⟩ = 0 ∧
        (∀ t : GalerkinTime, ‖U t‖ ^ 2 ≤ phaseGalerkinEnergyBound phase) ∧
        (∀ k i t, a (k, i) t = l2FourierCoeff k i (U t)) ∧
        ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : GalerkinTime,
          ‖phaseGalerkinL2Curve ν hν phase (φ n) t - U t‖ < ε := by
  obtain ⟨a, φ, U, hφ, hcoeff, hU, hzero, hE, huniform⟩ :=
    exists_phaseGalerkin_continuous_l2_limit ν hν phase
  refine ⟨a, φ, U, hφ, hU, hzero, hE, ?_, huniform⟩
  intro k i t
  have hpoint : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n) t)
      atTop (𝓝 (U t)) :=
    (BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto U |>.comp hU
  have hL : Tendsto (fun n => vectorFourierCoeff
      (phaseGalerkinVelocity ν hν phase (φ n) t) k i) atTop (𝓝 (l2FourierCoeff k i (U t))) := by
    simpa only [Function.comp_def, l2FourierCoeff_phaseGalerkinL2Curve] using
      (l2FourierCoeff k i).continuous.tendsto (U t) |>.comp hpoint
  have ha : Tendsto (fun n => vectorFourierCoeff
      (phaseGalerkinVelocity ν hν phase (φ n) t) k i) atTop (𝓝 (a (k, i) t)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hcoeff k i ε hε] with n hn
    simpa only [dist_eq_norm] using hn t.1 t.2
  exact tendsto_nhds_unique ha hL

end AnomDiss

module

public import RequestProject.TorusL2QuadraticFourier
public import RequestProject.NSPhaseGalerkinL2Limit

/-!
# Uniform-time convergence of the genuine quadratic L² Fourier flux

Strong convergence in the complete space of `L²`-valued continuous time curves
passes through the actual quadratic Fourier tensor. The proof uses its proven
bounded bilinear structure, and the resulting convergence is in the sup norm.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

def torusQuadraticFourierCurve {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (k : Fin 2 → ℤ) (j i : Fin 2) (U : X →ᵇ TorusVelocityL2) : X →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t => torusQuadraticFourierMoment k j i (U t),
      (continuous_torusQuadraticFourierMoment k j i).comp U.continuous⟩

@[simp] theorem torusQuadraticFourierCurve_apply {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (k : Fin 2 → ℤ) (j i : Fin 2)
    (U : X →ᵇ TorusVelocityL2) (t : X) :
    torusQuadraticFourierCurve k j i U t = torusQuadraticFourierMoment k j i (U t) := rfl

/-- Strong sup convergence of genuine `L²` velocity curves implies strong
sup convergence of every actual quadratic Fourier tensor moment. -/
theorem torusQuadraticFourierCurve_tendsto {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (k : Fin 2 → ℤ) (j i : Fin 2)
    {U : X →ᵇ TorusVelocityL2} {u : ℕ → (X →ᵇ TorusVelocityL2)}
    (hu : Tendsto u atTop (𝓝 U)) :
    Tendsto (fun n => torusQuadraticFourierCurve k j i (u n)) atTop
      (𝓝 (torusQuadraticFourierCurve k j i U)) := by
  let C : ℝ := ‖torusQuadraticFourierBilinear k j i‖
  have hb (n : ℕ) :
      ‖torusQuadraticFourierCurve k j i (u n) - torusQuadraticFourierCurve k j i U‖ ≤
        C * (‖u n‖ + ‖U‖) * ‖u n - U‖ := by
    apply (BoundedContinuousFunction.norm_le (by dsimp [C]; positivity)).mpr
    intro t
    change ‖torusQuadraticFourierMoment k j i (u n t) - torusQuadraticFourierMoment k j i (U t)‖ ≤ _
    refine (torusQuadraticFourierMoment_difference_le k j i (u n t) (U t)).trans ?_
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left
        (add_le_add ((u n).norm_coe_le_norm t) (U.norm_coe_le_norm t))
          (norm_nonneg (torusQuadraticFourierBilinear k j i))
    · exact (u n - U).norm_coe_le_norm t
    · exact norm_nonneg _
    · dsimp [C]
      positivity
  have hd : Tendsto (fun n => ‖u n - U‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using
      (hu.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => U) atTop (𝓝 U))).norm
  have hM : Tendsto (fun n => C * (‖u n‖ + ‖U‖) * ‖u n - U‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using ((hu.norm.add tendsto_const_nhds).const_mul C).mul hd
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hb hM

def torusNonlinearFourierCurve {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (k : Fin 2 → ℤ) (i : Fin 2) (U : X →ᵇ TorusVelocityL2) : X →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t => torusNonlinearFourierFlux k i (U t),
      (continuous_torusNonlinearFourierFlux k i).comp U.continuous⟩

@[simp] theorem torusNonlinearFourierCurve_apply {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (k : Fin 2 → ℤ) (i : Fin 2)
    (U : X →ᵇ TorusVelocityL2) (t : X) :
    torusNonlinearFourierCurve k i U t = torusNonlinearFourierFlux k i (U t) := rfl

theorem torusNonlinearFourierCurve_eq_sum {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (k : Fin 2 → ℤ) (i : Fin 2)
    (U : X →ᵇ TorusVelocityL2) :
    torusNonlinearFourierCurve k i U =
      ∑ j : Fin 2, (2 * π * Complex.I * (k j : ℂ)) • torusQuadraticFourierCurve k j i U := by
  apply BoundedContinuousFunction.ext
  intro t
  simp only [torusNonlinearFourierCurve_apply, torusNonlinearFourierFlux,
    BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.smul_apply,
    torusQuadraticFourierCurve_apply, smul_eq_mul]

/-- The actual nonlinear Fourier flux therefore converges uniformly in time
along the strong completed-space velocity subsequence. -/
theorem torusNonlinearFourierCurve_tendsto {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (k : Fin 2 → ℤ) (i : Fin 2)
    {U : X →ᵇ TorusVelocityL2} {u : ℕ → (X →ᵇ TorusVelocityL2)}
    (hu : Tendsto u atTop (𝓝 U)) :
    Tendsto (fun n => torusNonlinearFourierCurve k i (u n)) atTop
      (𝓝 (torusNonlinearFourierCurve k i U)) := by
  simp only [torusNonlinearFourierCurve_eq_sum]
  exact tendsto_finset_sum _ fun j _ =>
    (torusQuadraticFourierCurve_tendsto k j i hu).const_smul (2 * π * Complex.I * (k j : ℂ))

/-- The completed-space moment of each actual Galerkin field is its original
nonlinear Fourier flux, so the passage above is a passage of the actual PDE
nonlinearity. -/
theorem torusNonlinearFourierCurve_phaseGalerkin
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) (k : Fin 2 → ℤ) (i : Fin 2)
    (t : GalerkinTime) :
    torusNonlinearFourierCurve k i (phaseGalerkinL2Curve ν hν phase N) t =
      nonlinearFourierFlux (phaseGalerkinVelocity ν hν phase N t.1) k i := by
  rw [torusNonlinearFourierCurve_apply, phaseGalerkinL2Curve_eq,
    torusNonlinearFourierFlux_of_field]

/-- Explicit uniform passage of the genuine Galerkin nonlinear flux to the
completed-space velocity limit. -/
theorem phaseGalerkin_nonlinear_flux_uniform_convergence
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) (φ : ℕ → ℕ)
    (U : GalerkinTime →ᵇ TorusVelocityL2)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (k : Fin 2 → ℤ) (i : Fin 2) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : GalerkinTime,
      ‖nonlinearFourierFlux (phaseGalerkinVelocity ν hν phase (φ n) t.1) k i -
        torusNonlinearFourierFlux k i (U t)‖ < ε := by
  have h := bounded_curve_tendsto_uniform (torusNonlinearFourierCurve_tendsto k i hU)
  simpa only [torusNonlinearFourierCurve_apply, phaseGalerkinL2Curve_eq,
    torusNonlinearFourierFlux_of_field] using h

end AnomDiss

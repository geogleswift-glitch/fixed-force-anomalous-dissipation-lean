module

public import RequestProject.NSPhaseGalerkinEvolution

/-!
# The genuine Fourier heat Duhamel formula

The variation-of-constants identity is proved from the coefficient ODE of
the actual strong Galerkin limit.  Its source is the original force minus
the actual quadratic flux, both with the genuine Fourier Leray multiplier.
The final existence assertion has no PDE existence hypothesis.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

/-- Integrating factor for an actual coefficient ODE on the closed unit
interval.  Neither positivity of the damping nor a nonzero frequency is
required. -/
theorem galerkinTime_integrating_factor
    (d : ℝ) (a F : GalerkinTime →ᵇ ℂ)
    (ha : ∀ t : GalerkinTime, t.1 ∈ Ioo 0 1 →
      HasDerivAt (extendGalerkinTimeCurve a)
        ((-d : ℂ) * a t + F t) t.1)
    (t : GalerkinTime) :
    (∫ s in (0 : ℝ)..t.1,
      (Real.exp (d * s) : ℂ) * extendGalerkinTimeCurve F s) =
      (Real.exp (d * t.1) : ℂ) * a t - a ⟨0, by norm_num⟩ := by
  have hcE : Continuous (fun s : ℝ => (Real.exp (d * s) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hcA := continuous_extendGalerkinTimeCurve a
  have hcF := continuous_extendGalerkinTimeCurve F
  have hd : ∀ s ∈ Ioo (0 : ℝ) t.1,
      HasDerivAt (fun r => (Real.exp (d * r) : ℂ) * extendGalerkinTimeCurve a r)
        ((Real.exp (d * s) : ℂ) * extendGalerkinTimeCurve F s) s := by
    intro s hs
    have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le.trans t.2.2⟩
    have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, hs.2.trans_le t.2.2⟩
    have hE := (((hasDerivAt_id s).const_mul d).exp).ofReal_comp
    have hA := ha ⟨s, hs1⟩ hsI
    have hh := hE.fun_mul hA
    convert hh using 1 <;>
      simp only [id_eq, mul_one, extendGalerkinTimeCurve_of_mem a hs1,
        extendGalerkinTimeCurve_of_mem F hs1]
    push_cast
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.2.1
    (hcE.fun_mul hcA).continuousOn hd ((hcE.fun_mul hcF).intervalIntegrable 0 t.1)
  simpa only [Pi.mul_apply, extendGalerkinTimeCurve_of_mem a t.2,
    extendGalerkinTimeCurve_of_mem a (by norm_num : (0 : ℝ) ∈ Icc 0 1),
    mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul] using hFTC

/-- Exact variation of constants with the heat multiplier. -/
theorem galerkinTime_heat_duhamel
    (d : ℝ) (a F : GalerkinTime →ᵇ ℂ)
    (ha : ∀ t : GalerkinTime, t.1 ∈ Ioo 0 1 →
      HasDerivAt (extendGalerkinTimeCurve a)
        ((-d : ℂ) * a t + F t) t.1)
    (t : GalerkinTime) :
    a t = (Real.exp (-d * t.1) : ℂ) * a ⟨0, by norm_num⟩ +
      ∫ s in (0 : ℝ)..t.1,
        (Real.exp (-d * (t.1 - s)) : ℂ) * extendGalerkinTimeCurve F s := by
  have hIF := galerkinTime_integrating_factor d a F ha t
  have hprod : (Real.exp (-d * t.1) : ℂ) * (Real.exp (d * t.1) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    ring_nf
    simp
  have hkernel : ∀ s : ℝ,
      (Real.exp (-d * (t.1 - s)) : ℂ) * extendGalerkinTimeCurve F s =
        (Real.exp (-d * t.1) : ℂ) *
          ((Real.exp (d * s) : ℂ) * extendGalerkinTimeCurve F s) := by
    intro s
    have he : -d * (t.1 - s) = -d * t.1 + d * s := by ring
    rw [he, Real.exp_add, Complex.ofReal_mul, mul_assoc]
  simp_rw [hkernel]
  rw [intervalIntegral.integral_const_mul, hIF]
  rw [mul_sub, ← mul_assoc, hprod, one_mul]
  ring

/-- The actual force minus nonlinear flux curve, after the Fourier Leray
projection.  No diffusion is included in this source. -/
def phaseL2FourierSourceCurve (phase : Phase) (k : Fin 2 → ℤ) (i : Fin 2)
    (U : GalerkinTime →ᵇ TorusVelocityL2) : GalerkinTime →ᵇ ℂ :=
  lerayFourierCurveComponent k i (fun j => phaseForceFourierCurve phase k j) -
    lerayFourierCurveComponent k i (fun j => torusNonlinearFourierCurve k j U)

theorem phaseL2FourierSourceCurve_apply (phase : Phase) (k : Fin 2 → ℤ) (i : Fin 2)
    (U : GalerkinTime →ᵇ TorusVelocityL2) (t : GalerkinTime) :
    phaseL2FourierSourceCurve phase k i U t =
      fourierLeray k (vectorFourierCoeff (gForce phase t.1) k) i -
        fourierLeray k (WithLp.toLp 2 (fun j => torusNonlinearFourierFlux k j (U t))) i := by
  change lerayFourierCurveComponent k i (fun j => phaseForceFourierCurve phase k j) t -
    lerayFourierCurveComponent k i (fun j => torusNonlinearFourierCurve k j U) t = _
  rw [lerayFourierCurveComponent_apply, lerayFourierCurveComponent_apply]
  rfl

/-- Diffusion plus the genuine projected source is the actual Fourier rate. -/
theorem phaseL2FourierRHSCurve_eq_damping_add_source
    (ν : ℝ) (phase : Phase) (k : Fin 2 → ℤ) (i : Fin 2)
    (U : GalerkinTime →ᵇ TorusVelocityL2) (t : GalerkinTime) :
    phaseL2FourierRHSCurve ν phase k i U t =
      ((-(ν * fourierEigenvalue k) : ℝ) : ℂ) * l2FourierCoeff k i (U t) +
        phaseL2FourierSourceCurve phase k i U t := by
  rw [phaseL2FourierRHSCurve_apply, phaseL2FourierSourceCurve_apply]
  ring

/-- Frequencywise heat Duhamel formula for the genuine strong Galerkin
limit, including the zero frequency and both time endpoints. -/
theorem phaseGalerkin_l2_limit_fourier_heat_duhamel
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (k : Fin 2 → ℤ) (i : Fin 2) (t : GalerkinTime) :
    l2FourierCoeff k i (U t) =
      (Real.exp (-(ν * fourierEigenvalue k) * t.1) : ℂ) *
        l2FourierCoeff k i (U ⟨0, by norm_num⟩) +
      ∫ s in (0 : ℝ)..t.1,
        (Real.exp (-(ν * fourierEigenvalue k) * (t.1 - s)) : ℂ) *
          extendGalerkinTimeCurve (phaseL2FourierSourceCurve phase k i U) s := by
  apply galerkinTime_heat_duhamel (ν * fourierEigenvalue k)
    ((l2FourierCoeff k i).compLeftContinuousBounded GalerkinTime U)
    (phaseL2FourierSourceCurve phase k i U)
  intro r hr
  have hd := phaseGalerkin_l2_limit_fourier_hasDerivAt ν hν phase hφ hU k i r hr
  rw [phaseL2FourierRHSCurve_eq_damping_add_source] at hd
  simpa only [Complex.ofReal_neg, ContinuousLinearMap.compLeftContinuousBounded_apply] using hd

/-- Unconditional actual `L²` velocity existence, with zero initial data,
the energy bound and every frequency's genuine heat Duhamel formula. -/
theorem exists_phaseGalerkin_l2_fourier_heat_duhamel
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) :
    ∃ U : GalerkinTime →ᵇ TorusVelocityL2,
      U ⟨0, by norm_num⟩ = 0 ∧
      (∀ t : GalerkinTime, ‖U t‖ ^ 2 ≤ phaseGalerkinEnergyBound phase) ∧
      ∀ k i t, l2FourierCoeff k i (U t) =
        ∫ s in (0 : ℝ)..t.1,
          (Real.exp (-(ν * fourierEigenvalue k) * (t.1 - s)) : ℂ) *
            extendGalerkinTimeCurve (phaseL2FourierSourceCurve phase k i U) s := by
  obtain ⟨a, φ, U, hφ, hU, hz, hE, -, -⟩ :=
    exists_phaseGalerkin_l2_limit_with_fourier_identification ν hν phase
  refine ⟨U, hz, hE, ?_⟩
  intro k i t
  have h := phaseGalerkin_l2_limit_fourier_heat_duhamel ν hν phase hφ hU k i t
  simpa only [hz, map_zero, mul_zero, zero_add] using h

end AnomDiss

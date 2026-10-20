module

public import RequestProject.CompactTimeIntegral
public import RequestProject.TorusL2QuadraticFourierCurves
public import RequestProject.NSPhaseGalerkinL2FourierLimit

/-!
# Passing the actual Fourier evolution to the completed L² velocity limit

Linear coefficients and genuine quadratic flux curves converge in the sup
norm. The fixed original force is represented by its actual continuous
coefficient curves. The true Fourier Leray multiplier acts coordinate-wise,
and time integration is a bounded linear functional on the curve space.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

private theorem continuousOn_phaseForce_test_pair (phase : Phase)
    (q : Pt 2 → Pt 2) (hq : Continuous q) :
    ContinuousOn (fun t => cellVectorPair q (gForce phase t)) (Icc 0 1) := by
  apply continuousOn_integral_cell' (by norm_num : (0 : ℝ) ≤ 1)
  exact continuousOn_finset_sum _ fun i _ =>
    ((((continuous_apply i).comp hq).comp continuous_snd).continuousOn).mul
      ((continuous_apply i).comp_continuousOn (continuous_phaseForce phase).continuousOn)

theorem continuousOn_phaseForce_fourierCoefficient (phase : Phase)
    (k : Fin 2 → ℤ) (i : Fin 2) :
    ContinuousOn (fun t => vectorFourierCoeff (gForce phase t) k i) (Icc 0 1) := by
  have hR : ContinuousOn (fun t => (vectorFourierCoeff (gForce phase t) k i).re) (Icc 0 1) := by
    refine (continuousOn_phaseForce_test_pair phase
      (realFourierMode k (EuclideanSpace.single i (1 : ℂ)))
      (contDiff_realFourierMode k _).continuous).congr ?_
    intro t _
    change (vectorFourierCoeff (gForce phase t) k i).re =
      cellVectorPair (realFourierMode k (EuclideanSpace.single i (1 : ℂ))) (gForce phase t)
    rw [realFourierMode_cellPair k _ _ (gForce_slice_props phase t).2.1.continuous,
      EuclideanSpace.inner_single_left]
    simp
  have hI : ContinuousOn (fun t => (vectorFourierCoeff (gForce phase t) k i).im) (Icc 0 1) := by
    refine (continuousOn_phaseForce_test_pair phase
      (realFourierMode k (EuclideanSpace.single i Complex.I))
      (contDiff_realFourierMode k _).continuous).congr ?_
    intro t _
    change (vectorFourierCoeff (gForce phase t) k i).im =
      cellVectorPair (realFourierMode k (EuclideanSpace.single i Complex.I)) (gForce phase t)
    rw [realFourierMode_cellPair k _ _ (gForce_slice_props phase t).2.1.continuous,
      EuclideanSpace.inner_single_left]
    simp [Complex.mul_re]
  have hc := (Complex.continuous_ofReal.comp_continuousOn hR).add
    ((Complex.continuous_ofReal.comp_continuousOn hI).mul
      (continuousOn_const : ContinuousOn (fun _ : ℝ => Complex.I) (Icc 0 1)))
  exact hc.congr (fun _ _ => (Complex.re_add_im _).symm)

def phaseForceFourierCurve (phase : Phase) (k : Fin 2 → ℤ) (i : Fin 2) : GalerkinTime →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t => vectorFourierCoeff (gForce phase t.1) k i,
      continuousOn_iff_continuous_restrict.1 (continuousOn_phaseForce_fourierCoefficient phase k i)⟩

@[simp] theorem phaseForceFourierCurve_apply (phase : Phase) (k : Fin 2 → ℤ)
    (i : Fin 2) (t : GalerkinTime) :
    phaseForceFourierCurve phase k i t = vectorFourierCoeff (gForce phase t.1) k i := rfl

/-- The coordinate formula of the genuine Leray projection, applied to
bounded continuous coefficient curves. It also covers the zero mode. -/
def lerayFourierCurveComponent (k : Fin 2 → ℤ) (i : Fin 2)
    (a : Fin 2 → (GalerkinTime →ᵇ ℂ)) : GalerkinTime →ᵇ ℂ :=
  a i - ((k i : ℂ) / ((‖fourierWave k‖ ^ 2 : ℝ) : ℂ)) •
    (∑ j : Fin 2, (k j : ℂ) • a j)

@[simp] theorem lerayFourierCurveComponent_apply (k : Fin 2 → ℤ) (i : Fin 2)
    (a : Fin 2 → (GalerkinTime →ᵇ ℂ)) (t : GalerkinTime) :
    lerayFourierCurveComponent k i a t =
      fourierLeray k (WithLp.toLp 2 (fun j => a j t)) i := by
  rw [fourierLeray_apply_formula]
  simp only [lerayFourierCurveComponent, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.sum_apply,
    fourierDivSymbol, smul_eq_mul]
  ring

theorem lerayFourierCurveComponent_tendsto (k : Fin 2 → ℤ) (i : Fin 2)
    {a : Fin 2 → (GalerkinTime →ᵇ ℂ)} {b : ℕ → Fin 2 → (GalerkinTime →ᵇ ℂ)}
    (hb : ∀ j, Tendsto (fun n => b n j) atTop (𝓝 (a j))) :
    Tendsto (fun n => lerayFourierCurveComponent k i (b n)) atTop
      (𝓝 (lerayFourierCurveComponent k i a)) := by
  unfold lerayFourierCurveComponent
  exact (hb i).sub ((tendsto_finset_sum _ (fun j _ => (hb j).const_smul (k j : ℂ))).const_smul
    ((k i : ℂ) / ((‖fourierWave k‖ ^ 2 : ℝ) : ℂ)))

/-- The actual projected Fourier evolution rate of a genuine completed-space
velocity time curve, including the original fixed force. -/
def phaseL2FourierRHSCurve (ν : ℝ) (phase : Phase) (k : Fin 2 → ℤ) (i : Fin 2)
    (U : GalerkinTime →ᵇ TorusVelocityL2) : GalerkinTime →ᵇ ℂ :=
  ((-(ν * fourierEigenvalue k) : ℝ) : ℂ) •
      ((l2FourierCoeff k i).compLeftContinuousBounded GalerkinTime U) -
    lerayFourierCurveComponent k i (fun j => torusNonlinearFourierCurve k j U) +
      lerayFourierCurveComponent k i (fun j => phaseForceFourierCurve phase k j)

theorem phaseL2FourierRHSCurve_apply (ν : ℝ) (phase : Phase) (k : Fin 2 → ℤ) (i : Fin 2)
    (U : GalerkinTime →ᵇ TorusVelocityL2) (t : GalerkinTime) :
    phaseL2FourierRHSCurve ν phase k i U t =
      ((-(ν * fourierEigenvalue k) : ℝ) : ℂ) * l2FourierCoeff k i (U t) -
        fourierLeray k (WithLp.toLp 2 (fun j => torusNonlinearFourierFlux k j (U t))) i +
          fourierLeray k (vectorFourierCoeff (gForce phase t.1) k) i := by
  change ((-(ν * fourierEigenvalue k) : ℝ) : ℂ) * l2FourierCoeff k i (U t) -
    lerayFourierCurveComponent k i (fun j => torusNonlinearFourierCurve k j U) t +
      lerayFourierCurveComponent k i (fun j => phaseForceFourierCurve phase k j) t = _
  rw [lerayFourierCurveComponent_apply, lerayFourierCurveComponent_apply]
  rfl

/-- Strong completed-space velocity convergence passes through all terms of
the actual nonlinear projected Fourier evolution rate. -/
theorem phaseL2FourierRHSCurve_tendsto (ν : ℝ) (phase : Phase) (k : Fin 2 → ℤ) (i : Fin 2)
    {U : GalerkinTime →ᵇ TorusVelocityL2} {u : ℕ → (GalerkinTime →ᵇ TorusVelocityL2)}
    (hu : Tendsto u atTop (𝓝 U)) :
    Tendsto (fun n => phaseL2FourierRHSCurve ν phase k i (u n)) atTop
      (𝓝 (phaseL2FourierRHSCurve ν phase k i U)) := by
  have hcoef : Tendsto (fun n => (l2FourierCoeff k i).compLeftContinuousBounded GalerkinTime (u n))
      atTop (𝓝 ((l2FourierCoeff k i).compLeftContinuousBounded GalerkinTime U)) :=
    ((l2FourierCoeff k i).compLeftContinuousBounded GalerkinTime).continuous.tendsto U |>.comp hu
  exact ((hcoef.const_smul ((-(ν * fourierEigenvalue k) : ℝ) : ℂ)).sub
    (lerayFourierCurveComponent_tendsto k i (fun j => torusNonlinearFourierCurve_tendsto k j hu))).add
      tendsto_const_nhds

end AnomDiss

module

public import RequestProject.CountableCurveCompactness
public import RequestProject.NSPhaseGalerkinCoefficient

/-!
# One subsequence for all actual Galerkin Fourier coefficient curves

The chosen finite ODE solutions have bounded genuine Fourier coefficients.
Their proven time Lipschitz moduli are eventually uniform at each fixed
frequency. Countable-product Arzelà--Ascoli yields one increasing subsequence
converging uniformly in time at every frequency and velocity coordinate.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction NNReal

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

abbrev GalerkinTime := Icc (0 : ℝ) 1
abbrev GalerkinCoefficientIndex := (Fin 2 → ℤ) × Fin 2

private theorem continuousOn_phaseGalerkin_test_pair
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ)
    (φ : Pt 2 → Pt 2) (hφ : Continuous φ) :
    ContinuousOn (fun t => cellVectorPair φ (phaseGalerkinVelocity ν hν phase N t)) (Icc 0 1) := by
  apply continuousOn_integral_cell' (by norm_num : (0 : ℝ) ≤ 1)
  exact continuousOn_finset_sum _ fun i _ =>
    ((((continuous_apply i).comp hφ).comp continuous_snd).continuousOn).mul
      ((continuous_apply i).comp_continuousOn (phaseGalerkinVelocity_continuousOn ν hν phase N))

/-- Continuity of each genuine coefficient curve, including cutoffs before
that frequency is retained. -/
theorem continuousOn_phaseGalerkin_coefficient
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) (k : Fin 2 → ℤ) (i : Fin 2) :
    ContinuousOn (fun t => vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N t) k i)
      (Icc 0 1) := by
  have hR : ContinuousOn
      (fun t => (vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N t) k i).re)
      (Icc 0 1) := by
    refine (continuousOn_phaseGalerkin_test_pair ν hν phase N
      (realFourierMode k (fourierLeray k (EuclideanSpace.single i (1 : ℂ))))
      (contDiff_realFourierMode k _).continuous).congr ?_
    intro t _
    exact (projected_realFourierMode_reads_re k i (phaseGalerkinVelocity ν hν phase N t)
      ((phaseGalerkinVelocity_contDiff ν hν phase N t).of_le (natCast_le_infty 1))
      (phaseGalerkinVelocity_periodic ν hν phase N t)
      (phaseGalerkinVelocity_solenoidal ν hν phase N t)).symm
  have hI : ContinuousOn
      (fun t => (vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N t) k i).im)
      (Icc 0 1) := by
    refine (continuousOn_phaseGalerkin_test_pair ν hν phase N
      (realFourierMode k (fourierLeray k (EuclideanSpace.single i Complex.I)))
      (contDiff_realFourierMode k _).continuous).congr ?_
    intro t _
    exact (projected_realFourierMode_reads_im k i (phaseGalerkinVelocity ν hν phase N t)
      ((phaseGalerkinVelocity_contDiff ν hν phase N t).of_le (natCast_le_infty 1))
      (phaseGalerkinVelocity_periodic ν hν phase N t)
      (phaseGalerkinVelocity_solenoidal ν hν phase N t)).symm
  have hc := (Complex.continuous_ofReal.comp_continuousOn hR).add
    ((Complex.continuous_ofReal.comp_continuousOn hI).mul
      (continuousOn_const : ContinuousOn (fun _ : ℝ => Complex.I) (Icc 0 1)))
  exact hc.congr (fun t _ => (Complex.re_add_im _).symm)

/-- The actual coefficient curve on the original compact time interval. -/
def phaseGalerkinCoefficientCurve (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ)
    (m : GalerkinCoefficientIndex) : GalerkinTime →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t => vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N t.1) m.1 m.2,
      continuousOn_iff_continuous_restrict.1
        (continuousOn_phaseGalerkin_coefficient ν hν phase N m.1 m.2)⟩

@[simp] theorem phaseGalerkinCoefficientCurve_apply
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) (m : GalerkinCoefficientIndex)
    (t : GalerkinTime) :
    phaseGalerkinCoefficientCurve ν hν phase N m t =
      vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N t.1) m.1 m.2 := rfl

/-- Every fixed Fourier coordinate has one eventual Lipschitz constant as a
bounded continuous curve on `[0,1]`. -/
theorem phaseGalerkinCoefficientCurve_eventually_lipschitz
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) (m : GalerkinCoefficientIndex) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      LipschitzWith (Real.toNNReal (phaseGalerkinCoefficientLipschitzBound ν phase m.1))
        (phaseGalerkinCoefficientCurve ν hν phase n m) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (phaseGalerkin_coefficient_eventually_lipschitz ν hν phase m.1 m.2)
  refine ⟨N, fun n hn => LipschitzWith.of_dist_le_mul fun s t => ?_⟩
  have h := hN n hn t.1 t.2 s.1 s.2
  have hc := mul_le_mul_of_nonneg_right
    (Real.le_coe_toNNReal (phaseGalerkinCoefficientLipschitzBound ν phase m.1))
    (abs_nonneg (s.1 - t.1))
  exact (by simpa only [dist_eq_norm, phaseGalerkinCoefficientCurve_apply,
    Subtype.dist_eq, Real.norm_eq_abs] using h.trans hc)

/-- One strictly increasing subsequence converges uniformly in time at every
integer frequency and velocity coordinate of the genuine ODE solutions. -/
theorem exists_phaseGalerkin_coefficient_subsequence
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) :
    ∃ a : GalerkinCoefficientIndex → (GalerkinTime →ᵇ ℂ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ ∀ m,
        Tendsto (fun n => phaseGalerkinCoefficientCurve ν hν phase (φ n) m) atTop (𝓝 (a m)) := by
  apply exists_countable_uniform_curve_subsequence
    (phaseGalerkinCoefficientCurve ν hν phase)
    (fun _ => sqrt (phaseGalerkinEnergyBound phase))
    (fun m => Real.toNNReal (phaseGalerkinCoefficientLipschitzBound ν phase m.1))
  · intro n m t
    exact phaseGalerkin_coefficient_norm_bound ν hν phase n t.2 m.1 m.2
  · exact phaseGalerkinCoefficientCurve_eventually_lipschitz ν hν phase

/-- Explicitly, the same subsequence converges uniformly over the entire
closed time interval for every actual Fourier coefficient. -/
theorem exists_phaseGalerkin_uniform_coefficient_subsequence
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) :
    ∃ a : GalerkinCoefficientIndex → (GalerkinTime →ᵇ ℂ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ ∀ k i ε, 0 < ε → ∀ᶠ n in atTop,
        ∀ (t : ℝ) (ht : t ∈ Icc 0 1),
          ‖vectorFourierCoeff (phaseGalerkinVelocity ν hν phase (φ n) t) k i -
              a (k, i) ⟨t, ht⟩‖ < ε := by
  obtain ⟨a, φ, hφ, hlim⟩ := exists_phaseGalerkin_coefficient_subsequence ν hν phase
  refine ⟨a, φ, hφ, fun k i ε hε => ?_⟩
  have h := bounded_curve_tendsto_uniform (hlim (k, i)) ε hε
  filter_upwards [h] with n hn
  intro t ht
  exact hn ⟨t, ht⟩

end AnomDiss

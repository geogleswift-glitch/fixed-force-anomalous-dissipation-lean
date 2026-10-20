module

public import RequestProject.TorusVelocityL2
public import RequestProject.NSPhaseGalerkinL2Compactness

/-!
# A genuine continuous L² velocity limit

The actual finite fields are embedded isometrically into the completed
Euclidean-valued cell `L²` space. Their uniform spatial Cauchy subsequence is
Cauchy in the Banach space of continuous `L²`-valued time curves, and therefore
has a genuine continuous limit on the whole closed unit interval.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

def phaseGalerkinL2Curve (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) :
    GalerkinTime →ᵇ TorusVelocityL2 :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t => (fourierGalerkinModel (fourierFrequencyBox (N + 1))).toL2Isometry
      (phaseGalerkinState ν hν phase N t.1),
      (fourierGalerkinModel (fourierFrequencyBox (N + 1))).toL2Isometry.continuous.comp
        (continuousOn_iff_continuous_restrict.1 (phaseGalerkinState_continuousOn ν hν phase N))⟩

theorem phaseGalerkinL2Curve_eq (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) (t : GalerkinTime) :
    phaseGalerkinL2Curve ν hν phase N t = periodicVelocityToL2
      (phaseGalerkinVelocity ν hν phase N t)
      (phaseGalerkinVelocity_contDiff ν hν phase N t).continuous
      (phaseGalerkinVelocity_periodic ν hν phase N t) := rfl

theorem phaseGalerkinL2Curve_norm_sq (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) (t : GalerkinTime) :
    ‖phaseGalerkinL2Curve ν hν phase N t‖ ^ 2 = l2sqV (phaseGalerkinVelocity ν hν phase N t) := by
  rw [phaseGalerkinL2Curve_eq]
  exact norm_periodicVelocityToL2_sq _ _ _

theorem phaseGalerkinL2Curve_sub_norm_sq (ν : ℝ) (hν : 0 < ν) (phase : Phase)
    (N M : ℕ) (t : GalerkinTime) :
    ‖phaseGalerkinL2Curve ν hν phase N t - phaseGalerkinL2Curve ν hν phase M t‖ ^ 2 =
      l2sqV (phaseGalerkinVelocity ν hν phase N t - phaseGalerkinVelocity ν hν phase M t) := by
  rw [phaseGalerkinL2Curve_eq, phaseGalerkinL2Curve_eq]
  exact norm_periodicVelocityToL2_sub_sq _ _ _ _ _ _

theorem phaseGalerkinL2Curve_initial (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) :
    phaseGalerkinL2Curve ν hν phase N ⟨0, by norm_num⟩ = 0 := by
  change (fourierGalerkinModel (fourierFrequencyBox (N + 1))).toL2Isometry
    (phaseGalerkinState ν hν phase N 0) = 0
  rw [phaseGalerkinState_initial, map_zero]

/-- Actual uniform spatial `L²` Cauchyness is Cauchyness in the complete space
of `L²`-valued continuous time curves. -/
theorem phaseGalerkinL2Curve_cauchy_of_spatial_cauchy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) (φ : ℕ → ℕ)
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → ∀ m, N ≤ m → ∀ t ∈ Icc 0 1,
      l2sqV (phaseGalerkinVelocity ν hν phase (φ n) t -
        phaseGalerkinVelocity ν hν phase (φ m) t) < ε) :
    CauchySeq (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hc ((ε / 2) ^ 2) (sq_pos_of_pos (by linarith))
  refine ⟨N, fun n hn m hm => ?_⟩
  have hbound : ‖phaseGalerkinL2Curve ν hν phase (φ n) -
      phaseGalerkinL2Curve ν hν phase (φ m)‖ ≤ ε / 2 := by
    apply (BoundedContinuousFunction.norm_le (by linarith : (0 : ℝ) ≤ ε / 2)).mpr
    intro t
    have hs := hN n hn m hm t.1 t.2
    rw [← phaseGalerkinL2Curve_sub_norm_sq ν hν phase (φ n) (φ m) t] at hs
    exact ((sq_lt_sq₀ (norm_nonneg _) (by linarith : (0 : ℝ) ≤ ε / 2)).mp hs).le
  rw [dist_eq_norm]
  exact hbound.trans_lt (by linarith)

/-- A continuous `L²` limit and one genuine increasing subsequence of the
phase-force ODE solutions, with both time-uniform `L²` and coefficient convergence. -/
theorem exists_phaseGalerkin_continuous_l2_limit
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) :
    ∃ a : GalerkinCoefficientIndex → (GalerkinTime →ᵇ ℂ), ∃ φ : ℕ → ℕ,
      ∃ U : GalerkinTime →ᵇ TorusVelocityL2,
        StrictMono φ ∧
        (∀ k i ε, 0 < ε → ∀ᶠ n in atTop, ∀ (t : ℝ) (ht : t ∈ Icc 0 1),
          ‖vectorFourierCoeff (phaseGalerkinVelocity ν hν phase (φ n) t) k i -
            a (k, i) ⟨t, ht⟩‖ < ε) ∧
        Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U) ∧
        U ⟨0, by norm_num⟩ = 0 ∧
        (∀ t : GalerkinTime, ‖U t‖ ^ 2 ≤ phaseGalerkinEnergyBound phase) ∧
        ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : GalerkinTime,
          ‖phaseGalerkinL2Curve ν hν phase (φ n) t - U t‖ < ε := by
  obtain ⟨a, φ, hφ, hcoeff, hcauchy⟩ := exists_phaseGalerkin_uniform_l2_cauchy_subsequence ν hν phase
  obtain ⟨U, hU⟩ := cauchySeq_tendsto_of_complete
    (phaseGalerkinL2Curve_cauchy_of_spatial_cauchy ν hν phase φ hcauchy)
  have hpoint (t : GalerkinTime) : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n) t)
      atTop (𝓝 (U t)) :=
    (BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto U |>.comp hU
  have hzero : U ⟨0, by norm_num⟩ = 0 := by
    have h := hpoint ⟨0, by norm_num⟩
    simp only [phaseGalerkinL2Curve_initial] at h
    exact (tendsto_nhds_unique h tendsto_const_nhds)
  refine ⟨a, φ, U, hφ, hcoeff, hU, hzero, ?_, ?_⟩
  · intro t
    have hnorm := ((hpoint t).norm).pow 2
    apply le_of_tendsto hnorm
    exact Eventually.of_forall fun n => by
      rw [phaseGalerkinL2Curve_norm_sq]
      exact phaseGalerkinVelocity_energy_bound ν hν phase (φ n) t.2
  · intro ε hε
    filter_upwards [Metric.tendsto_nhds.1 hU ε hε] with n hn
    intro t
    rw [← dist_eq_norm]
    exact (BoundedContinuousFunction.dist_coe_le_dist t).trans_lt hn

end AnomDiss

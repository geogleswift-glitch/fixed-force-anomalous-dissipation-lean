module

public import RequestProject.NSPhaseGalerkinSequence
public import RequestProject.NSFourierCoefficientTime

/-!
# Bounds and time equicontinuity for the chosen Galerkin coefficients

The constants use only the fixed phase, viscosity and frequency. Every fixed
mode belongs to all sufficiently large frequency boxes, so its actual temporal
Fourier coefficients have a uniform Lipschitz modulus along the chosen sequence.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

theorem exists_phaseForceL2Bound (phase : Phase) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ t ∈ Icc 0 1, l2sqV (gForce phase t) ≤ F := by
  have hc : ContinuousOn (fun t => l2sqV (gForce phase t)) (Icc 0 1) := by
    apply continuousOn_integral_cell' (by norm_num : (0 : ℝ) ≤ 1)
    exact continuousOn_finset_sum _ fun i _ =>
      (((continuous_apply i).comp_continuousOn (continuous_phaseForce phase).continuousOn).pow 2)
  obtain ⟨F, hF⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max F 0, le_max_right _ _, fun t ht => ?_⟩
  have hFt : |l2sqV (gForce phase t)| ≤ F := by
    simpa only [Real.norm_eq_abs] using hF t ht
  exact (le_abs_self _).trans (hFt.trans (le_max_left F 0))

def phaseForceL2Bound (phase : Phase) : ℝ := Classical.choose (exists_phaseForceL2Bound phase)

theorem phaseForceL2Bound_nonneg (phase : Phase) : 0 ≤ phaseForceL2Bound phase :=
  (Classical.choose_spec (exists_phaseForceL2Bound phase)).1

theorem phaseForce_l2_le (phase : Phase) {t : ℝ} (ht : t ∈ Icc 0 1) :
    l2sqV (gForce phase t) ≤ phaseForceL2Bound phase :=
  (Classical.choose_spec (exists_phaseForceL2Bound phase)).2 t ht

theorem fourierFrequencyBox_eventually_mem (k : Fin 2 → ℤ) :
    ∀ᶠ N : ℕ in atTop, k ∈ fourierFrequencyBox (N + 1) := by
  let B : ℕ := ∑ i : Fin 2, (k i).natAbs
  filter_upwards [eventually_ge_atTop B] with N hN
  rw [mem_fourierFrequencyBox]
  intro i
  have hi : (k i).natAbs ≤ B := Finset.single_le_sum
    (f := fun j : Fin 2 => (k j).natAbs) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hnat : (k i).natAbs ≤ N + 1 := hi.trans (hN.trans (Nat.le_succ N))
  have hint : ((k i).natAbs : ℤ) ≤ ((N + 1 : ℕ) : ℤ) := by exact_mod_cast hnat
  simpa only [Int.natCast_natAbs] using hint

def phaseGalerkinCoefficientLipschitzBound (ν : ℝ) (phase : Phase) (k : Fin 2 → ℤ) : ℝ :=
  2 * (ν * (fourierTestDerivativeBound k * (phaseGalerkinGradientBound ν phase + 4)) +
    (phaseForceL2Bound phase + 2) +
      (2 * phaseGalerkinEnergyBound phase + phaseGalerkinGradientBound ν phase))

theorem phaseGalerkin_coefficient_time_lipschitz (ν : ℝ) (hν : 0 < ν) (phase : Phase)
    (N : ℕ) {k : Fin 2 → ℤ} (hk : k ∈ fourierFrequencyBox (N + 1)) (i : Fin 2) :
    ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
      ‖vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N t) k i -
        vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N s) k i‖ ≤
          phaseGalerkinCoefficientLipschitzBound ν phase k * |t - s| := by
  exact fourier_galerkin_coefficient_time_lipschitz (fourierFrequencyBox (N + 1)) hk i hν.le
    (phaseGalerkinState ν hν phase N) (phaseGalerkinStateDerivative ν hν phase N) (gForce phase)
    (fun t _ => (gForce_slice_props phase t).2.1.continuous)
    (fun t ht => phaseGalerkinState_hasDerivAt ν hν phase N (t := t) ht)
    (fun t ht => phaseGalerkinVelocity_energy_bound ν hν phase N (t := t) ht)
    (fun t ht => phaseGalerkinVelocity_gradient_bound ν hν phase N (t := t) ht)
    (fun t ht => phaseForce_l2_le phase (t := t) ht)
    (fun t ht z => (Classical.choose_spec
      (exists_phase_fourier_galerkin_bounds (fourierFrequencyBox (N + 1)) hν phase)).2.2.1 t ht z)

/-- Each fixed actual Fourier coordinate has a uniform time modulus once
its frequency is retained; omitting finitely many cutoffs costs no subsequence. -/
theorem phaseGalerkin_coefficient_eventually_lipschitz (ν : ℝ) (hν : 0 < ν) (phase : Phase)
    (k : Fin 2 → ℤ) (i : Fin 2) :
    ∀ᶠ N : ℕ in atTop, ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
      ‖vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N t) k i -
        vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N s) k i‖ ≤
          phaseGalerkinCoefficientLipschitzBound ν phase k * |t - s| :=
  (fourierFrequencyBox_eventually_mem k).mono fun N hN =>
    phaseGalerkin_coefficient_time_lipschitz ν hν phase N hN i

theorem phaseGalerkin_coefficient_norm_sq_bound (ν : ℝ) (hν : 0 < ν) (phase : Phase)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) (k : Fin 2 → ℤ) (i : Fin 2) :
    ‖vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N t) k i‖ ^ 2 ≤
      phaseGalerkinEnergyBound phase := by
  let v := phaseGalerkinVelocity ν hν phase N t
  have hv := (phaseGalerkinVelocity_contDiff ν hν phase N t).continuous
  have h := realFourierTruncation_l2_error {k} v hv (phaseGalerkinVelocity_periodic ν hν phase N t)
  have hn : 0 ≤ l2sqV (v - realFourierTruncation {k} v) :=
    integral_nonneg fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
  simp only [Finset.sum_singleton] at h
  have hi : ‖vectorFourierCoeff v k i‖ ^ 2 ≤ ∑ j, ‖vectorFourierCoeff v k j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 2 => ‖vectorFourierCoeff v k j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hE := phaseGalerkinVelocity_energy_bound ν hν phase N ht
  change ‖vectorFourierCoeff v k i‖ ^ 2 ≤ _
  change l2sqV v ≤ _ at hE
  linarith

theorem phaseGalerkin_coefficient_norm_bound (ν : ℝ) (hν : 0 < ν) (phase : Phase)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) (k : Fin 2 → ℤ) (i : Fin 2) :
    ‖vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N t) k i‖ ≤
      sqrt (phaseGalerkinEnergyBound phase) :=
  Real.le_sqrt_of_sq_le (phaseGalerkin_coefficient_norm_sq_bound ν hν phase N ht k i)

end AnomDiss

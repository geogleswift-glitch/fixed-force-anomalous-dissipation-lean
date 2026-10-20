module

public import RequestProject.NSPhaseGalerkin
public import RequestProject.FourierFrequencyBox

/-!
# A chosen sequence of actual phase-force Galerkin solutions

The cutoffs are the concrete boxes of radius `N + 1`. Their selected solutions
satisfy uniform energy and enstrophy bounds, and their genuine spatial `L²`
tails are uniformly small when projected to any fixed sufficiently large box.
No PDE limit or compactness statement is assumed here.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

def phaseForceEnergy (phase : Phase) : ℝ :=
  ∫ s in (0 : ℝ)..1, l2sqV (gForce phase s)

def phaseGalerkinEnergyBound (phase : Phase) : ℝ := phaseForceEnergy phase * exp 1

def phaseGalerkinGradientBound (ν : ℝ) (phase : Phase) : ℝ :=
  (1 / ν) * phaseForceEnergy phase

def phaseGalerkinState (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) :
    ℝ → (fourierGalerkinModel (fourierFrequencyBox (N + 1))).State :=
  Classical.choose (exists_phase_fourier_galerkin_bounds (fourierFrequencyBox (N + 1)) hν phase)

def phaseGalerkinStateDerivative (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) (t : ℝ) :
    (fourierGalerkinModel (fourierFrequencyBox (N + 1))).State :=
  (fourierGalerkinModel (fourierFrequencyBox (N + 1))).nsField ν
      (phaseGalerkinState ν hν phase N t) +
    (fourierGalerkinModel (fourierFrequencyBox (N + 1))).projection
      (phaseForceContinuousMap phase t)

def phaseGalerkinVelocity (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) (t : ℝ) : Pt 2 → Pt 2 :=
  (fourierGalerkinModel (fourierFrequencyBox (N + 1))).eval (phaseGalerkinState ν hν phase N t)

def phaseGalerkinDerivative (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) (t : ℝ) : Pt 2 → Pt 2 :=
  (fourierGalerkinModel (fourierFrequencyBox (N + 1))).eval
    (phaseGalerkinStateDerivative ν hν phase N t)

theorem phaseGalerkinState_initial (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) :
    phaseGalerkinState ν hν phase N 0 = 0 :=
  (Classical.choose_spec
    (exists_phase_fourier_galerkin_bounds (fourierFrequencyBox (N + 1)) hν phase)).1

theorem phaseGalerkinState_hasDerivAt (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    HasDerivAt (phaseGalerkinState ν hν phase N) (phaseGalerkinStateDerivative ν hν phase N t) t :=
  (Classical.choose_spec
    (exists_phase_fourier_galerkin_bounds (fourierFrequencyBox (N + 1)) hν phase)).2.1 t ht

theorem phaseGalerkinVelocity_initial (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) :
    phaseGalerkinVelocity ν hν phase N 0 = 0 := by
  unfold phaseGalerkinVelocity
  rw [phaseGalerkinState_initial, map_zero]

theorem phaseGalerkinVelocity_mem (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) (t : ℝ) :
    phaseGalerkinVelocity ν hν phase N t ∈ solenoidalFourierSpace (fourierFrequencyBox (N + 1)) :=
  (phaseGalerkinState ν hν phase N t).2

theorem phaseGalerkinVelocity_contDiff (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (phaseGalerkinVelocity ν hν phase N t) :=
  (fourierGalerkinModel (fourierFrequencyBox (N + 1))).eval_contDiff _

theorem phaseGalerkinVelocity_periodic (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) (t : ℝ) :
    IsPeriodic (phaseGalerkinVelocity ν hν phase N t) :=
  (fourierGalerkinModel (fourierFrequencyBox (N + 1))).eval_periodic _

theorem phaseGalerkinVelocity_solenoidal (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ)
    (t : ℝ) (x : Pt 2) : divergence (phaseGalerkinVelocity ν hν phase N t) x = 0 :=
  (fourierGalerkinModel (fourierFrequencyBox (N + 1))).eval_solenoidal _ x

theorem phaseGalerkinVelocity_hasDerivAt (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 1) (x : Pt 2) :
    HasDerivAt (fun s => phaseGalerkinVelocity ν hν phase N s x)
      (phaseGalerkinDerivative ν hν phase N t x) t :=
  (fourierGalerkinModel (fourierFrequencyBox (N + 1))).hasDerivAt_eval
    (phaseGalerkinState_hasDerivAt ν hν phase N ht) x

theorem phaseGalerkinState_continuousOn (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) :
    ContinuousOn (phaseGalerkinState ν hν phase N) (Icc 0 1) := fun t ht =>
  (phaseGalerkinState_hasDerivAt ν hν phase N (t := t) ht).continuousAt.continuousWithinAt

theorem phaseGalerkinStateDerivative_continuousOn (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) :
    ContinuousOn (phaseGalerkinStateDerivative ν hν phase N) (Icc 0 1) := by
  let G := fourierGalerkinModel (fourierFrequencyBox (N + 1))
  change ContinuousOn (fun t => G.nsField ν (phaseGalerkinState ν hν phase N t) +
    G.projection (phaseForceContinuousMap phase t)) (Icc 0 1)
  exact ((G.contDiff_nsField ν).continuous.comp_continuousOn
    (phaseGalerkinState_continuousOn ν hν phase N)).add
      (G.continuousOn_projected_force (phaseForceContinuousMap phase)
        (by norm_num : (0 : ℝ) ≤ 1) (continuous_phaseForce phase).continuousOn)

theorem phaseGalerkinVelocity_continuousOn (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) :
    ContinuousOn (fun q : ℝ × Pt 2 => phaseGalerkinVelocity ν hν phase N q.1 q.2)
      (Icc 0 1 ×ˢ univ) :=
  (fourierGalerkinModel (fourierFrequencyBox (N + 1))).continuousOn_eval_curve
    (phaseGalerkinState_continuousOn ν hν phase N)

theorem phaseGalerkinDerivative_continuousOn (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) :
    ContinuousOn (fun q : ℝ × Pt 2 => phaseGalerkinDerivative ν hν phase N q.1 q.2)
      (Icc 0 1 ×ˢ univ) :=
  (fourierGalerkinModel (fourierFrequencyBox (N + 1))).continuousOn_eval_curve
    (phaseGalerkinStateDerivative_continuousOn ν hν phase N)

theorem phaseGalerkinVelocity_weak (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 1) (z : Pt 2 → Pt 2)
    (hz : z ∈ solenoidalFourierSpace (fourierFrequencyBox (N + 1))) :
    cellVectorPair z (phaseGalerkinDerivative ν hν phase N t) +
      cellVectorPair z (conv (phaseGalerkinVelocity ν hν phase N t)
        (phaseGalerkinVelocity ν hν phase N t)) =
      ν * cellVectorPair z (lap (phaseGalerkinVelocity ν hν phase N t)) +
        cellVectorPair z (gForce phase t) := by
  exact (Classical.choose_spec
    (exists_phase_fourier_galerkin_bounds (fourierFrequencyBox (N + 1)) hν phase)).2.2.1 t ht ⟨z, hz⟩

theorem phaseGalerkinVelocity_energy_bound (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    l2sqV (phaseGalerkinVelocity ν hν phase N t) ≤ phaseGalerkinEnergyBound phase :=
  (Classical.choose_spec
    (exists_phase_fourier_galerkin_bounds (fourierFrequencyBox (N + 1)) hν phase)).2.2.2.1 t ht

theorem phaseGalerkinVelocity_gradient_bound (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    (∫ x in cell 2, gradSqV (phaseGalerkinVelocity ν hν phase N t) x) ≤
      phaseGalerkinGradientBound ν phase :=
  (Classical.choose_spec
    (exists_phase_fourier_galerkin_bounds (fourierFrequencyBox (N + 1)) hν phase)).2.2.2.2.1 t ht

theorem phaseGalerkinVelocity_laplacian_bound (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ) :
    ν * (∫ s in (0 : ℝ)..1, l2sqV (lap (phaseGalerkinVelocity ν hν phase N s))) ≤
      phaseGalerkinGradientBound ν phase :=
  (Classical.choose_spec
    (exists_phase_fourier_galerkin_bounds (fourierFrequencyBox (N + 1)) hν phase)).2.2.2.2.2

/-- This is an actual spatial error, uniformly controlled in Galerkin index
and time by the fixed phase force and viscosity. -/
theorem phaseGalerkinVelocity_fourier_tail (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 1) {K : ℕ} (hK : 0 < K) :
    l2sqV (phaseGalerkinVelocity ν hν phase N t -
      realFourierTruncation (fourierFrequencyBox K) (phaseGalerkinVelocity ν hν phase N t)) ≤
      phaseGalerkinGradientBound ν phase / (4 * π ^ 2 * (K : ℝ) ^ 2) := by
  have htail := fourier_box_l2_error_le (phaseGalerkinVelocity ν hν phase N t)
    ((phaseGalerkinVelocity_contDiff ν hν phase N t).of_le (natCast_le_infty 2))
    (phaseGalerkinVelocity_periodic ν hν phase N t) hK
  exact htail.trans (div_le_div_of_nonneg_right
    (phaseGalerkinVelocity_gradient_bound ν hν phase N ht) (by positivity))

def phaseGalerkinTailBound (ν : ℝ) (phase : Phase) (K : ℕ) : ℝ :=
  phaseGalerkinGradientBound ν phase / (4 * π ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2)

theorem phaseGalerkinTailBound_tendsto_zero (ν : ℝ) (phase : Phase) :
    Tendsto (phaseGalerkinTailBound ν phase) atTop (𝓝 0) := by
  have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul
    (phaseGalerkinGradientBound ν phase / (4 * π ^ 2))
  have heq : (fun K : ℕ => phaseGalerkinGradientBound ν phase / (4 * π ^ 2) *
      (1 / ((K : ℝ) + 1)) ^ 2) = phaseGalerkinTailBound ν phase := by
    funext K
    simp only [phaseGalerkinTailBound, Nat.cast_add, Nat.cast_one,
      div_eq_mul_inv, one_mul, mul_inv_rev, inv_pow]
    ring
  simpa only [heq, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using h

/-- Uniform approximation of the whole sequence by one fixed finite block,
at all times in the original unit interval. -/
theorem phaseGalerkinVelocity_uniform_fourier_tail (ν : ℝ) (hν : 0 < ν) (phase : Phase)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ N : ℕ, ∀ t ∈ Icc 0 1,
      l2sqV (phaseGalerkinVelocity ν hν phase N t -
        realFourierTruncation (fourierFrequencyBox (K + 1))
          (phaseGalerkinVelocity ν hν phase N t)) < ε := by
  obtain ⟨K, hK⟩ := ((phaseGalerkinTailBound_tendsto_zero ν phase).eventually
    (Iio_mem_nhds hε)).exists
  refine ⟨K, fun N t ht => ?_⟩
  exact (phaseGalerkinVelocity_fourier_tail ν hν phase N ht (Nat.succ_pos K)).trans_lt hK

end AnomDiss

module

public import RequestProject.NSFourierGalerkin
public import RequestProject.NSGalerkinExistence
public import RequestProject.TimeSmoothForceContinuity
public import RequestProject.ForceRegularity

/-!
# Genuine Galerkin solutions for the manuscript's phase force

These existence theorems apply the constructed finite equations to the actual
`gForce` and zero horizontal initial datum used in the main theorem. All force
continuity and spatial membership evidence is proved from its definition.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

def phaseForceContinuousMap (phase : Phase) (t : ℝ) : C(Pt 2, Pt 2) :=
  ⟨gForce phase t, (gForce_slice_props phase t).2.1.continuous⟩

@[simp] theorem phaseForceContinuousMap_apply (phase : Phase) (t : ℝ) (x : Pt 2) :
    phaseForceContinuousMap phase t x = gForce phase t x := rfl

theorem continuous_phaseForce (phase : Phase) :
    Continuous (fun q : ℝ × Pt 2 => gForce phase q.1 q.2) :=
  ((force_regularity.1 phase).1.toIsTimeSmoothForce).continuous_uncurry

/-- Every finite truncation of the actual horizontal equation has a global
zero-data solution. There is no auxiliary existence hypothesis. -/
theorem exists_phase_fourier_galerkin (S : Finset (Fin 2 → ℤ)) {ν : ℝ}
    (hν : 0 < ν) (phase : Phase) :
    ∃ v V' : ℝ → Pt 2 → Pt 2,
      v 0 = 0 ∧
      (∀ t, v t ∈ solenoidalFourierSpace S) ∧
      (∀ t, V' t ∈ solenoidalFourierSpace S) ∧
      (∀ t, ContDiff ℝ ∞ (v t) ∧ IsPeriodic (v t) ∧ ∀ x, divergence (v t) x = 0) ∧
      (∀ t ∈ Icc 0 1, ∀ x, HasDerivAt (fun s => v s x) (V' t x) t) ∧
      ∀ t ∈ Icc 0 1, ∀ z ∈ solenoidalFourierSpace S,
        (∫ x in cell 2, dot (z x) (V' t x)) +
            (∫ x in cell 2, dot (z x) (conv (v t) (v t) x)) =
          ν * (∫ x in cell 2, dot (z x) (lap (v t) x)) +
            (∫ x in cell 2, dot (z x) (gForce phase t x)) :=
  exists_fourier_galerkin_curve S hν.le (by norm_num : (0 : ℝ) ≤ 1) 0
    ((solenoidalFourierSpace S).zero_mem) (phaseForceContinuousMap phase)
    (continuous_phaseForce phase).continuousOn

/-- Uniform energy, enstrophy and integrated second-derivative bounds for
the actual zero-data phase-force Galerkin systems. -/
theorem exists_phase_fourier_galerkin_bounds (S : Finset (Fin 2 → ℤ)) {ν : ℝ}
    (hν : 0 < ν) (phase : Phase) :
    ∃ u : ℝ → (fourierGalerkinModel S).State,
      u 0 = 0 ∧
      (∀ t ∈ Icc 0 1, HasDerivAt u
        ((fourierGalerkinModel S).nsField ν (u t) +
          (fourierGalerkinModel S).projection (phaseForceContinuousMap phase t)) t) ∧
      (∀ t ∈ Icc 0 1, ∀ z : (fourierGalerkinModel S).State,
        cellVectorPair ((fourierGalerkinModel S).eval z)
            ((fourierGalerkinModel S).eval ((fourierGalerkinModel S).nsField ν (u t) +
              (fourierGalerkinModel S).projection (phaseForceContinuousMap phase t))) +
          cellVectorPair ((fourierGalerkinModel S).eval z)
            (conv ((fourierGalerkinModel S).eval (u t)) ((fourierGalerkinModel S).eval (u t))) =
          ν * cellVectorPair ((fourierGalerkinModel S).eval z)
            (lap ((fourierGalerkinModel S).eval (u t))) +
          cellVectorPair ((fourierGalerkinModel S).eval z) (gForce phase t)) ∧
      (∀ t ∈ Icc 0 1, l2sqV ((fourierGalerkinModel S).eval (u t)) ≤
        (∫ s in (0 : ℝ)..1, l2sqV (gForce phase s)) * exp 1) ∧
      (∀ t ∈ Icc 0 1, (∫ x in cell 2, gradSqV ((fourierGalerkinModel S).eval (u t)) x) ≤
        (1 / ν) * (∫ s in (0 : ℝ)..1, l2sqV (gForce phase s))) ∧
      ν * (∫ s in (0 : ℝ)..1, l2sqV (lap ((fourierGalerkinModel S).eval (u s)))) ≤
        (1 / ν) * (∫ s in (0 : ℝ)..1, l2sqV (gForce phase s)) := by
  let G := fourierGalerkinModel S
  have hlap : ∀ v : G.State, lap (G.eval v) ∈ G.space := fun v =>
    lap_mem_solenoidalFourierSpace S v.2
  obtain ⟨u, hu0, hud, hweak, hE, _, hG, hL⟩ := G.exists_ns_galerkin_bounds hν
    (by norm_num : (0 : ℝ) ≤ 1) hlap (phaseForceContinuousMap phase)
    (continuous_phaseForce phase).continuousOn 0
  have hZ : l2sqV (G.eval 0) = 0 := by simp [l2sqV]
  have hD : (∫ x in cell 2, gradSqV (G.eval 0) x) = 0 := by
    simp [gradSqV, pd]
  have hforce : ∀ t, (phaseForceContinuousMap phase t : Pt 2 → Pt 2) = gForce phase t :=
    fun _ => rfl
  refine ⟨u, hu0, hud, hweak, ?_, ?_, ?_⟩
  · simpa only [hZ, zero_add, hforce, G] using hE
  · simpa only [hD, zero_add, hforce, G] using hG
  · simpa only [hD, zero_add, hforce, G] using hL

end AnomDiss

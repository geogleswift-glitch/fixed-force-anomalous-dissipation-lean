module

public import RequestProject.NSGalerkinFourierEquation
public import RequestProject.NSPhaseGalerkinSequence

/-!
# Integrated actual Galerkin coefficient equations

The coefficient ODE is integrated by the fundamental theorem of calculus.
For the manuscript's zero horizontal initial datum this gives the exact
integral equation at every retained frequency on the whole unit interval.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

/-- The actual retained complex Fourier equation satisfies the ordinary
fundamental theorem of calculus; no evolution equation is assumed separately. -/
theorem fourierGalerkin_coefficient_integral_eq (S : Finset (Fin 2 → ℤ))
    {k : Fin 2 → ℤ} (hk : k ∈ S) (i : Fin 2) (ν : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (u : ℝ → (fourierGalerkinModel S).State) (f : ℝ → C(Pt 2, Pt 2))
    (hf : ContinuousOn (fun q : ℝ × Pt 2 => f q.1 q.2) (Icc 0 T ×ˢ univ))
    (hud : ∀ t ∈ Icc 0 T, HasDerivAt u ((fourierGalerkinModel S).nsField ν (u t) +
      (fourierGalerkinModel S).projection (f t)) t) :
    ∀ t ∈ Icc 0 T,
      vectorFourierCoeff ((fourierGalerkinModel S).eval (u t)) k i =
        vectorFourierCoeff ((fourierGalerkinModel S).eval (u 0)) k i +
          ∫ s in (0 : ℝ)..t, galerkinFourierRHS ν ((fourierGalerkinModel S).eval (u s)) (f s) k i := by
  let G := fourierGalerkinModel S
  have hu : ContinuousOn u (Icc 0 T) := fun t ht => (hud t ht).continuousAt.continuousWithinAt
  have hstate : ContinuousOn (fun s => G.nsField ν (u s) + G.projection (f s)) (Icc 0 T) :=
    ((G.contDiff_nsField ν).continuous.comp_continuousOn hu).add
      (G.continuousOn_projected_force f hT hf)
  have hr : ContinuousOn (fun s => galerkinFourierRHS ν (G.eval (u s)) (f s) k i) (Icc 0 T) := by
    refine ((G.fourierCoeffCLM k i).continuous.comp_continuousOn hstate).congr ?_
    intro s hs
    exact (fourierGalerkin_rhs_coefficient S hk i ν (u s) (f s)).symm
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hi : IntervalIntegrable (fun s => galerkinFourierRHS ν (G.eval (u s)) (f s) k i)
      volume 0 t := (hr.mono hsub).intervalIntegrable_of_Icc ht.1
  have hd : ∀ s ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun r => vectorFourierCoeff (G.eval (u r)) k i)
        (galerkinFourierRHS ν (G.eval (u s)) (f s) k i) s := by
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact hasDerivAt_fourierGalerkin_coefficient S hk i ν u f (hud s (hsub hs))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [hFTC]
  abel

/-- The chosen actual phase-force sequence satisfies the zero-data Fourier
integral equation at every frequency included in its concrete cutoff. -/
theorem phaseGalerkin_coefficient_integral_eq (ν : ℝ) (hν : 0 < ν) (phase : Phase) (N : ℕ)
    {k : Fin 2 → ℤ} (hk : k ∈ fourierFrequencyBox (N + 1)) (i : Fin 2)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N t) k i =
      ∫ s in (0 : ℝ)..t,
        galerkinFourierRHS ν (phaseGalerkinVelocity ν hν phase N s) (gForce phase s) k i := by
  have h := fourierGalerkin_coefficient_integral_eq (fourierFrequencyBox (N + 1)) hk i ν
    (by norm_num : (0 : ℝ) ≤ 1) (phaseGalerkinState ν hν phase N) (phaseForceContinuousMap phase)
    (continuous_phaseForce phase).continuousOn
    (fun s hs => phaseGalerkinState_hasDerivAt ν hν phase N (t := s) hs) t ht
  change vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N t) k i =
    vectorFourierCoeff (phaseGalerkinVelocity ν hν phase N 0) k i +
      ∫ s in (0 : ℝ)..t,
        galerkinFourierRHS ν (phaseGalerkinVelocity ν hν phase N s) (gForce phase s) k i at h
  rw [phaseGalerkinVelocity_initial] at h
  have hz : vectorFourierCoeff (0 : Pt 2 → Pt 2) k i = 0 := by
    simp [vectorFourierCoeff_apply, fc]
  simpa only [hz, zero_add] using h

end AnomDiss

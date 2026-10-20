module

public import RequestProject.NSFourierModeTests

/-!
# Dimension-independent time modulus of actual Fourier coefficients

The two real Galerkin tests at a retained frequency read the real and imaginary
parts of the genuine velocity Fourier coefficient. Their Lipschitz constants
are independent of the cutoff, under the proven uniform energy and enstrophy
bounds.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

/-- Actual Fourier coefficients of finite Galerkin trajectories are uniformly
Lipschitz at each fixed frequency once that frequency is retained. -/
theorem fourier_galerkin_coefficient_time_lipschitz
    (S : Finset (Fin 2 → ℤ)) {k : Fin 2 → ℤ} (hk : k ∈ S) (i : Fin 2)
    {ν T E H F : ℝ} (hν : 0 ≤ ν)
    (u u' : ℝ → (fourierGalerkinModel S).State) (g : ℝ → Pt 2 → Pt 2)
    (hg : ∀ t ∈ Icc 0 T, Continuous (g t))
    (hud : ∀ t ∈ Icc 0 T, HasDerivAt u (u' t) t)
    (hE : ∀ t ∈ Icc 0 T, l2sqV ((fourierGalerkinModel S).eval (u t)) ≤ E)
    (hH : ∀ t ∈ Icc 0 T,
      (∫ x in cell 2, gradSqV ((fourierGalerkinModel S).eval (u t)) x) ≤ H)
    (hF : ∀ t ∈ Icc 0 T, l2sqV (g t) ≤ F)
    (hweak : ∀ t ∈ Icc 0 T, ∀ w : (fourierGalerkinModel S).State,
      cellVectorPair ((fourierGalerkinModel S).eval w) ((fourierGalerkinModel S).eval (u' t)) +
          cellVectorPair ((fourierGalerkinModel S).eval w)
            (conv ((fourierGalerkinModel S).eval (u t)) ((fourierGalerkinModel S).eval (u t))) =
        ν * cellVectorPair ((fourierGalerkinModel S).eval w)
          (lap ((fourierGalerkinModel S).eval (u t))) +
            cellVectorPair ((fourierGalerkinModel S).eval w) (g t)) :
    ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      ‖vectorFourierCoeff ((fourierGalerkinModel S).eval (u t)) k i -
          vectorFourierCoeff ((fourierGalerkinModel S).eval (u s)) k i‖ ≤
        (2 * (ν * (fourierTestDerivativeBound k * (H + 4)) +
          (F + 2) + (2 * E + H))) * |t - s| := by
  let G := fourierGalerkinModel S
  let wR : G.State := fourierGalerkinModeTest S hk (EuclideanSpace.single i (1 : ℂ))
  let wI : G.State := fourierGalerkinModeTest S hk (EuclideanSpace.single i Complex.I)
  have hAR : ∀ x j, |G.eval wR x j| ≤ 1 := by
    intro x j
    simpa only [G, wR, fourierGalerkinModeTest_eval, EuclideanSpace.norm_single, norm_one] using
      projected_realFourierMode_bound k (EuclideanSpace.single i (1 : ℂ)) x j
  have hAI : ∀ x j, |G.eval wI x j| ≤ 1 := by
    intro x j
    simpa only [G, wI, fourierGalerkinModeTest_eval, EuclideanSpace.norm_single,
      Complex.norm_I] using
      projected_realFourierMode_bound k (EuclideanSpace.single i Complex.I) x j
  have hDR : ∀ x j l, |pd l (G.eval wR) x j| ≤ fourierTestDerivativeBound k := by
    intro x j l
    simpa only [G, wR, fourierGalerkinModeTest_eval, EuclideanSpace.norm_single, norm_one,
      mul_one] using
      projected_realFourierMode_derivative_bound k (EuclideanSpace.single i (1 : ℂ)) x j l
  have hDI : ∀ x j l, |pd l (G.eval wI) x j| ≤ fourierTestDerivativeBound k := by
    intro x j l
    simpa only [G, wI, fourierGalerkinModeTest_eval, EuclideanSpace.norm_single,
      Complex.norm_I, mul_one] using
      projected_realFourierMode_derivative_bound k (EuclideanSpace.single i Complex.I) x j l
  have hR := G.test_coefficient_lipschitz hν (by norm_num : (0 : ℝ) ≤ 1)
    (fourierTestDerivativeBound_nonneg k) u u' g wR hg hAR hDR hud hE hH hF
    (fun t ht => hweak t ht wR)
  have hI := G.test_coefficient_lipschitz hν (by norm_num : (0 : ℝ) ≤ 1)
    (fourierTestDerivativeBound_nonneg k) u u' g wI hg hAI hDI hud hE hH hF
    (fun t ht => hweak t ht wI)
  have hreadR (r : ℝ) :
      cellVectorPair (G.eval wR) (G.eval (u r)) = (vectorFourierCoeff (G.eval (u r)) k i).re :=
    projected_realFourierMode_reads_re k i (G.eval (u r))
      ((G.eval_contDiff (u r)).of_le (natCast_le_infty 1))
      (G.eval_periodic (u r)) (G.eval_solenoidal (u r))
  have hreadI (r : ℝ) :
      cellVectorPair (G.eval wI) (G.eval (u r)) = (vectorFourierCoeff (G.eval (u r)) k i).im :=
    projected_realFourierMode_reads_im k i (G.eval (u r))
      ((G.eval_contDiff (u r)).of_le (natCast_le_infty 1))
      (G.eval_periodic (u r)) (G.eval_solenoidal (u r))
  intro s hs t ht
  have hr := hR s hs t ht
  have hi := hI s hs t ht
  rw [hreadR t, hreadR s] at hr
  rw [hreadI t, hreadI s] at hi
  simp only [one_mul] at hr hi
  have hb := Complex.norm_le_abs_re_add_abs_im
    (vectorFourierCoeff (G.eval (u t)) k i - vectorFourierCoeff (G.eval (u s)) k i)
  simp only [Complex.sub_re, Complex.sub_im] at hb
  change ‖vectorFourierCoeff (G.eval (u t)) k i - vectorFourierCoeff (G.eval (u s)) k i‖ ≤ _
  nlinarith

end AnomDiss

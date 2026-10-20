module

public import RequestProject.FourierHeatDuhamelSmoothing
public import RequestProject.FourierSobolevInterpolation

/-!
# Time estimates from actual Fourier rate energies

Finite coefficient vectors permit the Hilbert-space integral estimate
before taking the infinite sum. Thus a uniform square-energy bound on
the actual rates yields a Lipschitz square-energy bound on increments.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff
noncomputable section

namespace AnomDiss

theorem integral_finiteFourierWeightedVector {ι : Type*} [Fintype ι]
    (eigen : ι → ℝ) (p a b : ℝ) (F : ℝ → ι → ℂ)
    (hF : ∀ k, Continuous (fun s => F s k)) :
    (∫ s in a..b, finiteFourierWeightedVector eigen p (F s)) =
      finiteFourierWeightedVector eigen p (fun k => ∫ s in a..b, F s k) := by
  let H : ℝ → EuclideanSpace ℂ ι := fun s => finiteFourierWeightedVector eigen p (F s)
  have hc : Continuous H := by
    apply (PiLp.continuous_toLp 2 (fun _ : ι => ℂ)).comp
    exact continuous_pi fun k => (hF k).fun_const_smul ((1 + eigen k) ^ (p / 2))
  apply PiLp.ext
  intro k
  let L : EuclideanSpace ℂ ι →L[ℝ] ℂ := PiLp.proj 2 (fun _ : ι => ℂ) k
  change L (∫ s in a..b, H s) = _
  rw [← L.intervalIntegral_comp_comm (hc.intervalIntegrable a b)]
  change (∫ s in a..b, (1 + eigen k) ^ (p / 2) • F s k) = _
  rw [intervalIntegral.integral_smul]
  rfl

theorem finite_fourier_integral_energy_le {ι : Type*} [Fintype ι]
    (eigen : ι → ℝ) (heigen : ∀ k, 0 ≤ eigen k) {p a b B : ℝ}
    (hab : a ≤ b) (hB : 0 ≤ B) (F : ℝ → ι → ℂ)
    (hF : ∀ k, Continuous (fun s => F s k))
    (henergy : ∀ s ∈ Icc a b, (∑ k, (1 + eigen k) ^ p * ‖F s k‖ ^ 2) ≤ B) :
    (∑ k, (1 + eigen k) ^ p * ‖∫ s in a..b, F s k‖ ^ 2) ≤ B * (b - a) ^ 2 := by
  have hn (s : ℝ) (hs : s ∈ Icc a b) :
      ‖finiteFourierWeightedVector eigen p (F s)‖ ≤ Real.sqrt B := by
    have he := henergy s hs
    rw [← norm_sq_finiteFourierWeightedVector eigen heigen] at he
    nlinarith [norm_nonneg (finiteFourierWeightedVector eigen p (F s)),
      Real.sqrt_nonneg B, Real.sq_sqrt hB]
  have hi : IntervalIntegrable (fun _ : ℝ => Real.sqrt B) volume a b := intervalIntegrable_const
  have h := intervalIntegral.norm_integral_le_of_norm_le hab
    (Eventually.of_forall fun s hs => hn s ⟨hs.1.le, hs.2⟩) hi
  rw [integral_finiteFourierWeightedVector eigen p a b F hF,
    intervalIntegral.integral_const] at h
  simp only [smul_eq_mul] at h
  have hb : 0 ≤ (b-a) * Real.sqrt B := mul_nonneg (sub_nonneg.mpr hab) (Real.sqrt_nonneg _)
  have hh := (sq_le_sq₀ (norm_nonneg _) hb).mpr h
  rw [norm_sq_finiteFourierWeightedVector eigen heigen, mul_pow, Real.sq_sqrt hB] at hh
  nlinarith only [hh]

theorem fourier_integral_energy_le {p a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B)
    (F : ℝ → (Fin 2 → ℤ) → ℂ) (hF : ∀ k, Continuous (fun s => F s k))
    (henergy : ∀ s ∈ Icc a b,
      Summable (fun k => (1 + fourierEigenvalue k) ^ p * ‖F s k‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ p * ‖F s k‖ ^ 2) ≤ B) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ p * ‖∫ s in a..b, F s k‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ p * ‖∫ s in a..b, F s k‖ ^ 2) ≤ B * (b-a) ^ 2 := by
  have hn (k : Fin 2 → ℤ) :
      0 ≤ (1 + fourierEigenvalue k) ^ p * ‖∫ s in a..b, F s k‖ ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  have hf (S : Finset (Fin 2 → ℤ)) :
      (∑ k ∈ S, (1 + fourierEigenvalue k) ^ p * ‖∫ s in a..b, F s k‖ ^ 2) ≤ B * (b-a) ^ 2 := by
    have h := finite_fourier_integral_energy_le (p := p)
      (fun k : S => fourierEigenvalue k) (fun k => fourierEigenvalue_nonneg k)
      hab hB (fun s (k : S) => F s k) (fun k => hF k) (fun s hs => by
        rw [Finset.sum_coe_sort S (fun k : Fin 2 → ℤ =>
          (1 + fourierEigenvalue k) ^ p * ‖F s k‖ ^ 2)]
        exact ((henergy s hs).1.sum_le_tsum S
          (fun k _ => mul_nonneg (Real.rpow_nonneg
            (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _))).trans (henergy s hs).2)
    rw [Finset.sum_coe_sort S (fun k : Fin 2 → ℤ =>
      (1 + fourierEigenvalue k) ^ p * ‖∫ s in a..b, F s k‖ ^ 2)] at h
    exact h
  exact ⟨summable_of_sum_le hn hf, Real.tsum_le_of_sum_le hn hf⟩

end AnomDiss

module

public import RequestProject.FourierGalerkinApproximation

/-!
# Spectral H¹ control of actual Fourier tails

The weights are the true eigenvalues `4π²|k|²`. The identities are derived
from periodic integration by parts and Parseval; no compactness or existence
assumption is introduced.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

def vectorFourierEnergy (v : Pt 2 → Pt 2) (k : Fin 2 → ℤ) : ℝ :=
  ∑ i, ‖vectorFourierCoeff v k i‖ ^ 2

lemma vectorFourierEnergy_nonneg (v : Pt 2 → Pt 2) (k : Fin 2 → ℤ) :
    0 ≤ vectorFourierEnergy v k := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem vectorFourierCoeff_pd (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v)
    (hp : IsPeriodic v) (j : Fin 2) (k : Fin 2 → ℤ) :
    vectorFourierCoeff (pd j v) k =
      (2 * π * Complex.I * (k j : ℂ)) • vectorFourierCoeff v k := by
  ext i
  have hc : ContDiff ℝ 1 (fun x => v x i) := contDiff_pi.1 hv i
  have he : pd j (fun x => (v x i : ℂ)) = fun x => (pd j v x i : ℂ) := by
    change pd j (fun x => Complex.ofRealCLM (v x i)) = _
    rw [pd_clm_fun Complex.ofRealCLM _ j (hc.differentiable one_ne_zero)]
    funext x
    rw [pd_component v x (hv.differentiable one_ne_zero x)]
    rfl
  simp only [vectorFourierCoeff_apply, PiLp.smul_apply, smul_eq_mul]
  rw [← he]
  exact fc_pd _ (Complex.ofRealCLM.contDiff.comp hc)
    (fun x n => by
      change (v (x + intVec n) i : ℂ) = (v x i : ℂ)
      rw [hp]) j k

lemma norm_fourierDerivativeFactor_sq (k : Fin 2 → ℤ) (j : Fin 2) :
    ‖(2 * π * Complex.I * (k j : ℂ))‖ ^ 2 = 4 * π ^ 2 * (k j : ℝ) ^ 2 := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, Complex.norm_intCast, mul_one, mul_pow, sq_abs]
  norm_num

theorem vectorFourierEnergy_pd (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v)
    (hp : IsPeriodic v) (j : Fin 2) (k : Fin 2 → ℤ) :
    vectorFourierEnergy (pd j v) k =
      (4 * π ^ 2 * (k j : ℝ) ^ 2) * vectorFourierEnergy v k := by
  simp only [vectorFourierEnergy, vectorFourierCoeff_pd v hv hp,
    PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_mul, mul_pow, norm_fourierDerivativeFactor_sq]

theorem vectorFourierEnergy_gradient (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v)
    (hp : IsPeriodic v) (k : Fin 2 → ℤ) :
    (∑ j, vectorFourierEnergy (pd j v) k) =
      fourierEigenvalue k * vectorFourierEnergy v k := by
  simp only [vectorFourierEnergy_pd v hv hp, ← Finset.sum_mul]
  congr 1
  unfold fourierEigenvalue euclNorm
  rw [Real.sq_sqrt (by positivity)]
  simp only [intVec, Finset.mul_sum]

theorem sum_l2sqV_pd_eq_gradient (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 2 v) :
    (∑ j, l2sqV (pd j v)) = ∫ x in cell 2, gradSqV v x := by
  have hj : ∀ j, Continuous (pd j v) := fun j =>
    (contDiff_pd_of_C2 v hv j).continuous
  simp only [l2sqV]
  rw [← integral_finset_sum (f := fun j x => ∑ i, pd j v x i ^ 2) _
    (fun j _ => integrableOn_cell_of_continuous (continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp (hj j)).pow 2))]
  rfl

/-- The actual torus squared gradient equals the Fourier H¹ energy. -/
theorem parseval_gradient_cell (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 2 v)
    (hp : IsPeriodic v) :
    HasSum (fun k => fourierEigenvalue k * vectorFourierEnergy v k)
      (∫ x in cell 2, gradSqV v x) := by
  have hs : HasSum (fun k => ∑ j, vectorFourierEnergy (pd j v) k)
      (∑ j, l2sqV (pd j v)) :=
    hasSum_sum fun j _ => parseval_vector_cell (pd j v)
      (contDiff_pd_of_C2 v hv j).continuous (isPeriodic_pd v hp j)
  rw [sum_l2sqV_pd_eq_gradient v hv] at hs
  exact hs.congr_fun fun k => (vectorFourierEnergy_gradient v (hv.of_le (by norm_num)) hp k).symm

lemma hasSum_fourier_tail (v : Pt 2 → Pt 2) (hv : Continuous v)
    (hp : IsPeriodic v) (S : Finset (Fin 2 → ℤ)) :
    HasSum (fun k => if k ∈ S then 0 else vectorFourierEnergy v k)
      (l2sqV v - ∑ k ∈ S, vectorFourierEnergy v k) := by
  have hfinite : HasSum (fun k => if k ∈ S then vectorFourierEnergy v k else 0)
      (∑ k ∈ S, vectorFourierEnergy v k) := by
    have h := hasSum_sum_of_ne_finset_zero
      (f := fun k => if k ∈ S then vectorFourierEnergy v k else 0)
      (s := S) (L := SummationFilter.unconditional _) (fun k hk => if_neg hk)
    simpa only [Finset.sum_ite_mem, Finset.inter_self] using h
  have hs := (parseval_vector_cell v hv hp).sub hfinite
  exact hs.congr_fun fun k => by split_ifs <;> simp [vectorFourierEnergy]

/-- A lower frequency weight on the omitted modes bounds their L² tail by
the true gradient energy divided by that weight. -/
theorem fourier_tail_le_gradient_div (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 2 v)
    (hp : IsPeriodic v) (S : Finset (Fin 2 → ℤ)) {R : ℝ} (hR : 0 < R)
    (hfreq : ∀ k ∉ S, R ≤ fourierEigenvalue k) :
    l2sqV v - ∑ k ∈ S, vectorFourierEnergy v k ≤
      (∫ x in cell 2, gradSqV v x) / R := by
  have htail := (hasSum_fourier_tail v hv.continuous hp S).mul_left R
  have hbound := hasSum_le (fun k => show
      R * (if k ∈ S then 0 else vectorFourierEnergy v k) ≤
        fourierEigenvalue k * vectorFourierEnergy v k from by
      by_cases hk : k ∈ S
      · simp only [if_pos hk, mul_zero]
        exact mul_nonneg (fourierEigenvalue_nonneg k) (vectorFourierEnergy_nonneg v k)
      · rw [if_neg hk]
        exact mul_le_mul_of_nonneg_right (hfreq k hk) (vectorFourierEnergy_nonneg v k))
    htail (parseval_gradient_cell v hv hp)
  rw [le_div_iff₀ hR]
  simpa only [mul_comm] using hbound

theorem realFourierTruncation_l2_error_le_gradient_div
    (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 2 v) (hp : IsPeriodic v)
    (S : Finset (Fin 2 → ℤ)) {R : ℝ} (hR : 0 < R)
    (hfreq : ∀ k ∉ S, R ≤ fourierEigenvalue k) :
    l2sqV (v - realFourierTruncation S v) ≤ (∫ x in cell 2, gradSqV v x) / R :=
  (realFourierTruncation_l2_error S v hv.continuous hp).trans
    (fourier_tail_le_gradient_div v hv hp S hR hfreq)

end AnomDiss

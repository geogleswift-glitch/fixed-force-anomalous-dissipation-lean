module

public import RequestProject.FourierGalerkinSpectral

/-!
# Increasing Fourier cutoffs and uniform high-frequency tails

These concrete cutoffs exhaust the integer lattice. The omitted-frequency
eigenvalue estimate converts a uniform genuine H¹ bound into a uniform L²
approximation estimate, independently of the Galerkin dimension.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

def fourierFrequencyBox (N : ℕ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) (N : ℤ)

@[simp] lemma mem_fourierFrequencyBox (N : ℕ) (k : Fin 2 → ℤ) :
    k ∈ fourierFrequencyBox N ↔ ∀ i, |k i| ≤ (N : ℤ) := by
  simp only [fourierFrequencyBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

theorem fourierFrequencyBox_mono {N M : ℕ} (hNM : N ≤ M) :
    fourierFrequencyBox N ⊆ fourierFrequencyBox M := by
  intro k hk
  rw [mem_fourierFrequencyBox] at hk ⊢
  exact fun i => (hk i).trans (by exact_mod_cast hNM)

theorem fourierEigenvalue_outside_box (N : ℕ) (k : Fin 2 → ℤ)
    (hk : k ∉ fourierFrequencyBox N) :
    4 * π ^ 2 * (N : ℝ) ^ 2 ≤ fourierEigenvalue k := by
  rw [mem_fourierFrequencyBox] at hk
  push_neg at hk
  obtain ⟨i, hi⟩ := hk
  have hreal : (N : ℝ) < |(k i : ℝ)| := by exact_mod_cast hi
  have hsq : (N : ℝ) ^ 2 ≤ (k i : ℝ) ^ 2 := by
    have h := (sq_le_sq₀ (Nat.cast_nonneg N) (abs_nonneg (k i : ℝ))).2 hreal.le
    simpa only [sq_abs] using h
  have hsum : (k i : ℝ) ^ 2 ≤ ∑ j : Fin 2, (k j : ℝ) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (k j : ℝ)) (Finset.mem_univ i)
  unfold fourierEigenvalue euclNorm
  rw [Real.sq_sqrt (by positivity)]
  simp only [intVec]
  exact mul_le_mul_of_nonneg_left (hsq.trans hsum) (by positivity)

/-- A uniform H¹ bound gives a dimension-independent L² tail bound for the
concrete increasing Fourier boxes. -/
theorem fourier_box_l2_error_le (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 2 v)
    (hp : IsPeriodic v) {N : ℕ} (hN : 0 < N) :
    l2sqV (v - realFourierTruncation (fourierFrequencyBox N) v) ≤
      (∫ x in cell 2, gradSqV v x) / (4 * π ^ 2 * (N : ℝ) ^ 2) := by
  apply realFourierTruncation_l2_error_le_gradient_div v hv hp
    (fourierFrequencyBox N) (by positivity)
  exact fun k hk => fourierEigenvalue_outside_box N k hk

theorem solenoidal_fourier_box_l2_error_le (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 2 v)
    (hp : IsPeriodic v) (hdiv : ∀ x, divergence v x = 0) {N : ℕ} (hN : 0 < N) :
    l2sqV (v - solenoidalFourierPolynomial (fourierFrequencyBox N) (vectorFourierCoeff v)) ≤
      (∫ x in cell 2, gradSqV v x) / (4 * π ^ 2 * (N : ℝ) ^ 2) := by
  rw [solenoidalFourierPolynomial_eq_realTruncation _ v (hv.of_le (by norm_num)) hp hdiv]
  exact fourier_box_l2_error_le v hv hp hN

end AnomDiss

module

public import RequestProject.NSGalerkinModeTime
public import RequestProject.FourierGalerkinDensity
public import RequestProject.NSFourierGalerkin

/-!
# Actual Fourier coefficients as finite Galerkin tests

A Fourier coefficient of a real solenoidal velocity is tested by the genuine
Leray-projected real spatial mode. The tests belong to the finite Fourier
space whenever their frequency is included.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

/-- Pairing a real Fourier mode with the actual velocity gives the real part
of the corresponding complex Fourier pairing. -/
theorem realFourierMode_cellPair (k : Fin 2 → ℤ) (a : FourierVelocity)
    (v : Pt 2 → Pt 2) (hv : Continuous v) :
    cellVectorPair (realFourierMode k a) v = (inner ℂ a (vectorFourierCoeff v k)).re := by
  have hcmp (i : Fin 2) :
      (∫ x in cell 2, realFourierMode k a x i * v x i) =
        (conj (a i) * fc (fun x => (v x i : ℂ)) k).re := by
    have hi : IntegrableOn (fun x => (v x i : ℂ) * expChar (-intVec k) x) (cell 2) :=
      ((Complex.continuous_ofReal.comp ((continuous_apply i).comp hv)).mul
        (continuous_expChar _)).continuousOn.integrableOn_compact isCompact_Icc
    calc
      (∫ x in cell 2, realFourierMode k a x i * v x i) =
          ∫ x in cell 2, (conj (a i) * ((v x i : ℂ) * expChar (-intVec k) x)).re := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x _
        dsimp only
        rw [expChar_neg_eq_conj]
        simp only [realFourierMode, Complex.mul_re, Complex.mul_im,
          Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      _ = (∫ x in cell 2, conj (a i) * ((v x i : ℂ) * expChar (-intVec k) x)).re :=
        integral_re (hi.const_mul _)
      _ = (conj (a i) * fc (fun x => (v x i : ℂ)) k).re := by
        rw [integral_const_mul]
        rfl
  unfold cellVectorPair dot
  rw [integral_finset_sum (f := fun i x => realFourierMode k a x i * v x i) _
    (fun i _ => integrableOn_cell_of_continuous
      (((continuous_apply i).comp (contDiff_realFourierMode k a).continuous).mul
        ((continuous_apply i).comp hv)))]
  simp only [hcmp, PiLp.inner_apply, RCLike.inner_apply, vectorFourierCoeff_apply,
    Fin.sum_univ_two, Complex.add_re]
  simp [mul_comm]

/-- Leray projection of the spatial test preserves its actual pairing with
a solenoidal velocity. -/
theorem projected_realFourierMode_cellPair (k : Fin 2 → ℤ) (a : FourierVelocity)
    (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v) (hp : IsPeriodic v)
    (hdiv : ∀ x, divergence v x = 0) :
    cellVectorPair (realFourierMode k (fourierLeray k a)) v =
      (inner ℂ a (vectorFourierCoeff v k)).re := by
  rw [realFourierMode_cellPair k _ v hv.continuous, fourierLeray_self_adjoint,
    fourierLeray_vectorFourierCoeff v hv hp hdiv]

/-- A projected individual test mode belongs to the genuine finite spatial
Fourier range whenever the frequency is retained. -/
theorem projected_realFourierMode_mem (S : Finset (Fin 2 → ℤ))
    {k : Fin 2 → ℤ} (hk : k ∈ S) (a : FourierVelocity) :
    realFourierMode k (fourierLeray k a) ∈ solenoidalFourierSpace S := by
  refine ⟨fun j => if j.1 = k then a else 0, ?_⟩
  funext x
  change (∑ j ∈ S, realFourierMode j (fourierLeray j
    (fourierCoefficientExtension S (fun j => if j.1 = k then a else 0) j)) x) = _
  rw [Finset.sum_eq_single k]
  · simp [fourierCoefficientExtension_mem S _ k hk]
  · intro j hj hjk
    simp only [fourierCoefficientExtension_mem S _ j hj, if_neg hjk,
      map_zero, realFourierMode_zero, Pi.zero_apply]
  · exact fun h => (h hk).elim

/-- The actual fixed Fourier test has a dimension-independent amplitude
bound, inherited from the genuine orthogonal multiplier. -/
theorem projected_realFourierMode_bound (k : Fin 2 → ℤ) (a : FourierVelocity)
    (x : Pt 2) (i : Fin 2) :
    |realFourierMode k (fourierLeray k a) x i| ≤ ‖a‖ := by
  calc
    |realFourierMode k (fourierLeray k a) x i| ≤
        ‖fourierLeray k a i * expChar (intVec k) x‖ := Complex.abs_re_le_norm _
    _ = ‖fourierLeray k a i‖ := by rw [norm_mul, norm_expChar, mul_one]
    _ ≤ ‖fourierLeray k a‖ := PiLp.norm_apply_le _ i
    _ ≤ ‖a‖ := norm_fourierLeray_apply_le k a

theorem realFourierMode_component_bound (k : Fin 2 → ℤ) (a : FourierVelocity)
    (x : Pt 2) (i : Fin 2) : |realFourierMode k a x i| ≤ ‖a‖ := by
  calc
    |realFourierMode k a x i| ≤ ‖a i * expChar (intVec k) x‖ := Complex.abs_re_le_norm _
    _ = ‖a i‖ := by rw [norm_mul, norm_expChar, mul_one]
    _ ≤ ‖a‖ := PiLp.norm_apply_le _ i

/-- The fixed mode's first-derivative factor, independent of the cutoff. -/
def fourierTestDerivativeBound (k : Fin 2 → ℤ) : ℝ :=
  2 * π * (|(k 0 : ℝ)| + |(k 1 : ℝ)|)

theorem fourierTestDerivativeBound_nonneg (k : Fin 2 → ℤ) :
    0 ≤ fourierTestDerivativeBound k := by unfold fourierTestDerivativeBound; positivity

/-- The derivative bound for the actual projected spatial Fourier test. -/
theorem projected_realFourierMode_derivative_bound (k : Fin 2 → ℤ) (a : FourierVelocity)
    (x : Pt 2) (i j : Fin 2) :
    |pd j (realFourierMode k (fourierLeray k a)) x i| ≤
      fourierTestDerivativeBound k * ‖a‖ := by
  have hj : |(k j : ℝ)| ≤ |(k 0 : ℝ)| + |(k 1 : ℝ)| := by
    fin_cases j
    · exact le_add_of_nonneg_right (abs_nonneg _)
    · exact le_add_of_nonneg_left (abs_nonneg _)
  have hc : ‖(2 * π * Complex.I * (k j : ℂ))‖ = 2 * π * |(k j : ℝ)| := by
    simp [Complex.norm_real, Complex.norm_intCast,
      Real.norm_eq_abs, abs_of_pos pi_pos]
  have hcs : ‖(2 * π * Complex.I * (k j : ℂ))‖ ≤ fourierTestDerivativeBound k := by
    rw [hc]
    exact mul_le_mul_of_nonneg_left hj (by positivity)
  rw [pd_realFourierMode]
  calc
    |realFourierMode k ((2 * π * Complex.I * (k j : ℂ)) • fourierLeray k a) x i| ≤
        ‖(2 * π * Complex.I * (k j : ℂ)) • fourierLeray k a‖ :=
      realFourierMode_component_bound k _ x i
    _ = ‖(2 * π * Complex.I * (k j : ℂ))‖ * ‖fourierLeray k a‖ := norm_smul _ _
    _ ≤ fourierTestDerivativeBound k * ‖a‖ :=
      mul_le_mul hcs (norm_fourierLeray_apply_le k a) (norm_nonneg _)
        (fourierTestDerivativeBound_nonneg k)

/-- The real coordinate of the true Fourier coefficient is read by a
projected unit real mode. -/
theorem projected_realFourierMode_reads_re (k : Fin 2 → ℤ) (i : Fin 2)
    (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v) (hp : IsPeriodic v)
    (hdiv : ∀ x, divergence v x = 0) :
    cellVectorPair (realFourierMode k (fourierLeray k (EuclideanSpace.single i (1 : ℂ)))) v =
      (vectorFourierCoeff v k i).re := by
  rw [projected_realFourierMode_cellPair k _ v hv hp hdiv, EuclideanSpace.inner_single_left]
  simp

/-- The imaginary coordinate is read by the projected unit imaginary mode. -/
theorem projected_realFourierMode_reads_im (k : Fin 2 → ℤ) (i : Fin 2)
    (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v) (hp : IsPeriodic v)
    (hdiv : ∀ x, divergence v x = 0) :
    cellVectorPair (realFourierMode k (fourierLeray k (EuclideanSpace.single i Complex.I))) v =
      (vectorFourierCoeff v k i).im := by
  rw [projected_realFourierMode_cellPair k _ v hv hp hdiv, EuclideanSpace.inner_single_left]
  simp [Complex.mul_re]

/-- The test as an actual member of the cutoff Fourier Hilbert state. -/
def fourierGalerkinModeTest (S : Finset (Fin 2 → ℤ))
    {k : Fin 2 → ℤ} (hk : k ∈ S) (a : FourierVelocity) : (fourierGalerkinModel S).State :=
  ⟨realFourierMode k (fourierLeray k a), projected_realFourierMode_mem S hk a⟩

@[simp] theorem fourierGalerkinModeTest_eval (S : Finset (Fin 2 → ℤ))
    {k : Fin 2 → ℤ} (hk : k ∈ S) (a : FourierVelocity) :
    (fourierGalerkinModel S).eval (fourierGalerkinModeTest S hk a) =
      realFourierMode k (fourierLeray k a) := rfl

end AnomDiss

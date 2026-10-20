module

public import RequestProject.FourierPolynomial

/-!
# Differential closure of real solenoidal Fourier spaces

All identities refer to the actual reconstructed spatial fields. In particular,
the Laplacian maps every finite Fourier space to itself, so the negative
Laplacian is an admissible Galerkin test field.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

/-- The positive Laplace eigenvalue for a unit-period Fourier mode. -/
def fourierEigenvalue (k : Fin 2 → ℤ) : ℝ :=
  4 * π ^ 2 * euclNorm (intVec k) ^ 2

lemma fourierEigenvalue_nonneg (k : Fin 2 → ℤ) : 0 ≤ fourierEigenvalue k := by
  unfold fourierEigenvalue
  positivity

lemma realFourierMode_add (k : Fin 2 → ℤ) (a b : FourierVelocity) :
    realFourierMode k (a + b) = realFourierMode k a + realFourierMode k b := by
  funext x i
  simp [realFourierMode, add_mul]

lemma realFourierMode_real_smul (k : Fin 2 → ℤ) (c : ℝ) (a : FourierVelocity) :
    realFourierMode k (c • a) = c • realFourierMode k a := by
  funext x i
  simp [realFourierMode, Complex.real_smul, mul_assoc]

@[simp] lemma realFourierMode_zero (k : Fin 2 → ℤ) : realFourierMode k 0 = 0 := by
  funext x i
  simp [realFourierMode]

lemma solenoidalFourierPolynomial_add (S : Finset (Fin 2 → ℤ))
    (a b : (Fin 2 → ℤ) → FourierVelocity) :
    solenoidalFourierPolynomial S (a + b) =
      solenoidalFourierPolynomial S a + solenoidalFourierPolynomial S b := by
  funext x
  simp [solenoidalFourierPolynomial, realFourierMode_add, Finset.sum_add_distrib]

lemma solenoidalFourierPolynomial_real_smul (S : Finset (Fin 2 → ℤ)) (c : ℝ)
    (a : (Fin 2 → ℤ) → FourierVelocity) :
    solenoidalFourierPolynomial S (c • a) = c • solenoidalFourierPolynomial S a := by
  funext x
  simp [solenoidalFourierPolynomial, ContinuousLinearMap.map_smul_of_tower,
    realFourierMode_real_smul, Finset.smul_sum]

@[simp] lemma solenoidalFourierPolynomial_zero (S : Finset (Fin 2 → ℤ)) :
    solenoidalFourierPolynomial S 0 = 0 := by
  funext x
  simp [solenoidalFourierPolynomial]

/-- The spatial partial derivative is reconstructed from the differentiated
coefficient, including its actual phase rotation. -/
theorem pd_realFourierMode (k : Fin 2 → ℤ) (a : FourierVelocity) (j : Fin 2) :
    pd j (realFourierMode k a) =
      realFourierMode k ((2 * π * Complex.I * (k j : ℂ)) • a) := by
  funext x i
  rw [pd_realFourierMode_component]
  simp only [realFourierMode, PiLp.smul_apply, smul_eq_mul]
  congr 1
  ring

/-- Every real vector mode has its genuine Laplace eigenvalue. -/
theorem lap_realFourierMode (k : Fin 2 → ℤ) (a : FourierVelocity) :
    lap (realFourierMode k a) = (-fourierEigenvalue k) • realFourierMode k a := by
  funext x i
  rw [← lap_component _ ((contDiff_realFourierMode k a).of_le (by norm_cast)) i x]
  let L : ℂ →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ (a i))
  change lap (fun y => L (expChar (intVec k) y)) x = _
  rw [lap_re_expChar]
  rfl

lemma lap_finite_sum {ι : Type*} (S : Finset ι) (f : ι → Pt 2 → Pt 2)
    (hf : ∀ k ∈ S, ContDiff ℝ 2 (f k)) (x : Pt 2) :
    lap (fun y => ∑ k ∈ S, f k y) x = ∑ k ∈ S, lap (f k) x := by
  have hd : ∀ j, pd j (fun y => ∑ k ∈ S, f k y) =
      fun y => ∑ k ∈ S, pd j (f k) y := fun j => funext fun y =>
    pd_finite_sum S f (fun k hk => (hf k hk).differentiable (by norm_num)) j y
  unfold lap
  simp only [hd, pd_finite_sum S (fun k => pd _ (f k))
    (fun k hk => (contDiff_pd_of_C2 _ (hf k hk) _).differentiable (by norm_num))]
  rw [Finset.sum_comm]

/-- The finite solenoidal space is invariant under the actual Laplacian. -/
theorem lap_solenoidalFourierPolynomial (S : Finset (Fin 2 → ℤ))
    (a : (Fin 2 → ℤ) → FourierVelocity) :
    lap (solenoidalFourierPolynomial S a) =
      solenoidalFourierPolynomial S (fun k => (-fourierEigenvalue k) • a k) := by
  funext x
  unfold solenoidalFourierPolynomial
  rw [lap_finite_sum S _ (fun k _ => (contDiff_realFourierMode k _).of_le (by norm_cast))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [lap_realFourierMode, ContinuousLinearMap.map_smul_of_tower,
    realFourierMode_real_smul]

end AnomDiss

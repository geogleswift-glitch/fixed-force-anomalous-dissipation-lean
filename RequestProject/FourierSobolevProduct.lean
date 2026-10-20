module

public import RequestProject.FourierConvolutionYoung
public import RequestProject.FourierLatticeSummability
public import RequestProject.FourierProductWeights
public import RequestProject.NSPhaseGalerkinQuadraticConvolution

/-!
# The genuine two-dimensional fractional Sobolev product estimate

The true inhomogeneous Laplace weights, proved lattice summability, and
discrete Young inequality give H¹ × H¹ → H^{1−δ} for every 0 < δ < 1.
The estimate applies to the genuine quadratic Fourier moments of the
constructed Navier--Stokes velocity limit.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 1200000

private def sobolevSubEquiv (k : Fin 2 → ℤ) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun l := k - l
  invFun l := k - l
  left_inv l := by dsimp; abel
  right_inv l := by dsimp; abel

theorem fourierSobolevWeight_rpow_neg (k : Fin 2 → ℤ) (δ : ℝ) :
    fourierSobolevWeight k ^ (-δ) = (1 + fourierEigenvalue k) ^ (-δ / 2) := by
  rw [fourierSobolevWeight, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by positivity [fourierEigenvalue_nonneg k])]
  congr 1
  ring

theorem fourierSobolevWeight_fractional_energy_eq (k : Fin 2 → ℤ) (s : ℝ) (z : ℂ) :
    (fourierSobolevWeight k ^ s * ‖z‖) ^ 2 =
      (1 + fourierEigenvalue k) ^ s * ‖z‖ ^ 2 := by
  have h1 := Real.rpow_mul (fourierSobolevWeight_nonneg k) s (2 : ℝ)
  simp only [Real.rpow_two] at h1
  have h2 := Real.rpow_mul (fourierSobolevWeight_nonneg k) (2 : ℝ) s
  simp only [Real.rpow_two, fourierSobolevWeight_sq] at h2
  have hw : (fourierSobolevWeight k ^ s) ^ 2 = (1 + fourierEigenvalue k) ^ s :=
    h1.symm.trans ((congrArg (fun r : ℝ => fourierSobolevWeight k ^ r) (mul_comm s 2)).trans h2)
  rw [mul_pow, hw]

/-- Exact fractional product estimate on the genuine two-dimensional
Fourier lattice. Absolute convergence and fractional weighted square
summability are proved, with an explicit finite lattice-kernel constant. -/
theorem fourier_h1_product_fractional
    (a b : (Fin 2 → ℤ) → ℂ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ha : Summable (fun k => (1 + fourierEigenvalue k) * ‖a k‖ ^ 2))
    (hb : Summable (fun k => (1 + fourierEigenvalue k) * ‖b k‖ ^ 2)) :
    (∀ k, Summable (fun l => ‖a l * b (k - l)‖)) ∧
    Summable (fun k => (fourierSobolevWeight k ^ (1 - δ) *
      ‖∑' l, a l * b (k - l)‖) ^ 2) ∧
    (∑' k, (fourierSobolevWeight k ^ (1 - δ) * ‖∑' l, a l * b (k - l)‖) ^ 2) ≤
      4 * (2 ^ (1 - δ)) ^ 2 *
        (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-(1 + δ))) *
        (∑' k, (1 + fourierEigenvalue k) * ‖a k‖ ^ 2) *
        (∑' k, (1 + fourierEigenvalue k) * ‖b k‖ ^ 2) := by
  let Apos := fun k => fourierSobolevWeight k * ‖a k‖
  let Bpos := fun k => fourierSobolevWeight k * ‖b k‖
  let Aneg := fun k => ‖a k‖ * fourierSobolevWeight k ^ (-δ)
  let Bneg := fun k => ‖b k‖ * fourierSobolevWeight k ^ (-δ)
  let Ea := ∑' k, (1 + fourierEigenvalue k) * ‖a k‖ ^ 2
  let Eb := ∑' k, (1 + fourierEigenvalue k) * ‖b k‖ ^ 2
  let K := ∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-(1 + δ))
  let C : ℝ := 2 ^ (1 - δ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hAp : ∀ k, 0 ≤ Apos k := fun k =>
    mul_nonneg (fourierSobolevWeight_nonneg k) (norm_nonneg _)
  have hBp : ∀ k, 0 ≤ Bpos k := fun k =>
    mul_nonneg (fourierSobolevWeight_nonneg k) (norm_nonneg _)
  have hAn : ∀ k, 0 ≤ Aneg k := fun k =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _)
  have hBn : ∀ k, 0 ≤ Bneg k := fun k =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _)
  have hAs : Summable (fun k => Apos k ^ 2) := by
    simpa only [Apos, mul_pow, fourierSobolevWeight_sq] using ha
  have hBs : Summable (fun k => Bpos k ^ 2) := by
    simpa only [Bpos, mul_pow, fourierSobolevWeight_sq] using hb
  have hAe : (∑' k, Apos k ^ 2) = Ea := by
    simp only [Ea, Apos, mul_pow, fourierSobolevWeight_sq]
  have hBe : (∑' k, Bpos k ^ 2) = Eb := by
    simp only [Eb, Bpos, mul_pow, fourierSobolevWeight_sq]
  obtain ⟨hAns, hAnbound⟩ := fourier_weighted_l1_of_h1 hδ0 ha
  obtain ⟨hBns, hBnbound⟩ := fourier_weighted_l1_of_h1 hδ0 hb
  have hAnsum : Summable Aneg := by
    simpa only [Aneg, fourierSobolevWeight_rpow_neg] using hAns
  have hBnsum : Summable Bneg := by
    simpa only [Bneg, fourierSobolevWeight_rpow_neg] using hBns
  have hAnb : (∑' k, Aneg k) ≤ Real.sqrt Ea * Real.sqrt K := by
    simpa only [Aneg, fourierSobolevWeight_rpow_neg, Ea, K] using hAnbound
  have hBnb : (∑' k, Bneg k) ≤ Real.sqrt Eb * Real.sqrt K := by
    simpa only [Bneg, fourierSobolevWeight_rpow_neg, Eb, K] using hBnbound
  obtain ⟨hconv1, hsq1, hb1⟩ := discrete_young_l2_l1_nonneg Apos Bneg hAp hBn hAs hBnsum
  obtain ⟨hconv2, hsq2, hb2⟩ := discrete_young_l2_l1_nonneg Bpos Aneg hBp hAn hBs hAnsum
  let C1 := fun k => ∑' l, Apos l * Bneg (k - l)
  let C2 := fun k => ∑' l, Bpos l * Aneg (k - l)
  have hC1 : ∀ k, 0 ≤ C1 k := fun k => tsum_nonneg fun l => mul_nonneg (hAp l) (hBn _)
  have hC2 : ∀ k, 0 ≤ C2 k := fun k => tsum_nonneg fun l => mul_nonneg (hBp l) (hAn _)
  have hrev (k : Fin 2 → ℤ) : Summable (fun l => Aneg l * Bpos (k - l)) := by
    have hs := (sobolevSubEquiv k).summable_iff.mpr (hconv2 k)
    change Summable (fun l => Bpos (k - l) * Aneg (k - (k - l))) at hs
    have he (l : Fin 2 → ℤ) : k - (k - l) = l := by abel
    simpa only [he, mul_comm] using hs
  have hswap (k : Fin 2 → ℤ) : (∑' l, Aneg l * Bpos (k - l)) = C2 k := by
    have hs := (sobolevSubEquiv k).tsum_eq (fun l => Bpos l * Aneg (k - l))
    change (∑' l, Bpos (k - l) * Aneg (k - (k - l))) = C2 k at hs
    have he (l : Fin 2 → ℤ) : k - (k - l) = l := by abel
    simpa only [he, mul_comm] using hs
  have hterm (k l : Fin 2 → ℤ) :
      fourierSobolevWeight k ^ (1 - δ) * ‖a l * b (k - l)‖ ≤
        C * (Apos l * Bneg (k - l) + Aneg l * Bpos (k - l)) := by
    have hw := fourierSobolevWeight_product_bound l (k - l) hδ0.le hδ1.le
    have he : l + (k - l) = k := by abel
    rw [he] at hw
    apply (mul_le_mul_of_nonneg_right hw (norm_nonneg (a l * b (k - l)))).trans_eq
    simp only [Apos, Bpos, Aneg, Bneg, C, norm_mul]
    ring
  have hdom (k : Fin 2 → ℤ) :
      Summable (fun l => C * (Apos l * Bneg (k - l) + Aneg l * Bpos (k - l))) :=
    ((hconv1 k).add (hrev k)).mul_left C
  have habs (k : Fin 2 → ℤ) : Summable (fun l => ‖a l * b (k - l)‖) := by
    apply (hdom k).of_nonneg_of_le (fun l => norm_nonneg _)
    intro l
    have hw := Real.one_le_rpow (one_le_fourierSobolevWeight k) (sub_nonneg.mpr hδ1.le)
    have hnorm : ‖a l * b (k - l)‖ ≤
        fourierSobolevWeight k ^ (1 - δ) * ‖a l * b (k - l)‖ := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hw (norm_nonneg (a l * b (k - l)))
    exact hnorm.trans (hterm k l)
  have hpoint (k : Fin 2 → ℤ) :
      fourierSobolevWeight k ^ (1 - δ) * ‖∑' l, a l * b (k - l)‖ ≤ C * (C1 k + C2 k) := by
    calc
      _ ≤ fourierSobolevWeight k ^ (1 - δ) * ∑' l, ‖a l * b (k - l)‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (habs k))
          (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _)
      _ = ∑' l, fourierSobolevWeight k ^ (1 - δ) * ‖a l * b (k - l)‖ := tsum_mul_left.symm
      _ ≤ ∑' l, C * (Apos l * Bneg (k - l) + Aneg l * Bpos (k - l)) :=
        Summable.tsum_le_tsum (hterm k) ((habs k).mul_left _) (hdom k)
      _ = _ := by rw [tsum_mul_left, (hconv1 k).tsum_add (hrev k), hswap k]
  have hsquare (k : Fin 2 → ℤ) :
      (fourierSobolevWeight k ^ (1 - δ) * ‖∑' l, a l * b (k - l)‖) ^ 2 ≤
        2 * C ^ 2 * (C1 k ^ 2 + C2 k ^ 2) := by
    have h := (sq_le_sq₀
      (mul_nonneg (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _) (norm_nonneg _))
      (mul_nonneg hC (add_nonneg (hC1 k) (hC2 k)))).mpr (hpoint k)
    have htwo : (C1 k + C2 k) ^ 2 ≤ 2 * (C1 k ^ 2 + C2 k ^ 2) := by
      nlinarith [sq_nonneg (C1 k - C2 k)]
    calc
      _ ≤ C ^ 2 * (C1 k + C2 k) ^ 2 := by simpa only [mul_pow] using h
      _ ≤ C ^ 2 * (2 * (C1 k ^ 2 + C2 k ^ 2)) :=
        mul_le_mul_of_nonneg_left htwo (sq_nonneg C)
      _ = _ := by ring
  have hmajor : Summable (fun k => 2 * C ^ 2 * (C1 k ^ 2 + C2 k ^ 2)) :=
    (hsq1.add hsq2).mul_left _
  have hresult : Summable (fun k => (fourierSobolevWeight k ^ (1 - δ) *
      ‖∑' l, a l * b (k - l)‖) ^ 2) :=
    hmajor.of_nonneg_of_le (fun k => sq_nonneg _) hsquare
  have hEa0 : 0 ≤ Ea := tsum_nonneg fun k =>
    mul_nonneg (by positivity [fourierEigenvalue_nonneg k]) (sq_nonneg _)
  have hEb0 : 0 ≤ Eb := tsum_nonneg fun k =>
    mul_nonneg (by positivity [fourierEigenvalue_nonneg k]) (sq_nonneg _)
  have hK0 : 0 ≤ K := tsum_nonneg fun k =>
    Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _
  have hAn2 : (∑' k, Aneg k) ^ 2 ≤ Ea * K := by
    have h := (sq_le_sq₀ (tsum_nonneg hAn)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hAnb
    simpa only [mul_pow, Real.sq_sqrt hEa0, Real.sq_sqrt hK0] using h
  have hBn2 : (∑' k, Bneg k) ^ 2 ≤ Eb * K := by
    have h := (sq_le_sq₀ (tsum_nonneg hBn)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hBnb
    simpa only [mul_pow, Real.sq_sqrt hEb0, Real.sq_sqrt hK0] using h
  refine ⟨habs, hresult, ?_⟩
  rw [hAe] at hb1
  rw [hBe] at hb2
  calc
    _ ≤ ∑' k, 2 * C ^ 2 * (C1 k ^ 2 + C2 k ^ 2) :=
      Summable.tsum_le_tsum hsquare hresult hmajor
    _ = 2 * C ^ 2 * ((∑' k, C1 k ^ 2) + ∑' k, C2 k ^ 2) := by
      rw [tsum_mul_left, hsq1.tsum_add hsq2]
    _ ≤ 2 * C ^ 2 * ((∑' k, Bneg k) ^ 2 * Ea + (∑' k, Aneg k) ^ 2 * Eb) :=
      mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (by positivity)
    _ ≤ 2 * C ^ 2 * ((Eb * K) * Ea + (Ea * K) * Eb) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_right hBn2 hEa0) (mul_le_mul_of_nonneg_right hAn2 hEb0))
        (by positivity)
    _ = _ := by dsimp [C, K, Ea, Eb]; ring

/-- Genuine limit components have uniformly bounded inhomogeneous H¹
Fourier energy. -/
theorem phaseGalerkin_l2_limit_component_h1_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (i : Fin 2) :
    Summable (fun k => (1 + fourierEigenvalue k) * ‖l2FourierCoeff k i (U t)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) * ‖l2FourierCoeff k i (U t)‖ ^ 2) ≤
        phaseGalerkinEnergyBound phase + phaseGalerkinGradientBound ν phase := by
  obtain ⟨hE, hEb, hG, hGb⟩ := phaseGalerkin_l2_limit_fourier_sobolev_energy ν hν phase hU t
  have hv : Summable (fun k => (1 + fourierEigenvalue k) * l2VelocityFourierEnergy (U t) k) := by
    simpa only [add_mul, one_mul] using hE.add hG
  have hpoint (k : Fin 2 → ℤ) :
      (1 + fourierEigenvalue k) * ‖l2FourierCoeff k i (U t)‖ ^ 2 ≤
        (1 + fourierEigenvalue k) * l2VelocityFourierEnergy (U t) k :=
    mul_le_mul_of_nonneg_left (l2FourierCoeff_sq_le_energy (U t) k i)
      (by positivity [fourierEigenvalue_nonneg k])
  have hs : Summable (fun k => (1 + fourierEigenvalue k) * ‖l2FourierCoeff k i (U t)‖ ^ 2) :=
    hv.of_nonneg_of_le (fun k => mul_nonneg (by positivity [fourierEigenvalue_nonneg k])
      (sq_nonneg _)) hpoint
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' k, (1 + fourierEigenvalue k) * l2VelocityFourierEnergy (U t) k :=
      Summable.tsum_le_tsum hpoint hs hv
    _ = (∑' k, l2VelocityFourierEnergy (U t) k) +
        ∑' k, fourierEigenvalue k * l2VelocityFourierEnergy (U t) k := by
      simp only [add_mul, one_mul]
      exact hE.tsum_add hG
    _ ≤ _ := add_le_add hEb hGb

/-- The actual completed-space quadratic Fourier tensor has the genuine
H^{1−δ} energy and a bound uniform in the original closed time interval.
It is identified with the true spatial L² product, not a formal sequence. -/
theorem phaseGalerkin_l2_limit_quadratic_fourier_fractional_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (j i : Fin 2) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ (1 - δ) *
      ‖torusQuadraticFourierMoment k j i (U t)‖ ^ 2) ∧
    (∑' k, (1 + fourierEigenvalue k) ^ (1 - δ) *
      ‖torusQuadraticFourierMoment k j i (U t)‖ ^ 2) ≤
      4 * (2 ^ (1 - δ)) ^ 2 *
        (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-(1 + δ))) *
        (phaseGalerkinEnergyBound phase + phaseGalerkinGradientBound ν phase) ^ 2 := by
  obtain ⟨ha, haBound⟩ := phaseGalerkin_l2_limit_component_h1_energy ν hν phase hU t j
  obtain ⟨hb, hbBound⟩ := phaseGalerkin_l2_limit_component_h1_energy ν hν phase hU t i
  obtain ⟨-, hs, hbprod⟩ := fourier_h1_product_fractional
    (fun k => l2FourierCoeff k j (U t)) (fun k => l2FourierCoeff k i (U t)) hδ0 hδ1 ha hb
  have hsActual : Summable (fun k => (1 + fourierEigenvalue k) ^ (1 - δ) *
      ‖torusQuadraticFourierMoment k j i (U t)‖ ^ 2) := by
    simpa only [fourierSobolevWeight_fractional_energy_eq,
      phaseGalerkin_l2_limit_quadraticFourierMoment_eq_tsum ν hν phase hU t] using hs
  have hActual : (∑' k, (1 + fourierEigenvalue k) ^ (1 - δ) *
      ‖torusQuadraticFourierMoment k j i (U t)‖ ^ 2) ≤
      4 * (2 ^ (1 - δ)) ^ 2 *
        (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-(1 + δ))) *
        (∑' k, (1 + fourierEigenvalue k) * ‖l2FourierCoeff k j (U t)‖ ^ 2) *
        (∑' k, (1 + fourierEigenvalue k) * ‖l2FourierCoeff k i (U t)‖ ^ 2) := by
    simpa only [fourierSobolevWeight_fractional_energy_eq,
      phaseGalerkin_l2_limit_quadraticFourierMoment_eq_tsum ν hν phase hU t] using hbprod
  have hj0 : 0 ≤ ∑' k, (1 + fourierEigenvalue k) * ‖l2FourierCoeff k j (U t)‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (by positivity [fourierEigenvalue_nonneg k]) (sq_nonneg _)
  have hi0 : 0 ≤ ∑' k, (1 + fourierEigenvalue k) * ‖l2FourierCoeff k i (U t)‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (by positivity [fourierEigenvalue_nonneg k]) (sq_nonneg _)
  have htotal0 : 0 ≤ phaseGalerkinEnergyBound phase + phaseGalerkinGradientBound ν phase :=
    hj0.trans haBound
  have hK0 : 0 ≤ ∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-(1 + δ)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _
  refine ⟨hsActual, hActual.trans ?_⟩
  have hm := mul_le_mul haBound hbBound hi0 htotal0
  calc
    _ = (4 * (2 ^ (1 - δ)) ^ 2 *
        (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-(1 + δ)))) *
        ((∑' k, (1 + fourierEigenvalue k) * ‖l2FourierCoeff k j (U t)‖ ^ 2) *
          ∑' k, (1 + fourierEigenvalue k) * ‖l2FourierCoeff k i (U t)‖ ^ 2) := by ring
    _ ≤ (4 * (2 ^ (1 - δ)) ^ 2 *
        (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-(1 + δ)))) *
        ((phaseGalerkinEnergyBound phase + phaseGalerkinGradientBound ν phase) *
          (phaseGalerkinEnergyBound phase + phaseGalerkinGradientBound ν phase)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end AnomDiss

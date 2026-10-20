module

public import RequestProject.PhaseForceSobolev
public import RequestProject.NSPhaseGalerkinHigherHeat

/-!
# Every Sobolev order below three for the actual NS velocity

The actual force has every order below one. The actual nonlinear source
has first-order energy by the already proved second-order velocity bound.
Their genuine difference therefore has every order below one, and the
true Fourier Duhamel estimate yields every positive velocity order below
three. No source or velocity regularity is assumed in the final results.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

/-- The genuine force is solenoidal, so its proved fractional energy also
holds for the exact Leray projection used in the coefficient equation. -/
theorem phaseForce_leray_uniform_sobolev_energy_below_one
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (phase : Phase) (t : ℝ) (i : Fin 2),
      Summable (fun k => (1 + fourierEigenvalue k) ^ p *
        ‖fourierLeray k (vectorFourierCoeff (gForce phase t) k) i‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ p *
        ‖fourierLeray k (vectorFourierCoeff (gForce phase t) k) i‖ ^ 2) ≤ B := by
  obtain ⟨B, hB, henergy⟩ := gForce_uniform_sobolev_energy hp₀ hp₁
  refine ⟨B, hB, fun phase t i => ?_⟩
  have he (k : Fin 2 → ℤ) : fourierLeray k (vectorFourierCoeff (gForce phase t) k) i =
      vectorFourierCoeff (gForce phase t) k i := by
    exact congrArg (fun a : FourierVelocity => a i) (fourierLeray_vectorFourierCoeff
      (gForce phase t) ((gForce_slice_props phase t).2.1.of_le (natCast_le_infty 1))
      (gForce_slice_props phase t).1 (gForce_slice_props phase t).2.2.1 k)
  simpa only [he] using henergy phase t i

/-- Every actual strong Galerkin limit has uniform energy of its genuine
full projected source at each order `0≤p<1`. -/
theorem phaseGalerkin_l2_limit_uniform_source_sobolev_below_one
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + fourierEigenvalue k) ^ p *
        ‖phaseL2FourierSourceCurve phase k i U t‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ p *
        ‖phaseL2FourierSourceCurve phase k i U t‖ ^ 2) ≤ B := by
  obtain ⟨BF, hBF, hForce⟩ := phaseForce_leray_uniform_sobolev_energy_below_one hp₀ hp₁
  obtain ⟨BU, hBU, hVelocity⟩ := phaseGalerkin_l2_limit_uniform_h2_energy ν hν phase hφ hU
  refine ⟨2 * BF + 2 * phaseNonlinearFirstEnergyBound BU,
    add_nonneg (mul_nonneg (by norm_num) hBF)
      (mul_nonneg (by norm_num) (phaseNonlinearFirstEnergyBound_nonneg BU)), fun i t => ?_⟩
  let F : (Fin 2 → ℤ) → ℂ := fun k =>
    fourierLeray k (vectorFourierCoeff (gForce phase t.1) k) i
  let N : (Fin 2 → ℤ) → ℂ := fun k =>
    fourierLeray k (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q (U t))) i
  obtain ⟨hsF, hbF⟩ := hForce phase t.1 i
  obtain ⟨hsN1, hbN1⟩ := phaseGalerkin_l2_limit_leray_nonlinear_first_energy
    ν hν phase hU t hBU (fun j => hVelocity j t) i
  have hNpoint (k : Fin 2 → ℤ) :
      (1 + fourierEigenvalue k) ^ p * ‖N k‖ ^ 2 ≤
        (1 + fourierEigenvalue k) * ‖N k‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by linarith [fourierEigenvalue_nonneg k] : 1 ≤ 1 + fourierEigenvalue k) hp₁.le
  have hNnonneg (k : Fin 2 → ℤ) : 0 ≤ (1 + fourierEigenvalue k) ^ p * ‖N k‖ ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  have hsN := hsN1.of_nonneg_of_le hNnonneg hNpoint
  have hbN := (Summable.tsum_le_tsum hNpoint hsN hsN1).trans hbN1
  have hpoint (k : Fin 2 → ℤ) :
      (1 + fourierEigenvalue k) ^ p * ‖phaseL2FourierSourceCurve phase k i U t‖ ^ 2 ≤
        2 * ((1 + fourierEigenvalue k) ^ p * ‖F k‖ ^ 2) +
          2 * ((1 + fourierEigenvalue k) ^ p * ‖N k‖ ^ 2) := by
    have hn := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg (F k))
      (norm_nonneg (N k)))).2 (norm_sub_le (F k) (N k))
    have hsq : ‖F k - N k‖ ^ 2 ≤ 2 * ‖F k‖ ^ 2 + 2 * ‖N k‖ ^ 2 := by
      nlinarith [sq_nonneg (‖F k‖ - ‖N k‖)]
    rw [phaseL2FourierSourceCurve_apply]
    exact (mul_le_mul_of_nonneg_left hsq
      (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _)).trans_eq (by ring)
  have hmajor := (hsF.mul_left 2).add (hsN.mul_left 2)
  have hn (k : Fin 2 → ℤ) : 0 ≤ (1 + fourierEigenvalue k) ^ p *
      ‖phaseL2FourierSourceCurve phase k i U t‖ ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  have hs := hmajor.of_nonneg_of_le hn hpoint
  refine ⟨hs, (Summable.tsum_le_tsum hpoint hs hmajor).trans ?_⟩
  rw [(hsF.mul_left 2).tsum_add (hsN.mul_left 2), tsum_mul_left, tsum_mul_left]
  exact add_le_add (mul_le_mul_of_nonneg_left hbF (by norm_num))
    (mul_le_mul_of_nonneg_left hbN (by norm_num))

/-- Every actual strong Galerkin limit has uniform true velocity
coefficient energy at every positive Sobolev order strictly below three. -/
theorem phaseGalerkin_l2_limit_uniform_sobolev_below_three
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {r : ℝ} (hr₀ : 0 < r) (hr₃ : r < 3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k i (U t)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k i (U t)‖ ^ 2) ≤ B := by
  let p : ℝ := r / 3
  let γ : ℝ := 2 * r / 3
  have hp₀ : 0 ≤ p := by dsimp only [p]; positivity
  have hp₁ : p < 1 := by dsimp only [p]; linarith
  have hγ₀ : 0 ≤ γ := by dsimp only [γ]; positivity
  have hγ₁ : γ < 2 := by dsimp only [γ]; linarith
  obtain ⟨B, hB, hsource⟩ := phaseGalerkin_l2_limit_uniform_source_sobolev_below_one
    ν hν phase hφ hU hp₀ hp₁
  have hfinite : ∀ t : GalerkinTime, ∀ i : Fin 2, ∀ S : Finset (Fin 2 → ℤ),
      (∑ k ∈ S, (1 + fourierEigenvalue k) ^ p *
        ‖phaseL2FourierSourceCurve phase k i U t‖ ^ 2) ≤ B := by
    intro t i S
    exact ((hsource i t).1.sum_le_tsum S (fun k _ =>
      mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _))).trans
        (hsource i t).2
  have hh := phaseGalerkin_l2_limit_fourier_uniform_gain_of_source_energy
    ν hν phase hφ hU hγ₀ hγ₁ hB hfinite
  refine ⟨fourierHeatRealGainConstant (γ / 2) ^ 2 * B *
    (1 + ν ^ (-(γ / 2)) * (1 / (1 - γ / 2))) ^ 2,
    mul_nonneg (mul_nonneg (sq_nonneg _) hB) (sq_nonneg _), ?_⟩
  have he : p + γ = r := by dsimp only [p, γ]; ring
  simpa only [he] using hh

/-- One and the same unconditionally constructed zero-initial actual
limit satisfies all positive velocity Sobolev orders below three. -/
theorem exists_phaseGalerkin_l2_limit_uniform_sobolev_below_three
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) :
    ∃ (φ : ℕ → ℕ) (U : GalerkinTime →ᵇ TorusVelocityL2), StrictMono φ ∧
      Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U) ∧
      U ⟨0, by norm_num⟩ = 0 ∧
      ∀ r : ℝ, 0 < r → r < 3 → ∃ B : ℝ, 0 ≤ B ∧
        ∀ i : Fin 2, ∀ t : GalerkinTime,
        Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k i (U t)‖ ^ 2) ∧
        (∑' k, (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k i (U t)‖ ^ 2) ≤ B := by
  obtain ⟨φ, U, hφ, hU, hz, _⟩ := exists_phaseGalerkin_l2_limit_uniform_h2_energy ν hν phase
  exact ⟨φ, U, hφ, hU, hz, fun _ hr₀ hr₃ =>
    phaseGalerkin_l2_limit_uniform_sobolev_below_three ν hν phase hφ hU hr₀ hr₃⟩

end AnomDiss

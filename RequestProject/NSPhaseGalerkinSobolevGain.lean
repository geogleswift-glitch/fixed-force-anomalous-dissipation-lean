module

public import RequestProject.FourierHeatDuhamelSmoothing
public import RequestProject.NSPhaseGalerkinSourceSobolev

/-!
# Genuine Sobolev gain of the actual Navier–Stokes Galerkin limit

The existing Fourier mild equation is identified with the actual causal
Duhamel coefficient. The proved negative-order source energy then gives
uniform `H^r` coefficient energy for every `r<2`. No classical-solution or
Navier–Stokes existence interface is assumed.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

/-- The original projected nonlinear source, extended continuously by
clamping outside the supplied unit time slab. -/
def phaseL2FourierSourceExtension (phase : Phase) (i : Fin 2)
    (U : GalerkinTime →ᵇ TorusVelocityL2) (s : ℝ) (k : Fin 2 → ℤ) : ℂ :=
  extendGalerkinTimeCurve (phaseL2FourierSourceCurve phase k i U) s

lemma continuous_phaseL2FourierSourceExtension (phase : Phase) (i : Fin 2)
    (U : GalerkinTime →ᵇ TorusVelocityL2) (k : Fin 2 → ℤ) :
    Continuous (fun s => phaseL2FourierSourceExtension phase i U s k) :=
  continuous_extendGalerkinTimeCurve _

/-- Every actual strong Galerkin limit has zero initial Fourier coefficient;
this follows from the genuine initial values of the approximating curves. -/
theorem phaseGalerkin_l2_limit_fourier_initial_zero
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (k : Fin 2 → ℤ) (i : Fin 2) :
    l2FourierCoeff k i (U ⟨0, by norm_num⟩) = 0 := by
  have hlim := fun m : GalerkinCoefficientIndex =>
    phaseGalerkin_l2_coefficient_curve_tendsto ν hν phase hU m.1 m.2
  exact phaseGalerkin_limit_coefficient_initial hlim k i

/-- The actual NS limit coefficient is precisely the actual Duhamel
coefficient of its original projected force minus nonlinear flux. -/
theorem phaseGalerkin_l2_limit_fourier_eq_heatDuhamelCoefficient
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (k : Fin 2 → ℤ) (i : Fin 2) (t : GalerkinTime) :
    l2FourierCoeff k i (U t) = heatDuhamelCoefficient fourierEigenvalue ν
      (phaseL2FourierSourceExtension phase i U) t.1 k := by
  have hh := phaseGalerkin_l2_limit_fourier_heat_duhamel ν hν phase hφ hU k i t
  rw [phaseGalerkin_l2_limit_fourier_initial_zero ν hν phase hU k i,
    mul_zero, zero_add] at hh
  rw [hh, heatDuhamelCoefficient_eq_standard]
  apply intervalIntegral.integral_congr
  intro s hs
  have he : -(ν * fourierEigenvalue k) * (t.1 - s) =
      -(ν * (t.1 - s) * fourierEigenvalue k) := by ring
  simp only [phaseL2FourierSourceExtension, Complex.real_smul, he]

/-- Transfers a genuine source energy bound through the proved mild
identity. This intermediate estimate assumes only the source energy,
not any regularity of the unknown solution. -/
theorem phaseGalerkin_l2_limit_fourier_uniform_gain_of_source_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {p γ B : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 2) (hB : 0 ≤ B)
    (hsource : ∀ t : GalerkinTime, ∀ i : Fin 2, ∀ S : Finset (Fin 2 → ℤ),
      (∑ k ∈ S, (1 + fourierEigenvalue k) ^ p *
        ‖phaseL2FourierSourceCurve phase k i U t‖ ^ 2) ≤ B) :
    ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + fourierEigenvalue k) ^ (p + γ) *
        ‖l2FourierCoeff k i (U t)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ (p + γ) *
        ‖l2FourierCoeff k i (U t)‖ ^ 2) ≤
        fourierHeatRealGainConstant (γ / 2) ^ 2 * B *
          (1 + ν ^ (-(γ / 2)) * (1 / (1 - γ / 2))) ^ 2 := by
  intro i t
  have he : ∀ s ∈ Icc (0 : ℝ) 1, ∀ S : Finset (Fin 2 → ℤ),
      (∑ k ∈ S, (1 + fourierEigenvalue k) ^ p *
        ‖phaseL2FourierSourceExtension phase i U s k‖ ^ 2) ≤ B := by
    intro s hs S
    simp only [phaseL2FourierSourceExtension, extendGalerkinTimeCurve_of_mem _ hs]
    exact hsource ⟨s, hs⟩ i S
  have hh := fourier_heatDuhamel_uniform_sobolev_gain hγ₀ hγ₁ hν hB
    (phaseL2FourierSourceExtension phase i U)
    (continuous_phaseL2FourierSourceExtension phase i U) he t.1 t.2
  have heq : ∀ k, heatDuhamelCoefficient fourierEigenvalue ν
      (phaseL2FourierSourceExtension phase i U) t.1 k = l2FourierCoeff k i (U t) :=
    fun k => (phaseGalerkin_l2_limit_fourier_eq_heatDuhamelCoefficient ν hν phase hφ hU k i t).symm
  simpa only [heq, Real.one_rpow] using hh

/-- An explicit bound for each actual velocity coefficient family's
`H^r` square energy, for `0<r<2`. -/
def phaseL2VelocitySobolevGainBound (ν : ℝ) (phase : Phase) (r : ℝ) : ℝ :=
  fourierHeatRealGainConstant ((r + 2) / 4) ^ 2 *
    phaseL2FourierSourceSobolevBound ν phase ((2 - r) / 2) *
      (1 + ν ^ (-((r + 2) / 4)) * (1 / (1 - (r + 2) / 4))) ^ 2

lemma phaseL2VelocitySobolevGainBound_nonneg (ν : ℝ) (phase : Phase) (r : ℝ) :
    0 ≤ phaseL2VelocitySobolevGainBound ν phase r := by
  unfold phaseL2VelocitySobolevGainBound
  exact mul_nonneg (mul_nonneg (sq_nonneg _)
    (phaseL2FourierSourceSobolevBound_nonneg ν phase _)) (sq_nonneg _)

/-- The actual strong NS Galerkin limit gains every positive Sobolev order
below two, from its proved nonlinear source estimate and its actual mild
identity. The estimate is uniform in time and in the vector component. -/
theorem phaseGalerkin_l2_limit_positive_sobolev_gain
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {r : ℝ} (hr₀ : 0 < r) (hr₂ : r < 2) :
    ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + fourierEigenvalue k) ^ r *
        ‖l2FourierCoeff k i (U t)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ r *
        ‖l2FourierCoeff k i (U t)‖ ^ 2) ≤ phaseL2VelocitySobolevGainBound ν phase r := by
  let δ := (2 - r) / 2
  let γ := (r + 2) / 2
  have hδ₀ : 0 < δ := by dsimp [δ]; linarith
  have hδ₁ : δ < 1 := by dsimp [δ]; linarith
  have hγ₀ : 0 ≤ γ := by dsimp [γ]; linarith
  have hγ₁ : γ < 2 := by dsimp [γ]; linarith
  have hsource : ∀ t : GalerkinTime, ∀ i : Fin 2, ∀ S : Finset (Fin 2 → ℤ),
      (∑ k ∈ S, (1 + fourierEigenvalue k) ^ (-δ) *
        ‖phaseL2FourierSourceCurve phase k i U t‖ ^ 2) ≤
          phaseL2FourierSourceSobolevBound ν phase δ := by
    intro t i S
    obtain ⟨hs, hbound⟩ := phaseGalerkin_l2_limit_source_negative_energy
      ν hν phase hU t i hδ₀ hδ₁
    exact (hs.sum_le_tsum S (fun k _ => mul_nonneg
      (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _))).trans hbound
  have hh := phaseGalerkin_l2_limit_fourier_uniform_gain_of_source_energy
    ν hν phase hφ hU hγ₀ hγ₁ (phaseL2FourierSourceSobolevBound_nonneg ν phase δ) hsource
  have hexp : -δ + γ = r := by dsimp [δ, γ]; ring
  have hhalf : γ / 2 = (r + 2) / 4 := by dsimp [γ]; ring
  simpa only [hexp, hhalf, δ, phaseL2VelocitySobolevGainBound] using hh

/-- Nonpositive real Sobolev orders are already controlled by the genuine
kinetic Fourier energy of the same strong limit. -/
theorem phaseGalerkin_l2_limit_nonpositive_sobolev_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {r : ℝ} (hr : r ≤ 0) (i : Fin 2) (t : GalerkinTime) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k i (U t)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k i (U t)‖ ^ 2) ≤
        max (phaseGalerkinEnergyBound phase) 0 := by
  have hn : ∀ k, 0 ≤ (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k i (U t)‖ ^ 2 := by
    intro k
    positivity [fourierEigenvalue_nonneg k]
  have hfinite : ∀ S : Finset (Fin 2 → ℤ),
      (∑ k ∈ S, (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k i (U t)‖ ^ 2) ≤
        max (phaseGalerkinEnergyBound phase) 0 := by
    intro S
    calc
      _ ≤ ∑ k ∈ S, l2VelocityFourierEnergy (U t) k := Finset.sum_le_sum fun k hk => by
        have hw := Real.rpow_le_one_of_one_le_of_nonpos
          (by linarith [fourierEigenvalue_nonneg k] : 1 ≤ 1 + fourierEigenvalue k) hr
        exact ((mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans_eq (one_mul _)).trans
          (l2FourierCoeff_sq_le_energy (U t) k i)
      _ ≤ phaseGalerkinEnergyBound phase := phaseGalerkin_l2_limit_fourier_finite_energy ν hν phase hU t S
      _ ≤ _ := le_max_left _ _
  exact ⟨summable_of_sum_le hn hfinite, Real.tsum_le_of_sum_le hn hfinite⟩

/-- Every real Sobolev order below two has a genuine uniform bound for the
actual same completed-space NS limit, with no extra regularity premise. -/
theorem phaseGalerkin_l2_limit_uniform_sobolev_below_two
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {r : ℝ} (hr : r < 2) :
    ∃ B, 0 ≤ B ∧ ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k i (U t)‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k i (U t)‖ ^ 2) ≤ B := by
  by_cases hr₀ : 0 < r
  · exact ⟨phaseL2VelocitySobolevGainBound ν phase r,
      phaseL2VelocitySobolevGainBound_nonneg ν phase r,
      phaseGalerkin_l2_limit_positive_sobolev_gain ν hν phase hφ hU hr₀ hr⟩
  · exact ⟨max (phaseGalerkinEnergyBound phase) 0, le_max_right _ _, fun i t =>
      phaseGalerkin_l2_limit_nonpositive_sobolev_energy ν hν phase hU (le_of_not_gt hr₀) i t⟩

/-- Unconditional existence of an actual strong NS Galerkin limit whose
true coefficient energies are uniformly bounded at every order below two. -/
theorem exists_phaseGalerkin_l2_limit_uniform_sobolev_below_two
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) :
    ∃ (φ : ℕ → ℕ) (U : GalerkinTime →ᵇ TorusVelocityL2),
      StrictMono φ ∧
      Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U) ∧
      U ⟨0, by norm_num⟩ = 0 ∧
      ∀ r : ℝ, r < 2 → ∃ B, 0 ≤ B ∧ ∀ i : Fin 2, ∀ t : GalerkinTime,
        Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k i (U t)‖ ^ 2) ∧
        (∑' k, (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k i (U t)‖ ^ 2) ≤ B := by
  obtain ⟨a, φ, U, hφ, hU, hz, _, _, _⟩ :=
    exists_phaseGalerkin_l2_limit_with_fourier_identification ν hν phase
  exact ⟨φ, U, hφ, hU, hz, fun r hr =>
    phaseGalerkin_l2_limit_uniform_sobolev_below_two ν hν phase hφ hU hr⟩


/-- The two vector components give the genuine vector Fourier energy bound
with exactly twice the displayed scalar-coordinate constant. -/
theorem phaseGalerkin_l2_limit_positive_vector_sobolev_gain
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {r : ℝ} (hr₀ : 0 < r) (hr₂ : r < 2) (t : GalerkinTime) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ r * l2VelocityFourierEnergy (U t) k) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ r * l2VelocityFourierEnergy (U t) k) ≤
        2 * phaseL2VelocitySobolevGainBound ν phase r := by
  have hcoord := phaseGalerkin_l2_limit_positive_sobolev_gain ν hν phase hφ hU hr₀ hr₂
  have hzero := hcoord 0 t
  have hone := hcoord 1 t
  have he : (fun k => (1 + fourierEigenvalue k) ^ r * l2VelocityFourierEnergy (U t) k) =
      fun k => (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k 0 (U t)‖ ^ 2 +
        (1 + fourierEigenvalue k) ^ r * ‖l2FourierCoeff k 1 (U t)‖ ^ 2 := by
    funext k
    simp only [l2VelocityFourierEnergy, Fin.sum_univ_two, mul_add]
  rw [he]
  refine ⟨hzero.1.add hone.1, ?_⟩
  rw [hzero.1.tsum_add hone.1]
  linarith [hzero.2, hone.2]

end AnomDiss


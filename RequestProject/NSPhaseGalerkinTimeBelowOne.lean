module

public import RequestProject.NSPhaseGalerkinTimeEnergy
public import RequestProject.NSPhaseGalerkinSobolevBelowThree
public import RequestProject.FourierTimeInterpolation

/-!
# Earned time estimates below one derivative

The true force, nonlinearity, and velocity estimates supply the rate
energy hypotheses internally. The coefficient increments are Lipschitz
at every Sobolev level below one. Interpolation gives a time Hölder
modulus for the first absolute Fourier moment of the actual velocity.
-/

@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction
noncomputable section
namespace AnomDiss

theorem phaseGalerkin_l2_limit_uniform_rate_energy_below_one
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∃ B, 0 ≤ B ∧ ∀ i : Fin 2, ∀ t : GalerkinTime,
      Summable (fun k => (1+fourierEigenvalue k)^p * ‖phaseL2FourierRHSCurve ν phase k i U t‖^2) ∧
      (∑' k, (1+fourierEigenvalue k)^p * ‖phaseL2FourierRHSCurve ν phase k i U t‖^2) ≤ B := by
  obtain ⟨A, hA, hvelocity⟩ := phaseGalerkin_l2_limit_uniform_sobolev_below_three
    ν hν phase hφ hU (r := p+2) (by linarith) (by linarith)
  obtain ⟨B, hB, hsource⟩ := phaseGalerkin_l2_limit_uniform_source_sobolev_below_one
    ν hν phase hφ hU hp0 hp1
  refine ⟨2*(ν^2*A)+2*B, by positivity, ?_⟩
  intro i t
  exact phaseGalerkin_l2_limit_rate_energy_of_velocity_source_energy ν phase U i t
    (hvelocity i t) (hsource i t)

theorem phaseGalerkin_l2_limit_uniform_increment_energy_below_one
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∃ B, 0 ≤ B ∧ ∀ i : Fin 2, ∀ s t : GalerkinTime,
      Summable (fun k => (1+fourierEigenvalue k)^p *
        ‖l2FourierCoeff k i (U t)-l2FourierCoeff k i (U s)‖^2) ∧
      (∑' k, (1+fourierEigenvalue k)^p *
        ‖l2FourierCoeff k i (U t)-l2FourierCoeff k i (U s)‖^2) ≤ B*|t.1-s.1|^2 := by
  obtain ⟨B, hB, hrate⟩ := phaseGalerkin_l2_limit_uniform_rate_energy_below_one
    ν hν phase hφ hU hp0 hp1
  exact ⟨B, hB, fun i s t => phaseGalerkin_l2_limit_fourier_increment_energy_of_rate_energy
    ν hν phase hφ hU hB i (hrate i) s t⟩

theorem phaseGalerkin_l2_limit_uniform_first_moment_time_holder
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C, 0 ≤ C ∧ ∀ i : Fin 2, ∀ s t : GalerkinTime,
      Summable (fun k => (1+‖intVec k‖) *
        ‖l2FourierCoeff k i (U t)-l2FourierCoeff k i (U s)‖) ∧
      (∑' k, (1+‖intVec k‖) *
        ‖l2FourierCoeff k i (U t)-l2FourierCoeff k i (U s)‖) ≤ C*|t.1-s.1|^(β/2) := by
  let δ : ℝ := (1-β)/4
  let p : ℝ := 1-δ
  let q : ℝ := 3-δ
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  have hp0 : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : p < 1 := by dsimp [p]; linarith
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq3 : q < 3 := by dsimp [q]; linarith
  obtain ⟨D, hD, hincrement⟩ := phaseGalerkin_l2_limit_uniform_increment_energy_below_one
    ν hν phase hφ hU hp0 hp1
  obtain ⟨B, hB, hvelocity⟩ := phaseGalerkin_l2_limit_uniform_sobolev_below_three
    ν hν phase hφ hU hq0 hq3
  let C : ℝ := 2^((1 : ℝ)) * (Real.sqrt (D^(β/2) * (4*B)^(1-β/2)) *
    Real.sqrt (∑' k : Fin 2 → ℤ,
      (1+fourierEigenvalue k)^(-((β/2)*p+(1-β/2)*q-1))))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro i s t
  have hstrong := fourier_energy_sub_bound
    (fun k => l2FourierCoeff k i (U t)) (fun k => l2FourierCoeff k i (U s))
    (hvelocity i t).1 (hvelocity i s).1 (hvelocity i t).2 (hvelocity i s).2
  have hg : 1 < (β/2)*p+(1-β/2)*q-1 := by
    dsimp [p, q, δ]
    nlinarith
  have hh := fourier_covering_increment_l1_bound
    (fun k => l2FourierCoeff k i (U t)-l2FourierCoeff k i (U s))
    (p := p) (q := q) (m := 1) (D := D) (B := 4*B) (d := |t.1-s.1|) (γ := β/2)
    (by linarith) (by linarith) (by norm_num) hg hD (by positivity) (abs_nonneg _)
    (hincrement i s t).1 hstrong.1 (hincrement i s t).2 (by linarith [hstrong.2])
  simpa only [Real.rpow_one, C] using hh

end AnomDiss

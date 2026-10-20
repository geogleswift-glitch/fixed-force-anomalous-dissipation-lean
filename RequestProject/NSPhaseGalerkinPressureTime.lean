module

public import RequestProject.NSPhaseGalerkinPressureReal
public import RequestProject.FourierSobolevMixedProduct
public import RequestProject.NSPhaseGalerkinTimeBelowOne
public import RequestProject.FourierSeriesTimeRegularity
public import RequestProject.ParabolicHolderOperations

/-! # Time estimates for the same genuine pressure coefficients -/

@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction
noncomputable section
namespace AnomDiss

set_option maxHeartbeats 1600000

private theorem mixed_product_energy_of_bounds
    (a b : (Fin 2 → ℤ) → ℂ) {p E L : ℝ} (hp : 0 ≤ p) (hL : 0 ≤ L)
    (ha : Summable (fun k => (1+fourierEigenvalue k)^p * ‖a k‖^2))
    (hEa : (∑' k, (1+fourierEigenvalue k)^p * ‖a k‖^2) ≤ E)
    (hb : Summable (fun k => fourierSobolevWeight k^p * ‖b k‖))
    (hLb : (∑' k, fourierSobolevWeight k^p * ‖b k‖) ≤ L) :
    (∀ k, Summable (fun l => ‖a l * b (k-l)‖)) ∧
    Summable (fun k => (1+fourierEigenvalue k)^p * ‖∑' l, a l * b (k-l)‖^2) ∧
    (∑' k, (1+fourierEigenvalue k)^p * ‖∑' l, a l * b (k-l)‖^2) ≤
      (4*(2^p)^2*L^2)*E := by
  obtain ⟨habs, hs, hbnd⟩ := fourier_sobolev_mixed_product a b hp ha hb
  have hs0 : 0 ≤ ∑' k, fourierSobolevWeight k^p * ‖b k‖ :=
    tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _) (norm_nonneg _)
  have hsq : (∑' k, fourierSobolevWeight k^p * ‖b k‖)^2 ≤ L^2 :=
    (sq_le_sq₀ hs0 hL).mpr hLb
  have hE0 : 0 ≤ ∑' k, (1+fourierEigenvalue k)^p * ‖a k‖^2 :=
    tsum_nonneg fun k => mul_nonneg
      (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  refine ⟨habs, hs, hbnd.trans ?_⟩
  have hm := mul_le_mul hsq hEa hE0 (sq_nonneg L)
  calc
    _ = (4*(2^p)^2)*((∑' k, fourierSobolevWeight k^p * ‖b k‖)^2 *
        (∑' k, (1+fourierEigenvalue k)^p * ‖a k‖^2)) := by ring
    _ ≤ (4*(2^p)^2)*(L^2*E) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

private def pressureTimeSubEquiv (k : Fin 2 → ℤ) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun l := k-l
  invFun l := k-l
  left_inv l := by dsimp; abel
  right_inv l := by dsimp; abel

/-- Genuine quadratic coefficient increments are Lipschitz in every
Sobolev energy below one, from earned velocity increments and H² energy. -/
theorem phaseGalerkin_l2_limit_uniform_quadratic_increment_energy_below_one
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∃ C, 0 ≤ C ∧ ∀ j i : Fin 2, ∀ s t : GalerkinTime,
      Summable (fun k => (1+fourierEigenvalue k)^p *
        ‖torusQuadraticFourierMoment k j i (U t)-torusQuadraticFourierMoment k j i (U s)‖^2) ∧
      (∑' k, (1+fourierEigenvalue k)^p *
        ‖torusQuadraticFourierMoment k j i (U t)-torusQuadraticFourierMoment k j i (U s)‖^2) ≤
          C*|t.1-s.1|^2 := by
  obtain ⟨B, hB, henergy⟩ := phaseGalerkin_l2_limit_uniform_h2_energy ν hν phase hφ hU
  obtain ⟨D, hD, hincrement⟩ := phaseGalerkin_l2_limit_uniform_increment_energy_below_one
    ν hν phase hφ hU hp0 hp1
  let K : ℝ := ∑' k : Fin 2 → ℤ, (1+fourierEigenvalue k)^(-(2-p))
  let L : ℝ := Real.sqrt B * Real.sqrt K
  have hL : 0 ≤ L := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmoment (i : Fin 2) (t : GalerkinTime) :
      Summable (fun k => fourierSobolevWeight k^p * ‖l2FourierCoeff k i (U t)‖) ∧
      (∑' k, fourierSobolevWeight k^p * ‖l2FourierCoeff k i (U t)‖) ≤ L := by
    have hE : Summable (fun k => (1+fourierEigenvalue k)^(2 : ℝ) * ‖l2FourierCoeff k i (U t)‖^2) := by
      simpa only [Real.rpow_two] using (henergy i t).1
    obtain ⟨hs, hb⟩ := fourier_weighted_l1_of_sobolev (q := p) (by linarith : 1 < 2-p) hE
    refine ⟨hs, hb.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg K)
    apply Real.sqrt_le_sqrt
    simpa only [Real.rpow_two] using (henergy i t).2
  let M : ℝ := 4*(2^p)^2*L^2
  refine ⟨4*M*D, by dsimp [M]; positivity, ?_⟩
  intro j i s t
  let A := fun k => l2FourierCoeff k j (U t)-l2FourierCoeff k j (U s)
  let C := fun k => l2FourierCoeff k i (U t)-l2FourierCoeff k i (U s)
  obtain ⟨habs1, hs1, hb1⟩ := mixed_product_energy_of_bounds A
    (fun k => l2FourierCoeff k i (U t)) hp0 hL (hincrement j s t).1
    (hincrement j s t).2 (hmoment i t).1 (hmoment i t).2
  obtain ⟨habs2, hs2, hb2⟩ := mixed_product_energy_of_bounds C
    (fun k => l2FourierCoeff k j (U s)) hp0 hL (hincrement i s t).1
    (hincrement i s t).2 (hmoment j s).1 (hmoment j s).2
  let F1 := fun k => ∑' l, A l*l2FourierCoeff (k-l) i (U t)
  let F2 := fun k => ∑' l, C l*l2FourierCoeff (k-l) j (U s)
  have hrev (k : Fin 2 → ℤ) : Summable (fun l => l2FourierCoeff l j (U s)*C (k-l)) := by
    have hs := (pressureTimeSubEquiv k).summable_iff.mpr (summable_norm_iff.mp (habs2 k))
    change Summable (fun l => C (k-l)*l2FourierCoeff (k-(k-l)) j (U s)) at hs
    have he (l : Fin 2 → ℤ) : k-(k-l) = l := by abel
    simpa only [he, mul_comm] using hs
  have heq (k : Fin 2 → ℤ) :
      torusQuadraticFourierMoment k j i (U t)-torusQuadraticFourierMoment k j i (U s) = F1 k+F2 k := by
    rw [phaseGalerkin_l2_limit_quadraticFourierMoment_eq_tsum ν hν phase hU t,
      phaseGalerkin_l2_limit_quadraticFourierMoment_eq_tsum ν hν phase hU s]
    have hst := summable_norm_iff.mp (phaseGalerkin_l2_limit_convolution_norm_summable ν hν phase hU t k j i)
    have hss := summable_norm_iff.mp (phaseGalerkin_l2_limit_convolution_norm_summable ν hν phase hU s k j i)
    rw [← hst.tsum_sub hss]
    calc
      _ = ∑' l, (A l*l2FourierCoeff (k-l) i (U t)+l2FourierCoeff l j (U s)*C (k-l)) := by
        apply tsum_congr
        intro l
        dsimp [A, C]
        ring
      _ = F1 k+(∑' l, l2FourierCoeff l j (U s)*C (k-l)) :=
        (summable_norm_iff.mp (habs1 k)).tsum_add (hrev k)
      _ = _ := by rw [fourier_convolution_comm (fun l => l2FourierCoeff l j (U s)) C k]
  have hh := fourier_energy_add_bound F1 F2 hs1 hs2 hb1 hb2
  refine ⟨?_, ?_⟩
  · simpa only [heq] using hh.1
  · have hbtotal : (∑' k, (1+fourierEigenvalue k)^p * ‖F1 k+F2 k‖^2) ≤
        (4*M*D)*|t.1-s.1|^2 := hh.2.trans_eq (by dsimp [M]; ring)
    simpa only [heq] using hbtotal

def pressureRieszSymbol (k : Fin 2 → ℤ) (i j : Fin 2) : ℂ :=
  if k = 0 then 0 else
    ((2*π*Complex.I*(k i : ℂ))*(2*π*Complex.I*(k j : ℂ))) / (fourierEigenvalue k : ℂ)

theorem norm_pressureRieszSymbol_le_one (k : Fin 2 → ℤ) (i j : Fin 2) :
    ‖pressureRieszSymbol k i j‖ ≤ 1 := by
  by_cases hk : k = 0
  · simp only [pressureRieszSymbol, if_pos hk, norm_zero]; norm_num
  have hEig : 0 < fourierEigenvalue k :=
    lt_of_lt_of_le zero_lt_one (one_le_fourierEigenvalue_of_ne_zero k hk)
  rw [pressureRieszSymbol, if_neg hk, norm_div, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hEig.le]
  apply (div_le_one hEig).mpr
  have hi := norm_fourierDerivativeFactor_sq_le_eigenvalue k i
  have hj := norm_fourierDerivativeFactor_sq_le_eigenvalue k j
  nlinarith [sq_nonneg (‖(2*π*Complex.I*(k i : ℂ))‖-‖(2*π*Complex.I*(k j : ℂ))‖)]

theorem torusPressureFourierCoefficient_eq_riesz_tensor (V : TorusVelocityL2) (k : Fin 2 → ℤ) :
    torusPressureFourierCoefficient V k = ∑ i : Fin 2, ∑ j : Fin 2,
      pressureRieszSymbol k i j * torusQuadraticFourierMoment k j i V := by
  by_cases hk : k = 0
  · simp only [torusPressureFourierCoefficient, pressureRieszSymbol, if_pos hk,
      zero_mul, Finset.sum_const_zero]
  simp only [torusPressureFourierCoefficient, pressureRieszSymbol, if_neg hk, Fin.sum_univ_two]
  ring

private lemma norm_sum_fin2_fin2_sq_le_time (F : Fin 2 → Fin 2 → ℂ) :
    ‖∑ i : Fin 2, ∑ j : Fin 2, F i j‖^2 ≤ 4*∑ i : Fin 2, ∑ j : Fin 2, ‖F i j‖^2 := by
  have hn : ‖∑ i : Fin 2, ∑ j : Fin 2, F i j‖ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖F i j‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)).mpr hn
  simp only [Fin.sum_univ_two] at hs ⊢
  nlinarith [sq_nonneg (‖F 0 0‖-‖F 0 1‖), sq_nonneg (‖F 0 0‖-‖F 1 0‖),
    sq_nonneg (‖F 0 0‖-‖F 1 1‖), sq_nonneg (‖F 0 1‖-‖F 1 0‖),
    sq_nonneg (‖F 0 1‖-‖F 1 1‖), sq_nonneg (‖F 1 0‖-‖F 1 1‖)]

theorem torusPressureFourierCoefficient_sub_sq_le_tensor (V W : TorusVelocityL2) (k : Fin 2 → ℤ) :
    ‖torusPressureFourierCoefficient V k-torusPressureFourierCoefficient W k‖^2 ≤
      4*∑ i : Fin 2, ∑ j : Fin 2,
        ‖torusQuadraticFourierMoment k j i V-torusQuadraticFourierMoment k j i W‖^2 := by
  have he : torusPressureFourierCoefficient V k-torusPressureFourierCoefficient W k =
      ∑ i : Fin 2, ∑ j : Fin 2, pressureRieszSymbol k i j *
        (torusQuadraticFourierMoment k j i V-torusQuadraticFourierMoment k j i W) := by
    rw [torusPressureFourierCoefficient_eq_riesz_tensor, torusPressureFourierCoefficient_eq_riesz_tensor]
    simp only [Fin.sum_univ_two]
    ring
  rw [he]
  apply (norm_sum_fin2_fin2_sq_le_time _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, mul_pow]
  have hsym := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (norm_pressureRieszSymbol_le_one k i j)
  simpa only [one_pow, one_mul] using mul_le_mul_of_nonneg_right hsym
    (sq_nonneg ‖torusQuadraticFourierMoment k j i V-torusQuadraticFourierMoment k j i W‖)

theorem phaseGalerkin_l2_limit_uniform_pressure_increment_energy_below_one
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∃ D, 0 ≤ D ∧ ∀ s t : GalerkinTime,
      Summable (fun k => (1+fourierEigenvalue k)^p *
        ‖torusPressureFourierCoefficient (U t) k-torusPressureFourierCoefficient (U s) k‖^2) ∧
      (∑' k, (1+fourierEigenvalue k)^p *
        ‖torusPressureFourierCoefficient (U t) k-torusPressureFourierCoefficient (U s) k‖^2) ≤
          D*|t.1-s.1|^2 := by
  obtain ⟨C, hC, hquadratic⟩ :=
    phaseGalerkin_l2_limit_uniform_quadratic_increment_energy_below_one ν hν phase hφ hU hp0 hp1
  refine ⟨16*C, by positivity, ?_⟩
  intro s t
  let Q := fun (i j : Fin 2) (k : Fin 2 → ℤ) => (1+fourierEigenvalue k)^p *
    ‖torusQuadraticFourierMoment k j i (U t)-torusQuadraticFourierMoment k j i (U s)‖^2
  have hQ (i j : Fin 2) : Summable (Q i j) ∧ (∑' k, Q i j k) ≤ C*|t.1-s.1|^2 :=
    hquadratic j i s t
  have ht : Summable (fun k => ∑ i : Fin 2, ∑ j : Fin 2, Q i j k) := by
    simpa only [Fin.sum_univ_two] using
      (((hQ 0 0).1.add (hQ 0 1).1).add ((hQ 1 0).1.add (hQ 1 1).1))
  have hp (k : Fin 2 → ℤ) :
      (1+fourierEigenvalue k)^p *
        ‖torusPressureFourierCoefficient (U t) k-torusPressureFourierCoefficient (U s) k‖^2 ≤
          4*∑ i : Fin 2, ∑ j : Fin 2, Q i j k := by
    have h := mul_le_mul_of_nonneg_left
      (torusPressureFourierCoefficient_sub_sq_le_tensor (U t) (U s) k)
      (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k] : 0 ≤ 1+fourierEigenvalue k) p)
    exact h.trans_eq (by simp only [Q, Fin.sum_univ_two]; ring)
  have hs := (ht.mul_left 4).of_nonneg_of_le (fun k => mul_nonneg
    (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)) hp
  refine ⟨hs, (Summable.tsum_le_tsum hp hs (ht.mul_left 4)).trans ?_⟩
  rw [tsum_mul_left]
  simp only [Fin.sum_univ_two]
  rw [((hQ 0 0).1.add (hQ 0 1).1).tsum_add ((hQ 1 0).1.add (hQ 1 1).1),
    (hQ 0 0).1.tsum_add (hQ 0 1).1, (hQ 1 0).1.tsum_add (hQ 1 1).1]
  linarith [(hQ 0 0).2, (hQ 0 1).2, (hQ 1 0).2, (hQ 1 1).2]

/-- Interpolation of the actual weak pressure increments with the
earned H^{3−δ} bound gives the first absolute-moment time modulus. -/
theorem phaseGalerkin_l2_limit_uniform_pressure_first_moment_time_holder
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C, 0 ≤ C ∧ ∀ s t : GalerkinTime,
      Summable (fun k => (1+‖intVec k‖) *
        ‖torusPressureFourierCoefficient (U t) k-torusPressureFourierCoefficient (U s) k‖) ∧
      (∑' k, (1+‖intVec k‖) *
        ‖torusPressureFourierCoefficient (U t) k-torusPressureFourierCoefficient (U s) k‖) ≤
          C*|t.1-s.1|^(β/2) := by
  let δ : ℝ := (1-β)/4
  let p : ℝ := 1-δ
  let q : ℝ := 3-δ
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  have hp0 : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : p < 1 := by dsimp [p]; linarith
  obtain ⟨D, hD, hincrement⟩ := phaseGalerkin_l2_limit_uniform_pressure_increment_energy_below_one
    ν hν phase hφ hU hp0 hp1
  obtain ⟨B, hB, hpressure⟩ := phaseGalerkin_l2_limit_uniform_pressure_sobolev_energy
    ν hν phase hφ hU hδ0 hδ1
  let C : ℝ := 2^((1 : ℝ)) * (Real.sqrt (D^(β/2) * (4*B)^(1-β/2)) *
    Real.sqrt (∑' k : Fin 2 → ℤ,
      (1+fourierEigenvalue k)^(-((β/2)*p+(1-β/2)*q-1))))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro s t
  have hstrong := fourier_energy_sub_bound
    (torusPressureFourierCoefficient (U t)) (torusPressureFourierCoefficient (U s))
    (hpressure t).1 (hpressure s).1 (hpressure t).2 (hpressure s).2
  have hg : 1 < (β/2)*p+(1-β/2)*q-1 := by
    dsimp [p, q, δ]
    nlinarith
  have hh := fourier_covering_increment_l1_bound
    (fun k => torusPressureFourierCoefficient (U t) k-torusPressureFourierCoefficient (U s) k)
    (p := p) (q := q) (m := 1) (D := D) (B := 4*B) (d := |t.1-s.1|) (γ := β/2)
    (by linarith) (by linarith) (by norm_num) hg hD (by positivity) (abs_nonneg _)
    (hincrement s t).1 hstrong.1 (hincrement s t).2 (by linarith [hstrong.2])
  simpa only [Real.rpow_one, C] using hh

theorem phaseGalerkin_l2_limit_pressure_first_frequency_moment_summable
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) : Summable (fun k => ‖intVec k‖ * ‖torusPressureFourierCoefficient (U t) k‖) := by
  obtain ⟨M, hM, hmoment⟩ := phaseGalerkin_l2_limit_uniform_pressure_covering_moment
    ν hν phase hφ hU (β := 0) (by norm_num) (by norm_num)
  have hs : Summable (fun k => (1+‖intVec k‖) * ‖torusPressureFourierCoefficient (U t) k‖) := by
    simpa only [add_zero, Real.rpow_one] using (hmoment t).1
  apply hs.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro k
  exact mul_le_mul_of_nonneg_right (by linarith : ‖intVec k‖ ≤ 1+‖intVec k‖) (norm_nonneg _)

/-- The pressure and its actual first spatial derivatives are uniformly
bounded on the original closed time interval. -/
theorem phaseGalerkin_l2_limit_real_pressure_uniform_C1_bounds
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U)) :
    ∃ M, 0 ≤ M ∧ ∀ t : GalerkinTime,
      (∀ x, ‖torusRealPressure (U t) x‖ ≤ M) ∧
      ∀ j x, ‖pd j (torusRealPressure (U t)) x‖ ≤ ‖(2*π*Complex.I : ℂ)‖ * M := by
  obtain ⟨M, hM, hmoment⟩ := phaseGalerkin_l2_limit_uniform_pressure_covering_moment
    ν hν phase hφ hU (β := 0) (by norm_num) (by norm_num)
  have hm (t : GalerkinTime) :
      Summable (fun k => (1+‖intVec k‖) * ‖torusPressureFourierCoefficient (U t) k‖) ∧
      (∑' k, (1+‖intVec k‖) * ‖torusPressureFourierCoefficient (U t) k‖) ≤ M := by
    simpa only [add_zero, Real.rpow_one] using hmoment t
  refine ⟨M, hM, ?_⟩
  intro t
  have ha := phaseGalerkin_l2_limit_pressure_absolute ν hν phase hφ hU t
  have hda := phaseGalerkin_l2_limit_pressure_first_frequency_moment_summable ν hν phase hφ hU t
  constructor
  · intro x
    have hnorm (k : Fin 2 → ℤ) : ‖torusPressureFourierCoefficient (U t) k‖ ≤
        (1+‖intVec k‖) * ‖torusPressureFourierCoefficient (U t) k‖ := by
      nlinarith [mul_nonneg (norm_nonneg (intVec k)) (norm_nonneg (torusPressureFourierCoefficient (U t) k))]
    have hsumb := (Summable.tsum_le_tsum hnorm ha (hm t).1).trans (hm t).2
    have hr : ‖torusRealPressure (U t) x‖ ≤
        ‖complexFourierSeries (torusPressureFourierCoefficient (U t)) x‖ := by
      simpa only [torusRealPressure, Real.norm_eq_abs] using Complex.abs_re_le_norm
        (complexFourierSeries (torusPressureFourierCoefficient (U t)) x)
    exact hr.trans ((norm_complexFourierSeries_le ha x).trans hsumb)
  · intro j x
    have hh := norm_pd_complexFourierSeries_sub_le_first_moment
      (a := torusPressureFourierCoefficient (U t)) (b := fun _ => 0)
      ha (by simp) hda (by simp)
      (by simpa only [sub_zero] using (hm t).1)
      (by simpa only [sub_zero] using (hm t).2) j x
    have hz : complexFourierSeries (fun _ : Fin 2 → ℤ => (0 : ℂ)) = (0 : Pt 2 → ℂ) := by
      funext z
      simp only [complexFourierSeries, complexFourierSeriesTerm, zero_mul, tsum_zero, Pi.zero_apply]
    rw [hz] at hh
    have hcomplex : ‖pd j (complexFourierSeries (torusPressureFourierCoefficient (U t))) x‖ ≤
        ‖(2*π*Complex.I : ℂ)‖ * M := by
      simpa only [pd_zero_fun, Pi.zero_apply, sub_zero] using hh
    have hr : ‖pd j (torusRealPressure (U t)) x‖ ≤
        ‖pd j (complexFourierSeries (torusPressureFourierCoefficient (U t))) x‖ := by
      rw [pd_torusRealPressure_slice ν hν phase hφ hU]
      simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm
        (pd j (complexFourierSeries (torusPressureFourierCoefficient (U t))) x)
    exact hr.trans hcomplex

/-- The actual real pressure and its genuine gradient have the required
β/2 time modulus, uniformly in space, including both time endpoints. -/
theorem phaseGalerkin_l2_limit_real_pressure_time_holder
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    TimeHolder 1 (β/2) (phaseL2PressureExtension U) ∧
      ∀ j, TimeHolder 1 (β/2) (fun t => pd j (phaseL2PressureExtension U t)) := by
  obtain ⟨C, hC, hmoment⟩ := phaseGalerkin_l2_limit_uniform_pressure_first_moment_time_holder
    ν hν phase hφ hU hβ0 hβ1
  constructor
  · refine ⟨C, ?_⟩
    intro t ht s hs x
    rw [phaseL2PressureExtension_of_mem U ht, phaseL2PressureExtension_of_mem U hs]
    have hh := norm_complexFourierSeries_sub_le_first_moment
      (phaseGalerkin_l2_limit_pressure_absolute ν hν phase hφ hU ⟨t, ht⟩)
      (phaseGalerkin_l2_limit_pressure_absolute ν hν phase hφ hU ⟨s, hs⟩)
      (hmoment ⟨s, hs⟩ ⟨t, ht⟩).1 (hmoment ⟨s, hs⟩ ⟨t, ht⟩).2 x
    have hr : ‖torusRealPressure (U ⟨t, ht⟩) x-torusRealPressure (U ⟨s, hs⟩) x‖ ≤
        ‖complexFourierSeries (torusPressureFourierCoefficient (U ⟨t, ht⟩)) x-
          complexFourierSeries (torusPressureFourierCoefficient (U ⟨s, hs⟩)) x‖ := by
      simpa only [torusRealPressure, Real.norm_eq_abs, Complex.sub_re] using Complex.abs_re_le_norm
        (complexFourierSeries (torusPressureFourierCoefficient (U ⟨t, ht⟩)) x-
          complexFourierSeries (torusPressureFourierCoefficient (U ⟨s, hs⟩)) x)
    exact hr.trans hh
  · intro j
    refine ⟨‖(2*π*Complex.I : ℂ)‖*C, ?_⟩
    intro t ht s hs x
    change ‖pd j (phaseL2PressureExtension U t) x-pd j (phaseL2PressureExtension U s) x‖ ≤ _
    rw [phaseL2PressureExtension_of_mem U ht, phaseL2PressureExtension_of_mem U hs]
    have hh := norm_pd_complexFourierSeries_sub_le_first_moment
      (phaseGalerkin_l2_limit_pressure_absolute ν hν phase hφ hU ⟨t, ht⟩)
      (phaseGalerkin_l2_limit_pressure_absolute ν hν phase hφ hU ⟨s, hs⟩)
      (phaseGalerkin_l2_limit_pressure_first_frequency_moment_summable ν hν phase hφ hU ⟨t, ht⟩)
      (phaseGalerkin_l2_limit_pressure_first_frequency_moment_summable ν hν phase hφ hU ⟨s, hs⟩)
      (hmoment ⟨s, hs⟩ ⟨t, ht⟩).1 (hmoment ⟨s, hs⟩ ⟨t, ht⟩).2 j x
    have hr : ‖pd j (torusRealPressure (U ⟨t, ht⟩)) x-pd j (torusRealPressure (U ⟨s, hs⟩)) x‖ ≤
        ‖pd j (complexFourierSeries (torusPressureFourierCoefficient (U ⟨t, ht⟩))) x-
          pd j (complexFourierSeries (torusPressureFourierCoefficient (U ⟨s, hs⟩))) x‖ := by
      rw [pd_torusRealPressure_slice ν hν phase hφ hU, pd_torusRealPressure_slice ν hν phase hφ hU]
      simpa only [Real.norm_eq_abs, Complex.sub_re] using Complex.abs_re_le_norm
        (pd j (complexFourierSeries (torusPressureFourierCoefficient (U ⟨t, ht⟩))) x-
          pd j (complexFourierSeries (torusPressureFourierCoefficient (U ⟨s, hs⟩))) x)
    exact (hr.trans hh).trans_eq (by ring)

/-- All five fields of the pressure parabolic space follow for the same
genuine real pressure, for every exponent in the original open interval. -/
theorem phaseGalerkin_l2_limit_real_pressure_parabolic_C01
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsParabolicC01 1 β (phaseL2PressureExtension U) := by
  obtain ⟨M, hM, hbound⟩ := phaseGalerkin_l2_limit_real_pressure_uniform_C1_bounds ν hν phase hφ hU
  obtain ⟨H, hH, hspace⟩ := phaseGalerkin_l2_limit_real_pressure_spatial_holder
    ν hν phase hφ hU hβ0.le hβ1
  obtain ⟨htime, hgradtime⟩ := phaseGalerkin_l2_limit_real_pressure_time_holder ν hν phase hφ hU hβ0 hβ1
  refine { smooth_x := ?_, bdd := ?_, holder_time := htime, bdd_d1 := ?_, holder_d1 := ?_ }
  · intro t ht
    rw [phaseL2PressureExtension_of_mem U ht]
    exact contDiff_torusRealPressure_slice ν hν phase hφ hU ⟨t, ht⟩
  · refine ⟨M, ?_⟩
    intro t ht x
    rw [phaseL2PressureExtension_of_mem U ht]
    exact (hbound ⟨t, ht⟩).1 x
  · intro j
    refine ⟨‖(2*π*Complex.I : ℂ)‖*M, ?_⟩
    intro t ht x
    change ‖pd j (phaseL2PressureExtension U t) x‖ ≤ _
    rw [phaseL2PressureExtension_of_mem U ht]
    exact (hbound ⟨t, ht⟩).2 j x
  · intro j
    apply parHolder_of_spatial_time _ (hgradtime j)
    refine ⟨H, ?_⟩
    intro t ht x y
    change ‖pd j (phaseL2PressureExtension U t) x-pd j (phaseL2PressureExtension U t) y‖ ≤ _
    rw [phaseL2PressureExtension_of_mem U ht]
    exact hspace ⟨t, ht⟩ j x y

end AnomDiss

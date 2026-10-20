module

public import RequestProject.FourierSobolevProduct

/-!
# Negative-order Fourier energy of the genuine Navier--Stokes source

The original force and the actual quadratic velocity product give a
uniform H^{−δ} bound for the same projected source in the genuine heat
Duhamel formula. The physical derivative has its full `2πi` multiplier.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 1000000

def phaseQuadraticFractionalBound (ν : ℝ) (phase : Phase) (δ : ℝ) : ℝ :=
  4 * (2 ^ (1 - δ)) ^ 2 *
    (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-(1 + δ))) *
    (phaseGalerkinEnergyBound phase + phaseGalerkinGradientBound ν phase) ^ 2

theorem phaseQuadraticFractionalBound_nonneg (ν : ℝ) (phase : Phase) (δ : ℝ) :
    0 ≤ phaseQuadraticFractionalBound ν phase δ := by
  have hK : 0 ≤ ∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-(1 + δ)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _
  unfold phaseQuadraticFractionalBound
  positivity

def quadraticFourierFractionalTensorEnergy (δ : ℝ) (U : TorusVelocityL2)
    (k : Fin 2 → ℤ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, (1 + fourierEigenvalue k) ^ (1 - δ) *
    ‖torusQuadraticFourierMoment k j i U‖ ^ 2

theorem quadraticFourierFractionalTensorEnergy_nonneg (δ : ℝ) (U : TorusVelocityL2)
    (k : Fin 2 → ℤ) : 0 ≤ quadraticFourierFractionalTensorEnergy δ U k :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)

theorem phaseGalerkin_l2_limit_quadratic_tensor_fractional_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Summable (quadraticFourierFractionalTensorEnergy δ (U t)) ∧
      (∑' k, quadraticFourierFractionalTensorEnergy δ (U t) k) ≤
        4 * phaseQuadraticFractionalBound ν phase δ := by
  let Q := fun (j i : Fin 2) (k : Fin 2 → ℤ) =>
    (1 + fourierEigenvalue k) ^ (1 - δ) * ‖torusQuadraticFourierMoment k j i (U t)‖ ^ 2
  have hQ (j i : Fin 2) : Summable (Q j i) ∧
      (∑' k, Q j i k) ≤ phaseQuadraticFractionalBound ν phase δ :=
    phaseGalerkin_l2_limit_quadratic_fourier_fractional_energy ν hν phase hU t j i hδ0 hδ1
  have hs := (((hQ 0 0).1.add (hQ 1 0).1).add ((hQ 0 1).1.add (hQ 1 1).1))
  refine ⟨?_, ?_⟩
  · change Summable (fun k => ∑ i : Fin 2, ∑ j : Fin 2,
      (1 + fourierEigenvalue k) ^ (1 - δ) * ‖torusQuadraticFourierMoment k j i (U t)‖ ^ 2)
    simpa only [Fin.sum_univ_two, Q] using hs
  · change (∑' k, ∑ i : Fin 2, ∑ j : Fin 2, Q j i k) ≤ _
    simp only [Fin.sum_univ_two]
    rw [((hQ 0 0).1.add (hQ 1 0).1).tsum_add ((hQ 0 1).1.add (hQ 1 1).1),
      (hQ 0 0).1.tsum_add (hQ 1 0).1, (hQ 0 1).1.tsum_add (hQ 1 1).1]
    linarith [(hQ 0 0).2, (hQ 1 0).2, (hQ 0 1).2, (hQ 1 1).2]

theorem norm_fourierLeray_component_sq_le (k : Fin 2 → ℤ)
    (a : FourierVelocity) (i : Fin 2) :
    ‖fourierLeray k a i‖ ^ 2 ≤ ∑ j : Fin 2, ‖a j‖ ^ 2 := by
  have h := (PiLp.norm_apply_le (fourierLeray k a) i).trans (norm_fourierLeray_apply_le k a)
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
  simpa only [EuclideanSpace.norm_sq_eq] using hs

/-- The complete physical Fourier derivative factors have precisely the
true Laplace eigenvalue as their squared sum. -/
theorem sum_norm_fourierDerivativeFactor_sq (k : Fin 2 → ℤ) :
    (∑ j : Fin 2, ‖(2 * π * Complex.I * (k j : ℂ))‖ ^ 2) = fourierEigenvalue k := by
  simp_rw [norm_fourierDerivativeFactor_sq]
  unfold fourierEigenvalue euclNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [intVec, Finset.mul_sum]

/-- Cauchy--Schwarz controls the actual nonlinear flux, with no lost
physical derivative factor and no spatial differentiability premise. -/
theorem torusNonlinearFourierFlux_sq_le (k : Fin 2 → ℤ) (i : Fin 2) (U : TorusVelocityL2) :
    ‖torusNonlinearFourierFlux k i U‖ ^ 2 ≤
      fourierEigenvalue k * ∑ j : Fin 2, ‖torusQuadraticFourierMoment k j i U‖ ^ 2 := by
  have hn : ‖torusNonlinearFourierFlux k i U‖ ≤
      ∑ j : Fin 2, ‖(2 * π * Complex.I * (k j : ℂ))‖ *
        ‖torusQuadraticFourierMoment k j i U‖ := by
    simpa only [torusNonlinearFourierFlux, norm_mul] using
      norm_sum_le (Finset.univ : Finset (Fin 2))
        (fun j => (2 * π * Complex.I * (k j : ℂ)) * torusQuadraticFourierMoment k j i U)
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 2))
    (fun j => ‖(2 * π * Complex.I * (k j : ℂ))‖)
    (fun j => ‖torusQuadraticFourierMoment k j i U‖)
  rw [sum_norm_fourierDerivativeFactor_sq] at hcs
  exact hs.trans hcs

/-- One true projected nonlinear coefficient at order `−δ` is bounded
by the actual quadratic tensor energy at order `1−δ`. -/
theorem leray_nonlinear_negative_weight_le_tensor (k : Fin 2 → ℤ) (i : Fin 2)
    (U : TorusVelocityL2) (δ : ℝ) :
    (1 + fourierEigenvalue k) ^ (-δ) *
      ‖fourierLeray k (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q U)) i‖ ^ 2 ≤
        quadraticFourierFractionalTensorEnergy δ U k := by
  let A : FourierVelocity := WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q U)
  let M := ∑ q : Fin 2, ∑ j : Fin 2, ‖torusQuadraticFourierMoment k j q U‖ ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hw : 0 ≤ (1 + fourierEigenvalue k) ^ (-δ) :=
    Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _
  have hbase : 0 < 1 + fourierEigenvalue k :=
    add_pos_of_pos_of_nonneg zero_lt_one (fourierEigenvalue_nonneg k)
  have hproj : ‖fourierLeray k A i‖ ^ 2 ≤
      ∑ q : Fin 2, ‖torusNonlinearFourierFlux k q U‖ ^ 2 :=
    norm_fourierLeray_component_sq_le k A i
  have hsum : (∑ q : Fin 2, ‖torusNonlinearFourierFlux k q U‖ ^ 2) ≤
      fourierEigenvalue k * M := by
    calc
      _ ≤ ∑ q : Fin 2, fourierEigenvalue k *
          ∑ j : Fin 2, ‖torusQuadraticFourierMoment k j q U‖ ^ 2 :=
        Finset.sum_le_sum fun q _ => torusNonlinearFourierFlux_sq_le k q U
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hpow : (1 + fourierEigenvalue k) ^ (-δ) * (1 + fourierEigenvalue k) =
      (1 + fourierEigenvalue k) ^ (1 - δ) := by
    rw [show 1 - δ = -δ + 1 by ring,
      Real.rpow_add hbase, Real.rpow_one]
  change (1 + fourierEigenvalue k) ^ (-δ) * ‖fourierLeray k A i‖ ^ 2 ≤ _
  calc
    _ ≤ (1 + fourierEigenvalue k) ^ (-δ) *
        ∑ q : Fin 2, ‖torusNonlinearFourierFlux k q U‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hproj hw
    _ ≤ (1 + fourierEigenvalue k) ^ (-δ) * (fourierEigenvalue k * M) :=
      mul_le_mul_of_nonneg_left hsum hw
    _ ≤ (1 + fourierEigenvalue k) ^ (-δ) * ((1 + fourierEigenvalue k) * M) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hM) hw
    _ = _ := by
      rw [← mul_assoc, hpow]
      dsimp [M]
      simp only [quadraticFourierFractionalTensorEnergy, Finset.mul_sum]

theorem phaseGalerkin_l2_limit_leray_nonlinear_negative_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (i : Fin 2) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ (-δ) *
      ‖fourierLeray k (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q (U t))) i‖ ^ 2) ∧
    (∑' k, (1 + fourierEigenvalue k) ^ (-δ) *
      ‖fourierLeray k (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q (U t))) i‖ ^ 2) ≤
        4 * phaseQuadraticFractionalBound ν phase δ := by
  obtain ⟨hs, hb⟩ := phaseGalerkin_l2_limit_quadratic_tensor_fractional_energy ν hν phase hU t hδ0 hδ1
  have hn : ∀ k, 0 ≤ (1 + fourierEigenvalue k) ^ (-δ) *
      ‖fourierLeray k (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q (U t))) i‖ ^ 2 :=
    fun k => mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  have hpoint := fun k => leray_nonlinear_negative_weight_le_tensor k i (U t) δ
  have hs' := hs.of_nonneg_of_le hn hpoint
  exact ⟨hs', (Summable.tsum_le_tsum hpoint hs' hs).trans hb⟩

/-- The original, actually projected force has uniformly bounded negative
Fourier energy, directly from its true spatial L² bound. -/
theorem phaseForce_leray_negative_energy (phase : Phase) (t : GalerkinTime)
    (i : Fin 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ (-δ) *
      ‖fourierLeray k (vectorFourierCoeff (gForce phase t.1) k) i‖ ^ 2) ∧
    (∑' k, (1 + fourierEigenvalue k) ^ (-δ) *
      ‖fourierLeray k (vectorFourierCoeff (gForce phase t.1) k) i‖ ^ 2) ≤
        phaseForceL2Bound phase := by
  have hs := parseval_vector_cell (gForce phase t.1)
    (gForce_slice_props phase t.1).2.1.continuous (gForce_slice_props phase t.1).1
  have hn : ∀ k, 0 ≤ (1 + fourierEigenvalue k) ^ (-δ) *
      ‖fourierLeray k (vectorFourierCoeff (gForce phase t.1) k) i‖ ^ 2 :=
    fun k => mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  have hpoint (k : Fin 2 → ℤ) :
      (1 + fourierEigenvalue k) ^ (-δ) *
        ‖fourierLeray k (vectorFourierCoeff (gForce phase t.1) k) i‖ ^ 2 ≤
          vectorFourierEnergy (gForce phase t.1) k := by
    have hw := Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [fourierEigenvalue_nonneg k] : 1 ≤ 1 + fourierEigenvalue k)
      (neg_nonpos.mpr hδ)
    calc
      _ ≤ ‖fourierLeray k (vectorFourierCoeff (gForce phase t.1) k) i‖ ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (sq_nonneg _)
      _ ≤ _ := norm_fourierLeray_component_sq_le k _ i
  have hs' := hs.summable.of_nonneg_of_le hn hpoint
  refine ⟨hs', ?_⟩
  calc
    _ ≤ ∑' k, vectorFourierEnergy (gForce phase t.1) k :=
      Summable.tsum_le_tsum hpoint hs' hs.summable
    _ = l2sqV (gForce phase t.1) := hs.tsum_eq
    _ ≤ _ := phaseForce_l2_le phase t.2

def phaseL2FourierSourceSobolevBound (ν : ℝ) (phase : Phase) (δ : ℝ) : ℝ :=
  2 * phaseForceL2Bound phase + 8 * phaseQuadraticFractionalBound ν phase δ

theorem phaseL2FourierSourceSobolevBound_nonneg (ν : ℝ) (phase : Phase) (δ : ℝ) :
    0 ≤ phaseL2FourierSourceSobolevBound ν phase δ := by
  have hF := phaseForceL2Bound_nonneg phase
  have hQ := phaseQuadraticFractionalBound_nonneg ν phase δ
  unfold phaseL2FourierSourceSobolevBound
  positivity

/-- The same genuine source appearing in the actual NS heat Duhamel
formula has uniformly bounded H^{−δ} energy at every time in `[0,1]`. -/
theorem phaseGalerkin_l2_limit_source_negative_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (i : Fin 2) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ (-δ) *
      ‖phaseL2FourierSourceCurve phase k i U t‖ ^ 2) ∧
    (∑' k, (1 + fourierEigenvalue k) ^ (-δ) *
      ‖phaseL2FourierSourceCurve phase k i U t‖ ^ 2) ≤
        phaseL2FourierSourceSobolevBound ν phase δ := by
  let F := fun k => fourierLeray k (vectorFourierCoeff (gForce phase t.1) k) i
  let N := fun k => fourierLeray k
    (WithLp.toLp 2 (fun q => torusNonlinearFourierFlux k q (U t))) i
  obtain ⟨hF, hFb⟩ := phaseForce_leray_negative_energy phase t i hδ0.le
  obtain ⟨hN, hNb⟩ := phaseGalerkin_l2_limit_leray_nonlinear_negative_energy ν hν phase hU t i hδ0 hδ1
  have hpoint (k : Fin 2 → ℤ) :
      (1 + fourierEigenvalue k) ^ (-δ) * ‖phaseL2FourierSourceCurve phase k i U t‖ ^ 2 ≤
        2 * ((1 + fourierEigenvalue k) ^ (-δ) * ‖F k‖ ^ 2) +
          2 * ((1 + fourierEigenvalue k) ^ (-δ) * ‖N k‖ ^ 2) := by
    have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg (F k)) (norm_nonneg (N k)))).mpr
      (norm_sub_le (F k) (N k))
    have hsq : ‖F k - N k‖ ^ 2 ≤ 2 * ‖F k‖ ^ 2 + 2 * ‖N k‖ ^ 2 := by
      nlinarith [sq_nonneg (‖F k‖ - ‖N k‖)]
    rw [phaseL2FourierSourceCurve_apply]
    exact (mul_le_mul_of_nonneg_left hsq
      (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _)).trans_eq (by ring)
  have hmajor := (hF.mul_left 2).add (hN.mul_left 2)
  have hn (k : Fin 2 → ℤ) : 0 ≤ (1 + fourierEigenvalue k) ^ (-δ) *
      ‖phaseL2FourierSourceCurve phase k i U t‖ ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  have hs := hmajor.of_nonneg_of_le hn hpoint
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' k, (2 * ((1 + fourierEigenvalue k) ^ (-δ) * ‖F k‖ ^ 2) +
          2 * ((1 + fourierEigenvalue k) ^ (-δ) * ‖N k‖ ^ 2)) :=
      Summable.tsum_le_tsum hpoint hs hmajor
    _ = 2 * (∑' k, (1 + fourierEigenvalue k) ^ (-δ) * ‖F k‖ ^ 2) +
        2 * (∑' k, (1 + fourierEigenvalue k) ^ (-δ) * ‖N k‖ ^ 2) := by
      rw [(hF.mul_left 2).tsum_add (hN.mul_left 2), tsum_mul_left, tsum_mul_left]
    _ ≤ 2 * phaseForceL2Bound phase + 2 * (4 * phaseQuadraticFractionalBound ν phase δ) :=
      add_le_add (mul_le_mul_of_nonneg_left hFb (by norm_num))
        (mul_le_mul_of_nonneg_left hNb (by norm_num))
    _ = _ := by unfold phaseL2FourierSourceSobolevBound; ring

/-- The same source bound on every finite set of actual frequencies. -/
theorem phaseGalerkin_l2_limit_source_negative_finite_energy
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (i : Fin 2) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (S : Finset (Fin 2 → ℤ)) :
    (∑ k ∈ S, (1 + fourierEigenvalue k) ^ (-δ) *
      ‖phaseL2FourierSourceCurve phase k i U t‖ ^ 2) ≤
        phaseL2FourierSourceSobolevBound ν phase δ := by
  obtain ⟨hs, hb⟩ := phaseGalerkin_l2_limit_source_negative_energy ν hν phase hU t i hδ0 hδ1
  exact (hs.sum_le_tsum S (fun k _ => mul_nonneg
    (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _))).trans hb

end AnomDiss

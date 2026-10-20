module

public import RequestProject.NSPhaseForceHeatFourier

/-!
# Uniform fractional Sobolev energy of the actual constructed force

Each active force piece is a rescaled shear eigenfield. Its genuine
Fourier coefficients are supported on a single Laplacian eigenvalue
shell. The proved decay of the pieces therefore supplies every uniform
Sobolev order strictly below one, for all phases and all real times.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 1000000

/-- Every time derivative piece is a genuine eigenfield of the physical
unit-torus Laplacian at its rescaled frequency. -/
theorem lap_fpiece (w : Phase) (r j : ℕ) (t : ℝ) (x : Pt 2) :
    lap (fpiece w r j t) x = -(4 * π ^ 2 * kk j ^ 2) • fpiece w r j t x := by
  let c := iteratedDeriv (r + 1) (cf₀.coef (w j).1) ((t - sj j) / δs j)
  let A := 1 / (kk j * δs j ^ (r + 2))
  have he := (eigenspace_properties c).2.2.2.2.1
  change lap (fun y => A • eField c (kk j • y - (w j).2)) x =
    -(4 * π ^ 2 * kk j ^ 2) • (A • eField c (kk j • x - (w j).2))
  rw [lap_affine _ ((eigenspace_properties c).1.of_le (natCast_le_infty 2)), he,
    smul_smul, smul_smul]
  congr 1
  ring

/-- A nonzero genuine Fourier component of an eigenfield lies on its
actual Laplacian eigenvalue shell. -/
theorem vectorFourierCoeff_eigenvalue_shell {v : Pt 2 → Pt 2}
    (hv : ContDiff ℝ 2 v) (hp : IsPeriodic v) {L : ℝ}
    (heig : ∀ x, lap v x = -L • v x) (k : Fin 2 → ℤ) (i : Fin 2)
    (hne : vectorFourierCoeff v k i ≠ 0) : fourierEigenvalue k = L := by
  have he : vectorFourierCoeff (lap v) k i = (-L : ℂ) * vectorFourierCoeff v k i := by
    change fc (fun x => (lap v x i : ℂ)) k = (-L : ℂ) * fc (fun x => (v x i : ℂ)) k
    unfold fc
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    change (lap v x i : ℂ) * expChar (-intVec k) x = _
    rw [heig x]
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hL : vectorFourierCoeff (lap v) k i =
      (-fourierEigenvalue k : ℂ) * vectorFourierCoeff v k i := by
    simpa only [PiLp.smul_apply, Complex.real_smul, Complex.ofReal_neg] using
      congrArg (fun a : FourierVelocity => a i) (vectorFourierCoeff_lap v hv hp k)
  rw [he] at hL
  change (-L : ℂ) * vectorFourierCoeff v k i =
    (-fourierEigenvalue k : ℂ) * vectorFourierCoeff v k i at hL
  have hh : -L = -fourierEigenvalue k := by
    simpa only [Complex.neg_re, Complex.ofReal_re] using
      congrArg Complex.re (mul_right_cancel₀ hne hL)
  exact neg_injective hh.symm

/-- The fractional square energy of a genuine periodic eigenfield is
exactly its component `L²` energy times its shell weight. -/
theorem hasSum_eigenfield_fourier_sobolev {v : Pt 2 → Pt 2}
    (hv : ContDiff ℝ 2 v) (hp : IsPeriodic v) {L : ℝ}
    (heig : ∀ x, lap v x = -L • v x) (s : ℝ) (i : Fin 2) :
    HasSum (fun k => (1 + fourierEigenvalue k) ^ s * ‖vectorFourierCoeff v k i‖ ^ 2)
      ((1 + L) ^ s * ∫ x in cell 2, ‖(v x i : ℂ)‖ ^ 2) := by
  have hc : Continuous (fun x => (v x i : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_apply i).comp hv.continuous)
  have hpc : IsPeriodic (fun x => (v x i : ℂ)) := by
    intro x n
    change ((v (x + intVec n) i : ℝ) : ℂ) = _
    rw [hp x n]
  have hs := (parseval_cell_complex (fun x => (v x i : ℂ)) hc hpc).mul_left ((1 + L) ^ s)
  apply hs.congr_fun
  intro k
  change (1 + fourierEigenvalue k) ^ s * ‖vectorFourierCoeff v k i‖ ^ 2 =
    (1 + L) ^ s * ‖vectorFourierCoeff v k i‖ ^ 2
  by_cases hz : vectorFourierCoeff v k i = 0
  · simp only [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
  · rw [vectorFourierCoeff_eigenvalue_shell hv hp heig k i hz]

/-- The scale occurring in each force piece's order-`s` energy is
uniformly bounded whenever `s<1`. -/
theorem force_piece_sobolev_scale_bounded {s : ℝ} (hs : s < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j : ℕ, 1 ≤ j →
      kk j ^ (s - 1) * δs j ^ (-2 : ℝ) ≤ K := by
  let X : ℕ → ℝ := fun j => kk j ^ (s - 1) * δs j ^ (-2 : ℝ)
  have hdecay : Tendsto (fun j : ℕ => X j / ηs j) atTop (𝓝 0) := by
    simpa only [X, Nat.cast_zero, neg_zero, zero_sub] using piece_decay hs 0
  have hb := Metric.isBounded_range_of_tendsto (fun j => X j / ηs j) hdecay
  obtain ⟨B, hB⟩ := hb.exists_norm_le
  have hB0 : 0 ≤ B := (norm_nonneg (X 0 / ηs 0)).trans (hB _ (mem_range_self 0))
  have hτ : 0 ≤ τstar := by unfold τstar; positivity
  refine ⟨B * τstar, mul_nonneg hB0 hτ, fun j hj => ?_⟩
  have hη := ηs_pos j hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hηle : ηs j ≤ τstar := by
    unfold ηs
    exact div_le_self hτ (by nlinarith : (1 : ℝ) ≤ (j : ℝ) ^ 2)
  have hY : X j / ηs j ≤ B :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB _ (mem_range_self j))
  calc
    X j = (X j / ηs j) * ηs j := by field_simp
    _ ≤ B * ηs j := mul_le_mul_of_nonneg_right hY hη.le
    _ ≤ B * τstar := mul_le_mul_of_nonneg_left hηle hB0

/-- The shell weight of a force piece grows at most like its frequency
to the true order `2s`. -/
theorem force_piece_sobolev_shell_weight {s : ℝ} (hs : 0 ≤ s) (j : ℕ) :
    (1 + 4 * π ^ 2 * kk j ^ 2) ^ s ≤
      (1 + 4 * π ^ 2) ^ s * (kk j ^ s) ^ 2 := by
  have hk := one_le_kk j
  have hk0 : 0 ≤ kk j := le_trans zero_le_one hk
  have hbase : 1 + 4 * π ^ 2 * kk j ^ 2 ≤ (1 + 4 * π ^ 2) * kk j ^ 2 := by
    nlinarith [sq_nonneg (kk j - 1)]
  calc
    _ ≤ ((1 + 4 * π ^ 2) * kk j ^ 2) ^ s :=
      Real.rpow_le_rpow (by positivity) hbase hs
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (sq_nonneg _)]
      congr 1
      calc
        (kk j ^ 2) ^ s = kk j ^ ((2 : ℝ) * s) := by
          simpa only [Nat.cast_ofNat] using (Real.rpow_natCast_mul hk0 2 s).symm
        _ = kk j ^ (s * (2 : ℝ)) := by congr 1; ring
        _ = (kk j ^ s) ^ 2 := by
          simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast hk0 s 2

/-- All phases and all real times have a uniform genuine order-`s`
Fourier square energy for every `0≤s<1`. -/
theorem gForce_uniform_sobolev_energy {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (w : Phase) (t : ℝ) (i : Fin 2),
      Summable (fun k => (1 + fourierEigenvalue k) ^ s *
        ‖vectorFourierCoeff (gForce w t) k i‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ s *
        ‖vectorFourierCoeff (gForce w t) k i‖ ^ 2) ≤ B := by
  obtain ⟨C, hC0, hC⟩ := fpiece_bound (α := 0) le_rfl zero_le_one 0
  obtain ⟨K, hK0, hK⟩ := force_piece_sobolev_scale_bounded hs₁
  refine ⟨(1 + 4 * π ^ 2) ^ s * (C * K) ^ 2, by positivity, fun w t i => ?_⟩
  rw [← forceD_zero_eq]
  rcases forceD_single w 0 t with hz | ⟨j, hj, _, he⟩
  · rw [hz]
    simp only [vectorFourierCoeff_apply, Pi.zero_apply, Complex.ofReal_zero, fc, zero_mul,
      integral_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
      summable_zero, tsum_zero, true_and]
    positivity
  · rw [he]
    let v := fpiece w 0 j t
    have hv := (fpiece_props w 0 j t).2.1.of_le (natCast_le_infty 2)
    have hp := (fpiece_props w 0 j t).1
    have hs := hasSum_eigenfield_fourier_sobolev hv hp (lap_fpiece w 0 j t) s i
    have hkpos : 0 < kk j := zero_lt_one.trans_le (one_le_kk j)
    have hδpos := δs_pos j hj
    let A : ℝ := C * kk j ^ (-1 : ℝ) * δs j ^ (-2 : ℝ)
    have hA0 : 0 ≤ A := by dsimp only [A]; positivity
    have hbound : ∀ x, ‖(v x i : ℂ)‖ ≤ A := by
      intro x
      have hvb : ‖v x‖ ≤ A := by
        simpa only [v, A, sub_zero, zero_sub, Real.rpow_zero,
          show (0 : ℝ) - 1 = -1 by norm_num, Nat.cast_zero, neg_zero] using (hC w j hj t).1 x
      have hi : ‖(v x i : ℂ)‖ ≤ ‖v x‖ := by
        simpa only [Complex.norm_real] using norm_le_pi_norm (v x) i
      exact hi.trans hvb
    have hc : Continuous (fun x => (v x i : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_apply i).comp hv.continuous)
    have hL2 := integral_cell_norm_sq_le_const hc hA0 hbound
    have hAeq : kk j ^ s * A = C * (kk j ^ (s - 1) * δs j ^ (-2 : ℝ)) := by
      dsimp only [A]
      rw [Real.rpow_sub hkpos, Real.rpow_one, Real.rpow_neg_one]
      ring
    have hscale : 0 ≤ kk j ^ (s - 1) * δs j ^ (-2 : ℝ) := by positivity
    refine ⟨hs.summable, ?_⟩
    rw [hs.tsum_eq]
    calc
      _ ≤ (1 + 4 * π ^ 2 * kk j ^ 2) ^ s * A ^ 2 :=
        mul_le_mul_of_nonneg_left hL2 (by positivity)
      _ ≤ ((1 + 4 * π ^ 2) ^ s * (kk j ^ s) ^ 2) * A ^ 2 :=
        mul_le_mul_of_nonneg_right (force_piece_sobolev_shell_weight hs₀ j) (sq_nonneg _)
      _ = (1 + 4 * π ^ 2) ^ s * (kk j ^ s * A) ^ 2 := by ring
      _ = (1 + 4 * π ^ 2) ^ s * (C * (kk j ^ (s - 1) * δs j ^ (-2 : ℝ))) ^ 2 := by
        rw [hAeq]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (sq_le_sq₀ (mul_nonneg hC0 hscale) (mul_nonneg hC0 hK0)).2
          (mul_le_mul_of_nonneg_left (hK j hj) hC0)

end AnomDiss

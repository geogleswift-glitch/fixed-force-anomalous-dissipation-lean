module

public import RequestProject.PhaseForceHeatRegularity
public import RequestProject.NSPhaseGalerkinMild
public import RequestProject.FourierHeatDuhamelSmoothing

/-! # Fourier energy and coefficient identification for the genuine force heat term -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 1000000

/-- The physical Laplacian has its genuine unit-torus Fourier multiplier. -/
theorem fc_lap_C2 (f : Pt 2 → ℂ) (hf : ContDiff ℝ 2 f)
    (hp : IsPeriodic f) (k : Fin 2 → ℤ) :
    fc (lap f) k = (-fourierEigenvalue k : ℂ) * fc f k := by
  have hpd (j : Fin 2) : fc (pd j (pd j f)) k =
      (2 * π * Complex.I * (k j : ℂ)) *
        ((2 * π * Complex.I * (k j : ℂ)) * fc f k) := by
    rw [fc_pd (pd j f) (contDiff_pd_of_C2 f hf j) (isPeriodic_pd f hp j),
      fc_pd f (hf.of_le (by norm_num)) hp]
  unfold lap fc
  simp only [Finset.sum_mul]
  rw [integral_finset_sum (μ := volume.restrict (cell 2))
    (f := fun j x => pd j (pd j f) x * expChar (-intVec k) x)
    (Finset.univ : Finset (Fin 2)) (fun j _ =>
      ((continuous_pd_of_C1 _ (contDiff_pd_of_C2 f hf j) j).mul
        (continuous_expChar _)).continuousOn.integrableOn_compact isCompact_Icc)]
  change (∑ j : Fin 2, fc (pd j (pd j f)) k) = (-fourierEigenvalue k : ℂ) * fc f k
  simp only [hpd, Fin.sum_univ_two]
  unfold fourierEigenvalue euclNorm
  rw [sq_sqrt (by positivity)]
  simp only [intVec, Fin.sum_univ_two]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

theorem integral_cell_norm_sq_le_const {f : Pt 2 → ℂ} (hf : Continuous f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ x in cell 2, ‖f x‖ ^ 2) ≤ C ^ 2 := by
  have hi : IntegrableOn (fun x => ‖f x‖ ^ 2) (cell 2) :=
    (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hic : IntegrableOn (fun _x : Pt 2 => C ^ 2) (cell 2) :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  calc
    (∫ x in cell 2, ‖f x‖ ^ 2) ≤ (∫ _x in cell 2, C ^ 2) := by
      apply setIntegral_mono_on hi hic measurableSet_Icc
      intro x _
      exact (sq_le_sq₀ (norm_nonneg _) hC0).2 (hC x)
    _ = C ^ 2 := by simp [Measure.real, volume_cell_two]

/-- Bounded periodic `C²` functions have genuine square-summable `H²`
Fourier coefficients, with a bound from the function and its Laplacian. -/
theorem fourier_h2_energy_of_bounded_lap {f : Pt 2 → ℂ}
    (hf : ContDiff ℝ 2 f) (hp : IsPeriodic f) {C D : ℝ}
    (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖lap f x‖ ≤ D) :
    Summable (fun k => (1 + fourierEigenvalue k) ^ 2 * ‖fc f k‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ 2 * ‖fc f k‖ ^ 2) ≤
        2 * C ^ 2 + 2 * D ^ 2 := by
  have hP := parseval_cell_complex f hf.continuous hp
  have hL := parseval_cell_complex (lap f) (continuous_lap_C2 hf) (periodic_lap_C2 hf hp)
  have he (k : Fin 2 → ℤ) : ‖fc (lap f) k‖ ^ 2 =
      fourierEigenvalue k ^ 2 * ‖fc f k‖ ^ 2 := by
    rw [fc_lap_C2 f hf hp, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (fourierEigenvalue_nonneg k), mul_pow]
  simp_rw [he] at hL
  have hsum := (hP.summable.mul_left 2).add (hL.summable.mul_left 2)
  have hdom (k : Fin 2 → ℤ) :
      (1 + fourierEigenvalue k) ^ 2 * ‖fc f k‖ ^ 2 ≤
        2 * ‖fc f k‖ ^ 2 + 2 * (fourierEigenvalue k ^ 2 * ‖fc f k‖ ^ 2) := by
    nlinarith [sq_nonneg (fourierEigenvalue k - 1), sq_nonneg ‖fc f k‖,
      mul_nonneg (sq_nonneg (fourierEigenvalue k - 1)) (sq_nonneg ‖fc f k‖)]
  have hs : Summable (fun k => (1 + fourierEigenvalue k) ^ 2 * ‖fc f k‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hdom hsum
  refine ⟨hs, (hs.tsum_le_tsum hdom hsum).trans ?_⟩
  rw [Summable.tsum_add (hP.summable.mul_left 2) (hL.summable.mul_left 2),
    tsum_mul_left, tsum_mul_left, hP.tsum_eq, hL.tsum_eq]
  exact add_le_add (mul_le_mul_of_nonneg_left (integral_cell_norm_sq_le_const
    hf.continuous hC0 hC) (by norm_num))
    (mul_le_mul_of_nonneg_left (integral_cell_norm_sq_le_const
      (continuous_lap_C2 hf) hD0 hD) (by norm_num))

/-- The actual force contribution has a uniform `H²` bound on the entire
closed time interval, including its zero initial endpoint. -/
theorem phaseForceHeatComponent_uniform_h2_energy {ν : ℝ} (hν : 0 < ν)
    (w : Phase) (i : Fin 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      Summable (fun k => (1 + fourierEigenvalue k) ^ 2 *
        ‖fc (phaseForceHeatComponent ν w i t) k‖ ^ 2) ∧
      (∑' k, (1 + fourierEigenvalue k) ^ 2 *
        ‖fc (phaseForceHeatComponent ν w i t) k‖ ^ 2) ≤ B := by
  have hr := phaseForceHeatComponent_isParabolicC12 (T := 1) (β := 1 / 2)
    hν (by norm_num) (by norm_num) (by norm_num) w i
  obtain ⟨C, hC⟩ := hr.bdd
  obtain ⟨D₀, hD₀⟩ := hr.bdd_d2 0 0
  obtain ⟨D₁, hD₁⟩ := hr.bdd_d2 1 1
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 hzero 0)
  have hD00 : 0 ≤ D₀ := (norm_nonneg _).trans (hD₀ 0 hzero 0)
  have hD10 : 0 ≤ D₁ := (norm_nonneg _).trans (hD₁ 0 hzero 0)
  refine ⟨2 * C ^ 2 + 2 * (D₀ + D₁) ^ 2, by positivity, fun t ht => ?_⟩
  have hp : IsPeriodic (phaseForceHeatComponent ν w i t) := by
    apply heatDuhamel_periodic
    intro s x n
    change ((gForce w s (x + intVec n) i : ℝ) : ℂ) = _
    rw [(gForce_slice_props w s).1 x n]
  apply fourier_h2_energy_of_bounded_lap (hr.smooth_x t ht) hp hC0
    (add_nonneg hD00 hD10) (hC t ht)
  intro x
  simp only [lap, Fin.sum_univ_two]
  exact (norm_add_le _ _).trans (add_le_add (hD₀ t ht x) (hD₁ t ht x))

/-- The actual two-dimensional Gaussian characteristic function, with the
physical unit-torus frequency normalization. -/
theorem integral_expChar_gauss2 (v : ℝ≥0) (k : Fin 2 → ℤ) :
    (∫ ζ, expChar (intVec k) ζ ∂gauss2 v) =
      (Real.exp (-(v : ℝ) * fourierEigenvalue k / 2) : ℂ) := by
  have hcoord (j : Fin 2) :
      (∫ x : ℝ, Complex.exp (2 * π * Complex.I * (k j : ℂ) * (x : ℂ))
        ∂gaussianReal 0 v) =
        (Real.exp (-(v : ℝ) * (2 * π * (k j : ℝ)) ^ 2 / 2) : ℂ) := by
    calc
      _ = charFun (gaussianReal 0 v) (2 * π * (k j : ℝ)) := by
        rw [charFun_apply_real]
        congr 1
        funext x
        congr 1
        push_cast
        ring
      _ = _ := by
        rw [charFun_gaussianReal, Complex.ofReal_exp]
        congr 1
        push_cast
        ring
  simp_rw [expChar_intVec_eq_prod]
  rw [gauss2, integral_fintype_prod_eq_prod
    (fun j (x : ℝ) => Complex.exp (2 * π * Complex.I * (k j : ℂ) * (x : ℂ)))]
  simp_rw [hcoord]
  simp only [Fin.prod_univ_two, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  unfold fourierEigenvalue euclNorm
  rw [sq_sqrt (by positivity)]
  simp only [intVec, Fin.sum_univ_two]
  push_cast
  ring

/-- Fourier coefficients of genuine Gaussian averaging are multiplied by the
heat multiplier. Both integrals are justified by the bounded periodic datum. -/
theorem fc_heatOp {f : Pt 2 → ℂ} (hf : Continuous f) (hp : IsPeriodic f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (v : ℝ≥0) (k : Fin 2 → ℤ) :
    fc (heatOp v f) k =
      (Real.exp (-(v : ℝ) * fourierEigenvalue k / 2) : ℂ) * fc f k := by
  haveI : IsFiniteMeasure (volume.restrict (cell 2)) := by
    rw [isFiniteMeasure_restrict]
    simp [volume_cell_two]
  have hcont : Continuous (Function.uncurry fun (x ζ : Pt 2) =>
      f (x + ζ) * expChar (-intVec k) x) :=
    (hf.comp (continuous_fst.add continuous_snd)).mul
      ((continuous_expChar _).comp continuous_fst)
  have hswap : (∫ x in cell 2, ∫ ζ, f (x + ζ) * expChar (-intVec k) x ∂gauss2 v) =
      ∫ ζ, (∫ x in cell 2, f (x + ζ) * expChar (-intVec k) x) ∂gauss2 v := by
    apply integral_integral_swap
    apply Integrable.of_bound hcont.aestronglyMeasurable C
    exact Eventually.of_forall fun p => by
      simpa only [Function.uncurry, norm_mul, norm_expChar, mul_one] using hC (p.1 + p.2)
  unfold fc heatOp
  simp_rw [← integral_mul_const]
  rw [hswap]
  change (∫ ζ, fc (fun x => f (x + ζ)) k ∂gauss2 v) = _
  simp_rw [fc_translate f hf hp]
  rw [integral_mul_const, integral_expChar_gauss2]
  rfl

/-- Spatial Fourier coefficients commute with the genuine causal heat
Duhamel integral. The time integral includes the correct viscous multiplier. -/
theorem fc_heatDuhamel {ν : ℝ} (hν : 0 ≤ ν) {F : ℝ → Pt 2 → ℂ}
    (hF : Continuous (Function.uncurry F)) (hp : ∀ s, IsPeriodic (F s))
    {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C) {t : ℝ} (ht : 0 ≤ t)
    (k : Fin 2 → ℤ) :
    fc (heatDuhamel ν F t) k =
      ∫ s in (0 : ℝ)..t, (Real.exp (-(ν * (t - s) * fourierEigenvalue k)) : ℂ) *
        fc (F s) k := by
  have hFs (s : ℝ) : Continuous (F s) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hcont : Continuous (Function.uncurry fun (x : Pt 2) (s : ℝ) =>
      heatOp (Real.toNNReal (2 * ν * (t - s))) (F s) x * expChar (-intVec k) x) := by
    apply Continuous.mul
    · exact (continuous_heatOp_with_param hF hC).comp
        (by fun_prop : Continuous (fun p : Pt 2 × ℝ =>
          (p.2, Real.toNNReal (2 * ν * (t - p.2)), p.1)))
    · exact (continuous_expChar _).comp continuous_fst
  have hswap :
      (∫ x in cell 2, ∫ s in Ioc (0 : ℝ) t,
        heatOp (Real.toNNReal (2 * ν * (t - s))) (F s) x * expChar (-intVec k) x) =
      ∫ s in Ioc (0 : ℝ) t, ∫ x in cell 2,
        heatOp (Real.toNNReal (2 * ν * (t - s))) (F s) x * expChar (-intVec k) x := by
    apply integral_integral_swap
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
        (prod_mono subset_rfl Ioc_subset_Icc_self)
  unfold fc heatDuhamel
  simp only [intervalIntegral.integral_of_le ht]
  simp_rw [← integral_mul_const]
  rw [hswap]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  change fc (heatOp (Real.toNNReal (2 * ν * (t - s))) (F s)) k = _
  rw [fc_heatOp (hFs s) (hp s) (hC s)]
  congr 2
  rw [Real.coe_toNNReal _ (mul_nonneg (mul_nonneg (by norm_num) hν) (sub_nonneg.2 hs.2))]
  congr 1
  ring

/-- The actual force heat term is exactly the standard genuine Fourier
Duhamel coefficient; the force is fixed by its Leray projection. -/
theorem phaseForceHeatComponent_fourier {ν : ℝ} (hν : 0 ≤ ν)
    (w : Phase) (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) (k : Fin 2 → ℤ) :
    fc (phaseForceHeatComponent ν w i t) k =
      heatDuhamelCoefficient fourierEigenvalue ν
        (fun s k => vectorFourierCoeff (gForce w s) k i) t k := by
  let L : Pt 2 →L[ℝ] ℂ := Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)
  have hF : Continuous (Function.uncurry fun t x => (gForce w t x i : ℂ)) :=
    L.continuous.comp (force_regularity.1 w).1.toIsTimeSmoothForce.continuous_uncurry
  have hp : ∀ s, IsPeriodic (fun x => (gForce w s x i : ℂ)) := by
    intro s x n
    change ((gForce w s (x + intVec n) i : ℝ) : ℂ) = _
    rw [(gForce_slice_props w s).1 x n]
  obtain ⟨C, _, hB⟩ := forceD_uniform_holderBd (α := 0) (by norm_num) (by norm_num) 0
  have hC : ∀ s x, ‖(gForce w s x i : ℂ)‖ ≤ C := by
    intro s x
    have he : ‖(gForce w s x i : ℂ)‖ ≤ ‖gForce w s x‖ := by
      simpa only [Complex.norm_real] using norm_le_pi_norm (gForce w s x) i
    apply he.trans
    simpa only [forceD_zero_eq] using (hB w s).1 x
  rw [phaseForceHeatComponent, fc_heatDuhamel hν hF hp hC ht,
    heatDuhamelCoefficient_eq_standard]
  rfl

/-- The coefficient identification in exactly the projected-force form
which occurs in the genuine Navier–Stokes coefficient equation. -/
theorem phaseForceHeatComponent_fourier_leray {ν : ℝ} (hν : 0 ≤ ν)
    (w : Phase) (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) (k : Fin 2 → ℤ) :
    fc (phaseForceHeatComponent ν w i t) k =
      heatDuhamelCoefficient fourierEigenvalue ν
        (fun s k => fourierLeray k (vectorFourierCoeff (gForce w s) k) i) t k := by
  have he : (fun s k => fourierLeray k (vectorFourierCoeff (gForce w s) k) i) =
      (fun s k => vectorFourierCoeff (gForce w s) k i) := by
    funext s k
    have hfix := fourierLeray_vectorFourierCoeff (gForce w s)
      ((gForce_slice_props w s).2.1.of_le (natCast_le_infty 1))
      (gForce_slice_props w s).1 (gForce_slice_props w s).2.2.1 k
    exact congrArg (fun a : FourierVelocity => a i) hfix
  rw [he]
  exact phaseForceHeatComponent_fourier hν w i ht k

end AnomDiss

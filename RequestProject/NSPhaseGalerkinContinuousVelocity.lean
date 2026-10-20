module

public import RequestProject.NSPhaseGalerkinSobolevGain
public import RequestProject.FourierSobolevAlgebra
public import RequestProject.FourierSeriesRegularity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuous spatial reconstruction of the actual Navier–Stokes limit

The proved, uniform H^(3/2) energy implies genuine absolute Fourier
summability. Its character series reconstructs a real bounded periodic
velocity from the same strong Galerkin limit coefficients.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction ComplexConjugate

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 1200000

/-- The original Galerkin limit has the Fourier symmetry of a real field. -/
theorem phaseGalerkin_l2_limit_fourier_reality
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (k : Fin 2 → ℤ) (i : Fin 2) :
    l2FourierCoeff (-k) i (U t) = conj (l2FourierCoeff k i (U t)) := by
  have hlim := fun m : GalerkinCoefficientIndex =>
    phaseGalerkin_l2_coefficient_curve_tendsto ν hν phase hU m.1 m.2
  exact phaseGalerkin_limit_coefficient_reality hlim t k i

/-- A uniform absolute coefficient bound obtained from the actual H^(3/2)
energy, with the true summable two-dimensional lattice constant. -/
def phaseL2VelocityAbsoluteBound (ν : ℝ) (phase : Phase) : ℝ :=
  Real.sqrt (phaseL2VelocitySobolevGainBound ν phase (3 / 2)) *
    Real.sqrt (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-(3 / 2 : ℝ)))

lemma phaseL2VelocityAbsoluteBound_nonneg (ν : ℝ) (phase : Phase) :
    0 ≤ phaseL2VelocityAbsoluteBound ν phase := by
  unfold phaseL2VelocityAbsoluteBound
  positivity

/-- The actual limit coefficients are absolutely summable, uniformly in
time and vector component. -/
theorem phaseGalerkin_l2_limit_fourier_absolute
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (i : Fin 2) (t : GalerkinTime) :
    Summable (fun k => ‖l2FourierCoeff k i (U t)‖) ∧
      (∑' k, ‖l2FourierCoeff k i (U t)‖) ≤ phaseL2VelocityAbsoluteBound ν phase := by
  obtain ⟨hs, hb⟩ := phaseGalerkin_l2_limit_positive_sobolev_gain ν hν phase hφ hU
    (r := (3 / 2 : ℝ)) (by norm_num) (by norm_num) i t
  have hg : (1 : ℝ) < 3 / 2 - 0 := by norm_num
  obtain ⟨ha, haB⟩ := fourier_weighted_l1_of_sobolev (q := (0 : ℝ)) hg hs
  simp only [Real.rpow_zero, one_mul, sub_zero] at ha haB
  refine ⟨ha, haB.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hb) (Real.sqrt_nonneg _)

/-- The genuine real character series attached to the actual strong
Galerkin limit, on the covering space of the unit torus. -/
def phaseL2ContinuousVelocity (U : GalerkinTime →ᵇ TorusVelocityL2)
    (t : GalerkinTime) (x : Pt 2) : Pt 2 :=
  fun i => (complexFourierSeries (fun k => l2FourierCoeff k i (U t)) x).re

theorem continuous_phaseL2ContinuousVelocity_slice
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) : Continuous (phaseL2ContinuousVelocity U t) := by
  apply continuous_pi
  intro i
  exact Complex.continuous_re.comp (continuous_complexFourierSeries
    (phaseGalerkin_l2_limit_fourier_absolute ν hν phase hφ hU i t).1)

theorem isPeriodic_phaseL2ContinuousVelocity
    (U : GalerkinTime →ᵇ TorusVelocityL2) (t : GalerkinTime) :
    IsPeriodic (phaseL2ContinuousVelocity U t) := by
  intro x m
  funext i
  exact congrArg Complex.re (isPeriodic_complexFourierSeries
    (fun k => l2FourierCoeff k i (U t)) x m)

theorem norm_phaseL2ContinuousVelocity_le
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (x : Pt 2) :
    ‖phaseL2ContinuousVelocity U t x‖ ≤ phaseL2VelocityAbsoluteBound ν phase := by
  apply pi_norm_le_iff_of_nonneg (phaseL2VelocityAbsoluteBound_nonneg ν phase) |>.2
  intro i
  obtain ⟨hs, hb⟩ := phaseGalerkin_l2_limit_fourier_absolute ν hν phase hφ hU i t
  have hr : ‖(complexFourierSeries (fun k => l2FourierCoeff k i (U t)) x).re‖ ≤ ‖complexFourierSeries (fun k => l2FourierCoeff k i (U t)) x‖ := by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (complexFourierSeries (fun k => l2FourierCoeff k i (U t)) x)
  exact hr.trans ((norm_complexFourierSeries_le hs x).trans hb)

/-- The true series is real when the original coefficients satisfy the
conjugate symmetry inherited from the real Galerkin approximations. -/
theorem complexFourierSeries_real_of_symmetry {a : (Fin 2 → ℤ) → ℂ}
    (ha : Summable (fun k => ‖a k‖)) (hsym : ∀ k, a (-k) = conj (a k))
    (x : Pt 2) : (complexFourierSeries a x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change conj (∑' k, complexFourierSeriesTerm a k x) = _
  have hm := Complex.conjCLE.toContinuousLinearMap.map_tsum (summable_complexFourierSeriesTerm ha x)
  change conj (∑' k, complexFourierSeriesTerm a k x) = ∑' k, conj (complexFourierSeriesTerm a k x) at hm
  rw [hm]
  calc
    _ = ∑' k, complexFourierSeriesTerm a (-k) x := by
      apply tsum_congr
      intro k
      simp only [complexFourierSeriesTerm, hsym, map_mul, intVec_neg, expChar_neg_eq_conj]
    _ = _ := by simpa only [complexFourierSeries, Equiv.neg_apply] using (Equiv.neg (Fin 2 → ℤ)).tsum_eq (fun k => complexFourierSeriesTerm a k x)

lemma tsum_if_mem_zero_eq_tsum_compl {G : Type*} [AddCommMonoid G] [TopologicalSpace G]
    (f : (Fin 2 → ℤ) → G) (S : Finset (Fin 2 → ℤ)) :
    (∑' k, if k ∈ S then 0 else f k) = ∑' k : {k // k ∉ S}, f k := by
  classical
  have ht := tsum_subtype {k : Fin 2 → ℤ | k ∉ S} f
  change (∑' k : {k // k ∉ S}, f k) = _ at ht
  rw [ht]
  apply tsum_congr
  intro k
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs <;> simp_all

/-- A finite Fourier block leaves exactly the genuine absolute coefficient
tail as a uniform spatial error bound. -/
theorem norm_complexFourierSeries_sub_sum_le {a : (Fin 2 → ℤ) → ℂ}
    (ha : Summable (fun k => ‖a k‖)) (S : Finset (Fin 2 → ℤ)) (x : Pt 2) :
    ‖complexFourierSeries a x - ∑ k ∈ S, complexFourierSeriesTerm a k x‖ ≤
      ∑' k, if k ∈ S then 0 else ‖a k‖ := by
  have hs := (summable_complexFourierSeriesTerm ha x).sum_add_tsum_subtype_compl S
  have he : complexFourierSeries a x - ∑ k ∈ S, complexFourierSeriesTerm a k x =
      ∑' k : {k // k ∉ S}, complexFourierSeriesTerm a k x := by
    change (∑' k, complexFourierSeriesTerm a k x) - _ = _
    rw [← hs]
    abel
  rw [he, tsum_if_mem_zero_eq_tsum_compl]
  simpa only [norm_complexFourierSeriesTerm] using
    norm_tsum_le_tsum_norm (ha.subtype (fun k => k ∉ S) |>.congr
      (fun k => (norm_complexFourierSeriesTerm a k x).symm))

/-- The genuine complement kernel tail tends to zero as finite blocks
exhaust the integer lattice. -/
theorem tendsto_fourier_kernel_tail_zero (r : ℝ) :
    Tendsto (fun S : Finset (Fin 2 → ℤ) =>
      ∑' k, if k ∈ S then 0 else (1 + fourierEigenvalue k) ^ (-r)) atTop (𝓝 0) := by
  simpa only [tsum_if_mem_zero_eq_tsum_compl] using
    tendsto_tsum_compl_atTop_zero (fun k : Fin 2 → ℤ => (1 + fourierEigenvalue k) ^ (-r))

/-- Uniform actual H^(3/2) energy gives uniform finite-block convergence
on the full time-space slab. No summable pointwise coefficient envelope
or unproved differentiability of the velocity is assumed. -/
theorem phaseGalerkin_l2_limit_fourier_series_uniform
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (i : Fin 2) :
    TendstoUniformly (fun S : Finset (Fin 2 → ℤ) => fun z : GalerkinTime × Pt 2 =>
      ∑ k ∈ S, complexFourierSeriesTerm (fun k => l2FourierCoeff k i (U z.1)) k z.2)
      (fun z => complexFourierSeries (fun k => l2FourierCoeff k i (U z.1)) z.2) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have htail := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
    (tendsto_fourier_kernel_tail_zero (3 / 2))
  have hsmall := htail.const_mul (Real.sqrt (phaseL2VelocitySobolevGainBound ν phase (3 / 2)))
  simp only [Real.sqrt_zero, mul_zero] at hsmall
  filter_upwards [hsmall.eventually (Iio_mem_nhds hε)] with S hS
  intro z
  rw [dist_eq_norm]
  have hgain := phaseGalerkin_l2_limit_positive_sobolev_gain ν hν phase hφ hU
    (r := (3 / 2 : ℝ)) (by norm_num) (by norm_num) i z.1
  exact (norm_complexFourierSeries_sub_sum_le
    (phaseGalerkin_l2_limit_fourier_absolute ν hν phase hφ hU i z.1).1 S z.2).trans_lt
      ((fourier_l1_tail_bound (by norm_num : (1 : ℝ) < 3 / 2) hgain.1 hgain.2 S).trans_lt hS)

/-- Joint time-space continuity is proved by the actual uniform character
series, including the initial time of the original closed slab. -/
theorem continuous_phaseL2ContinuousVelocity
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U)) :
    Continuous (fun z : GalerkinTime × Pt 2 => phaseL2ContinuousVelocity U z.1 z.2) := by
  apply continuous_pi
  intro i
  apply Complex.continuous_re.comp
  apply (phaseGalerkin_l2_limit_fourier_series_uniform ν hν phase hφ hU i).continuous
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro S
  apply continuous_finset_sum
  intro k hk
  exact ((l2FourierCoeff k i).continuous.comp (U.continuous.comp continuous_fst)).mul
    ((continuous_expChar (intVec k)).comp continuous_snd)

/-- Finite real Fourier reconstruction acts continuously on the genuine
completed velocity space. -/
def l2FourierPartialSum (S : Finset (Fin 2 → ℤ)) :
    TorusVelocityL2 →L[ℝ] TorusVelocityL2 :=
  ∑ k ∈ S, ∑ i : Fin 2,
    ((Complex.reCLM.comp (l2FourierCoeff k i)).smulRight (l2FourierTestReal k i) +
      (Complex.imCLM.comp (l2FourierCoeff k i)).smulRight (l2FourierTestImag k i))

lemma periodicVelocityToL2_add
    (v w : Pt 2 → Pt 2) (hv : Continuous v) (hpv : IsPeriodic v)
    (hw : Continuous w) (hpw : IsPeriodic w) :
    periodicVelocityToL2 (v + w) (hv.add hw) (by intro x m; change v (x + intVec m) + w (x + intVec m) = v x + w x; rw [hpv, hpw]) =
      periodicVelocityToL2 v hv hpv + periodicVelocityToL2 w hw hpw := by
  have hpvw : IsPeriodic (v + w) := by
    intro x m
    change v (x + intVec m) + w (x + intVec m) = v x + w x
    rw [hpv, hpw]
  apply Lp.ext
  filter_upwards [periodicVelocityToL2_ae (v+w) (hv.add hw) hpvw,
    periodicVelocityToL2_ae v hv hpv, periodicVelocityToL2_ae w hw hpw,
    Lp.coeFn_add (periodicVelocityToL2 v hv hpv) (periodicVelocityToL2 w hw hpw)] with x hx hV hW hsum
  rw [hx, hsum]
  change euclideanVelocity (v+w) x = (periodicVelocityToL2 v hv hpv) x + (periodicVelocityToL2 w hw hpw) x
  rw [hV, hW]
  rfl

lemma periodicVelocityToL2_smul
    (c : ℝ) (v : Pt 2 → Pt 2) (hv : Continuous v) (hp : IsPeriodic v) :
    periodicVelocityToL2 (c • v) (hv.const_smul c) (by intro x m; change c • v (x + intVec m) = c • v x; rw [hp]) =
      c • periodicVelocityToL2 v hv hp := by
  have hpcv : IsPeriodic (c • v) := by
    intro x m
    change c • v (x + intVec m) = c • v x
    rw [hp]
  apply Lp.ext
  filter_upwards [periodicVelocityToL2_ae (c • v) (hv.const_smul c) hpcv,
    periodicVelocityToL2_ae v hv hp, Lp.coeFn_smul c (periodicVelocityToL2 v hv hp)] with x hx hV hsmul
  rw [hx, hsmul]
  change euclideanVelocity (c • v) x = c • ((periodicVelocityToL2 v hv hp) x)
  rw [hV]
  rfl

lemma continuous_sum_fields {ι : Type*} (S : Finset ι) (f : ι → Pt 2 → Pt 2)
    (hf : ∀ j, Continuous (f j)) : Continuous (∑ j ∈ S, f j) := by
  convert continuous_finset_sum S (fun j _ => hf j) using 1
  exact funext (fun x => Finset.sum_apply x S f)

lemma isPeriodic_sum_fields {ι : Type*} (S : Finset ι) (f : ι → Pt 2 → Pt 2)
    (hp : ∀ j, IsPeriodic (f j)) : IsPeriodic (∑ j ∈ S, f j) := by
  intro x m
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => hp j x m)

lemma periodicVelocityToL2_congr {v w : Pt 2 → Pt 2}
    (hv : Continuous v) (hpv : IsPeriodic v) (hw : Continuous w) (hpw : IsPeriodic w)
    (h : v = w) : periodicVelocityToL2 v hv hpv = periodicVelocityToL2 w hw hpw := by
  subst w
  rfl

lemma periodicVelocityToL2_sum {ι : Type*} (S : Finset ι) (f : ι → Pt 2 → Pt 2)
    (hf : ∀ j, Continuous (f j)) (hp : ∀ j, IsPeriodic (f j)) :
    periodicVelocityToL2 (∑ j ∈ S, f j) (continuous_sum_fields S f hf)
      (isPeriodic_sum_fields S f hp) =
      ∑ j ∈ S, periodicVelocityToL2 (f j) (hf j) (hp j) := by
  let L : (Pt 2 →ᵇ EuclideanSpace ℝ (Fin 2)) →L[ℝ] TorusVelocityL2 :=
    BoundedContinuousFunction.toLp 2 (volume.restrict (cell 2)) ℝ
  have he : periodicVelocityBCF (∑ j ∈ S, f j)
      (continuous_sum_fields S f hf)
      (isPeriodic_sum_fields S f hp) =
      ∑ j ∈ S, periodicVelocityBCF (f j) (hf j) (hp j) := by
    ext x i
    simp only [periodicVelocityBCF_apply, BoundedContinuousFunction.sum_apply,
      euclideanVelocity, WithLp.ofLp_sum, Finset.sum_apply]
  change L _ = ∑ j ∈ S, L _
  rw [he, map_sum]

lemma realFourierMode_eq_component_sum (k : Fin 2 → ℤ) (a : FourierVelocity) :
    realFourierMode k a = ∑ i : Fin 2,
      ((a i).re • realFourierMode k (EuclideanSpace.single i (1 : ℂ)) +
        (a i).im • realFourierMode k (EuclideanSpace.single i Complex.I)) := by
  ext x j
  fin_cases j <;>
    simp [realFourierMode, Fin.sum_univ_two, EuclideanSpace.single_apply, Complex.mul_re,
      sub_eq_add_neg]

/-- A finite character block formed from arbitrary completed-space
coefficients, without any reconstruction or smoothness assumption on `W`. -/
def l2FourierPartialVelocity (S : Finset (Fin 2 → ℤ)) (W : TorusVelocityL2) : Pt 2 → Pt 2 :=
  ∑ k ∈ S, realFourierMode k (WithLp.toLp 2 (fun i => l2FourierCoeff k i W))

lemma continuous_l2FourierPartialVelocity (S : Finset (Fin 2 → ℤ)) (W : TorusVelocityL2) :
    Continuous (l2FourierPartialVelocity S W) :=
  continuous_sum_fields S _ (fun k => (contDiff_realFourierMode k _).continuous)

lemma isPeriodic_l2FourierPartialVelocity (S : Finset (Fin 2 → ℤ)) (W : TorusVelocityL2) :
    IsPeriodic (l2FourierPartialVelocity S W) := by
  exact isPeriodic_sum_fields S _ (fun k => isPeriodic_realFourierMode k _)

lemma l2FourierPartialVelocity_apply (S : Finset (Fin 2 → ℤ)) (W : TorusVelocityL2)
    (x : Pt 2) (i : Fin 2) :
    l2FourierPartialVelocity S W x i =
      (∑ k ∈ S, complexFourierSeriesTerm (fun k => l2FourierCoeff k i W) k x).re := by
  simp only [l2FourierPartialVelocity, Finset.sum_apply, realFourierMode,
    complexFourierSeriesTerm]
  simpa only [Complex.coe_reAddGroupHom] using
    (map_sum Complex.reAddGroupHom
      (fun k => l2FourierCoeff k i W * expChar (intVec k) x) S).symm

theorem l2FourierPartialSum_eq_periodicVelocityToL2
    (S : Finset (Fin 2 → ℤ)) (W : TorusVelocityL2) :
    l2FourierPartialSum S W = periodicVelocityToL2 (l2FourierPartialVelocity S W)
      (continuous_l2FourierPartialVelocity S W) (isPeriodic_l2FourierPartialVelocity S W) := by
  let F := fun (k : Fin 2 → ℤ) (i : Fin 2) =>
    ((l2FourierCoeff k i W).re • realFourierMode k (EuclideanSpace.single i (1 : ℂ)) +
      (l2FourierCoeff k i W).im • realFourierMode k (EuclideanSpace.single i Complex.I))
  have hc (k : Fin 2 → ℤ) (i : Fin 2) : Continuous (F k i) := by
    have hR := (contDiff_realFourierMode k (EuclideanSpace.single i (1 : ℂ))).continuous
    have hI := (contDiff_realFourierMode k (EuclideanSpace.single i Complex.I)).continuous
    convert (hR.const_smul (l2FourierCoeff k i W).re).add
      (hI.const_smul (l2FourierCoeff k i W).im) using 1
  have hp (k : Fin 2 → ℤ) (i : Fin 2) : IsPeriodic (F k i) := by
    intro x m
    change (l2FourierCoeff k i W).re • realFourierMode k _ (x + intVec m) +
      (l2FourierCoeff k i W).im • realFourierMode k _ (x + intVec m) = _
    rw [isPeriodic_realFourierMode k _, isPeriodic_realFourierMode k _]
    rfl
  have he : l2FourierPartialVelocity S W = ∑ k ∈ S, ∑ i : Fin 2, F k i :=
    Finset.sum_congr rfl (fun k _ => realFourierMode_eq_component_sum k _)
  have hterm (k : Fin 2 → ℤ) (i : Fin 2) :
      periodicVelocityToL2 (F k i) (hc k i) (hp k i) =
        (l2FourierCoeff k i W).re • l2FourierTestReal k i +
          (l2FourierCoeff k i W).im • l2FourierTestImag k i := by
    dsimp only [F]
    have hR := (contDiff_realFourierMode k (EuclideanSpace.single i (1 : ℂ))).continuous
    have hI := (contDiff_realFourierMode k (EuclideanSpace.single i Complex.I)).continuous
    have hpR := isPeriodic_realFourierMode k (EuclideanSpace.single i (1 : ℂ))
    have hpI := isPeriodic_realFourierMode k (EuclideanSpace.single i Complex.I)
    have hcR : Continuous ((l2FourierCoeff k i W).re •
        realFourierMode k (EuclideanSpace.single i (1 : ℂ))) := by
      convert hR.const_smul (l2FourierCoeff k i W).re using 1
    have hcI : Continuous ((l2FourierCoeff k i W).im •
        realFourierMode k (EuclideanSpace.single i Complex.I)) := by
      convert hI.const_smul (l2FourierCoeff k i W).im using 1
    have hpRs : IsPeriodic ((l2FourierCoeff k i W).re •
        realFourierMode k (EuclideanSpace.single i (1 : ℂ))) := by
      intro x m
      change (l2FourierCoeff k i W).re • realFourierMode k _ (x + intVec m) = _
      rw [hpR]
      rfl
    have hpIs : IsPeriodic ((l2FourierCoeff k i W).im •
        realFourierMode k (EuclideanSpace.single i Complex.I)) := by
      intro x m
      change (l2FourierCoeff k i W).im • realFourierMode k _ (x + intVec m) = _
      rw [hpI]
      rfl
    rw [periodicVelocityToL2_add _ _ hcR hpRs hcI hpIs,
      periodicVelocityToL2_smul _ _ hR hpR, periodicVelocityToL2_smul _ _ hI hpI]
    rfl
  have hcK (k : Fin 2 → ℤ) := continuous_sum_fields Finset.univ (F k) (hc k)
  have hpK (k : Fin 2 → ℤ) := isPeriodic_sum_fields Finset.univ (F k) (hp k)
  calc
    _ = ∑ k ∈ S, ∑ i : Fin 2, periodicVelocityToL2 (F k i) (hc k i) (hp k i) := by
      simp only [hterm, l2FourierPartialSum, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
    _ = periodicVelocityToL2 (∑ k ∈ S, ∑ i : Fin 2, F k i)
        (continuous_sum_fields S _ hcK) (isPeriodic_sum_fields S _ hpK) := by
      rw [periodicVelocityToL2_sum S _ hcK hpK]
      apply Finset.sum_congr rfl
      intro k hk
      exact (periodicVelocityToL2_sum Finset.univ (F k) (hc k) (hp k)).symm
    _ = _ := periodicVelocityToL2_congr _ _ _ _ he.symm

theorem l2FourierPartialSum_periodicVelocityToL2
    (S : Finset (Fin 2 → ℤ)) (v : Pt 2 → Pt 2) (hv : Continuous v) (hp : IsPeriodic v) :
    l2FourierPartialSum S (periodicVelocityToL2 v hv hp) =
      periodicVelocityToL2 (realFourierTruncation S v)
        (continuous_realFourierTruncation S v)
        (by
          intro x m
          ext i
          simp only [realFourierTruncation]
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          rw [isPeriodic_expChar k x m]) := by
  rw [l2FourierPartialSum_eq_periodicVelocityToL2]
  apply periodicVelocityToL2_congr
  ext x i
  simp only [l2FourierPartialVelocity_apply, complexFourierSeriesTerm,
    l2FourierCoeff_periodicVelocityToL2, realFourierTruncation, vectorFourierCoeff_apply]
lemma l2sqV_le_two_mul_sq_of_component_bound (v : Pt 2 → Pt 2) (hv : Continuous v)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x i, |v x i| ≤ C) :
    l2sqV v ≤ 2 * C ^ 2 := by
  have hb (x : Pt 2) : (∑ i : Fin 2, v x i ^ 2) ≤ 2 * C ^ 2 := by
    have hsq (i : Fin 2) : v x i ^ 2 ≤ C ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hbound x i)
    simp only [Fin.sum_univ_two]
    linarith [hsq 0, hsq 1]
  calc
    l2sqV v ≤ ∫ x in cell 2, 2 * C ^ 2 :=
      setIntegral_mono_on (integrableOn_cell_of_continuous (continuous_finset_sum _
        (fun i _ => ((continuous_apply i).comp hv).pow 2)))
        (integrableOn_cell_of_continuous continuous_const) measurableSet_Icc (fun x _ => hb x)
    _ = _ := by simp [Measure.real, volume_cell]

/-- The finite operators converge to the original completed-space limit.
This is proved from actual Galerkin spatial tails, rather than assumed
Fourier completeness or a desired representative. -/
theorem phaseGalerkin_l2_limit_partialSum_tendsto
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) :
    Tendsto (fun S : Finset (Fin 2 → ℤ) => l2FourierPartialSum S (U t)) atTop (𝓝 (U t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := ((phaseGalerkinTailBound_tendsto_zero ν phase).eventually
    (Iio_mem_nhds (sq_pos_of_pos hε))).exists
  filter_upwards [eventually_ge_atTop (fourierFrequencyBox (K+1))] with S hS
  have hpoint := ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto U).comp hU
  have hnorm : Tendsto (fun n => ‖phaseGalerkinL2Curve ν hν phase (φ n) t -
      l2FourierPartialSum S (phaseGalerkinL2Curve ν hν phase (φ n) t)‖ ^ 2)
      atTop (𝓝 (‖U t - l2FourierPartialSum S (U t)‖ ^ 2)) := by
    exact (hpoint.sub ((l2FourierPartialSum S).continuous.tendsto _ |>.comp hpoint)).norm.pow 2
  have hb : ‖U t - l2FourierPartialSum S (U t)‖ ^ 2 ≤ phaseGalerkinTailBound ν phase K := by
    apply le_of_tendsto hnorm
    apply Eventually.of_forall
    intro n
    rw [phaseGalerkinL2Curve_eq, l2FourierPartialSum_periodicVelocityToL2,
      norm_periodicVelocityToL2_sub_sq]
    have ht := realFourierTruncation_l2_error_le_gradient_div
      (phaseGalerkinVelocity ν hν phase (φ n) t)
      ((phaseGalerkinVelocity_contDiff ν hν phase (φ n) t).of_le (natCast_le_infty 2))
      (phaseGalerkinVelocity_periodic ν hν phase (φ n) t) S
      (R := 4 * π ^ 2 * ((K+1 : ℕ) : ℝ) ^ 2) (by positivity [Real.pi_pos])
      (fun k hk => fourierEigenvalue_outside_box (K+1) k (fun hbox => hk (hS hbox)))
    exact ht.trans (div_le_div_of_nonneg_right
      (phaseGalerkinVelocity_gradient_bound ν hν phase (φ n) t.2) (by positivity))
  rw [dist_eq_norm, norm_sub_rev]
  nlinarith [norm_nonneg (U t - l2FourierPartialSum S (U t))]

/-- The same finite operators converge to the actual continuous series in
the genuine cell L² norm. -/
theorem phaseGalerkin_l2_limit_partialSum_series_tendsto
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) :
    Tendsto (fun S : Finset (Fin 2 → ℤ) => l2FourierPartialSum S (U t)) atTop
      (𝓝 (periodicVelocityToL2 (phaseL2ContinuousVelocity U t)
        (continuous_phaseL2ContinuousVelocity_slice ν hν phase hφ hU t)
        (isPeriodic_phaseL2ContinuousVelocity U t))) := by
  let R := fun S : Finset (Fin 2 → ℤ) =>
    Real.sqrt (phaseL2VelocitySobolevGainBound ν phase (3 / 2)) *
      Real.sqrt (∑' k, if k ∈ S then 0 else (1 + fourierEigenvalue k) ^ (-(3 / 2 : ℝ)))
  have hR0 (S) : 0 ≤ R S := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hR : Tendsto R atTop (𝓝 0) := by
    have h := ((Real.continuous_sqrt.tendsto (0 : ℝ)).comp
      (tendsto_fourier_kernel_tail_zero (3 / 2))).const_mul
      (Real.sqrt (phaseL2VelocitySobolevGainBound ν phase (3 / 2)))
    simpa only [R, Function.comp_def, Real.sqrt_zero, mul_zero] using h
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hR.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 2))] with S hS
  have hcomp (x : Pt 2) (i : Fin 2) :
      |(l2FourierPartialVelocity S (U t) - phaseL2ContinuousVelocity U t) x i| ≤ R S := by
    have hgain := phaseGalerkin_l2_limit_positive_sobolev_gain ν hν phase hφ hU
      (r := (3 / 2 : ℝ)) (by norm_num) (by norm_num) i t
    have hnorm := norm_complexFourierSeries_sub_sum_le
      (phaseGalerkin_l2_limit_fourier_absolute ν hν phase hφ hU i t).1 S x
    have hr := Complex.abs_re_le_norm
      (complexFourierSeries (fun k => l2FourierCoeff k i (U t)) x -
        ∑ k ∈ S, complexFourierSeriesTerm (fun k => l2FourierCoeff k i (U t)) k x)
    have he : |(l2FourierPartialVelocity S (U t) - phaseL2ContinuousVelocity U t) x i| =
        |(complexFourierSeries (fun k => l2FourierCoeff k i (U t)) x -
          ∑ k ∈ S, complexFourierSeriesTerm (fun k => l2FourierCoeff k i (U t)) k x).re| := by
      rw [Pi.sub_apply, Pi.sub_apply, l2FourierPartialVelocity_apply]
      change |(∑ k ∈ S, complexFourierSeriesTerm (fun k => l2FourierCoeff k i (U t)) k x).re -
          (complexFourierSeries (fun k => l2FourierCoeff k i (U t)) x).re| =
        |(complexFourierSeries (fun k => l2FourierCoeff k i (U t)) x).re -
          (∑ k ∈ S, complexFourierSeriesTerm (fun k => l2FourierCoeff k i (U t)) k x).re|
      exact abs_sub_comm _ _
    rw [he]
    exact (hr.trans hnorm).trans
      (fourier_l1_tail_bound (by norm_num : (1 : ℝ) < 3 / 2) hgain.1 hgain.2 S)
  have hn : ‖l2FourierPartialSum S (U t) -
      periodicVelocityToL2 (phaseL2ContinuousVelocity U t)
        (continuous_phaseL2ContinuousVelocity_slice ν hν phase hφ hU t)
        (isPeriodic_phaseL2ContinuousVelocity U t)‖ ^ 2 ≤ 2 * (R S) ^ 2 := by
    rw [l2FourierPartialSum_eq_periodicVelocityToL2, norm_periodicVelocityToL2_sub_sq]
    exact l2sqV_le_two_mul_sq_of_component_bound _
      ((continuous_l2FourierPartialVelocity S (U t)).sub
        (continuous_phaseL2ContinuousVelocity_slice ν hν phase hφ hU t)) (hR0 S) hcomp
  rw [dist_eq_norm]
  have hsq : (R S) ^ 2 < (ε / 2) ^ 2 :=
    (sq_lt_sq₀ (hR0 S) (by positivity : 0 ≤ ε / 2)).mpr hS
  nlinarith

/-- The reconstructed continuous real periodic velocity represents exactly
the original strong Galerkin limit in genuine cell L². -/
theorem phaseGalerkin_l2_limit_continuousVelocity_identification
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) :
    periodicVelocityToL2 (phaseL2ContinuousVelocity U t)
      (continuous_phaseL2ContinuousVelocity_slice ν hν phase hφ hU t)
      (isPeriodic_phaseL2ContinuousVelocity U t) = U t :=
  tendsto_nhds_unique (phaseGalerkin_l2_limit_partialSum_series_tendsto ν hν phase hφ hU t)
    (phaseGalerkin_l2_limit_partialSum_tendsto ν hν phase hU t)

/-- The original manuscript's integral Fourier coefficients of the
reconstructed spatial field are exactly the same completed-space values. -/
theorem phaseGalerkin_l2_limit_continuousVelocity_fourier
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (k : Fin 2 → ℤ) (i : Fin 2) :
    vectorFourierCoeff (phaseL2ContinuousVelocity U t) k i = l2FourierCoeff k i (U t) := by
  rw [← l2FourierCoeff_periodicVelocityToL2 k i (phaseL2ContinuousVelocity U t)
    (continuous_phaseL2ContinuousVelocity_slice ν hν phase hφ hU t)
    (isPeriodic_phaseL2ContinuousVelocity U t),
    phaseGalerkin_l2_limit_continuousVelocity_identification ν hν phase hφ hU t]

/-- A genuine strong Galerkin limit has an actual jointly continuous,
real, periodic and uniformly bounded spatial representative. The theorem
has no Navier–Stokes or classical-existence premise. -/
theorem exists_phaseGalerkin_l2_limit_continuous_velocity
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) :
    ∃ φ : ℕ → ℕ, ∃ U : GalerkinTime →ᵇ TorusVelocityL2,
      StrictMono φ ∧
      Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U) ∧
      ∃ hv : ∀ t, Continuous (phaseL2ContinuousVelocity U t),
        Continuous (fun z : GalerkinTime × Pt 2 => phaseL2ContinuousVelocity U z.1 z.2) ∧
        (∀ t, periodicVelocityToL2 (phaseL2ContinuousVelocity U t) (hv t)
          (isPeriodic_phaseL2ContinuousVelocity U t) = U t) ∧
        ∀ t x, ‖phaseL2ContinuousVelocity U t x‖ ≤ phaseL2VelocityAbsoluteBound ν phase := by
  obtain ⟨φ, U, hφ, hU, hzero, hreg⟩ :=
    exists_phaseGalerkin_l2_limit_uniform_sobolev_below_two ν hν phase
  refine ⟨φ, U, hφ, hU,
    continuous_phaseL2ContinuousVelocity_slice ν hν phase hφ hU,
    continuous_phaseL2ContinuousVelocity ν hν phase hφ hU, ?_, ?_⟩
  · exact phaseGalerkin_l2_limit_continuousVelocity_identification ν hν phase hφ hU
  · exact norm_phaseL2ContinuousVelocity_le ν hν phase hφ hU

/-- Termwise integration of the genuinely absolutely summable character
series recovers each original integral Fourier coefficient. -/
theorem fc_complexFourierSeries {a : (Fin 2 → ℤ) → ℂ}
    (ha : Summable (fun k => ‖a k‖)) (m : Fin 2 → ℤ) :
    fc (complexFourierSeries a) m = a m := by
  let F := fun (k : Fin 2 → ℤ) (x : Pt 2) =>
    a k * expChar (intVec k) x * expChar (-intVec m) x
  have hi (k) : Integrable (F k) (volume.restrict (cell 2)) := by
    have hc : Continuous (F k) := by
      change Continuous (fun x => a k * expChar (intVec k) x * expChar (-intVec m) x)
      exact (continuous_const.mul (continuous_expChar (intVec k))).mul
        (continuous_expChar (-intVec m))
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have hnorm (k) : (fun x => ‖F k x‖) = fun _ : Pt 2 => ‖a k‖ := by
    funext x
    simp only [F, norm_mul, norm_expChar, mul_one]
  have hs : Summable (fun k => ∫ x in cell 2, ‖F k x‖) := by
    simpa only [hnorm, integral_const, Measure.real, Measure.restrict_apply_univ,
      volume_cell, ENNReal.toReal_one,
      one_smul] using ha
  have he : (fun x => complexFourierSeries a x * expChar (-intVec m) x) =
      fun x => ∑' k, F k x := by
    funext x
    simp only [complexFourierSeries, complexFourierSeriesTerm, F, tsum_mul_right]
  rw [fc, he, ← integral_tsum_of_summable_integral_norm hi hs]
  have hterm (k) : (∫ x in cell 2, F k x) = a k * (if k = m then 1 else 0) := by
    simp only [F, mul_assoc]
    rw [integral_const_mul]
    change a k * fc (expChar (intVec k)) m = _
    rw [fc_expChar]
  simp only [hterm, mul_ite, mul_one, mul_zero, tsum_ite_eq]

/-- The real reconstruction has exactly the original Fourier coefficients
when the coefficients carry the genuine reality symmetry. -/
theorem fc_re_complexFourierSeries {a : (Fin 2 → ℤ) → ℂ}
    (ha : Summable (fun k => ‖a k‖)) (hsym : ∀ k, a (-k) = conj (a k))
    (m : Fin 2 → ℤ) : fc (fun x => ((complexFourierSeries a x).re : ℂ)) m = a m := by
  have he : (fun x => ((complexFourierSeries a x).re : ℂ)) = complexFourierSeries a := by
    funext x
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im]
      exact (complexFourierSeries_real_of_symmetry ha hsym x).symm
  rw [he, fc_complexFourierSeries ha]

end AnomDiss
